"""
Performance optimization utilities - Milestone 3.2.1

This module provides performance optimizations including:
- Parallel processing for CPU-intensive tasks
- Batch API call optimization
- Memory-efficient streaming
- Intelligent workload distribution
- Resource pooling and reuse
"""

import asyncio
import functools
import logging
import multiprocessing
import time
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor, as_completed
from typing import Any, Dict, List, Optional, Callable, Union, Tuple
from dataclasses import dataclass
import threading
from pathlib import Path
import queue

from .smart_cache import SmartCache, cached
from ..generator.models import ProofSketch
from ..parser.models import TheoremInfo
from ..exporter.models import ExportFormat, ExportOptions


@dataclass
class BatchConfig:
    """Configuration for batch operations."""
    batch_size: int = 10
    max_concurrent: int = 4
    timeout_seconds: int = 300
    retry_attempts: int = 3
    use_caching: bool = True
    memory_limit_mb: int = 1000


@dataclass
class WorkloadMetrics:
    """Metrics for workload performance tracking."""
    total_items: int
    processed_items: int
    failed_items: int
    total_time: float
    avg_time_per_item: float
    throughput_per_second: float
    memory_peak_mb: float
    cache_hit_rate: float


class ResourcePool:
    """Pool of reusable resources to avoid recreation overhead."""
    
    def __init__(self, factory: Callable, max_size: int = 10):
        """Initialize resource pool.
        
        Args:
            factory: Function to create new resources
            max_size: Maximum pool size
        """
        self.factory = factory
        self.max_size = max_size
        self.pool = queue.Queue(maxsize=max_size)
        self.created_count = 0
        self.lock = threading.Lock()
    
    def acquire(self):
        """Acquire resource from pool."""
        try:
            # Try to get existing resource
            return self.pool.get_nowait()
        except queue.Empty:
            # Create new resource if under limit
            with self.lock:
                if self.created_count < self.max_size:
                    self.created_count += 1
                    return self.factory()
                else:
                    # Wait for available resource
                    return self.pool.get(timeout=30)
    
    def release(self, resource):
        """Release resource back to pool."""
        try:
            self.pool.put_nowait(resource)
        except queue.Full:
            # Pool is full, discard resource
            pass


class PerformanceOptimizer:
    """Main performance optimization coordinator."""
    
    def __init__(self, cache: Optional[SmartCache] = None):
        """Initialize performance optimizer.
        
        Args:
            cache: Cache instance for optimization
        """
        self.cache = cache or SmartCache()
        self.logger = logging.getLogger(__name__)
        
        # Resource pools
        self.parser_pool = ResourcePool(
            lambda: self._create_parser(),
            max_size=multiprocessing.cpu_count()
        )
        self.generator_pool = ResourcePool(
            lambda: self._create_generator(),
            max_size=4  # Limited for API rate limiting
        )
        
        # Performance tracking
        self.metrics = {}
        self.metrics_lock = threading.Lock()
    
    def _create_parser(self):
        """Create parser instance for pool."""
        from ..parser.lean_parser import LeanParser
        return LeanParser()
    
    def _create_generator(self):
        """Create generator instance for pool."""
        from ..generator.offline import OfflineGenerator
        return OfflineGenerator()
    
    @staticmethod
    @functools.lru_cache(maxsize=10000)
    def cached_latex_conversion(lean_expr: str) -> str:
        """Cache LaTeX conversions with LRU cache.
        
        Args:
            lean_expr: Lean mathematical expression
            
        Returns:
            LaTeX-formatted string
        """
        from ..parser.mathlib_notation import MathlibNotationHandler
        handler = MathlibNotationHandler()
        return handler.convert_to_latex(lean_expr)
    
    @staticmethod
    @functools.lru_cache(maxsize=5000)
    def cached_html_conversion(lean_expr: str) -> str:
        """Cache HTML conversions with LRU cache."""
        from ..parser.mathlib_notation import MathlibNotationHandler
        handler = MathlibNotationHandler()
        return handler.convert_to_html(lean_expr)
    
    async def parallel_export(
        self,
        theorem: TheoremInfo,
        sketch: ProofSketch,
        animation_path: Optional[Path],
        formats: List[str],
        output_dir: Path,
        config: BatchConfig = None
    ) -> Dict[str, Any]:
        """Export theorem to multiple formats in parallel.
        
        Args:
            theorem: Theorem to export
            sketch: Generated proof sketch
            animation_path: Path to animation (optional)
            formats: List of export formats
            output_dir: Output directory
            config: Batch configuration
            
        Returns:
            Export results for each format
        """
        config = config or BatchConfig()
        
        # Create export tasks
        tasks = []
        
        async def export_format(format_name: str, exporter_class: type):
            """Export to specific format."""
            try:
                # Check cache first
                cache_key = self.cache.generate_export_key(sketch, format_name)
                cached_result = await self.cache.get(cache_key)
                
                if cached_result and config.use_caching:
                    self.logger.debug(f"Cache hit for {format_name} export")
                    return format_name, cached_result
                
                # Create exporter
                options = ExportOptions(
                    output_dir=output_dir / format_name,
                    create_subdirs=True
                )
                exporter = exporter_class(options)
                
                # Export in thread to avoid blocking
                result = await asyncio.to_thread(
                    self._export_with_timeout,
                    exporter, theorem, sketch, animation_path, config.timeout_seconds
                )
                
                # Cache result
                if config.use_caching:
                    await self.cache.set(cache_key, result, ttl=86400)
                
                return format_name, result
                
            except Exception as e:
                self.logger.error(f"Export failed for {format_name}: {e}")
                return format_name, {'error': str(e)}
        
        # Map formats to exporter classes
        format_map = {
            'html': self._get_html_exporter,
            'markdown': self._get_markdown_exporter,
            'pdf': self._get_pdf_exporter,
            'jupyter': self._get_jupyter_exporter
        }
        
        # Create tasks for requested formats
        for fmt in formats:
            if fmt in format_map:
                exporter_class = format_map[fmt]()
                task = export_format(fmt, exporter_class)
                tasks.append(task)
        
        # Execute exports in parallel with concurrency limit
        semaphore = asyncio.Semaphore(config.max_concurrent)
        
        async def bounded_task(task):
            async with semaphore:
                return await task
        
        bounded_tasks = [bounded_task(task) for task in tasks]
        results = await asyncio.gather(*bounded_tasks, return_exceptions=True)
        
        # Process results
        export_results = {}
        for result in results:
            if isinstance(result, Exception):
                self.logger.error(f"Export task failed: {result}")
                continue
            
            format_name, format_result = result
            export_results[format_name] = format_result
        
        return export_results
    
    def _export_with_timeout(self, exporter, theorem, sketch, animation_path, timeout):
        """Export with timeout protection."""
        import signal
        
        def timeout_handler(signum, frame):
            raise TimeoutError(f"Export timed out after {timeout}s")
        
        # Set timeout
        old_handler = signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(timeout)
        
        try:
            # Create export context
            from ..exporter.models import ExportContext
            context = ExportContext(
                format=exporter.format,
                output_dir=exporter.options.output_dir,
                sketches=[sketch]
            )
            
            return exporter.export_single(sketch, context)
        finally:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old_handler)
    
    def _get_html_exporter(self):
        """Get HTML exporter class."""
        from ..exporter.html import HTMLExporter
        return HTMLExporter
    
    def _get_markdown_exporter(self):
        """Get Markdown exporter class."""
        from ..exporter.markdown import MarkdownExporter
        return MarkdownExporter
    
    def _get_pdf_exporter(self):
        """Get PDF exporter class."""
        from ..exporter.pdf import PDFExporter
        return PDFExporter
    
    def _get_jupyter_exporter(self):
        """Get Jupyter exporter class."""
        from ..exporter.jupyter import JupyterExporter
        return JupyterExporter
    
    def batch_api_calls(
        self,
        items: List[Any],
        batch_size: int = 10,
        delay_seconds: float = 1.0
    ) -> List[List[Any]]:
        """Batch items for API calls to reduce overhead.
        
        Args:
            items: Items to batch
            batch_size: Size of each batch
            delay_seconds: Delay between batches
            
        Returns:
            List of batches
        """
        batches = []
        
        for i in range(0, len(items), batch_size):
            batch = items[i:i + batch_size]
            batches.append(batch)
        
        self.logger.info(f"Created {len(batches)} batches from {len(items)} items")
        return batches
    
    async def process_theorems_parallel(
        self,
        theorems: List[TheoremInfo],
        config: BatchConfig = None
    ) -> Tuple[List[ProofSketch], WorkloadMetrics]:
        """Process theorems in parallel with optimizations.
        
        Args:
            theorems: List of theorems to process
            config: Batch configuration
            
        Returns:
            Tuple of (processed sketches, metrics)
        """
        config = config or BatchConfig()
        start_time = time.time()
        
        processed_sketches = []
        failed_count = 0
        cache_hits = 0
        
        # Create batches
        batches = self.batch_api_calls(theorems, config.batch_size)
        
        # Process batches with concurrency control
        semaphore = asyncio.Semaphore(config.max_concurrent)
        
        async def process_batch(batch: List[TheoremInfo]) -> List[ProofSketch]:
            """Process a batch of theorems."""
            async with semaphore:
                batch_results = []
                
                for theorem in batch:
                    try:
                        # Check cache first
                        cache_key = self.cache.generate_key(theorem, "sketch")
                        cached_sketch = await self.cache.get(cache_key)
                        
                        if cached_sketch and config.use_caching:
                            batch_results.append(cached_sketch)
                            nonlocal cache_hits
                            cache_hits += 1
                            continue
                        
                        # Process theorem
                        sketch = await self._process_theorem_optimized(theorem, config)
                        
                        if sketch:
                            batch_results.append(sketch)
                            
                            # Cache result
                            if config.use_caching:
                                await self.cache.set(cache_key, sketch, ttl=86400)
                        else:
                            nonlocal failed_count
                            failed_count += 1
                            
                    except Exception as e:
                        self.logger.error(f"Failed to process {theorem.name}: {e}")
                        failed_count += 1
                
                return batch_results
        
        # Execute all batches
        batch_tasks = [process_batch(batch) for batch in batches]
        batch_results = await asyncio.gather(*batch_tasks, return_exceptions=True)
        
        # Collect results
        for result in batch_results:
            if isinstance(result, Exception):
                self.logger.error(f"Batch processing failed: {result}")
                failed_count += len(batches[0])  # Estimate
                continue
            
            processed_sketches.extend(result)
        
        # Calculate metrics
        total_time = time.time() - start_time
        total_items = len(theorems)
        processed_items = len(processed_sketches)
        
        metrics = WorkloadMetrics(
            total_items=total_items,
            processed_items=processed_items,
            failed_items=failed_count,
            total_time=total_time,
            avg_time_per_item=total_time / max(processed_items, 1),
            throughput_per_second=processed_items / total_time if total_time > 0 else 0,
            memory_peak_mb=0,  # Would need psutil to measure
            cache_hit_rate=(cache_hits / total_items) * 100 if total_items > 0 else 0
        )
        
        return processed_sketches, metrics
    
    async def _process_theorem_optimized(
        self,
        theorem: TheoremInfo,
        config: BatchConfig
    ) -> Optional[ProofSketch]:
        """Process single theorem with optimizations."""
        # Get generator from pool
        generator = self.generator_pool.acquire()
        
        try:
            # Process with timeout
            sketch = await asyncio.wait_for(
                asyncio.to_thread(generator.generate_proof_sketch, theorem),
                timeout=config.timeout_seconds
            )
            return sketch
            
        except asyncio.TimeoutError:
            self.logger.warning(f"Theorem processing timed out: {theorem.name}")
            return None
        except Exception as e:
            self.logger.error(f"Theorem processing failed: {theorem.name}: {e}")
            return None
        finally:
            # Return generator to pool
            self.generator_pool.release(generator)
    
    def optimize_memory_usage(self, target_mb: int = 500):
        """Optimize memory usage by clearing caches and pools."""
        self.logger.info(f"Optimizing memory usage (target: {target_mb}MB)")
        
        # Clear LRU caches
        self.cached_latex_conversion.cache_clear()
        self.cached_html_conversion.cache_clear()
        
        # Clear local cache
        self.cache.local_cache.clear()
        
        # Reset resource pools
        self.parser_pool = ResourcePool(lambda: self._create_parser())
        self.generator_pool = ResourcePool(lambda: self._create_generator(), max_size=4)
        
        self.logger.info("Memory optimization complete")
    
    def get_performance_metrics(self) -> Dict[str, Any]:
        """Get current performance metrics."""
        cache_stats = self.cache.get_stats()
        
        return {
            'cache_performance': cache_stats,
            'latex_cache_size': self.cached_latex_conversion.cache_info().currsize,
            'html_cache_size': self.cached_html_conversion.cache_info().currsize,
            'parser_pool_size': self.parser_pool.created_count,
            'generator_pool_size': self.generator_pool.created_count,
            'custom_metrics': self.metrics
        }
    
    def record_metric(self, name: str, value: Any):
        """Record custom performance metric."""
        with self.metrics_lock:
            self.metrics[name] = {
                'value': value,
                'timestamp': time.time()
            }


# Utility functions for common optimization patterns

def optimize_for_batch_processing():
    """Decorator to optimize function for batch processing."""
    def decorator(func):
        @functools.wraps(func)
        async def wrapper(*args, **kwargs):
            # Enable aggressive caching for batch operations
            kwargs.setdefault('use_cache', True)
            kwargs.setdefault('cache_ttl', 86400)  # 24 hours
            
            return await func(*args, **kwargs)
        return wrapper
    return decorator


def memory_efficient(max_memory_mb: int = 1000):
    """Decorator to enforce memory limits."""
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            import psutil
            process = psutil.Process()
            
            initial_memory = process.memory_info().rss / 1024 / 1024
            
            try:
                result = func(*args, **kwargs)
                
                current_memory = process.memory_info().rss / 1024 / 1024
                memory_used = current_memory - initial_memory
                
                if memory_used > max_memory_mb:
                    logging.warning(
                        f"Function {func.__name__} used {memory_used:.1f}MB "
                        f"(limit: {max_memory_mb}MB)"
                    )
                
                return result
                
            except MemoryError:
                logging.error(f"Function {func.__name__} exceeded memory limit")
                raise
        
        return wrapper
    return decorator


# Global optimizer instance
_global_optimizer: Optional[PerformanceOptimizer] = None


def get_optimizer() -> PerformanceOptimizer:
    """Get global performance optimizer instance."""
    global _global_optimizer
    if _global_optimizer is None:
        _global_optimizer = PerformanceOptimizer()
    return _global_optimizer