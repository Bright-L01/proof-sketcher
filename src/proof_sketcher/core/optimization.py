"""Performance optimizations for Proof Sketcher.

This module implements critical path optimizations including batch API calls,
parallel processing, lazy loading, and caching strategies.
"""

import asyncio
import hashlib
import json
import logging
import time
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Union

from .performance import (
    BatchOptimizer,
    ConnectionPool,
    PerformanceMonitor,
    ResourceLimiter,
    global_monitor,
    monitor_performance,
    monitor_async_performance
)
from ..core.exceptions import ProofSketcherError


class OptimizationError(ProofSketcherError):
    """Optimization-related errors."""
    pass


class CacheManager:
    """Advanced caching with TTL and intelligent eviction."""
    
    def __init__(
        self,
        max_size: int = 1000,
        default_ttl: float = 3600.0,  # 1 hour
        cache_dir: Optional[Path] = None
    ):
        """Initialize cache manager.
        
        Args:
            max_size: Maximum number of cache entries
            default_ttl: Default time-to-live in seconds
            cache_dir: Directory for persistent cache
        """
        self.max_size = max_size
        self.default_ttl = default_ttl
        self.cache_dir = cache_dir
        
        # In-memory cache with access tracking
        self._cache: OrderedDict[str, Any] = OrderedDict()
        self._ttl: Dict[str, float] = {}
        self._access_count: Dict[str, int] = {}
        self._hit_count = 0
        self._miss_count = 0
        
        self.logger = logging.getLogger(__name__)
        
        if cache_dir:
            cache_dir.mkdir(parents=True, exist_ok=True)
    
    def _is_expired(self, key: str) -> bool:
        """Check if cache entry is expired."""
        if key not in self._ttl:
            return False
        return time.time() > self._ttl[key]
    
    def _evict_expired(self) -> None:
        """Remove expired entries."""
        current_time = time.time()
        expired_keys = [
            key for key, expiry in self._ttl.items()
            if current_time > expiry
        ]
        
        for key in expired_keys:
            self._remove_entry(key)
    
    def _evict_lru(self) -> None:
        """Evict least recently used entries when cache is full."""
        while len(self._cache) >= self.max_size:
            # Find least accessed entry among oldest entries
            oldest_keys = list(self._cache.keys())[:10]  # Check first 10
            lru_key = min(oldest_keys, key=lambda k: self._access_count.get(k, 0))
            self._remove_entry(lru_key)
    
    def _remove_entry(self, key: str) -> None:
        """Remove cache entry."""
        self._cache.pop(key, None)
        self._ttl.pop(key, None)
        self._access_count.pop(key, None)
    
    def get(self, key: str) -> Optional[Any]:
        """Get value from cache.
        
        Args:
            key: Cache key
            
        Returns:
            Cached value or None if not found/expired
        """
        # Clean expired entries periodically
        if len(self._cache) % 100 == 0:
            self._evict_expired()
        
        if key in self._cache and not self._is_expired(key):
            # Move to end (most recently used)
            value = self._cache.pop(key)
            self._cache[key] = value
            self._access_count[key] = self._access_count.get(key, 0) + 1
            self._hit_count += 1
            
            global_monitor.increment_counter("cache_hits")
            return value
        
        self._miss_count += 1
        global_monitor.increment_counter("cache_misses")
        
        # Try persistent cache
        if self.cache_dir:
            return self._get_persistent(key)
        
        return None
    
    def put(self, key: str, value: Any, ttl: Optional[float] = None) -> None:
        """Put value in cache.
        
        Args:
            key: Cache key
            value: Value to cache
            ttl: Time-to-live in seconds
        """
        # Evict if necessary
        self._evict_expired()
        if len(self._cache) >= self.max_size:
            self._evict_lru()
        
        # Store in memory
        self._cache[key] = value
        self._ttl[key] = time.time() + (ttl or self.default_ttl)
        self._access_count[key] = 1
        
        global_monitor.increment_counter("cache_puts")
        
        # Store persistently if configured
        if self.cache_dir:
            self._put_persistent(key, value, ttl)
    
    def _get_persistent(self, key: str) -> Optional[Any]:
        """Get from persistent cache."""
        try:
            cache_file = self.cache_dir / f"{hashlib.md5(key.encode(), usedforsecurity=False).hexdigest()}.json"
            if not cache_file.exists():
                return None
            
            with open(cache_file, 'r') as f:
                data = json.load(f)
            
            # Check TTL
            if time.time() > data.get('expiry', 0):
                cache_file.unlink(missing_ok=True)
                return None
            
            # Move to memory cache
            self._cache[key] = data['value']
            self._ttl[key] = data['expiry']
            return data['value']
            
        except Exception as e:
            self.logger.warning(f"Persistent cache read failed: {e}")
            return None
    
    def _put_persistent(self, key: str, value: Any, ttl: Optional[float]) -> None:
        """Put to persistent cache."""
        try:
            cache_file = self.cache_dir / f"{hashlib.md5(key.encode(), usedforsecurity=False).hexdigest()}.json"
            data = {
                'key': key,
                'value': value,
                'expiry': time.time() + (ttl or self.default_ttl),
                'created': time.time()
            }
            
            with open(cache_file, 'w') as f:
                json.dump(data, f, default=str)
                
        except Exception as e:
            self.logger.warning(f"Persistent cache write failed: {e}")
    
    def invalidate(self, key: str) -> bool:
        """Invalidate cache entry.
        
        Args:
            key: Cache key
            
        Returns:
            True if entry was found and removed
        """
        found = key in self._cache
        self._remove_entry(key)
        
        # Remove from persistent cache
        if self.cache_dir:
            cache_file = self.cache_dir / f"{hashlib.md5(key.encode(), usedforsecurity=False).hexdigest()}.json"
            cache_file.unlink(missing_ok=True)
        
        return found
    
    def clear(self) -> None:
        """Clear all cache entries."""
        self._cache.clear()
        self._ttl.clear()
        self._access_count.clear()
        
        # Clear persistent cache
        if self.cache_dir:
            for cache_file in self.cache_dir.glob("*.json"):
                cache_file.unlink(missing_ok=True)
    
    def get_stats(self) -> Dict[str, Any]:
        """Get cache statistics.
        
        Returns:
            Dictionary with cache statistics
        """
        total_requests = self._hit_count + self._miss_count
        hit_rate = self._hit_count / total_requests if total_requests > 0 else 0
        
        return {
            "size": len(self._cache),
            "max_size": self.max_size,
            "hit_count": self._hit_count,
            "miss_count": self._miss_count,
            "hit_rate": hit_rate,
            "total_requests": total_requests,
            "expired_entries": sum(1 for key in self._cache if self._is_expired(key))
        }


class LazyLoader:
    """Lazy loading system for templates and resources."""
    
    def __init__(self, cache_manager: Optional[CacheManager] = None):
        """Initialize lazy loader.
        
        Args:
            cache_manager: Cache manager for loaded resources
        """
        self.cache = cache_manager or CacheManager()
        self.logger = logging.getLogger(__name__)
        
        # Registry of lazy-loadable resources
        self._loaders: Dict[str, Any] = {}
        self._loading: Set[str] = set()  # Prevent circular loading
    
    def register_loader(self, name: str, loader_func: Any) -> None:
        """Register a lazy loader function.
        
        Args:
            name: Resource name
            loader_func: Function to load the resource
        """
        self._loaders[name] = loader_func
    
    @monitor_performance("lazy_load")
    def load(self, name: str, *args, **kwargs) -> Any:
        """Lazy load a resource.
        
        Args:
            name: Resource name
            *args: Arguments for loader function
            **kwargs: Keyword arguments for loader function
            
        Returns:
            Loaded resource
        """
        # Create cache key from name and arguments
        cache_key = f"{name}:{hash((args, frozenset(kwargs.items())))}"
        
        # Check cache first
        cached_result = self.cache.get(cache_key)
        if cached_result is not None:
            return cached_result
        
        # Prevent circular loading
        if name in self._loading:
            raise OptimizationError(f"Circular loading detected for '{name}'")
        
        if name not in self._loaders:
            raise OptimizationError(f"No loader registered for '{name}'")
        
        try:
            self._loading.add(name)
            self.logger.debug(f"Lazy loading '{name}'")
            
            loader_func = self._loaders[name]
            result = loader_func(*args, **kwargs)
            
            # Cache the result
            self.cache.put(cache_key, result)
            
            return result
            
        finally:
            self._loading.discard(name)


class APIBatcher:
    """Batch API calls for efficiency."""
    
    def __init__(
        self,
        batch_size: int = 5,
        batch_timeout: float = 2.0,
        max_retries: int = 3
    ):
        """Initialize API batcher.
        
        Args:
            batch_size: Maximum requests per batch
            batch_timeout: Maximum time to wait for batch to fill
            max_retries: Maximum retry attempts
        """
        self.batch_size = batch_size
        self.batch_timeout = batch_timeout
        self.max_retries = max_retries
        
        self.logger = logging.getLogger(__name__)
        
        # Batching state
        self._pending_requests: List[Dict[str, Any]] = []
        self._batch_futures: List[asyncio.Future] = []
        self._batch_timer: Optional[asyncio.Handle] = None
    
    async def add_request(
        self,
        request_data: Dict[str, Any],
        api_func: Any,
        *args,
        **kwargs
    ) -> Any:
        """Add a request to the batch.
        
        Args:
            request_data: Data for the request
            api_func: API function to call
            *args: Arguments for API function
            **kwargs: Keyword arguments for API function
            
        Returns:
            Future that will resolve to the API response
        """
        # Create future for this request
        future = asyncio.Future()
        
        request = {
            'data': request_data,
            'func': api_func,
            'args': args,
            'kwargs': kwargs,
            'future': future,
            'retry_count': 0
        }
        
        self._pending_requests.append(request)
        self._batch_futures.append(future)
        
        # Start batch timer if not already running
        if self._batch_timer is None:
            self._batch_timer = asyncio.get_event_loop().call_later(
                self.batch_timeout,
                lambda: asyncio.create_task(self._process_batch())
            )
        
        # Process batch if it's full
        if len(self._pending_requests) >= self.batch_size:
            if self._batch_timer:
                self._batch_timer.cancel()
                self._batch_timer = None
            await self._process_batch()
        
        return await future
    
    async def _process_batch(self) -> None:
        """Process the current batch of requests."""
        if not self._pending_requests:
            return
        
        batch = self._pending_requests.copy()
        self._pending_requests.clear()
        self._batch_timer = None
        
        self.logger.debug(f"Processing batch of {len(batch)} requests")
        
        # Group requests by function for efficiency
        function_groups: Dict[str, List[Dict[str, Any]]] = {}
        for request in batch:
            func_key = str(request['func'])
            if func_key not in function_groups:
                function_groups[func_key] = []
            function_groups[func_key].append(request)
        
        # Process each function group
        for func_key, requests in function_groups.items():
            await self._process_function_group(requests)
    
    async def _process_function_group(self, requests: List[Dict[str, Any]]) -> None:
        """Process a group of requests for the same function."""
        # Try to batch the actual API calls
        try:
            # Check if the function supports batching
            first_request = requests[0]
            api_func = first_request['func']
            
            if hasattr(api_func, 'batch_call'):
                # Function supports native batching
                batch_data = [req['data'] for req in requests]
                results = await api_func.batch_call(batch_data)
                
                # Distribute results
                for request, result in zip(requests, results):
                    request['future'].set_result(result)
            else:
                # Fall back to parallel individual calls
                tasks = []
                for request in requests:
                    task = asyncio.create_task(
                        self._make_individual_call(request)
                    )
                    tasks.append(task)
                
                await asyncio.gather(*tasks, return_exceptions=True)
                
        except Exception as e:
            self.logger.error(f"Batch processing failed: {e}")
            # Set exception for all requests in the group
            for request in requests:
                if not request['future'].done():
                    request['future'].set_exception(e)
    
    async def _make_individual_call(self, request: Dict[str, Any]) -> None:
        """Make an individual API call with retry logic."""
        for attempt in range(self.max_retries + 1):
            try:
                api_func = request['func']
                args = request['args']
                kwargs = request['kwargs']
                
                result = await api_func(request['data'], *args, **kwargs)
                request['future'].set_result(result)
                return
                
            except Exception as e:
                request['retry_count'] += 1
                if attempt < self.max_retries:
                    delay = 2 ** attempt  # Exponential backoff
                    await asyncio.sleep(delay)
                    continue
                else:
                    request['future'].set_exception(e)
                    break


class ParallelExporter:
    """Parallel export processing with optimization."""
    
    def __init__(
        self,
        max_workers: int = 4,
        resource_limiter: Optional[ResourceLimiter] = None
    ):
        """Initialize parallel exporter.
        
        Args:
            max_workers: Maximum worker threads
            resource_limiter: Resource limiter instance
        """
        self.max_workers = max_workers
        self.resource_limiter = resource_limiter or ResourceLimiter()
        
        self.logger = logging.getLogger(__name__)
        self._executor = ThreadPoolExecutor(max_workers=max_workers)
    
    @monitor_async_performance("parallel_export")
    async def export_parallel(
        self,
        export_tasks: List[Tuple[Any, Path, str]],  # (data, path, format)
        progress_callback: Optional[Any] = None
    ) -> List[Dict[str, Any]]:
        """Export multiple items in parallel.
        
        Args:
            export_tasks: List of (data, output_path, format) tuples
            progress_callback: Optional progress callback
            
        Returns:
            List of export results
        """
        if not export_tasks:
            return []
        
        results = []
        completed = 0
        
        # Create semaphore for resource limiting
        semaphore = asyncio.Semaphore(self.max_workers)
        
        async def export_single(task_data, output_path, format_type):
            async with semaphore:
                with self.resource_limiter.limit_resources(f"export_{id(task_data)}"):
                    try:
                        # Import here to avoid circular imports
                        from ..exporter.html import HTMLExporter
                        from ..exporter.markdown import MarkdownExporter
                        
                        if format_type.lower() == 'html':
                            exporter = HTMLExporter()
                        elif format_type.lower() == 'markdown':
                            exporter = MarkdownExporter()
                        else:
                            raise OptimizationError(f"Unsupported format: {format_type}")
                        
                        # Run export in thread pool to avoid blocking
                        loop = asyncio.get_event_loop()
                        await loop.run_in_executor(
                            self._executor,
                            exporter.export_single,
                            task_data,
                            output_path
                        )
                        
                        return {
                            'success': True,
                            'path': str(output_path),
                            'format': format_type,
                            'size': output_path.stat().st_size if output_path.exists() else 0
                        }
                        
                    except Exception as e:
                        self.logger.error(f"Export failed for {output_path}: {e}")
                        return {
                            'success': False,
                            'path': str(output_path),
                            'format': format_type,
                            'error': str(e)
                        }
        
        # Submit all export tasks
        tasks = [
            export_single(data, path, fmt)
            for data, path, fmt in export_tasks
        ]
        
        # Process results as they complete
        for future in asyncio.as_completed(tasks):
            try:
                result = await future
                results.append(result)
                completed += 1
                
                if progress_callback:
                    progress_callback(completed, len(export_tasks))
                    
                global_monitor.increment_counter("exports_completed")
                if result['success']:
                    global_monitor.increment_counter("exports_success")
                else:
                    global_monitor.increment_counter("exports_failed")
                    
            except Exception as e:
                self.logger.error(f"Export task failed: {e}")
                results.append({
                    'success': False,
                    'error': str(e)
                })
        
        return results
    
    def shutdown(self, wait: bool = True):
        """Shutdown the parallel exporter.
        
        Args:
            wait: Whether to wait for pending tasks
        """
        self._executor.shutdown(wait=wait)


# Global optimization instances
cache_manager = CacheManager()
lazy_loader = LazyLoader(cache_manager)
api_batcher = APIBatcher()


def optimize_batch_processor():
    """Apply optimizations to batch processor."""
    # This function will be called to optimize the existing batch processor
    # with the new performance features
    from ..core.batch_processor import BatchProcessor
    
    # Monkey patch optimizations
    original_process = BatchProcessor.process_directory
    
    @monitor_async_performance("optimized_batch_process")
    async def optimized_process(self, *args, **kwargs):
        """Optimized version of process_directory."""
        with global_monitor.time_operation("batch_directory_processing"):
            return await original_process(self, *args, **kwargs)
    
    BatchProcessor.process_directory = optimized_process
    
    # Add caching to theorem processing
    original_process_theorem = BatchProcessor._process_single_theorem
    
    def cached_process_theorem(self, theorem, *args, **kwargs):
        """Cached version of theorem processing."""
        # Create cache key from theorem content
        cache_key = f"theorem:{hashlib.md5(str(theorem).encode(), usedforsecurity=False).hexdigest()}"
        
        # Check cache first
        cached_result = cache_manager.get(cache_key)
        if cached_result is not None:
            global_monitor.increment_counter("theorem_cache_hits")
            return cached_result
        
        # Process theorem
        result = original_process_theorem(self, theorem, *args, **kwargs)
        
        # Cache result
        cache_manager.put(cache_key, result, ttl=7200)  # 2 hours
        global_monitor.increment_counter("theorem_cache_misses")
        
        return result
    
    BatchProcessor._process_single_theorem = cached_process_theorem


def get_optimization_stats() -> Dict[str, Any]:
    """Get comprehensive optimization statistics.
    
    Returns:
        Dictionary with optimization statistics
    """
    return {
        "cache": cache_manager.get_stats(),
        "performance": global_monitor.get_metrics_summary(),
        "timestamp": time.time()
    }