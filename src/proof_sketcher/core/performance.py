"""Performance monitoring and optimization for Proof Sketcher.

This module provides comprehensive performance profiling, monitoring, and optimization
capabilities for production use.
"""

import asyncio
import cProfile
import functools
import gc
import io
import logging
import pstats
import time
import tracemalloc
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from threading import Lock
from typing import Any, AsyncGenerator, Awaitable, Callable, Dict, Generator, List, Optional, TypeVar, Union, cast

import psutil

from ..core.exceptions import ProofSketcherError


class PerformanceError(ProofSketcherError):
    """Performance-related errors."""
    pass


class ResourceLimitExceeded(PerformanceError):
    """Resource limit exceeded."""
    pass


class TimeoutError(PerformanceError):
    """Operation timed out."""
    pass


@dataclass
class PerformanceMetric:
    """A single performance metric."""
    name: str
    value: float
    unit: str
    timestamp: float
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class ProfileResult:
    """Results from performance profiling."""
    duration: float
    memory_peak: int
    memory_growth: int
    function_stats: Dict[str, Any]
    call_count: int
    metadata: Dict[str, Any] = field(default_factory=dict)


class PerformanceProfiler:
    """Advanced performance profiler with memory tracking."""
    
    def __init__(self, enable_memory: bool = True, enable_time: bool = True):
        """Initialize profiler.
        
        Args:
            enable_memory: Enable memory profiling
            enable_time: Enable time profiling
        """
        self.enable_memory = enable_memory
        self.enable_time = enable_time
        self.logger = logging.getLogger(__name__)
        
        # Profiling state
        self._profiler: Optional[cProfile.Profile] = None
        self._memory_start: int = 0
        self._time_start: float = 0
        
    @contextmanager
    def profile(self, name: str = "operation") -> Generator[ProfileResult, None, None]:
        """Context manager for profiling operations.
        
        Args:
            name: Name of the operation being profiled
            
        Yields:
            ProfileResult: The profiling results
        """
        # Initialize result container
        result = ProfileResult(
            duration=0.0,
            memory_peak=0,
            memory_growth=0,
            function_stats={},
            call_count=0,
            metadata={"name": name}
        )
        
        # Start profiling
        if self.enable_time:
            self._profiler = cProfile.Profile()
            self._profiler.enable()
            self._time_start = time.perf_counter()
        
        if self.enable_memory:
            if not tracemalloc.is_tracing():
                tracemalloc.start()
            self._memory_start = self._get_memory_usage()
        
        try:
            yield result
        finally:
            # Stop profiling and collect results
            if self.enable_time and self._profiler:
                self._profiler.disable()
                result.duration = time.perf_counter() - self._time_start
                result.function_stats = self._extract_function_stats()
                result.call_count = self._profiler.getstats().__len__()
            
            if self.enable_memory:
                current_memory = self._get_memory_usage()
                result.memory_growth = current_memory - self._memory_start
                
                if tracemalloc.is_tracing():
                    _, peak = tracemalloc.get_traced_memory()
                    result.memory_peak = peak
                    tracemalloc.stop()
    
    def _get_memory_usage(self) -> int:
        """Get current memory usage in bytes."""
        process = psutil.Process()
        return int(process.memory_info().rss)
    
    def _extract_function_stats(self) -> Dict[str, Any]:
        """Extract function statistics from profiler."""
        if not self._profiler:
            return {}
        
        # Capture stats to string buffer
        stats_stream = io.StringIO()
        stats = pstats.Stats(self._profiler, stream=stats_stream)
        stats.sort_stats('cumulative')
        stats.print_stats(10)  # Top 10 functions
        
        # Parse top functions
        stats.sort_stats('cumulative')
        top_functions: List[Dict[str, Any]] = []
        for func, (cc, nc, tt, ct, callers) in stats.stats.items():  # type: ignore[attr-defined]
            if len(top_functions) >= 10:
                break
            top_functions.append({
                "function": f"{func[0]}:{func[1]}({func[2]})",
                "call_count": cc,
                "total_time": tt,
                "cumulative_time": ct,
                "per_call": ct / cc if cc > 0 else 0
            })
        
        return {
            "total_calls": stats.total_calls,  # type: ignore[attr-defined]
            "primitive_calls": stats.prim_calls,  # type: ignore[attr-defined]
            "total_time": stats.total_tt,  # type: ignore[attr-defined]
            "top_functions": top_functions
        }


class ResourceLimiter:
    """Resource management and limiting."""
    
    def __init__(
        self,
        max_memory_mb: int = 2048,
        max_cpu_percent: float = 80.0,
        max_processing_time: int = 3600,
        max_concurrent_jobs: int = 4
    ):
        """Initialize resource limiter.
        
        Args:
            max_memory_mb: Maximum memory usage in MB
            max_cpu_percent: Maximum CPU usage percentage
            max_processing_time: Maximum processing time in seconds
            max_concurrent_jobs: Maximum concurrent jobs
        """
        self.max_memory_mb = max_memory_mb
        self.max_cpu_percent = max_cpu_percent
        self.max_processing_time = max_processing_time
        self.max_concurrent_jobs = max_concurrent_jobs
        
        self.logger = logging.getLogger(__name__)
        self._job_semaphore = asyncio.Semaphore(max_concurrent_jobs)
        self._active_jobs: Dict[str, float] = {}
        self._lock = Lock()
    
    @contextmanager
    def limit_resources(self, job_id: str = "default") -> Generator[None, None, None]:
        """Context manager for resource-limited operations.
        
        Args:
            job_id: Unique identifier for the job
        """
        with self._lock:
            if len(self._active_jobs) >= self.max_concurrent_jobs:
                raise ResourceLimitExceeded(
                    f"Maximum concurrent jobs ({self.max_concurrent_jobs}) exceeded"
                )
            self._active_jobs[job_id] = time.time()
        
        try:
            self._check_memory_limit()
            self._check_cpu_limit()
            yield
        finally:
            with self._lock:
                if job_id in self._active_jobs:
                    duration = time.time() - self._active_jobs[job_id]
                    if duration > self.max_processing_time:
                        self.logger.warning(
                            f"Job {job_id} exceeded time limit: {duration:.1f}s"
                        )
                    del self._active_jobs[job_id]
    
    def _check_memory_limit(self) -> None:
        """Check if memory usage is within limits."""
        process = psutil.Process()
        memory_mb = process.memory_info().rss / 1024 / 1024
        
        if memory_mb > self.max_memory_mb:
            # Try garbage collection first
            gc.collect()
            memory_mb = process.memory_info().rss / 1024 / 1024
            
            if memory_mb > self.max_memory_mb:
                raise ResourceLimitExceeded(
                    f"Memory usage ({memory_mb:.1f}MB) exceeds limit ({self.max_memory_mb}MB)"
                )
    
    def _check_cpu_limit(self) -> None:
        """Check if CPU usage is within limits."""
        cpu_percent = psutil.cpu_percent(interval=0.1)
        if cpu_percent > self.max_cpu_percent:
            self.logger.warning(f"High CPU usage: {cpu_percent:.1f}%")
            # Note: We log but don't raise an exception for CPU limits
            # as they're more of a guideline than a hard limit
    
    async def limit_async_resources(self, job_id: str = "default") -> AsyncGenerator[None, None]:
        """Async context manager for resource-limited operations."""
        async with self._job_semaphore:
            with self.limit_resources(job_id):
                yield


class PerformanceMonitor:
    """Comprehensive performance monitoring system."""
    
    def __init__(self, metrics_retention: int = 1000):
        """Initialize performance monitor.
        
        Args:
            metrics_retention: Number of metrics to retain in memory
        """
        self.metrics_retention = metrics_retention
        self.logger = logging.getLogger(__name__)
        
        # Metrics storage
        self._metrics: Dict[str, deque[PerformanceMetric]] = defaultdict(
            lambda: deque(maxlen=metrics_retention)
        )
        self._counters: Dict[str, int] = defaultdict(int)
        self._timers: Dict[str, float] = {}
        
        # Health status
        self._health_status = "healthy"
        self._health_checks: Dict[str, Callable[[], bool]] = {}
        
        # Lock for thread safety
        self._lock = Lock()
    
    def record_metric(
        self, 
        name: str, 
        value: float, 
        unit: str = "",
        metadata: Optional[Dict[str, Any]] = None
    ) -> None:
        """Record a performance metric.
        
        Args:
            name: Metric name
            value: Metric value
            unit: Unit of measurement
            metadata: Additional metadata
        """
        metric = PerformanceMetric(
            name=name,
            value=value,
            unit=unit,
            timestamp=time.time(),
            metadata=metadata or {}
        )
        
        with self._lock:
            self._metrics[name].append(metric)
    
    def increment_counter(self, name: str, value: int = 1) -> None:
        """Increment a counter metric.
        
        Args:
            name: Counter name
            value: Increment value
        """
        with self._lock:
            self._counters[name] += value
    
    def start_timer(self, name: str) -> None:
        """Start a named timer.
        
        Args:
            name: Timer name
        """
        with self._lock:
            self._timers[name] = time.perf_counter()
    
    def stop_timer(self, name: str) -> float:
        """Stop a named timer and record the duration.
        
        Args:
            name: Timer name
            
        Returns:
            Duration in seconds
        """
        with self._lock:
            if name not in self._timers:
                self.logger.warning(f"Timer '{name}' was not started")
                return 0.0
            
            duration = time.perf_counter() - self._timers[name]
            del self._timers[name]
            
            self.record_metric(f"{name}_duration", duration, "seconds")
            return duration
    
    @contextmanager
    def time_operation(self, name: str) -> Generator[None, None, None]:
        """Context manager for timing operations.
        
        Args:
            name: Operation name
        """
        self.start_timer(name)
        try:
            yield
        finally:
            self.stop_timer(name)
    
    def get_metrics_summary(self) -> Dict[str, Any]:
        """Get summary of all metrics.
        
        Returns:
            Dictionary with metrics summary
        """
        with self._lock:
            summary: Dict[str, Any] = {
                "timestamp": time.time(),
                "metrics": {},
                "counters": dict(self._counters),
                "active_timers": list(self._timers.keys()),
                "health_status": self._health_status
            }
            
            # Summarize metrics
            for name, metric_queue in self._metrics.items():
                if not metric_queue:
                    continue
                
                values = [m.value for m in metric_queue]
                summary["metrics"][name] = {
                    "count": len(values),
                    "min": min(values),
                    "max": max(values),
                    "avg": sum(values) / len(values),
                    "latest": values[-1],
                    "unit": metric_queue[-1].unit
                }
            
            return summary
    
    def register_health_check(self, name: str, check_func: Callable[[], bool]) -> None:
        """Register a health check function.
        
        Args:
            name: Health check name
            check_func: Function that returns True if healthy
        """
        self._health_checks[name] = check_func
    
    def run_health_checks(self) -> Dict[str, bool]:
        """Run all registered health checks.
        
        Returns:
            Dictionary of health check results
        """
        results = {}
        overall_healthy = True
        
        for name, check_func in self._health_checks.items():
            try:
                result = check_func()
                results[name] = result
                if not result:
                    overall_healthy = False
            except Exception as e:
                self.logger.error(f"Health check '{name}' failed: {e}")
                results[name] = False
                overall_healthy = False
        
        self._health_status = "healthy" if overall_healthy else "unhealthy"
        return results


class BatchOptimizer:
    """Optimizer for batch operations."""
    
    def __init__(
        self,
        max_batch_size: int = 10,
        max_concurrent_batches: int = 4,
        batch_timeout: float = 30.0
    ):
        """Initialize batch optimizer.
        
        Args:
            max_batch_size: Maximum items per batch
            max_concurrent_batches: Maximum concurrent batches
            batch_timeout: Timeout for batch operations
        """
        self.max_batch_size = max_batch_size
        self.max_concurrent_batches = max_concurrent_batches
        self.batch_timeout = batch_timeout
        
        self.logger = logging.getLogger(__name__)
    
    async def process_batches(
        self,
        items: List[Any],
        process_func: Callable[[List[Any]], Any],
        progress_callback: Optional[Callable[[int, int], None]] = None
    ) -> List[Any]:
        """Process items in optimized batches.
        
        Args:
            items: Items to process
            process_func: Function to process each batch
            progress_callback: Optional progress callback
            
        Returns:
            List of results
        """
        if not items:
            return []
        
        # Create batches
        batches = [
            items[i:i + self.max_batch_size]
            for i in range(0, len(items), self.max_batch_size)
        ]
        
        results = []
        completed = 0
        
        # Process batches with concurrency limit
        semaphore = asyncio.Semaphore(self.max_concurrent_batches)
        
        async def process_batch(batch: List[Any]) -> List[Any]:
            async with semaphore:
                try:
                    return await asyncio.wait_for(
                        asyncio.get_event_loop().run_in_executor(
                            None, process_func, batch
                        ),
                        timeout=self.batch_timeout
                    )
                except asyncio.TimeoutError:
                    self.logger.error(f"Batch timed out after {self.batch_timeout}s")
                    raise TimeoutError(f"Batch processing timed out")
        
        # Submit all batches
        tasks = [process_batch(batch) for batch in batches]
        
        # Process results as they complete
        for future in asyncio.as_completed(tasks):
            try:
                result = await future
                results.extend(result if isinstance(result, list) else [result])
                completed += 1
                
                if progress_callback:
                    progress_callback(completed, len(batches))
                    
            except Exception as e:
                self.logger.error(f"Batch processing failed: {e}")
                # Continue processing other batches
        
        return results


class ConnectionPool:
    """Connection pool for subprocess operations."""
    
    def __init__(
        self,
        max_connections: int = 5,
        connection_timeout: float = 30.0,
        reuse_connections: bool = True
    ):
        """Initialize connection pool.
        
        Args:
            max_connections: Maximum number of connections
            connection_timeout: Timeout for connections
            reuse_connections: Whether to reuse connections
        """
        self.max_connections = max_connections
        self.connection_timeout = connection_timeout
        self.reuse_connections = reuse_connections
        
        self.logger = logging.getLogger(__name__)
        self._pool = ThreadPoolExecutor(max_workers=max_connections)
        self._active_connections = 0
        self._lock = Lock()
    
    @contextmanager
    def get_connection(self) -> Generator[ThreadPoolExecutor, None, None]:
        """Get a connection from the pool."""
        with self._lock:
            if self._active_connections >= self.max_connections:
                raise ResourceLimitExceeded(
                    f"Maximum connections ({self.max_connections}) exceeded"
                )
            self._active_connections += 1
        
        try:
            yield self._pool
        finally:
            with self._lock:
                self._active_connections -= 1
    
    def submit_task(self, func: Callable[..., Any], *args: Any, **kwargs: Any) -> Any:
        """Submit a task to the connection pool.
        
        Args:
            func: Function to execute
            *args: Positional arguments
            **kwargs: Keyword arguments
            
        Returns:
            Future object
        """
        with self.get_connection() as pool:
            return pool.submit(func, *args, **kwargs)
    
    def shutdown(self, wait: bool = True) -> None:
        """Shutdown the connection pool.
        
        Args:
            wait: Whether to wait for pending tasks
        """
        self._pool.shutdown(wait=wait)


# Decorator for performance monitoring
F = TypeVar('F', bound=Callable[..., Any])

def monitor_performance(
    operation_name: str,
    monitor: Optional[PerformanceMonitor] = None
) -> Callable[[F], F]:
    """Decorator for automatic performance monitoring.
    
    Args:
        operation_name: Name of the operation
        monitor: Performance monitor instance
    """
    def decorator(func: F) -> F:
        @functools.wraps(func)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            perf_monitor = monitor or PerformanceMonitor()
            
            with perf_monitor.time_operation(operation_name):
                perf_monitor.increment_counter(f"{operation_name}_calls")
                try:
                    result = func(*args, **kwargs)
                    perf_monitor.increment_counter(f"{operation_name}_success")
                    return result
                except Exception as e:
                    perf_monitor.increment_counter(f"{operation_name}_error")
                    raise
        
        return cast(F, wrapper)
    return decorator


# Async version of the decorator
AF = TypeVar('AF', bound=Callable[..., Awaitable[Any]])

def monitor_async_performance(
    operation_name: str,
    monitor: Optional[PerformanceMonitor] = None
) -> Callable[[AF], AF]:
    """Decorator for automatic async performance monitoring.
    
    Args:
        operation_name: Name of the operation
        monitor: Performance monitor instance
    """
    def decorator(func: AF) -> AF:
        @functools.wraps(func)
        async def wrapper(*args: Any, **kwargs: Any) -> Any:
            perf_monitor = monitor or PerformanceMonitor()
            
            with perf_monitor.time_operation(operation_name):
                perf_monitor.increment_counter(f"{operation_name}_calls")
                try:
                    result = await func(*args, **kwargs)
                    perf_monitor.increment_counter(f"{operation_name}_success")
                    return result
                except Exception as e:
                    perf_monitor.increment_counter(f"{operation_name}_error")
                    raise
        
        return cast(AF, wrapper)
    return decorator


# Global performance monitor instance
global_monitor = PerformanceMonitor()


def get_performance_report() -> Dict[str, Any]:
    """Get comprehensive performance report.
    
    Returns:
        Dictionary with performance report
    """
    report = {
        "timestamp": time.time(),
        "system": {
            "cpu_percent": psutil.cpu_percent(),
            "memory": {
                "used": psutil.virtual_memory().used,
                "available": psutil.virtual_memory().available,
                "percent": psutil.virtual_memory().percent
            },
            "disk": {
                "used": psutil.disk_usage('/').used,
                "free": psutil.disk_usage('/').free,
                "percent": psutil.disk_usage('/').percent
            }
        },
        "application": global_monitor.get_metrics_summary(),
        "health_checks": global_monitor.run_health_checks()
    }
    
    return report