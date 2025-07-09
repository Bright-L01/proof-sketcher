"""
Resource limits and safety controls - Milestone 3.2.1

This module provides resource management and safety controls including:
- Memory usage limits
- Execution timeouts
- CPU usage monitoring
- Animation complexity limits
- Graceful degradation strategies
"""

import gc
import logging
import os
import resource
import signal
import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timedelta
from typing import Any, Callable, Dict, Optional, Union

import psutil


@dataclass
class ResourceLimits:
    """Resource limit configuration."""

    max_memory_mb: int = 1000
    max_execution_seconds: int = 300
    max_cpu_percent: float = 80.0
    max_animation_duration: int = 720  # 12 minutes
    max_proof_steps: int = 100
    max_file_size_mb: int = 50
    emergency_cleanup_threshold_mb: int = 1500


@dataclass
class ResourceUsage:
    """Current resource usage metrics."""

    memory_mb: float
    cpu_percent: float
    execution_time: float
    active_threads: int
    open_files: int
    timestamp: datetime


class ResourceMonitor:
    """Monitor resource usage in real-time."""

    def __init__(self, check_interval: float = 1.0):
        """Initialize resource monitor.

        Args:
            check_interval: How often to check resources (seconds)
        """
        self.check_interval = check_interval
        self.process = psutil.Process()
        self.monitoring = False
        self.monitor_thread: Optional[threading.Thread] = None
        self.usage_history: list[ResourceUsage] = []
        self.max_history = 300  # Keep 5 minutes at 1s intervals
        self.logger = logging.getLogger(__name__)

        # Callbacks for threshold violations
        self.memory_callback: Optional[Callable] = None
        self.cpu_callback: Optional[Callable] = None

    def start_monitoring(self, limits: ResourceLimits):
        """Start resource monitoring thread."""
        if self.monitoring:
            return

        self.monitoring = True
        self.limits = limits
        self.monitor_thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self.monitor_thread.start()
        self.logger.info("Resource monitoring started")

    def stop_monitoring(self):
        """Stop resource monitoring."""
        self.monitoring = False
        if self.monitor_thread:
            self.monitor_thread.join(timeout=2.0)
        self.logger.info("Resource monitoring stopped")

    def _monitor_loop(self):
        """Main monitoring loop."""
        while self.monitoring:
            try:
                usage = self._collect_usage()
                self.usage_history.append(usage)

                # Keep history size manageable
                if len(self.usage_history) > self.max_history:
                    self.usage_history.pop(0)

                # Check limits
                self._check_limits(usage)

                time.sleep(self.check_interval)

            except Exception as e:
                self.logger.warning(f"Resource monitoring error: {e}")
                time.sleep(self.check_interval)

    def _collect_usage(self) -> ResourceUsage:
        """Collect current resource usage."""
        memory_info = self.process.memory_info()
        memory_mb = memory_info.rss / 1024 / 1024

        cpu_percent = self.process.cpu_percent()

        # Get thread count
        try:
            active_threads = self.process.num_threads()
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            active_threads = threading.active_count()

        # Get open files count
        try:
            open_files = len(self.process.open_files())
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            open_files = 0

        return ResourceUsage(
            memory_mb=memory_mb,
            cpu_percent=cpu_percent,
            execution_time=time.time(),
            active_threads=active_threads,
            open_files=open_files,
            timestamp=datetime.now(),
        )

    def _check_limits(self, usage: ResourceUsage):
        """Check if usage exceeds limits."""
        # Memory check
        if usage.memory_mb > self.limits.max_memory_mb:
            self.logger.warning(
                f"Memory limit exceeded: {usage.memory_mb:.1f}MB > {self.limits.max_memory_mb}MB"
            )
            if self.memory_callback:
                try:
                    self.memory_callback(usage)
                except Exception as e:
                    self.logger.error(f"Memory callback failed: {e}")

        # Emergency memory cleanup
        if usage.memory_mb > self.limits.emergency_cleanup_threshold_mb:
            self.logger.critical(
                f"Emergency memory cleanup triggered at {usage.memory_mb:.1f}MB"
            )
            self._emergency_cleanup()

        # CPU check
        if usage.cpu_percent > self.limits.max_cpu_percent:
            self.logger.warning(
                f"CPU limit exceeded: {usage.cpu_percent:.1f}% > {self.limits.max_cpu_percent}%"
            )
            if self.cpu_callback:
                try:
                    self.cpu_callback(usage)
                except Exception as e:
                    self.logger.error(f"CPU callback failed: {e}")

    def _emergency_cleanup(self):
        """Perform emergency memory cleanup."""
        # Force garbage collection
        gc.collect()

        # Clear any global caches
        try:
            from .performance import get_optimizer

            optimizer = get_optimizer()
            optimizer.optimize_memory_usage(target_mb=500)
        except Exception as e:
            self.logger.error(f"Optimizer cleanup failed: {e}")

    def get_current_usage(self) -> ResourceUsage:
        """Get current resource usage."""
        return self._collect_usage()

    def get_peak_usage(self, window_minutes: int = 5) -> ResourceUsage:
        """Get peak usage in time window."""
        if not self.usage_history:
            return self.get_current_usage()

        cutoff_time = datetime.now() - timedelta(minutes=window_minutes)
        recent_usage = [u for u in self.usage_history if u.timestamp >= cutoff_time]

        if not recent_usage:
            return self.usage_history[-1]

        # Find peak memory usage
        peak_memory = max(recent_usage, key=lambda u: u.memory_mb)
        return peak_memory


class ResourceLimiter:
    """Enforce resource limits on operations."""

    def __init__(self, limits: ResourceLimits = None):
        """Initialize resource limiter.

        Args:
            limits: Resource limits configuration
        """
        self.limits = limits or ResourceLimits()
        self.monitor = ResourceMonitor()
        self.logger = logging.getLogger(__name__)

    @contextmanager
    def limit_memory(self, max_mb: int):
        """Context manager to limit memory usage.

        Args:
            max_mb: Maximum memory in MB
        """
        max_bytes = max_mb * 1024 * 1024

        # Set soft limit (process can exceed but will get warnings)
        try:
            soft, hard = resource.getrlimit(resource.RLIMIT_AS)
            resource.setrlimit(resource.RLIMIT_AS, (max_bytes, hard))

            self.logger.debug(f"Memory limit set to {max_mb}MB")

            try:
                yield
            finally:
                # Restore original limit
                resource.setrlimit(resource.RLIMIT_AS, (soft, hard))

        except (ValueError, OSError) as e:
            # Platform doesn't support memory limits or insufficient permissions
            self.logger.warning(f"Could not set memory limit: {e}")
            yield

    @contextmanager
    def timeout(self, seconds: int):
        """Context manager for operation timeout.

        Args:
            seconds: Timeout in seconds
        """

        def timeout_handler(signum, frame):
            raise TimeoutError(f"Operation timed out after {seconds}s")

        # Set alarm (Unix only)
        if hasattr(signal, "SIGALRM"):
            old_handler = signal.signal(signal.SIGALRM, timeout_handler)
            signal.alarm(seconds)

            try:
                yield
            finally:
                signal.alarm(0)
                signal.signal(signal.SIGALRM, old_handler)
        else:
            # Windows fallback - no signal support
            self.logger.warning("Timeout not supported on this platform")
            yield

    @contextmanager
    def resource_monitoring(self):
        """Context manager for automatic resource monitoring."""
        self.monitor.start_monitoring(self.limits)

        try:
            yield self.monitor
        finally:
            self.monitor.stop_monitoring()

    def limit_animation_complexity(self, theorem: Dict[str, Any]) -> Dict[str, Any]:
        """Limit animation complexity based on proof size.

        Args:
            theorem: Theorem data dictionary

        Returns:
            Animation configuration with complexity limits
        """
        # Analyze proof complexity
        proof_steps = len(theorem.get("proof_steps", []))
        statement_length = len(theorem.get("statement", ""))
        prerequisites = len(theorem.get("prerequisites", []))

        # Calculate complexity score
        complexity_score = proof_steps * 2 + statement_length // 50 + prerequisites

        self.logger.debug(f"Animation complexity score: {complexity_score}")

        # Determine animation settings based on complexity
        if complexity_score > 100:
            # Very complex - minimal animation
            config = {
                "max_duration": 180,  # 3 minutes
                "steps_per_frame": 10,
                "quality": "low",
                "fps": 15,
                "skip_details": True,
            }
        elif complexity_score > 50:
            # Complex - reduced animation
            config = {
                "max_duration": 300,  # 5 minutes
                "steps_per_frame": 5,
                "quality": "medium",
                "fps": 24,
                "skip_details": False,
            }
        elif complexity_score > 20:
            # Moderate - standard animation
            config = {
                "max_duration": 480,  # 8 minutes
                "steps_per_frame": 2,
                "quality": "medium",
                "fps": 30,
                "skip_details": False,
            }
        else:
            # Simple - full animation
            config = {
                "max_duration": self.limits.max_animation_duration,
                "steps_per_frame": 1,
                "quality": "high",
                "fps": 30,
                "skip_details": False,
            }

        # Apply absolute limits
        config["max_duration"] = min(
            config["max_duration"], self.limits.max_animation_duration
        )

        return config

    def check_file_size(self, file_path: str) -> bool:
        """Check if file size is within limits.

        Args:
            file_path: Path to file

        Returns:
            True if file size is acceptable
        """
        try:
            size_mb = os.path.getsize(file_path) / 1024 / 1024

            if size_mb > self.limits.max_file_size_mb:
                self.logger.warning(
                    f"File {file_path} exceeds size limit: "
                    f"{size_mb:.1f}MB > {self.limits.max_file_size_mb}MB"
                )
                return False

            return True

        except OSError as e:
            self.logger.error(f"Could not check file size: {e}")
            return False

    def enforce_proof_complexity(self, theorem: Dict[str, Any]) -> Dict[str, Any]:
        """Enforce limits on proof complexity.

        Args:
            theorem: Theorem data

        Returns:
            Modified theorem with complexity limits applied
        """
        proof_steps = theorem.get("proof_steps", [])

        # Limit number of proof steps
        if len(proof_steps) > self.limits.max_proof_steps:
            self.logger.warning(
                f"Proof has {len(proof_steps)} steps, "
                f"limiting to {self.limits.max_proof_steps}"
            )
            theorem["proof_steps"] = proof_steps[: self.limits.max_proof_steps]
            theorem["truncated"] = True

        # Limit statement length
        statement = theorem.get("statement", "")
        if len(statement) > 10000:  # 10k character limit
            self.logger.warning("Statement too long, truncating")
            theorem["statement"] = statement[:10000] + "..."
            theorem["truncated"] = True

        return theorem

    def get_resource_report(self) -> Dict[str, Any]:
        """Get comprehensive resource usage report."""
        current_usage = self.monitor.get_current_usage()
        peak_usage = self.monitor.get_peak_usage(window_minutes=5)

        system_memory = psutil.virtual_memory()
        system_cpu = psutil.cpu_percent(interval=1)

        return {
            "current_usage": {
                "memory_mb": current_usage.memory_mb,
                "cpu_percent": current_usage.cpu_percent,
                "active_threads": current_usage.active_threads,
                "open_files": current_usage.open_files,
            },
            "peak_usage_5min": {
                "memory_mb": peak_usage.memory_mb,
                "cpu_percent": peak_usage.cpu_percent,
            },
            "system_resources": {
                "total_memory_gb": system_memory.total / 1024 / 1024 / 1024,
                "available_memory_gb": system_memory.available / 1024 / 1024 / 1024,
                "memory_percent": system_memory.percent,
                "cpu_percent": system_cpu,
                "cpu_count": psutil.cpu_count(),
            },
            "limits": {
                "max_memory_mb": self.limits.max_memory_mb,
                "max_execution_seconds": self.limits.max_execution_seconds,
                "max_cpu_percent": self.limits.max_cpu_percent,
                "max_animation_duration": self.limits.max_animation_duration,
            },
            "status": {
                "memory_ok": current_usage.memory_mb < self.limits.max_memory_mb,
                "cpu_ok": current_usage.cpu_percent < self.limits.max_cpu_percent,
                "within_limits": (
                    current_usage.memory_mb < self.limits.max_memory_mb
                    and current_usage.cpu_percent < self.limits.max_cpu_percent
                ),
            },
        }


# Context managers for common resource limiting patterns


@contextmanager
def limited_memory(max_mb: int):
    """Quick context manager for memory limiting."""
    limiter = ResourceLimiter()
    with limiter.limit_memory(max_mb):
        yield


@contextmanager
def timed_operation(timeout_seconds: int):
    """Quick context manager for operation timeout."""
    limiter = ResourceLimiter()
    with limiter.timeout(timeout_seconds):
        yield


@contextmanager
def monitored_operation(limits: ResourceLimits = None):
    """Context manager for resource monitoring."""
    limiter = ResourceLimiter(limits)
    with limiter.resource_monitoring() as monitor:
        yield monitor


# Decorators for automatic resource limiting


def memory_limited(max_mb: int):
    """Decorator to limit function memory usage."""

    def decorator(func):
        def wrapper(*args, **kwargs):
            with limited_memory(max_mb):
                return func(*args, **kwargs)

        return wrapper

    return decorator


def time_limited(timeout_seconds: int):
    """Decorator to limit function execution time."""

    def decorator(func):
        def wrapper(*args, **kwargs):
            with timed_operation(timeout_seconds):
                return func(*args, **kwargs)

        return wrapper

    return decorator


def resource_monitored(limits: ResourceLimits = None):
    """Decorator to monitor function resource usage."""

    def decorator(func):
        def wrapper(*args, **kwargs):
            with monitored_operation(limits) as monitor:
                start_usage = monitor.get_current_usage()
                result = func(*args, **kwargs)
                end_usage = monitor.get_current_usage()

                # Log resource usage
                memory_delta = end_usage.memory_mb - start_usage.memory_mb
                logging.info(
                    f"Function {func.__name__} used {memory_delta:.1f}MB memory"
                )

                return result

        return wrapper

    return decorator
