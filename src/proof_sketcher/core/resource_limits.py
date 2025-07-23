"""Resource limits and timeout utilities for proof-sketcher."""

from __future__ import annotations

import asyncio
import resource
import signal
import time
from contextlib import contextmanager
from typing import Any, Callable

from .exceptions import (
    InvalidPathError,
    InvalidTheoremNameError,
    RateLimitExceeded,
    ResourceLimitExceeded,
)

try:
    import psutil

    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False


class TimeoutError(ResourceLimitExceeded):
    """Raised when an operation exceeds its timeout."""

    def __init__(self, seconds: int):
        """Initialize with timeout duration."""
        super().__init__("Time", f"{seconds}s", "exceeded")


@contextmanager
def timeout(seconds: int):
    """Context manager that raises TimeoutError after specified seconds.

    Args:
        seconds: Maximum seconds allowed for the operation

    Raises:
        TimeoutError: If the operation exceeds the timeout
    """

    def signal_handler(signum, frame):
        raise TimeoutError(seconds)

    # Set the signal handler
    old_handler = signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)

    try:
        yield
    finally:
        # Disable the alarm
        signal.alarm(0)
        # Restore the old handler
        signal.signal(signal.SIGALRM, old_handler)


async def async_timeout(coro, timeout_seconds: float):
    """Execute a coroutine with a timeout.

    Args:
        coro: Coroutine to execute
        timeout_seconds: Maximum seconds allowed

    Returns:
        Result of the coroutine

    Raises:
        asyncio.TimeoutError: If the operation times out
    """
    return await asyncio.wait_for(coro, timeout=timeout_seconds)


class ResourceMonitor:
    """Monitor resource usage during operations."""

    def __init__(self, max_memory_mb: int = 500, check_interval: float = 0.1):
        """Initialize resource monitor.

        Args:
            max_memory_mb: Maximum memory usage in megabytes
            check_interval: How often to check memory (seconds)
        """
        self.max_memory_mb = max_memory_mb
        self.check_interval = check_interval
        self.start_time = None
        self.initial_memory = 0
        self.peak_memory = 0
        self.process = None
        self._monitoring = False

        if PSUTIL_AVAILABLE:
            import os

            self.process = psutil.Process(os.getpid())

    def __enter__(self):
        """Start monitoring resources."""
        self.start_time = time.time()
        self._monitoring = True

        if self.process:
            self.initial_memory = self.process.memory_info().rss / (1024 * 1024)
            self.peak_memory = self.initial_memory

        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Stop monitoring and report."""
        self._monitoring = False
        elapsed = time.time() - self.start_time

        if self.process:
            final_memory = self.process.memory_info().rss / (1024 * 1024)
            memory_delta = final_memory - self.initial_memory

            # Could log this information if needed
            # print(f"Resource usage: {elapsed:.2f}s, "
            #       f"Memory: {memory_delta:.1f}MB (peak: {self.peak_memory:.1f}MB)")

    def check_memory(self):
        """Check if memory usage is within limits.

        Raises:
            MemoryError: If memory usage exceeds limit
        """
        if not self._monitoring or not self.process:
            return

        current_memory = self.process.memory_info().rss / (1024 * 1024)
        memory_used = current_memory - self.initial_memory

        if memory_used > self.max_memory_mb:
            raise ResourceLimitExceeded(
                "Memory", f"{self.max_memory_mb}MB", f"{memory_used:.1f}MB"
            )

        self.peak_memory = max(self.peak_memory, current_memory)

    async def monitor_async(self, coro):
        """Monitor memory usage during async operation.

        Args:
            coro: Coroutine to monitor

        Returns:
            Result of the coroutine

        Raises:
            MemoryError: If memory limit exceeded
        """

        async def monitor_task():
            while self._monitoring:
                self.check_memory()
                await asyncio.sleep(self.check_interval)

        with self:
            # Start monitoring task
            monitor = asyncio.create_task(monitor_task())

            try:
                # Run the actual coroutine
                result = await coro
                return result
            finally:
                # Stop monitoring
                self._monitoring = False
                monitor.cancel()
                try:
                    await monitor
                except asyncio.CancelledError:
                    pass


class RateLimiter:
    """Rate limiter for controlling API/generator calls."""

    def __init__(self, max_calls: int = 10, time_window: float = 60.0):
        """Initialize rate limiter.

        Args:
            max_calls: Maximum number of calls allowed
            time_window: Time window in seconds
        """
        self.max_calls = max_calls
        self.time_window = time_window
        self.calls = []
        self._lock = asyncio.Lock() if asyncio.get_event_loop().is_running() else None

    def _cleanup_old_calls(self):
        """Remove calls outside the time window."""
        current_time = time.time()
        cutoff_time = current_time - self.time_window
        self.calls = [call_time for call_time in self.calls if call_time > cutoff_time]

    def can_make_call(self) -> bool:
        """Check if a call can be made within rate limits."""
        self._cleanup_old_calls()
        return len(self.calls) < self.max_calls

    def record_call(self):
        """Record a call for rate limiting."""
        self._cleanup_old_calls()
        if len(self.calls) >= self.max_calls:
            raise RateLimitExceeded(self.max_calls, self.time_window)
        self.calls.append(time.time())

    async def acquire(self):
        """Acquire permission to make a call (async version)."""
        if self._lock is None:
            self._lock = asyncio.Lock()

        async with self._lock:
            while not self.can_make_call():
                # Wait until we can make a call
                await asyncio.sleep(0.1)
            self.record_call()

    def __enter__(self):
        """Context manager entry."""
        if not self.can_make_call():
            raise RateLimitExceeded(self.max_calls, self.time_window)
        self.record_call()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        pass


def sanitize_path(path: str) -> str:
    """Sanitize file path to prevent directory traversal attacks.

    Args:
        path: Path to sanitize

    Returns:
        Sanitized path

    Raises:
        InvalidPathError: If path contains dangerous patterns
    """
    import os
    import urllib.parse
    from pathlib import Path

    # Remove any null bytes
    if "\x00" in path:
        raise InvalidPathError("Path contains null bytes")

    # Limit path length to prevent DoS
    if len(path) > 4096:  # 4KB limit
        raise InvalidPathError("Path too long")

    # URL decode to catch encoded traversals
    try:
        decoded_path = urllib.parse.unquote(path)
    except Exception:
        decoded_path = path

    # Normalize unicode to catch full-width characters
    try:
        import unicodedata

        normalized_path = unicodedata.normalize("NFKD", decoded_path)
    except Exception:
        normalized_path = decoded_path

    # Check for Windows reserved names
    windows_reserved = {
        "CON",
        "PRN",
        "AUX",
        "NUL",
        "COM1",
        "COM2",
        "COM3",
        "COM4",
        "COM5",
        "COM6",
        "COM7",
        "COM8",
        "COM9",
        "LPT1",
        "LPT2",
        "LPT3",
        "LPT4",
        "LPT5",
        "LPT6",
        "LPT7",
        "LPT8",
        "LPT9",
    }
    path_parts = Path(normalized_path).parts
    for part in path_parts:
        if part.upper().split(".")[0] in windows_reserved:
            raise InvalidPathError(f"Windows reserved name: {part}")

    # Check for dangerous patterns in both original and decoded paths
    dangerous_patterns = [
        "..",
        "~",
        "$",
        "`",
        "|",
        ";",
        "&",
        "<",
        ">",
        "%2f",
        "%2F",
        "%5c",
        "%5C",
        "\\",
        "//",
        "/./",
        "/../",
    ]
    for check_path in [path, decoded_path, normalized_path]:
        for pattern in dangerous_patterns:
            if pattern in check_path.lower():
                raise InvalidPathError(f"Path contains dangerous pattern: {pattern}")

    # Resolve to absolute path and validate
    try:
        resolved = Path(normalized_path).resolve()

        # Ensure the resolved path doesn't escape the current working directory
        cwd = Path.cwd().resolve()
        try:
            resolved.relative_to(cwd)
        except ValueError:
            # Path is outside current working directory
            # Only allow if it's a standard system path or explicitly safe
            safe_prefixes = [
                "/tmp", 
                "/var/tmp", 
                "/private/var/folders",  # macOS temp dirs
                "/var/folders",  # macOS temp dirs alternate
                str(Path.home())
            ]
            if not any(str(resolved).startswith(prefix) for prefix in safe_prefixes):
                raise InvalidPathError("Path escapes current working directory")

        return str(resolved)
    except InvalidPathError:
        raise
    except Exception as e:
        raise InvalidPathError(f"Invalid path: {e}")


def sanitize_theorem_name(name: str) -> str:
    """Sanitize theorem name for safe use in filenames and displays.

    Args:
        name: Theorem name to sanitize

    Returns:
        Sanitized name
    """
    import re

    # Remove any characters that aren't alphanumeric, underscore, dash, or dot
    sanitized = re.sub(r"[^a-zA-Z0-9_\-.]", "_", name)

    # Remove leading/trailing dots and underscores
    sanitized = sanitized.strip("._")

    # Replace multiple underscores with single
    sanitized = re.sub(r"_+", "_", sanitized)

    # Limit length
    if len(sanitized) > 100:
        sanitized = sanitized[:100]

    # Ensure it's not empty
    if not sanitized:
        sanitized = "unnamed_theorem"

    return sanitized


def with_timeout(timeout_seconds: int):
    """Decorator to add timeout to functions.

    Args:
        timeout_seconds: Maximum seconds allowed

    Returns:
        Decorated function that times out
    """

    def decorator(func: Callable) -> Callable:
        def wrapper(*args, **kwargs) -> Any:
            with timeout(timeout_seconds):
                return func(*args, **kwargs)

        return wrapper

    return decorator
