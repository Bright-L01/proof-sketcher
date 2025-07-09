"""Resource management and monitoring for Proof Sketcher.

Features:
- Memory usage monitoring and limits
- Disk space checks and management
- Process cleanup on failure
- Temporary file management
- Resource allocation tracking
"""

import gc
import logging
import os
import shutil
import tempfile
import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Generator, List, Optional

import psutil

from .exceptions import DiskSpaceError, MemoryError, ResourceError, handle_error


@dataclass
class ResourceLimits:
    """Resource limit configuration."""

    max_memory_mb: Optional[int] = None  # Maximum memory usage in MB
    max_disk_mb: Optional[int] = None  # Maximum disk space to use in MB
    max_temp_files: Optional[int] = None  # Maximum temporary files
    max_processes: Optional[int] = None  # Maximum subprocess count
    cleanup_on_exit: bool = True  # Whether to cleanup on exit


@dataclass
class ResourceUsage:
    """Current resource usage snapshot."""

    memory_mb: float  # Current memory usage in MB
    disk_used_mb: float  # Disk space used in MB
    disk_available_mb: float  # Available disk space in MB
    temp_files_count: int  # Number of temporary files
    active_processes: int  # Number of active processes
    timestamp: float  # Timestamp of measurement


class TempFileManager:
    """Manager for temporary files with automatic cleanup."""

    def __init__(self, base_dir: Optional[Path] = None, max_files: int = 100):
        """Initialize temporary file manager.

        Args:
            base_dir: Base directory for temporary files
            max_files: Maximum number of temporary files to track
        """
        self.base_dir = base_dir or Path(tempfile.gettempdir()) / "proof_sketcher"
        self.max_files = max_files
        self.temp_files: List[Path] = []
        self.temp_dirs: List[Path] = []
        self.lock = threading.Lock()
        self.logger = logging.getLogger(__name__)

        # Ensure base directory exists
        self.base_dir.mkdir(parents=True, exist_ok=True)

    def create_temp_file(
        self, suffix: str = "", prefix: str = "proof_", content: Optional[str] = None
    ) -> Path:
        """Create a temporary file.

        Args:
            suffix: File suffix
            prefix: File prefix
            content: Optional content to write

        Returns:
            Path to temporary file
        """
        with self.lock:
            # Check limits
            if len(self.temp_files) >= self.max_files:
                self._cleanup_oldest_files(10)  # Remove 10 oldest files

            # Create temporary file
            fd, temp_path_str = tempfile.mkstemp(
                suffix=suffix, prefix=prefix, dir=self.base_dir
            )

            temp_path = Path(temp_path_str)

            try:
                if content:
                    with open(fd, "w") as f:
                        f.write(content)
                else:
                    os.close(fd)

                self.temp_files.append(temp_path)
                self.logger.debug(f"Created temporary file: {temp_path}")
                return temp_path

            except Exception as e:
                os.close(fd)
                if temp_path.exists():
                    temp_path.unlink()
                raise e

    def create_temp_dir(self, prefix: str = "proof_") -> Path:
        """Create a temporary directory.

        Args:
            prefix: Directory prefix

        Returns:
            Path to temporary directory
        """
        with self.lock:
            temp_dir = Path(tempfile.mkdtemp(prefix=prefix, dir=self.base_dir))
            self.temp_dirs.append(temp_dir)
            self.logger.debug(f"Created temporary directory: {temp_dir}")
            return temp_dir

    def cleanup_file(self, file_path: Path) -> bool:
        """Clean up a specific temporary file.

        Args:
            file_path: Path to file to clean up

        Returns:
            True if successful, False otherwise
        """
        try:
            if file_path.exists():
                file_path.unlink()

            with self.lock:
                if file_path in self.temp_files:
                    self.temp_files.remove(file_path)

            self.logger.debug(f"Cleaned up temporary file: {file_path}")
            return True

        except Exception as e:
            self.logger.warning(f"Failed to cleanup file {file_path}: {e}")
            return False

    def cleanup_dir(self, dir_path: Path) -> bool:
        """Clean up a temporary directory.

        Args:
            dir_path: Path to directory to clean up

        Returns:
            True if successful, False otherwise
        """
        try:
            if dir_path.exists():
                shutil.rmtree(dir_path)

            with self.lock:
                if dir_path in self.temp_dirs:
                    self.temp_dirs.remove(dir_path)

            self.logger.debug(f"Cleaned up temporary directory: {dir_path}")
            return True

        except Exception as e:
            self.logger.warning(f"Failed to cleanup directory {dir_path}: {e}")
            return False

    def cleanup_all(self) -> int:
        """Clean up all temporary files and directories.

        Returns:
            Number of items cleaned up
        """
        cleaned_count = 0

        # Clean up files
        # Copy to avoid modification during iteration
        files_to_remove = list(self.temp_files)
        for file_path in files_to_remove:
            if self.cleanup_file(file_path):
                cleaned_count += 1

        # Clean up directories
        dirs_to_remove = list(self.temp_dirs)
        for dir_path in dirs_to_remove:
            if self.cleanup_dir(dir_path):
                cleaned_count += 1

        self.logger.info(f"Cleaned up {cleaned_count} temporary items")
        return cleaned_count

    def _cleanup_oldest_files(self, count: int) -> None:
        """Clean up the oldest temporary files."""
        if len(self.temp_files) <= count:
            return

        # Sort by modification time
        files_with_mtime = []
        for file_path in self.temp_files:
            try:
                mtime = file_path.stat().st_mtime if file_path.exists() else 0
                files_with_mtime.append((file_path, mtime))
            except OSError:
                files_with_mtime.append((file_path, 0))

        files_with_mtime.sort(key=lambda x: x[1])  # Sort by mtime

        # Remove oldest files
        for file_path, _ in files_with_mtime[:count]:
            self.cleanup_file(file_path)

    def get_stats(self) -> Dict[str, Any]:
        """Get temporary file statistics."""
        total_size = 0
        for file_path in self.temp_files:
            try:
                if file_path.exists():
                    total_size += file_path.stat().st_size
            except OSError:
                continue

        return {
            "temp_files_count": len(self.temp_files),
            "temp_dirs_count": len(self.temp_dirs),
            "total_size_mb": total_size / (1024 * 1024),
            "base_dir": str(self.base_dir),
        }


class ProcessManager:
    """Manager for tracking and cleaning up processes."""

    def __init__(self, max_processes: int = 10):
        """Initialize process manager.

        Args:
            max_processes: Maximum number of processes to track
        """
        self.max_processes = max_processes
        self.active_processes: List[psutil.Process] = []
        self.lock = threading.Lock()
        self.logger = logging.getLogger(__name__)

    def register_process(self, process: psutil.Process) -> None:
        """Register a process for tracking.

        Args:
            process: Process to track
        """
        with self.lock:
            # Clean up dead processes first
            self._cleanup_dead_processes()

            # Check limits
            if len(self.active_processes) >= self.max_processes:
                raise ResourceError(
                    f"Too many active processes ({
                        len(
                            self.active_processes)} >= {
                        self.max_processes})",
                    context={"active_processes": len(self.active_processes)},
                )

            self.active_processes.append(process)
            self.logger.debug(f"Registered process: {process.pid}")

    def cleanup_process(self, process: psutil.Process) -> bool:
        """Clean up a specific process.

        Args:
            process: Process to clean up

        Returns:
            True if successful, False otherwise
        """
        try:
            if process.is_running():
                process.terminate()
                try:
                    process.wait(timeout=5)  # Wait up to 5 seconds
                except psutil.TimeoutExpired:
                    process.kill()  # Force kill if it doesn't terminate

            with self.lock:
                if process in self.active_processes:
                    self.active_processes.remove(process)

            self.logger.debug(f"Cleaned up process: {process.pid}")
            return True

        except Exception as e:
            self.logger.warning(f"Failed to cleanup process {process.pid}: {e}")
            return False

    def cleanup_all(self) -> int:
        """Clean up all tracked processes.

        Returns:
            Number of processes cleaned up
        """
        processes_to_cleanup = list(self.active_processes)
        cleaned_count = 0

        for process in processes_to_cleanup:
            if self.cleanup_process(process):
                cleaned_count += 1

        self.logger.info(f"Cleaned up {cleaned_count} processes")
        return cleaned_count

    def _cleanup_dead_processes(self) -> None:
        """Remove dead processes from tracking."""
        dead_processes = []
        for process in self.active_processes:
            if not process.is_running():
                dead_processes.append(process)

        for process in dead_processes:
            self.active_processes.remove(process)

    def get_stats(self) -> Dict[str, Any]:
        """Get process statistics."""
        self._cleanup_dead_processes()
        return {
            "active_processes": len(self.active_processes),
            "max_processes": self.max_processes,
        }


class ResourceMonitor:
    """System resource monitor with limits and alerts."""

    def __init__(
        self, limits: Optional[ResourceLimits] = None, check_interval: float = 1.0
    ):
        """Initialize resource monitor.

        Args:
            limits: Resource limits configuration
            check_interval: How often to check resources (seconds)
        """
        self.limits = limits or ResourceLimits()
        self.check_interval = check_interval
        self.logger = logging.getLogger(__name__)

        # Managers
        self.temp_manager = TempFileManager()
        self.process_manager = ProcessManager(
            max_processes=self.limits.max_processes or 10
        )

        # Monitoring state
        self.monitoring = False
        self.monitor_thread: Optional[threading.Thread] = None
        self.usage_history: List[ResourceUsage] = []
        self.max_history = 100

        # Callbacks
        self.warning_callbacks: List[Callable[[str, ResourceUsage], None]] = []
        self.error_callbacks: List[Callable[[str, ResourceUsage], None]] = []

    def start_monitoring(self) -> None:
        """Start background resource monitoring."""
        if self.monitoring:
            return

        self.monitoring = True
        self.monitor_thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self.monitor_thread.start()
        self.logger.info("Started resource monitoring")

    def stop_monitoring(self) -> None:
        """Stop background resource monitoring."""
        self.monitoring = False
        if self.monitor_thread:
            self.monitor_thread.join(timeout=2.0)
        self.logger.info("Stopped resource monitoring")

    def get_current_usage(self) -> ResourceUsage:
        """Get current resource usage snapshot."""
        process = psutil.Process()
        memory_info = process.memory_info()

        # Get disk usage for current working directory
        disk_usage = shutil.disk_usage(Path.cwd())

        return ResourceUsage(
            memory_mb=memory_info.rss / (1024 * 1024),
            disk_used_mb=(disk_usage.total - disk_usage.free) / (1024 * 1024),
            disk_available_mb=disk_usage.free / (1024 * 1024),
            temp_files_count=len(self.temp_manager.temp_files),
            active_processes=len(self.process_manager.active_processes),
            timestamp=time.time(),
        )

    def check_limits(self, usage: Optional[ResourceUsage] = None) -> None:
        """Check if current usage exceeds limits.

        Args:
            usage: Resource usage to check (defaults to current)

        Raises:
            ResourceError: If limits are exceeded
        """
        if usage is None:
            usage = self.get_current_usage()

        # Check memory limit
        if self.limits.max_memory_mb and usage.memory_mb > self.limits.max_memory_mb:
            raise MemoryError(
                f"Memory usage ({
                    usage.memory_mb:.1f} MB) exceeds limit ({
                    self.limits.max_memory_mb} MB)",
                context={
                    "current_memory_mb": usage.memory_mb,
                    "limit_mb": self.limits.max_memory_mb,
                },
            )

        # Check disk space
        if self.limits.max_disk_mb and usage.disk_used_mb > self.limits.max_disk_mb:
            raise DiskSpaceError(
                "Disk usage exceeds limit",
                required_space=int(self.limits.max_disk_mb * 1024 * 1024),
                available_space=int(usage.disk_available_mb * 1024 * 1024),
            )

        # Check available disk space (always check this)
        if usage.disk_available_mb < 100:  # Less than 100 MB available
            raise DiskSpaceError(
                f"Insufficient disk space ({usage.disk_available_mb:.1f} MB available)",
                available_space=int(usage.disk_available_mb * 1024 * 1024),
            )

    def add_warning_callback(
        self, callback: Callable[[str, ResourceUsage], None]
    ) -> None:
        """Add callback for resource warnings."""
        self.warning_callbacks.append(callback)

    def add_error_callback(
        self, callback: Callable[[str, ResourceUsage], None]
    ) -> None:
        """Add callback for resource errors."""
        self.error_callbacks.append(callback)

    def cleanup_all(self) -> Dict[str, int]:
        """Clean up all managed resources.

        Returns:
            Dictionary with cleanup counts
        """
        results = {}

        # Clean up temporary files
        results["temp_files"] = self.temp_manager.cleanup_all()

        # Clean up processes
        results["processes"] = self.process_manager.cleanup_all()

        # Force garbage collection
        gc.collect()
        results["gc_collected"] = gc.collect()

        self.logger.info(f"Resource cleanup completed: {results}")
        return results

    def _monitor_loop(self) -> None:
        """Background monitoring loop."""
        while self.monitoring:
            try:
                usage = self.get_current_usage()

                # Store in history
                self.usage_history.append(usage)
                if len(self.usage_history) > self.max_history:
                    self.usage_history.pop(0)

                # Check for warnings
                self._check_warnings(usage)

                # Check hard limits
                try:
                    self.check_limits(usage)
                except ResourceError as e:
                    for callback in self.error_callbacks:
                        try:
                            callback(str(e), usage)
                        except Exception as cb_error:
                            self.logger.error(f"Error in error callback: {cb_error}")

                time.sleep(self.check_interval)

            except Exception as e:
                self.logger.error(f"Error in resource monitoring loop: {e}")
                time.sleep(self.check_interval)

    def _check_warnings(self, usage: ResourceUsage) -> None:
        """Check for warning conditions."""
        warnings = []

        # Memory warnings (80% of limit)
        if (
            self.limits.max_memory_mb
            and usage.memory_mb > self.limits.max_memory_mb * 0.8
        ):
            warnings.append(f"High memory usage: {usage.memory_mb:.1f} MB")

        # Disk space warnings (90% full or less than 500 MB)
        if usage.disk_available_mb < 500:
            warnings.append(
                f"Low disk space: {
                    usage.disk_available_mb:.1f} MB available"
            )

        # Too many temp files
        if usage.temp_files_count > 50:
            warnings.append(f"Many temporary files: {usage.temp_files_count}")

        # Send warnings
        for warning in warnings:
            for callback in self.warning_callbacks:
                try:
                    callback(warning, usage)
                except Exception as cb_error:
                    self.logger.error(f"Error in warning callback: {cb_error}")

    def get_stats(self) -> Dict[str, Any]:
        """Get comprehensive resource statistics."""
        current_usage = self.get_current_usage()

        return {
            "current_usage": current_usage.__dict__,
            "limits": self.limits.__dict__,
            "temp_manager": self.temp_manager.get_stats(),
            "process_manager": self.process_manager.get_stats(),
            "monitoring": self.monitoring,
            "history_length": len(self.usage_history),
        }


# Global resource monitor instance
global_resource_monitor = ResourceMonitor()


@contextmanager
def resource_context(
    limits: Optional[ResourceLimits] = None, cleanup_on_exit: bool = True
) -> Generator[ResourceMonitor, None, None]:
    """Context manager for resource monitoring.

    Args:
        limits: Resource limits to enforce
        cleanup_on_exit: Whether to cleanup on exit

    Yields:
        ResourceMonitor instance
    """
    monitor = ResourceMonitor(limits)
    monitor.start_monitoring()

    try:
        yield monitor
    except Exception as e:
        # Handle resource-related errors
        try:
            monitor.check_limits()
        except ResourceError as resource_error:
            handle_error(resource_error)

        # Re-raise original exception
        raise e
    finally:
        monitor.stop_monitoring()
        if cleanup_on_exit:
            monitor.cleanup_all()


def check_disk_space(path: Path, required_mb: int) -> None:
    """Check if sufficient disk space is available.

    Args:
        path: Path to check
        required_mb: Required space in MB

    Raises:
        DiskSpaceError: If insufficient space
    """
    try:
        usage = shutil.disk_usage(path)
        available_mb = usage.free / (1024 * 1024)

        if available_mb < required_mb:
            raise DiskSpaceError(
                f"Insufficient disk space at {path}",
                required_space=required_mb * 1024 * 1024,
                available_space=int(usage.free),
            )
    except OSError as e:
        raise ResourceError(f"Failed to check disk space at {path}: {e}")


def check_memory_usage(max_mb: int) -> None:
    """Check if memory usage is within limits.

    Args:
        max_mb: Maximum memory in MB

    Raises:
        MemoryError: If memory usage exceeds limit
    """
    try:
        process = psutil.Process()
        memory_mb = process.memory_info().rss / (1024 * 1024)

        if memory_mb > max_mb:
            raise MemoryError(
                f"Memory usage ({memory_mb:.1f} MB) exceeds limit ({max_mb} MB)",
                context={"current_memory_mb": memory_mb, "limit_mb": max_mb},
            )
    except psutil.Error as e:
        raise ResourceError(f"Failed to check memory usage: {e}")
