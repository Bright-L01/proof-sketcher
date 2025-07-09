#!/usr/bin/env python3
"""Comprehensive tests for resource management functionality.

Tests the ResourceMonitor, TempFileManager, ProcessManager and related utilities
for managing system resources during proof sketching operations.
"""

import gc
import json
import os
import tempfile
import threading
import time
from pathlib import Path
from unittest.mock import MagicMock, Mock, patch

import psutil
import pytest

from proof_sketcher.core.exceptions import DiskSpaceError, MemoryError, ResourceError
from proof_sketcher.core.resources import (
    ProcessManager,
    ResourceLimits,
    ResourceMonitor,
    ResourceUsage,
    TempFileManager,
    check_disk_space,
    check_memory_usage,
    resource_context,
)


class TestResourceLimits:
    """Test ResourceLimits dataclass."""

    def test_default_limits(self):
        """Test default resource limits."""
        limits = ResourceLimits()
        assert limits.max_memory_mb is None
        assert limits.max_disk_mb is None
        assert limits.max_temp_files is None
        assert limits.max_processes is None
        assert limits.cleanup_on_exit is True

    def test_custom_limits(self):
        """Test custom resource limits."""
        limits = ResourceLimits(
            max_memory_mb=1024,
            max_disk_mb=5000,
            max_temp_files=50,
            max_processes=5,
            cleanup_on_exit=False,
        )
        assert limits.max_memory_mb == 1024
        assert limits.max_disk_mb == 5000
        assert limits.max_temp_files == 50
        assert limits.max_processes == 5
        assert limits.cleanup_on_exit is False


class TestResourceUsage:
    """Test ResourceUsage dataclass."""

    def test_resource_usage_creation(self):
        """Test creating resource usage snapshot."""
        usage = ResourceUsage(
            memory_mb=512.5,
            disk_used_mb=100.0,
            disk_available_mb=5000.0,
            temp_files_count=10,
            active_processes=3,
            timestamp=time.time(),
        )
        assert usage.memory_mb == 512.5
        assert usage.disk_used_mb == 100.0
        assert usage.disk_available_mb == 5000.0
        assert usage.temp_files_count == 10
        assert usage.active_processes == 3
        assert isinstance(usage.timestamp, float)


class TestTempFileManager:
    """Test TempFileManager class."""

    @pytest.fixture
    def temp_manager(self):
        """Create a TempFileManager instance for testing."""
        with tempfile.TemporaryDirectory() as tmpdir:
            manager = TempFileManager(base_dir=Path(tmpdir), max_files=5)
            yield manager
            # Cleanup should happen automatically

    def test_initialization(self, temp_manager):
        """Test temp file manager initialization."""
        assert temp_manager.base_dir.exists()
        assert temp_manager.max_files == 5
        assert len(temp_manager.temp_files) == 0
        assert len(temp_manager.temp_dirs) == 0

    def test_create_temp_file(self, temp_manager):
        """Test creating temporary files."""
        # Create file without content
        file1 = temp_manager.create_temp_file(suffix=".txt", prefix="test_")
        assert file1.exists()
        assert file1.suffix == ".txt"
        assert file1.name.startswith("test_")
        assert file1 in temp_manager.temp_files

        # Create file with content
        content = "Hello, World!"
        file2 = temp_manager.create_temp_file(content=content)
        assert file2.exists()
        assert file2.read_text() == content
        assert len(temp_manager.temp_files) == 2

    def test_create_temp_file_limit(self, temp_manager):
        """Test temp file creation limit enforcement."""
        # Create max files
        for i in range(5):
            temp_manager.create_temp_file(prefix=f"file{i}_")

        assert len(temp_manager.temp_files) == 5

        # Creating another should trigger cleanup
        file6 = temp_manager.create_temp_file(prefix="file6_")
        assert file6.exists()
        # Should have cleaned up oldest files
        assert len(temp_manager.temp_files) <= 5

    def test_create_temp_dir(self, temp_manager):
        """Test creating temporary directories."""
        dir1 = temp_manager.create_temp_dir(prefix="testdir_")
        assert dir1.exists()
        assert dir1.is_dir()
        assert dir1 in temp_manager.temp_dirs

        # Create file in temp dir
        test_file = dir1 / "test.txt"
        test_file.write_text("test content")
        assert test_file.exists()

    def test_cleanup_file(self, temp_manager):
        """Test cleaning up individual files."""
        file1 = temp_manager.create_temp_file()
        file2 = temp_manager.create_temp_file()

        assert len(temp_manager.temp_files) == 2

        # Cleanup file1
        success = temp_manager.cleanup_file(file1)
        assert success
        assert not file1.exists()
        assert file1 not in temp_manager.temp_files
        assert len(temp_manager.temp_files) == 1

        # Try to cleanup non-existent file
        success = temp_manager.cleanup_file(Path("/nonexistent"))
        assert not success

    def test_cleanup_dir(self, temp_manager):
        """Test cleaning up directories."""
        dir1 = temp_manager.create_temp_dir()
        # Add some files to the directory
        (dir1 / "file1.txt").write_text("content1")
        (dir1 / "file2.txt").write_text("content2")

        success = temp_manager.cleanup_dir(dir1)
        assert success
        assert not dir1.exists()
        assert dir1 not in temp_manager.temp_dirs

    def test_cleanup_all(self, temp_manager):
        """Test cleaning up all temporary resources."""
        # Create multiple files and dirs
        files = [temp_manager.create_temp_file() for _ in range(3)]
        dirs = [temp_manager.create_temp_dir() for _ in range(2)]

        # Add files to dirs
        for dir in dirs:
            (dir / "test.txt").write_text("test")

        count = temp_manager.cleanup_all()
        assert count == 5  # 3 files + 2 dirs

        # Verify all cleaned up
        for file in files:
            assert not file.exists()
        for dir in dirs:
            assert not dir.exists()

        assert len(temp_manager.temp_files) == 0
        assert len(temp_manager.temp_dirs) == 0

    def test_get_stats(self, temp_manager):
        """Test getting temp file statistics."""
        # Create some files
        temp_manager.create_temp_file(content="x" * 100)  # 100 bytes
        temp_manager.create_temp_file(content="y" * 200)  # 200 bytes
        temp_manager.create_temp_dir()

        stats = temp_manager.get_stats()
        assert stats["temp_files_count"] == 2
        assert stats["temp_dirs_count"] == 1
        assert stats["total_size_bytes"] >= 300  # At least 300 bytes
        assert stats["base_dir"] == str(temp_manager.base_dir)

    def test_thread_safety(self, temp_manager):
        """Test thread-safe operations."""
        results = []

        def create_files():
            for i in range(10):
                file = temp_manager.create_temp_file(prefix=f"thread_{i}_")
                results.append(file)

        # Run in multiple threads
        threads = [threading.Thread(target=create_files) for _ in range(3)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        # Should have created 30 files, but limited to max_files
        assert len(temp_manager.temp_files) <= temp_manager.max_files
        # All files that are tracked should exist
        for file in temp_manager.temp_files:
            assert file.exists()


class TestProcessManager:
    """Test ProcessManager class."""

    @pytest.fixture
    def process_manager(self):
        """Create a ProcessManager instance."""
        return ProcessManager(max_processes=3)

    def test_initialization(self, process_manager):
        """Test process manager initialization."""
        assert process_manager.max_processes == 3
        assert len(process_manager.processes) == 0

    def test_register_process(self, process_manager):
        """Test registering processes."""
        # Create mock process
        process = Mock(spec=psutil.Process)
        process.pid = 12345
        process.is_running.return_value = True

        process_manager.register_process(process)
        assert process in process_manager.processes
        assert len(process_manager.processes) == 1

    def test_register_process_limit(self, process_manager):
        """Test process registration limit."""
        # Register max processes
        for i in range(3):
            process = Mock(spec=psutil.Process)
            process.pid = 10000 + i
            process.is_running.return_value = True
            process_manager.register_process(process)

        # Try to register one more
        process4 = Mock(spec=psutil.Process)
        process4.pid = 10004
        process4.is_running.return_value = True

        with pytest.raises(ResourceError, match="Maximum process limit"):
            process_manager.register_process(process4)

    def test_cleanup_process(self, process_manager):
        """Test cleaning up individual processes."""
        # Create and register process
        process = Mock(spec=psutil.Process)
        process.pid = 12345
        process.is_running.return_value = True
        process.terminate.return_value = None
        process.wait.return_value = None

        process_manager.register_process(process)

        # Cleanup
        success = process_manager.cleanup_process(process)
        assert success
        assert process not in process_manager.processes
        process.terminate.assert_called_once()

    def test_cleanup_all(self, process_manager):
        """Test cleaning up all processes."""
        # Register multiple processes
        processes = []
        for i in range(3):
            process = Mock(spec=psutil.Process)
            process.pid = 10000 + i
            process.is_running.return_value = True
            process.terminate.return_value = None
            process.wait.return_value = None
            processes.append(process)
            process_manager.register_process(process)

        count = process_manager.cleanup_all()
        assert count == 3
        assert len(process_manager.processes) == 0

        for process in processes:
            process.terminate.assert_called_once()

    def test_cleanup_dead_processes(self, process_manager):
        """Test automatic cleanup of dead processes."""
        # Register mix of running and dead processes
        running_process = Mock(spec=psutil.Process)
        running_process.pid = 10001
        running_process.is_running.return_value = True

        dead_process = Mock(spec=psutil.Process)
        dead_process.pid = 10002
        dead_process.is_running.return_value = False

        process_manager.register_process(running_process)
        process_manager.register_process(dead_process)

        assert len(process_manager.processes) == 2

        # Cleanup dead processes
        process_manager._cleanup_dead_processes()

        assert len(process_manager.processes) == 1
        assert running_process in process_manager.processes
        assert dead_process not in process_manager.processes

    def test_get_stats(self, process_manager):
        """Test getting process statistics."""
        # Register a process
        process = Mock(spec=psutil.Process)
        process.pid = 12345
        process.is_running.return_value = True

        process_manager.register_process(process)

        stats = process_manager.get_stats()
        assert stats["active_processes"] == 1
        assert stats["max_processes"] == 3
        assert 12345 in stats["process_pids"]


class TestResourceMonitor:
    """Test ResourceMonitor class."""

    @pytest.fixture
    def resource_monitor(self):
        """Create a ResourceMonitor instance."""
        limits = ResourceLimits(
            max_memory_mb=512, max_disk_mb=1000, max_temp_files=20, max_processes=5
        )
        monitor = ResourceMonitor(limits=limits, check_interval=0.1)
        yield monitor
        # Ensure monitoring is stopped
        if monitor.monitoring:
            monitor.stop_monitoring()

    def test_initialization(self, resource_monitor):
        """Test resource monitor initialization."""
        assert resource_monitor.limits.max_memory_mb == 512
        assert resource_monitor.check_interval == 0.1
        assert not resource_monitor.monitoring
        assert resource_monitor.monitor_thread is None
        assert len(resource_monitor.usage_history) == 0

    def test_get_current_usage(self, resource_monitor):
        """Test getting current resource usage."""
        usage = resource_monitor.get_current_usage()

        assert isinstance(usage, ResourceUsage)
        assert usage.memory_mb > 0
        assert usage.disk_available_mb > 0
        assert usage.temp_files_count >= 0
        assert usage.active_processes >= 0
        assert usage.timestamp > 0

    def test_start_stop_monitoring(self, resource_monitor):
        """Test starting and stopping monitoring."""
        # Start monitoring
        resource_monitor.start_monitoring()
        assert resource_monitor.monitoring
        assert resource_monitor.monitor_thread is not None
        assert resource_monitor.monitor_thread.is_alive()

        # Wait for some monitoring cycles
        time.sleep(0.3)

        # Stop monitoring
        resource_monitor.stop_monitoring()
        assert not resource_monitor.monitoring
        # Thread should finish
        resource_monitor.monitor_thread.join(timeout=1)
        assert not resource_monitor.monitor_thread.is_alive()

    def test_check_limits_memory(self, resource_monitor):
        """Test checking memory limits."""
        # Create usage exceeding memory limit
        usage = ResourceUsage(
            memory_mb=600,  # Exceeds limit of 512
            disk_used_mb=100,
            disk_available_mb=900,
            temp_files_count=10,
            active_processes=2,
            timestamp=time.time(),
        )

        with pytest.raises(MemoryError, match="Memory usage.*exceeds limit"):
            resource_monitor.check_limits(usage)

    def test_check_limits_disk(self, resource_monitor):
        """Test checking disk limits."""
        # Create usage exceeding disk limit
        usage = ResourceUsage(
            memory_mb=400,
            disk_used_mb=800,
            disk_available_mb=50,  # Only 50MB available
            temp_files_count=10,
            active_processes=2,
            timestamp=time.time(),
        )

        with pytest.raises(DiskSpaceError, match="Disk space.*below limit"):
            resource_monitor.check_limits(usage)

    def test_check_limits_processes(self, resource_monitor):
        """Test checking process limits."""
        # Create usage exceeding process limit
        usage = ResourceUsage(
            memory_mb=400,
            disk_used_mb=500,
            disk_available_mb=500,
            temp_files_count=10,
            active_processes=6,  # Exceeds limit of 5
            timestamp=time.time(),
        )

        with pytest.raises(ResourceError, match="Process count.*exceeds limit"):
            resource_monitor.check_limits(usage)

    def test_warning_callbacks(self, resource_monitor):
        """Test warning callbacks."""
        warning_called = False
        warning_msg = None

        def warning_callback(msg, usage):
            nonlocal warning_called, warning_msg
            warning_called = True
            warning_msg = msg

        resource_monitor.add_warning_callback(warning_callback)

        # Create usage at 85% of memory limit (should trigger warning)
        usage = ResourceUsage(
            memory_mb=440,  # 85% of 512MB limit
            disk_used_mb=100,
            disk_available_mb=900,
            temp_files_count=10,
            active_processes=2,
            timestamp=time.time(),
        )

        resource_monitor._check_warnings(usage)

        assert warning_called
        assert "Memory usage" in warning_msg

    def test_error_callbacks(self, resource_monitor):
        """Test error callbacks."""
        error_called = False
        error_msg = None

        def error_callback(msg, usage):
            nonlocal error_called, error_msg
            error_called = True
            error_msg = msg

        resource_monitor.add_error_callback(error_callback)

        # Create usage exceeding limit
        usage = ResourceUsage(
            memory_mb=600,  # Exceeds limit
            disk_used_mb=100,
            disk_available_mb=900,
            temp_files_count=10,
            active_processes=2,
            timestamp=time.time(),
        )

        # Error callback should be called when limits are exceeded
        try:
            resource_monitor.check_limits(usage)
        except MemoryError:
            pass

        assert error_called
        assert "Memory usage" in error_msg

    def test_cleanup_all(self, resource_monitor):
        """Test cleaning up all resources."""
        # Create some temp files
        resource_monitor.temp_manager.create_temp_file()
        resource_monitor.temp_manager.create_temp_dir()

        stats = resource_monitor.cleanup_all()

        assert stats["temp_files_cleaned"] >= 1
        assert stats["temp_dirs_cleaned"] >= 1
        assert stats["processes_cleaned"] >= 0

    def test_get_stats(self, resource_monitor):
        """Test getting comprehensive statistics."""
        # Start monitoring to collect some data
        resource_monitor.start_monitoring()
        time.sleep(0.3)
        resource_monitor.stop_monitoring()

        stats = resource_monitor.get_stats()

        assert "current_usage" in stats
        assert "limits" in stats
        assert "temp_stats" in stats
        assert "process_stats" in stats
        assert "usage_history_count" in stats
        assert stats["usage_history_count"] > 0


class TestResourceContext:
    """Test resource_context context manager."""

    def test_resource_context_success(self):
        """Test resource context with successful operation."""
        limits = ResourceLimits(max_memory_mb=1024, cleanup_on_exit=True)

        with resource_context(limits) as monitor:
            assert isinstance(monitor, ResourceMonitor)
            assert monitor.monitoring

            # Create temp file
            temp_file = monitor.temp_manager.create_temp_file()
            assert temp_file.exists()

        # After context, monitoring should stop and cleanup should occur
        assert not monitor.monitoring
        assert not temp_file.exists()

    def test_resource_context_with_error(self):
        """Test resource context with error in operation."""
        limits = ResourceLimits(max_memory_mb=1024, cleanup_on_exit=True)

        temp_file = None
        try:
            with resource_context(limits) as monitor:
                # Create temp file
                temp_file = monitor.temp_manager.create_temp_file()
                assert temp_file.exists()

                # Simulate error
                raise ValueError("Test error")
        except ValueError:
            pass

        # Cleanup should still occur
        assert not temp_file.exists()

    def test_resource_context_no_cleanup(self):
        """Test resource context without cleanup."""
        limits = ResourceLimits(cleanup_on_exit=False)

        with resource_context(limits) as monitor:
            temp_file = monitor.temp_manager.create_temp_file()
            assert temp_file.exists()

        # File should still exist after context
        assert temp_file.exists()

        # Manual cleanup
        temp_file.unlink()


class TestUtilityFunctions:
    """Test utility functions."""

    def test_check_disk_space_sufficient(self):
        """Test disk space check with sufficient space."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Should not raise (assuming test system has >1MB free)
            check_disk_space(Path(tmpdir), required_mb=1)

    def test_check_disk_space_insufficient(self):
        """Test disk space check with insufficient space."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Request impossible amount
            with pytest.raises(DiskSpaceError, match="Insufficient disk space"):
                check_disk_space(Path(tmpdir), required_mb=1000000000)  # 1PB

    def test_check_memory_usage_sufficient(self):
        """Test memory check with sufficient memory."""
        # Get current memory usage
        process = psutil.Process()
        current_mb = process.memory_info().rss / 1024 / 1024

        # Should not raise
        check_memory_usage(max_mb=current_mb + 1000)

    def test_check_memory_usage_insufficient(self):
        """Test memory check with insufficient memory."""
        # Get current memory usage
        process = psutil.Process()
        current_mb = process.memory_info().rss / 1024 / 1024

        # Should raise
        with pytest.raises(MemoryError, match="Memory usage.*exceeds limit"):
            check_memory_usage(max_mb=current_mb - 10)  # Less than current


class TestResourceMonitorIntegration:
    """Integration tests for resource monitoring."""

    def test_full_monitoring_cycle(self):
        """Test a complete monitoring cycle with various operations."""
        limits = ResourceLimits(
            max_memory_mb=2048, max_disk_mb=1000, max_temp_files=10, max_processes=3
        )

        warnings = []

        def warning_handler(msg, usage):
            warnings.append(msg)

        with resource_context(limits) as monitor:
            monitor.add_warning_callback(warning_handler)

            # Create temp files
            files = []
            for i in range(5):
                file = monitor.temp_manager.create_temp_file(
                    content=f"Test content {i}" * 100
                )
                files.append(file)

            # Create temp directory
            temp_dir = monitor.temp_manager.create_temp_dir()
            (temp_dir / "test.txt").write_text("test" * 1000)

            # Wait for monitoring to capture usage
            time.sleep(0.3)

            # Get current stats
            stats = monitor.get_stats()
            assert stats["temp_stats"]["temp_files_count"] == 5
            assert stats["temp_stats"]["temp_dirs_count"] == 1

            # Check usage history was collected
            assert stats["usage_history_count"] > 0

        # All resources should be cleaned up
        for file in files:
            assert not file.exists()
        assert not temp_dir.exists()
