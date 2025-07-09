"""Unit tests for batch processing and optimization modules."""

import asyncio
import json
import tempfile
import time
from pathlib import Path
from unittest.mock import Mock, patch, AsyncMock

import pytest

from proof_sketcher.batch.parallel_processor import ParallelProcessor
from proof_sketcher.batch.project_scanner import ProjectScanner
from proof_sketcher.batch.cache_manager import CacheManager
from proof_sketcher.optimizations.batch_api import BatchOptimizer, BatchRequest, BatchResponse
from proof_sketcher.optimizations.smart_cache import SmartCache
from proof_sketcher.optimizations.performance import PerformanceBenchmark, PerformanceProfiler, PerformanceMonitor
from proof_sketcher.optimizations.resource_limits import ResourceLimiter, ResourceUsage
from proof_sketcher.optimizations.export_streaming import StreamingExporter, ExportStream
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.parser.models import TheoremInfo, ParseResult


@pytest.fixture
def sample_theorems():
    """Create sample theorems for testing."""
    return [
        TheoremInfo(
            name=f"theorem_{i}",
            statement=f"Statement {i}",
            proof=f"Proof {i}",
            line_number=i * 10,
            complexity_score=i + 1
        )
        for i in range(5)
    ]


@pytest.fixture
def sample_sketches():
    """Create sample proof sketches for testing."""
    return [
        ProofSketch(
            theorem_name=f"theorem_{i}",
            theorem_statement=f"Statement {i}",
            introduction=f"Introduction {i}",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description=f"Step for theorem {i}",
                    mathematical_content=f"Math {i}",
                    reasoning=f"Reasoning {i}",
                    tactics_used=["simp"],
                    intuition=f"Intuition {i}"
                )
            ],
            conclusion=f"Conclusion {i}",
            difficulty_level="easy"
        )
        for i in range(5)
    ]


class TestParallelProcessor:
    """Test parallel processing of theorems."""
    
    def test_processor_initialization(self):
        """Test processor initialization."""
        processor = ParallelProcessor(max_workers=4)
        assert processor.max_workers == 4
        assert processor.executor is not None
    
    def test_process_single_theorem(self, sample_theorems):
        """Test processing a single theorem."""
        processor = ParallelProcessor(max_workers=2)
        
        with patch.object(processor, '_generate_proof_sketch') as mock_generate:
            mock_sketch = ProofSketch(
                theorem_name="test",
                theorem_statement="test",
                introduction="test",
                key_steps=[],
                conclusion="test",
                difficulty_level="easy"
            )
            mock_generate.return_value = mock_sketch
            
            result = processor.process_theorem(sample_theorems[0])
            
            assert result["success"] is True
            assert result["theorem_name"] == sample_theorems[0].name
            assert result["proof_sketch"] == mock_sketch
    
    def test_process_directory(self, tmp_path):
        """Test processing a directory of Lean files."""
        # Create test files
        for i in range(3):
            lean_file = tmp_path / f"theorem{i}.lean"
            lean_file.write_text(f"theorem t{i} : Nat := {i}")
        
        processor = ParallelProcessor(max_workers=2)
        
        with patch.object(processor, 'process_file') as mock_process:
            mock_process.return_value = {
                "processed": 1,
                "successful": 1,
                "failed": 0,
                "results": [{"success": True}]
            }
            
            results = processor.process_directory(tmp_path)
            
            assert results["processed"] == 3
            assert results["successful"] == 3
            assert results["failed"] == 0
            assert mock_process.call_count == 3
    
    def test_batch_processing_with_limits(self, sample_theorems):
        """Test batch processing with resource limits."""
        processor = ParallelProcessor(
            max_workers=2,
            memory_limit_mb=100,
            timeout_minutes=5
        )
        
        with patch.object(processor, 'process_theorem') as mock_process:
            mock_process.return_value = {"success": True, "execution_time": 1.0}
            
            results = processor.process_batch(sample_theorems)
            
            assert len(results) == len(sample_theorems)
            assert all(r["success"] for r in results)
    
    def test_error_handling_in_parallel(self, sample_theorems):
        """Test error handling in parallel processing."""
        processor = ParallelProcessor(max_workers=2)
        
        with patch.object(processor, 'process_theorem') as mock_process:
            # First theorem succeeds, second fails
            mock_process.side_effect = [
                {"success": True},
                Exception("Processing error"),
                {"success": True}
            ]
            
            results = processor.process_batch(sample_theorems[:3])
            
            # Should handle errors gracefully
            assert len(results) == 3
            assert results[0]["success"] is True
            assert results[1]["success"] is False
            assert "error" in results[1]
            assert results[2]["success"] is True
    
    def test_progress_tracking(self, sample_theorems):
        """Test progress tracking during batch processing."""
        processor = ParallelProcessor(max_workers=2)
        
        progress_updates = []
        
        def track_progress(current, total, theorem_name):
            progress_updates.append((current, total, theorem_name))
        
        processor.progress_callback = track_progress
        
        with patch.object(processor, 'process_theorem') as mock_process:
            mock_process.return_value = {"success": True}
            
            processor.process_batch(sample_theorems)
            
            assert len(progress_updates) == len(sample_theorems)
            assert progress_updates[-1][0] == len(sample_theorems)


class TestProjectScanner:
    """Test project scanning and file discovery."""
    
    def test_scanner_initialization(self):
        """Test scanner initialization."""
        scanner = ProjectScanner()
        assert scanner.file_patterns is not None
        assert scanner.exclude_patterns is not None
    
    def test_scan_directory(self, tmp_path):
        """Test scanning a directory for Lean files."""
        # Create directory structure
        (tmp_path / "src").mkdir()
        (tmp_path / "test").mkdir()
        
        # Create Lean files
        (tmp_path / "src" / "main.lean").write_text("theorem main : True := trivial")
        (tmp_path / "src" / "helper.lean").write_text("theorem helper : False → True := by intro")
        (tmp_path / "test" / "test.lean").write_text("theorem test : 1 = 1 := rfl")
        
        # Create non-Lean file (should be ignored)
        (tmp_path / "README.md").write_text("# Project")
        
        scanner = ProjectScanner()
        files = scanner.scan_directory(tmp_path)
        
        assert len(files) == 3
        assert all(f.suffix == ".lean" for f in files)
        assert any("main.lean" in str(f) for f in files)
        assert any("helper.lean" in str(f) for f in files)
        assert any("test.lean" in str(f) for f in files)
    
    def test_scan_with_filters(self, tmp_path):
        """Test scanning with include/exclude filters."""
        # Create files
        (tmp_path / "include.lean").write_text("theorem include : True := trivial")
        (tmp_path / "exclude.lean").write_text("theorem exclude : True := trivial")
        (tmp_path / "test.lean").write_text("theorem test : True := trivial")
        
        scanner = ProjectScanner(
            include_patterns=["include*", "test*"],
            exclude_patterns=["exclude*"]
        )
        
        files = scanner.scan_directory(tmp_path)
        
        assert len(files) == 2
        assert any("include.lean" in str(f) for f in files)
        assert any("test.lean" in str(f) for f in files)
        assert not any("exclude.lean" in str(f) for f in files)
    
    def test_dependency_analysis(self, tmp_path):
        """Test dependency analysis of Lean files."""
        main_content = """
import Mathlib.Data.Nat.Basic
import ./helper

theorem main : Nat := 0
"""
        helper_content = """
import Mathlib.Logic.Basic

theorem helper : True := trivial
"""
        
        (tmp_path / "main.lean").write_text(main_content)
        (tmp_path / "helper.lean").write_text(helper_content)
        
        scanner = ProjectScanner()
        dependencies = scanner.analyze_dependencies(tmp_path)
        
        assert "main.lean" in dependencies
        assert "helper.lean" in dependencies
        assert "Mathlib.Data.Nat.Basic" in dependencies["main.lean"]
        assert "./helper" in dependencies["main.lean"]
    
    def test_project_statistics(self, tmp_path):
        """Test project statistics calculation."""
        # Create project structure
        for i in range(5):
            (tmp_path / f"theorem{i}.lean").write_text(
                f"theorem t{i} : Nat := {i}\n" * (i + 1)  # Varying sizes
            )
        
        scanner = ProjectScanner()
        stats = scanner.calculate_statistics(tmp_path)
        
        assert stats["total_files"] == 5
        assert stats["total_lines"] > 0
        assert stats["average_file_size"] > 0
        assert "file_size_distribution" in stats


class TestCacheManager:
    """Test cache management system."""
    
    def test_cache_manager_initialization(self, tmp_path):
        """Test cache manager initialization."""
        manager = CacheManager(cache_dir=tmp_path)
        assert manager.cache_dir == tmp_path
        assert manager.cache_dir.exists()
    
    def test_cache_operations(self, tmp_path, sample_sketches):
        """Test basic cache operations."""
        manager = CacheManager(cache_dir=tmp_path)
        
        key = "test_key"
        sketch = sample_sketches[0]
        
        # Store
        manager.put(key, sketch)
        assert manager.exists(key)
        
        # Retrieve
        retrieved = manager.get(key)
        assert retrieved is not None
        assert retrieved.theorem_name == sketch.theorem_name
        
        # Delete
        manager.delete(key)
        assert not manager.exists(key)
    
    def test_cache_expiration(self, tmp_path, sample_sketches):
        """Test cache expiration policies."""
        manager = CacheManager(
            cache_dir=tmp_path,
            default_ttl=0.001  # Very short TTL for testing
        )
        
        key = "expiring_key"
        sketch = sample_sketches[0]
        
        manager.put(key, sketch)
        assert manager.exists(key)
        
        # Wait for expiration (in real tests, we'd mock time)
        time.sleep(0.002)
        
        # Should be expired
        retrieved = manager.get(key)
        assert retrieved is None
    
    def test_cache_size_limits(self, tmp_path, sample_sketches):
        """Test cache size limits and eviction."""
        manager = CacheManager(
            cache_dir=tmp_path,
            max_size_mb=0.001  # Very small cache for testing
        )
        
        # Fill cache beyond limit
        for i, sketch in enumerate(sample_sketches):
            manager.put(f"key_{i}", sketch)
        
        # Should have evicted some entries
        cache_size = manager.get_cache_size()
        assert cache_size <= manager.max_size_mb * 1024 * 1024
    
    def test_cache_statistics(self, tmp_path, sample_sketches):
        """Test cache statistics collection."""
        manager = CacheManager(cache_dir=tmp_path)
        
        # Add some entries
        for i, sketch in enumerate(sample_sketches[:3]):
            manager.put(f"key_{i}", sketch)
        
        # Access some entries
        manager.get("key_0")
        manager.get("key_1")
        manager.get("nonexistent")  # Miss
        
        stats = manager.get_statistics()
        
        assert stats["total_entries"] == 3
        assert stats["cache_hits"] >= 2
        assert stats["cache_misses"] >= 1
        assert stats["hit_rate"] > 0


class TestBatchOptimizer:
    """Test batch processing optimization."""
    
    def test_batch_optimizer_initialization(self):
        """Test batch optimizer initialization."""
        optimizer = BatchOptimizer()
        assert optimizer.optimization_strategies is not None
    
    def test_batch_request_processing(self, sample_theorems):
        """Test batch request processing."""
        optimizer = BatchOptimizer()
        
        request = BatchRequest(
            theorems=sample_theorems,
            priority="normal",
            deadline=None
        )
        
        with patch.object(optimizer, '_process_batch_optimized') as mock_process:
            mock_response = BatchResponse(
                request_id="test_123",
                status="completed",
                results=[{"success": True} for _ in sample_theorems],
                processing_time=5.0,
                optimization_applied=["parallel_processing", "smart_caching"]
            )
            mock_process.return_value = mock_response
            
            response = optimizer.process_batch(request)
            
            assert response.status == "completed"
            assert len(response.results) == len(sample_theorems)
            assert response.processing_time > 0
    
    def test_optimization_strategy_selection(self, sample_theorems):
        """Test optimization strategy selection."""
        optimizer = BatchOptimizer()
        
        # Small batch
        small_request = BatchRequest(theorems=sample_theorems[:2])
        strategies = optimizer._select_optimization_strategies(small_request)
        assert "parallel_processing" in strategies
        
        # Large batch
        large_theorems = sample_theorems * 20  # 100 theorems
        large_request = BatchRequest(theorems=large_theorems)
        strategies = optimizer._select_optimization_strategies(large_request)
        assert "batch_grouping" in strategies
        assert "resource_pooling" in strategies
    
    def test_load_balancing(self, sample_theorems):
        """Test load balancing across workers."""
        optimizer = BatchOptimizer(max_workers=4)
        
        with patch.object(optimizer, '_get_worker_loads') as mock_loads:
            mock_loads.return_value = [10, 5, 8, 3]  # Worker loads
            
            assignments = optimizer._balance_load(sample_theorems)
            
            assert len(assignments) == 4  # One per worker
            # Worker 3 (load=3) should get more theorems
            assert len(assignments[3]) >= len(assignments[0])


class TestSmartCache:
    """Test smart caching system."""
    
    def test_smart_cache_initialization(self, tmp_path):
        """Test smart cache initialization."""
        cache = SmartCache(cache_dir=tmp_path)
        assert cache.cache_dir == tmp_path
        assert cache.predictor is not None
        assert cache.optimizer is not None
    
    def test_adaptive_caching(self, tmp_path, sample_sketches):
        """Test adaptive caching based on usage patterns."""
        cache = SmartCache(cache_dir=tmp_path)
        
        # Simulate access patterns
        for i in range(10):
            # Access first sketch frequently
            cache.get_or_compute("frequent_key", lambda: sample_sketches[0])
            
            # Access second sketch occasionally
            if i % 3 == 0:
                cache.get_or_compute("occasional_key", lambda: sample_sketches[1])
        
        # Analyze cache efficiency
        efficiency = cache.analyze_efficiency()
        
        assert efficiency["hit_rate"] > 0
        assert "frequent_key" in efficiency["hot_keys"]
    
    def test_predictive_preloading(self, tmp_path, sample_sketches):
        """Test predictive cache preloading."""
        cache = SmartCache(cache_dir=tmp_path)
        
        # Train access pattern
        patterns = [
            ("theorem_1", "theorem_2"),  # Often accessed together
            ("theorem_2", "theorem_3"),
            ("theorem_1", "theorem_3")
        ]
        
        cache.train_access_patterns(patterns)
        
        # Access theorem_1, should predict theorem_2 and theorem_3
        with patch.object(cache, '_preload_predicted') as mock_preload:
            cache.get_or_compute("theorem_1", lambda: sample_sketches[0])
            
            mock_preload.assert_called()
            predicted = mock_preload.call_args[0][0]
            assert "theorem_2" in predicted or "theorem_3" in predicted
    
    def test_cache_optimization(self, tmp_path, sample_sketches):
        """Test cache optimization strategies."""
        cache = SmartCache(cache_dir=tmp_path)
        
        # Fill cache with various access patterns
        for i, sketch in enumerate(sample_sketches):
            key = f"sketch_{i}"
            cache.put(key, sketch)
            
            # Simulate different access frequencies
            for _ in range(i + 1):
                cache.get(key)
        
        # Run optimization
        before_size = cache.get_cache_size()
        optimization_result = cache.optimize()
        after_size = cache.get_cache_size()
        
        assert optimization_result["entries_optimized"] >= 0
        assert optimization_result["space_saved"] >= 0


class TestPerformanceTools:
    """Test performance monitoring and profiling tools."""
    
    def test_performance_benchmark(self, sample_theorems):
        """Test performance benchmarking."""
        benchmark = PerformanceBenchmark()
        
        def mock_parse_function(theorem):
            time.sleep(0.001)  # Simulate work
            return ParseResult(theorems=[theorem], success=True)
        
        def mock_generate_function(theorem):
            time.sleep(0.002)  # Simulate work
            return ProofSketch(
                theorem_name=theorem.name,
                theorem_statement=theorem.statement,
                introduction="Test",
                key_steps=[],
                conclusion="Test",
                difficulty_level="easy"
            )
        
        results = benchmark.run(
            parse_function=mock_parse_function,
            generate_function=mock_generate_function,
            test_data=sample_theorems[:3]
        )
        
        assert "parse_time" in results
        assert "generate_time" in results
        assert "total_time" in results
        assert results["total_time"] > 0
    
    def test_performance_profiler(self, sample_theorems):
        """Test performance profiler."""
        profiler = PerformanceProfiler()
        
        def test_function():
            # Simulate some work
            for i in range(1000):
                _ = i ** 2
            time.sleep(0.001)
            return "result"
        
        with profiler:
            result = test_function()
        
        profile_data = profiler.get_profile_data()
        
        assert "execution_time" in profile_data
        assert "memory_usage" in profile_data
        assert "function_calls" in profile_data
        assert result == "result"
    
    def test_performance_monitor(self):
        """Test performance monitoring."""
        monitor = PerformanceMonitor()
        
        # Start monitoring
        monitor.start()
        
        # Simulate some work
        time.sleep(0.01)
        
        # Get metrics
        metrics = monitor.get_current_metrics()
        
        assert "cpu_usage" in metrics
        assert "memory_usage" in metrics
        assert "execution_time" in metrics
        
        monitor.stop()


class TestResourceLimiter:
    """Test resource limiting and management."""
    
    def test_resource_limiter_initialization(self):
        """Test resource limiter initialization."""
        limiter = ResourceLimiter(
            max_memory_mb=100,
            max_cpu_percent=80,
            max_execution_time=300
        )
        
        assert limiter.max_memory_mb == 100
        assert limiter.max_cpu_percent == 80
        assert limiter.max_execution_time == 300
    
    def test_memory_limit_enforcement(self):
        """Test memory limit enforcement."""
        limiter = ResourceLimiter(max_memory_mb=50)
        
        with patch('psutil.Process') as mock_process:
            # Mock high memory usage
            mock_process.return_value.memory_info.return_value.rss = 100 * 1024 * 1024  # 100MB
            
            usage = limiter.check_resource_usage()
            
            assert usage.memory_mb > limiter.max_memory_mb
            assert not usage.within_limits
    
    def test_execution_time_limiting(self):
        """Test execution time limiting."""
        limiter = ResourceLimiter(max_execution_time=1)  # 1 second
        
        def long_running_task():
            time.sleep(2)  # 2 seconds
            return "completed"
        
        with pytest.raises(TimeoutError):
            limiter.execute_with_limits(long_running_task)
    
    def test_resource_monitoring(self):
        """Test continuous resource monitoring."""
        limiter = ResourceLimiter()
        
        def task_with_monitoring():
            # Simulate work
            for i in range(100):
                usage = limiter.get_current_usage()
                assert isinstance(usage, ResourceUsage)
                time.sleep(0.001)
            return "done"
        
        result = limiter.execute_with_limits(task_with_monitoring)
        assert result == "done"


class TestStreamingExporter:
    """Test streaming export system."""
    
    def test_streaming_exporter_initialization(self, tmp_path):
        """Test streaming exporter initialization."""
        exporter = StreamingExporter(output_dir=tmp_path)
        assert exporter.output_dir == tmp_path
        assert exporter.active_streams == {}
    
    def test_create_export_stream(self, tmp_path, sample_sketches):
        """Test creating an export stream."""
        exporter = StreamingExporter(output_dir=tmp_path)
        
        stream = exporter.create_stream("test_stream", format="html")
        
        assert isinstance(stream, ExportStream)
        assert stream.stream_id == "test_stream"
        assert stream.format == "html"
        assert "test_stream" in exporter.active_streams
    
    def test_streaming_export(self, tmp_path, sample_sketches):
        """Test streaming export of proof sketches."""
        exporter = StreamingExporter(output_dir=tmp_path)
        
        stream = exporter.create_stream("batch_export", format="html")
        
        # Stream sketches one by one
        for sketch in sample_sketches:
            stream.add_sketch(sketch)
        
        # Finalize stream
        result = stream.finalize()
        
        assert result["success"] is True
        assert result["exported_count"] == len(sample_sketches)
        assert len(result["output_files"]) > 0
    
    def test_concurrent_streams(self, tmp_path, sample_sketches):
        """Test handling multiple concurrent export streams."""
        exporter = StreamingExporter(output_dir=tmp_path)
        
        # Create multiple streams
        html_stream = exporter.create_stream("html_export", format="html")
        md_stream = exporter.create_stream("md_export", format="markdown")
        
        # Add different sketches to each stream
        html_stream.add_sketch(sample_sketches[0])
        html_stream.add_sketch(sample_sketches[1])
        
        md_stream.add_sketch(sample_sketches[2])
        md_stream.add_sketch(sample_sketches[3])
        
        # Finalize both
        html_result = html_stream.finalize()
        md_result = md_stream.finalize()
        
        assert html_result["exported_count"] == 2
        assert md_result["exported_count"] == 2
        assert len(exporter.active_streams) == 0  # Should be cleaned up


if __name__ == "__main__":
    pytest.main([__file__, "-v"])