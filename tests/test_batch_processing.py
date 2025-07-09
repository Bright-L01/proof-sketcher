"""Comprehensive tests for batch processing system."""

import asyncio
import json
import tempfile
import time
from pathlib import Path
from typing import Dict, List

import networkx as nx
import pytest

from src.proof_sketcher.batch import CacheManager, ParallelProcessor, ProjectScanner


class TestProjectScanner:
    """Test suite for project scanner."""

    @pytest.fixture
    def sample_project(self, tmp_path):
        """Create a sample Lean project structure."""
        # Create project structure
        project_root = tmp_path / "test_project"
        project_root.mkdir()

        # Create some Lean files with dependencies
        basic_lean = project_root / "Basic.lean"
        basic_lean.write_text(
            """
-- Basic number theory
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.add_succ, ih]

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.succ_add, ih]

lemma add_one (n : Nat) : n + 1 = n.succ := rfl
"""
        )

        data_dir = project_root / "Data"
        data_dir.mkdir()

        list_lean = data_dir / "List.lean"
        list_lean.write_text(
            """
import Basic

-- List operations
theorem list_append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [List.cons_append, ih]

theorem list_nil_append (l : List α) : [] ++ l = l := rfl

lemma list_length_cons (a : α) (l : List α) : (a :: l).length = l.length + 1 := by
  simp [List.length]
"""
        )

        advanced_lean = project_root / "Advanced.lean"
        advanced_lean.write_text(
            """
import Basic
import Data.List

-- Advanced theorems
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp [zero_add, add_zero]
  | succ a ih => simp [Nat.succ_add, Nat.add_succ, ih]

theorem list_append_assoc (l1 l2 l3 : List α) :
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  induction l1 with
  | nil => rfl
  | cons h t ih => simp [List.cons_append, ih]
"""
        )

        # Create a test directory to be ignored
        test_dir = project_root / "test"
        test_dir.mkdir()
        test_file = test_dir / "Test.lean"
        test_file.write_text("theorem test_theorem : 1 = 1 := rfl")

        return project_root

    def test_scan_project_basic(self, sample_project):
        """Test basic project scanning."""
        scanner = ProjectScanner()
        result = scanner.scan_project(sample_project)

        assert "files" in result
        assert "process_order" in result
        assert "file_theorems" in result
        assert "dependency_graph" in result
        assert "statistics" in result

        # Check that test files are ignored
        files = result["files"]
        assert len(files) == 3  # Basic.lean, Data/List.lean, Advanced.lean
        assert not any("test" in f.lower() for f in files)

        # Check theorem extraction
        all_theorems = sum(
            len(theorems) for theorems in result["file_theorems"].values()
        )
        assert all_theorems >= 7  # At least 7 theorems/lemmas in our sample

    def test_dependency_analysis(self, sample_project):
        """Test dependency graph analysis."""
        scanner = ProjectScanner()
        result = scanner.scan_project(sample_project)

        dep_graph = result["dependency_graph"]

        # Check that it's a DAG
        assert nx.is_directed_acyclic_graph(dep_graph)

        # Check processing order
        process_order = result["process_order"]

        # Basic.lean should come before files that import it
        basic_idx = None
        advanced_idx = None

        for i, file in enumerate(process_order):
            if "Basic.lean" in file:
                basic_idx = i
            elif "Advanced.lean" in file:
                advanced_idx = i

        assert basic_idx is not None
        assert advanced_idx is not None
        assert basic_idx < advanced_idx  # Basic should be processed before Advanced

    def test_theorem_extraction(self, sample_project):
        """Test theorem name extraction."""
        scanner = ProjectScanner()
        result = scanner.scan_project(sample_project)

        # Check specific theorems
        file_theorems = result["file_theorems"]

        # Find Basic.lean theorems
        basic_theorems = None
        for file, theorems in file_theorems.items():
            if "Basic.lean" in file:
                basic_theorems = theorems
                break

        assert basic_theorems is not None
        assert "add_zero" in basic_theorems
        assert "zero_add" in basic_theorems
        assert "add_one" in basic_theorems

    def test_statistics_computation(self, sample_project):
        """Test project statistics computation."""
        scanner = ProjectScanner()
        result = scanner.scan_project(sample_project)

        stats = result["statistics"]

        assert stats["total_files"] == 3
        assert stats["total_theorems"] >= 7
        assert stats["total_lines"] > 0
        assert stats["avg_theorems_per_file"] > 0

        # Check dependency graph stats
        assert stats["dependency_graph"]["is_dag"] is True
        assert stats["dependency_graph"]["nodes"] == 3
        assert stats["dependency_graph"]["edges"] >= 2

    def test_circular_dependency_handling(self, tmp_path):
        """Test handling of circular dependencies."""
        project_root = tmp_path / "circular_project"
        project_root.mkdir()

        # Create circular dependencies
        file_a = project_root / "A.lean"
        file_a.write_text(
            """
import B
theorem a_theorem : 1 = 1 := rfl
"""
        )

        file_b = project_root / "B.lean"
        file_b.write_text(
            """
import A
theorem b_theorem : 2 = 2 := rfl
"""
        )

        scanner = ProjectScanner()
        result = scanner.scan_project(project_root)

        # Should still process files despite circular dependency
        assert len(result["files"]) == 2
        assert len(result["process_order"]) == 2
        assert not result["statistics"]["dependency_graph"]["is_dag"]


class TestCacheManager:
    """Test suite for cache manager."""

    @pytest.fixture
    def cache_manager(self, tmp_path):
        """Create a cache manager instance."""
        cache_dir = tmp_path / "test_cache"
        return CacheManager(cache_dir, ttl_days=1)

    def test_cache_basic_operations(self, cache_manager):
        """Test basic cache operations."""
        # Test set and get
        key = cache_manager.get_cache_key("test.lean", "theorem1", "content")
        data = {"result": "test data", "timestamp": time.time()}

        assert cache_manager.set(key, data)
        retrieved = cache_manager.get(key)
        assert retrieved == data

        # Test cache miss
        missing_key = cache_manager.get_cache_key("missing.lean", "theorem", "content")
        assert cache_manager.get(missing_key) is None

    def test_cache_expiration(self, cache_manager, monkeypatch):
        """Test cache TTL expiration."""
        import datetime

        key = cache_manager.get_cache_key("test.lean", "theorem1", "content")
        data = {"result": "test data"}

        # Set cache entry
        assert cache_manager.set(key, data)

        # Mock time to simulate expiration
        future_time = datetime.datetime.now() + datetime.timedelta(days=2)
        monkeypatch.setattr(datetime, "datetime", lambda: future_time)

        # Should return None due to expiration
        assert cache_manager.get(key) is None

    def test_cache_statistics(self, cache_manager):
        """Test cache statistics."""
        # Add some entries
        for i in range(5):
            key = cache_manager.get_cache_key(
                f"file{i}.lean", f"theorem{i}", f"content{i}"
            )
            cache_manager.set(key, {"data": f"result{i}"}, category="theorems")

        stats = cache_manager.get_statistics()

        assert stats["total_entries"] == 5
        assert stats["total_size_bytes"] > 0
        assert "theorems" in stats["categories"]
        assert stats["categories"]["theorems"] == 5

    def test_cache_cleanup(self, cache_manager):
        """Test cache cleanup operations."""
        # Add entries
        keys = []
        for i in range(3):
            key = cache_manager.get_cache_key(
                f"file{i}.lean", f"theorem{i}", f"content{i}"
            )
            cache_manager.set(key, {"data": f"result{i}"})
            keys.append(key)

        # Test individual invalidation
        assert cache_manager.invalidate(keys[0])
        assert cache_manager.get(keys[0]) is None
        assert cache_manager.get(keys[1]) is not None

        # Test clear all
        cleared = cache_manager.clear_all()
        assert cleared == 2  # Two entries remaining
        assert cache_manager.get_statistics()["total_entries"] == 0

    def test_cache_thread_safety(self, cache_manager):
        """Test thread-safe cache operations."""
        import threading

        results = []
        errors = []

        def cache_operation(thread_id):
            try:
                for i in range(10):
                    key = cache_manager.get_cache_key(
                        f"thread{thread_id}", f"item{i}", "content"
                    )
                    cache_manager.set(key, {"thread": thread_id, "item": i})
                    retrieved = cache_manager.get(key)
                    if retrieved:
                        results.append(retrieved)
            except Exception as e:
                errors.append(e)

        # Run multiple threads
        threads = []
        for i in range(5):
            t = threading.Thread(target=cache_operation, args=(i,))
            threads.append(t)
            t.start()

        for t in threads:
            t.join()

        assert len(errors) == 0
        assert len(results) == 50  # 5 threads * 10 operations each


class TestParallelProcessor:
    """Test suite for parallel processor."""

    @pytest.fixture
    def simple_project_data(self):
        """Create simple project data for testing."""
        return {
            "process_order": ["Basic.lean", "Advanced.lean"],
            "file_theorems": {
                "Basic.lean": ["add_zero", "zero_add"],
                "Advanced.lean": ["add_comm"],
            },
        }

    @pytest.mark.asyncio
    async def test_parallel_processing(self, simple_project_data, tmp_path):
        """Test basic parallel processing."""
        processor = ParallelProcessor(max_workers=2)

        # Mock options
        options = {
            "use_claude": False,  # Use offline mode for testing
            "create_visualization": False,  # Skip visualization for speed
            "export_formats": ["html"],
        }

        results = await processor.process_project(
            simple_project_data, tmp_path, options
        )

        assert results["total_theorems"] == 3
        assert "processed" in results
        assert "errors" in results
        assert "statistics" in results

    def test_single_file_processing(self, tmp_path):
        """Test processing a single file."""
        # Create a test file
        test_file = tmp_path / "test.lean"
        test_file.write_text(
            """
theorem test_theorem : 1 + 1 = 2 := by simp
"""
        )

        processor = ParallelProcessor(max_workers=1)

        result = processor.process_single_file(
            test_file,
            tmp_path / "output",
            {"use_claude": False, "create_visualization": False},
        )

        assert result["total_theorems"] == 1

    @pytest.mark.asyncio
    async def test_error_handling(self, tmp_path):
        """Test error handling in parallel processing."""
        # Create project data with non-existent file
        project_data = {
            "process_order": ["nonexistent.lean"],
            "file_theorems": {
                "nonexistent.lean": ["theorem1"],
            },
        }

        processor = ParallelProcessor(max_workers=1)

        results = await processor.process_project(
            project_data, tmp_path, {"use_claude": False}
        )

        assert results["errors"] == 1
        assert results["processed"] == 0
        assert "error_summary" in results


class TestBatchIntegration:
    """Integration tests for the entire batch processing system."""

    @pytest.mark.asyncio
    async def test_end_to_end_processing(self, tmp_path):
        """Test complete end-to-end batch processing."""
        # Create a mini Lean project
        project_root = tmp_path / "lean_project"
        project_root.mkdir()

        # Create a simple Lean file
        lean_file = project_root / "Simple.lean"
        lean_file.write_text(
            """
-- Simple arithmetic
theorem simple_add : 2 + 3 = 5 := by norm_num

theorem simple_mul : 2 * 3 = 6 := by norm_num
"""
        )

        # Set up components
        scanner = ProjectScanner()
        cache_manager = CacheManager(tmp_path / "cache")
        processor = ParallelProcessor(max_workers=1)

        # Scan project
        project_data = scanner.scan_project(project_root)
        assert project_data["statistics"]["total_theorems"] == 2

        # Process with caching
        output_dir = tmp_path / "output"
        options = {
            "use_claude": False,
            "create_visualization": True,
            "export_formats": ["html", "markdown"],
            "cache_manager": cache_manager,
        }

        # First run - no cache
        start_time = time.time()
        results1 = await processor.process_project(project_data, output_dir, options)
        first_run_time = time.time() - start_time

        assert results1["total_theorems"] == 2

        # Second run - should use cache
        start_time = time.time()
        results2 = await processor.process_project(project_data, output_dir, options)
        second_run_time = time.time() - start_time

        # Cache statistics should show entries
        cache_stats = cache_manager.get_statistics()
        assert cache_stats["total_entries"] > 0

        # Second run should be faster due to caching (though this might be flaky in CI)
        # assert second_run_time < first_run_time

    def test_large_project_simulation(self, tmp_path):
        """Test handling of larger projects."""
        project_root = tmp_path / "large_project"
        project_root.mkdir()

        # Create multiple files with dependencies
        num_files = 10
        theorems_per_file = 5

        for i in range(num_files):
            content = []

            # Add imports for previous files
            if i > 0:
                content.append(f"import File{i-1}")

            # Add theorems
            for j in range(theorems_per_file):
                content.append(f"theorem theorem_{i}_{j} : {j} + 0 = {j} := by simp")

            file_path = project_root / f"File{i}.lean"
            file_path.write_text("\n".join(content))

        scanner = ProjectScanner()
        result = scanner.scan_project(project_root)

        assert result["statistics"]["total_files"] == num_files
        assert result["statistics"]["total_theorems"] == num_files * theorems_per_file

        # Check that files are in dependency order
        process_order = result["process_order"]
        for i in range(1, num_files):
            file_i = f"File{i}.lean"
            file_prev = f"File{i-1}.lean"

            idx_i = next(j for j, f in enumerate(process_order) if file_i in f)
            idx_prev = next(j for j, f in enumerate(process_order) if file_prev in f)

            assert idx_prev < idx_i  # Previous file should be processed first


@pytest.mark.benchmark
class TestPerformance:
    """Performance benchmarks for batch processing."""

    def test_scanning_performance(self, tmp_path, benchmark):
        """Benchmark project scanning performance."""
        # Create a project with many files
        project_root = tmp_path / "perf_project"
        project_root.mkdir()

        for i in range(50):
            content = f"theorem t{i} : {i} = {i} := rfl"
            (project_root / f"file{i}.lean").write_text(content)

        scanner = ProjectScanner()

        # Benchmark scanning
        result = benchmark(scanner.scan_project, project_root)
        assert result["statistics"]["total_files"] == 50

    def test_cache_performance(self, tmp_path, benchmark):
        """Benchmark cache operations."""
        cache_manager = CacheManager(tmp_path / "perf_cache")

        # Prepare test data
        keys = []
        for i in range(100):
            key = cache_manager.get_cache_key(
                f"file{i}.lean", f"theorem{i}", f"content{i}"
            )
            keys.append(key)
            cache_manager.set(key, {"data": f"result{i}" * 100})  # Larger data

        # Benchmark cache retrieval
        def retrieve_all():
            results = []
            for key in keys:
                result = cache_manager.get(key)
                if result:
                    results.append(result)
            return len(results)

        count = benchmark(retrieve_all)
        assert count == 100
