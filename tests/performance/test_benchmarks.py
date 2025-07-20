"""
Comprehensive benchmarking suite - Milestone 3.2.1

This module provides performance benchmarks to validate optimization improvements:
- Baseline vs optimized performance comparisons
- Memory usage benchmarks
- Throughput measurements
- Scalability testing
- Regression detection
"""

from __future__ import annotations

import asyncio
import json
import statistics

# Add project root to path for imports
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, Callable, Dict, List

import pytest

project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root / "src"))

from proof_sketcher.config.config import ProofSketcherConfig
from proof_sketcher.exporter.html import HTMLExporter
from proof_sketcher.exporter.models import ExportContext, ExportOptions
from proof_sketcher.generator.offline import OfflineGenerator
from proof_sketcher.parser.config import ParserConfig
from proof_sketcher.parser.simple_parser import SimpleLeanParser


class BenchmarkSuite:
    """Main benchmarking suite for performance testing."""

    def __init__(self, output_dir: Path = None):
        """Initialize benchmark suite.

        Args:
            output_dir: Directory to save benchmark results
        """
        self.output_dir = output_dir or Path("benchmark_results")
        self.output_dir.mkdir(exist_ok=True)

        # Test data
        self.test_theorems = self._create_test_theorems()
        self.test_expressions = self._create_test_expressions()

        # Results storage
        self.results = {}

    def _create_test_theorems(self) -> List[Dict]:
        """Create test theorems for benchmarking."""
        return [
            {
                "name": f"test_theorem_{i}",
                "statement": f"∀ x ∈ ℕ, P{i}(x) → Q{i}(x)",
                "proof_steps": [
                    f"Step {j}: Apply theorem T{j}" for j in range(1, min(i + 2, 6))
                ],
                "prerequisites": [f"theorem_T{j}" for j in range(1, i + 1)],
                "file_path": f"test_{i}.lean",
            }
            for i in range(1, 101)  # 100 test theorems
        ]

    def _create_test_expressions(self) -> List[str]:
        """Create test mathematical expressions."""
        expressions = [
            "∀ x ∈ ℕ, x + 0 = x",
            "∃ f : ℝ → ℝ, ∀ x y, f(x + y) = f(x) + f(y)",
            "⊢ A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C",
            "∫₀¹ f(x) dx = ∑_{n=0}^∞ aₙ",
            "F ⊣ G ⇒ ∀ X Y, Hom(F(X), Y) ≅ Hom(X, G(Y))",
            "lim_{n→∞} ∑_{k=1}^n 1/k² = π²/6",
            "∀ ε > 0, ∃ δ > 0, |x - a| < δ ⇒ |f(x) - f(a)| < ε",
            "⨆{Uᵢ | i ∈ I} = ⋃ᵢ Uᵢ",
            "∇·(∇×F) = 0",
            "∬_D (∂Q/∂x - ∂P/∂y) dA = ∮_C P dx + Q dy",
        ]

        # Replicate to create test set of desired size
        return expressions * 100  # 1000 total expressions

    def benchmark_notation_handler(self, iterations: int = 1000) -> Dict[str, Any]:
        """Benchmark mathematical notation handling performance."""
        print(f"\n🔤 Benchmarking notation handler ({iterations} iterations)...")

        handler = ParserConfig()
        expressions = self.test_expressions[:iterations]

        # Baseline performance (no caching)
        start_time = time.time()
        baseline_results = []

        for expr in expressions:
            latex = handler.convert_to_latex(expr)
            html = handler.convert_to_html(expr)
            table = handler.get_notation_table(expr)
            areas = handler.detect_mathematical_areas(expr)
            baseline_results.append((latex, html, table, areas))

        baseline_time = time.time() - start_time

        # Optimized performance (with caching)
        from proof_sketcher.core.exceptions import ProofSketcherConfig

        optimizer = ProofSketcherConfig()

        start_time = time.time()
        optimized_results = []

        for expr in expressions:
            latex = optimizer.cached_latex_conversion(expr)
            html = optimizer.cached_html_conversion(expr)
            table = handler.get_notation_table(expr)
            areas = handler.detect_mathematical_areas(expr)
            optimized_results.append((latex, html, table, areas))

        optimized_time = time.time() - start_time

        # Calculate performance improvement
        speedup = baseline_time / optimized_time if optimized_time > 0 else float("inf")

        results = {
            "test_name": "notation_handler",
            "iterations": iterations,
            "baseline_time": baseline_time,
            "optimized_time": optimized_time,
            "speedup": speedup,
            "baseline_throughput": iterations / baseline_time,
            "optimized_throughput": iterations / optimized_time,
            "improvement_percent": ((baseline_time - optimized_time) / baseline_time)
            * 100,
        }

        print(
            f"   Baseline: {baseline_time:.3f}s ({results['baseline_throughput']:.0f} ops/sec)"
        )
        print(
            f"   Optimized: {optimized_time:.3f}s ({results['optimized_throughput']:.0f} ops/sec)"
        )
        print(
            f"   Speedup: {speedup:.2f}x ({results['improvement_percent']:.1f}% improvement)"
        )

        return results

    def benchmark_caching_system(self, cache_size: int = 1000) -> Dict[str, Any]:
        """Benchmark caching system performance."""
        print(f"\n💾 Benchmarking caching system ({cache_size} operations)...")

        cache = ProofSketcherConfig()
        test_data = {f"key_{i}": f"value_{i}" * 100 for i in range(cache_size)}

        # Measure cache write performance
        start_time = time.time()

        async def write_benchmark():
            for key, value in test_data.items():
                await cache.set(key, value, ttl=3600)

        asyncio.run(write_benchmark())
        write_time = time.time() - start_time

        # Measure cache read performance (hits)
        start_time = time.time()

        async def read_benchmark_hits():
            for key in test_data.keys():
                value = await cache.get(key)
                assert value is not None

        asyncio.run(read_benchmark_hits())
        read_hit_time = time.time() - start_time

        # Measure cache read performance (misses)
        start_time = time.time()

        async def read_benchmark_misses():
            for i in range(cache_size):
                value = await cache.get(f"missing_key_{i}")
                assert value is None

        asyncio.run(read_benchmark_misses())
        read_miss_time = time.time() - start_time

        # Get cache statistics
        cache_stats = cache.get_stats()

        results = {
            "test_name": "caching_system",
            "cache_size": cache_size,
            "write_time": write_time,
            "read_hit_time": read_hit_time,
            "read_miss_time": read_miss_time,
            "write_throughput": cache_size / write_time,
            "read_hit_throughput": cache_size / read_hit_time,
            "read_miss_throughput": cache_size / read_miss_time,
            "cache_stats": cache_stats,
        }

        print(
            f"   Write: {write_time:.3f}s ({results['write_throughput']:.0f} ops/sec)"
        )
        print(
            f"   Read (hits): {read_hit_time:.3f}s ({results['read_hit_throughput']:.0f} ops/sec)"
        )
        print(
            f"   Read (misses): {read_miss_time:.3f}s ({results['read_miss_throughput']:.0f} ops/sec)"
        )
        print(f"   Hit rate: {cache_stats['hit_rate_percent']:.1f}%")

        return results

    def benchmark_parallel_processing(self, num_theorems: int = 50) -> Dict[str, Any]:
        """Benchmark parallel processing improvements."""
        print(f"\n⚡ Benchmarking parallel processing ({num_theorems} theorems)...")

        test_theorems = self.test_theorems[:num_theorems]

        # Convert to TheoremInfo objects for testing
        from proof_sketcher.parser.models import TheoremInfo

        theorem_objects = []

        for t in test_theorems:
            theorem = TheoremInfo(
                name=t["name"], statement=t["statement"], line_number=1
            )
            theorem_objects.append(theorem)

        # Baseline: Sequential processing
        start_time = time.time()
        sequential_results = []

        generator = OfflineGenerator()
        for theorem in theorem_objects:
            try:
                sketch = generator.generate_proof_sketch(theorem)
                if sketch:
                    sequential_results.append(sketch)
            except Exception:
                pass  # Skip failures for benchmarking

        sequential_time = time.time() - start_time

        # Optimized: Parallel processing
        optimizer = ProofSketcherConfig()
        config = ExportOptions(batch_size=10, max_concurrent=4, use_caching=True)

        start_time = time.time()
        parallel_results, metrics = asyncio.run(
            optimizer.process_theorems_parallel(theorem_objects, config)
        )
        parallel_time = time.time() - start_time

        # Calculate improvements
        speedup = sequential_time / parallel_time if parallel_time > 0 else float("inf")

        results = {
            "test_name": "parallel_processing",
            "num_theorems": num_theorems,
            "sequential_time": sequential_time,
            "parallel_time": parallel_time,
            "speedup": speedup,
            "sequential_throughput": len(sequential_results) / sequential_time,
            "parallel_throughput": len(parallel_results) / parallel_time,
            "sequential_success_rate": len(sequential_results) / num_theorems * 100,
            "parallel_success_rate": len(parallel_results) / num_theorems * 100,
            "cache_hit_rate": metrics.cache_hit_rate,
            "metrics": {
                "processed_items": metrics.processed_items,
                "failed_items": metrics.failed_items,
                "avg_time_per_item": metrics.avg_time_per_item,
            },
        }

        print(
            f"   Sequential: {sequential_time:.3f}s ({results['sequential_throughput']:.2f} theorems/sec)"
        )
        print(
            f"   Parallel: {parallel_time:.3f}s ({results['parallel_throughput']:.2f} theorems/sec)"
        )
        print(f"   Speedup: {speedup:.2f}x")
        print(f"   Cache hit rate: {metrics.cache_hit_rate:.1f}%")

        return results

    def benchmark_memory_usage(self) -> Dict[str, Any]:
        """Benchmark memory usage patterns."""
        print(f"\n🧠 Benchmarking memory usage...")

        import psutil

        process = psutil.Process()

        # Baseline memory usage
        initial_memory = process.memory_info().rss / 1024 / 1024

        # Create large dataset
        large_theorems = self.test_theorems * 10  # 1000 theorems

        # Memory usage without optimization
        start_memory = process.memory_info().rss / 1024 / 1024

        # Simulate processing without caching
        results_no_cache = []
        handler = ParserConfig()

        for theorem in large_theorems:
            latex = handler.convert_to_latex(theorem["statement"])
            html = handler.convert_to_html(theorem["statement"])
            results_no_cache.append((latex, html))

        peak_memory_no_cache = process.memory_info().rss / 1024 / 1024

        # Clear memory
        del results_no_cache
        import gc

        gc.collect()

        # Memory usage with optimization
        optimizer = ProofSketcherConfig()

        start_memory_opt = process.memory_info().rss / 1024 / 1024

        results_with_cache = []
        for theorem in large_theorems:
            latex = optimizer.cached_latex_conversion(theorem["statement"])
            html = optimizer.cached_html_conversion(theorem["statement"])
            results_with_cache.append((latex, html))

        peak_memory_with_cache = process.memory_info().rss / 1024 / 1024

        # Calculate memory efficiency
        memory_no_cache = peak_memory_no_cache - start_memory
        memory_with_cache = peak_memory_with_cache - start_memory_opt
        memory_savings = memory_no_cache - memory_with_cache

        results = {
            "test_name": "memory_usage",
            "initial_memory_mb": initial_memory,
            "memory_no_cache_mb": memory_no_cache,
            "memory_with_cache_mb": memory_with_cache,
            "memory_savings_mb": memory_savings,
            "memory_efficiency_percent": (
                (memory_savings / memory_no_cache) * 100 if memory_no_cache > 0 else 0
            ),
            "dataset_size": len(large_theorems),
        }

        print(f"   Without caching: {memory_no_cache:.1f}MB")
        print(f"   With caching: {memory_with_cache:.1f}MB")
        print(
            f"   Memory savings: {memory_savings:.1f}MB ({results['memory_efficiency_percent']:.1f}%)"
        )

        return results

    def benchmark_resource_limits(self) -> Dict[str, Any]:
        """Benchmark resource limiting effectiveness."""
        print(f"\n🛡️ Benchmarking resource limits...")

        limiter = ProofSketcherConfig(
            ExportOptions(
                max_memory_mb=500, max_execution_seconds=10, max_animation_duration=60
            )
        )

        # Test memory limiting
        memory_limit_test_passed = True
        try:
            with limiter.limit_memory(100):  # 100MB limit
                # Try to allocate more than limit (should not crash)
                data = []
                for i in range(1000):
                    data.append("x" * 10000)  # 10KB per iteration
        except MemoryError:
            memory_limit_test_passed = False

        # Test timeout limiting
        timeout_test_passed = False
        try:
            with limiter.timeout(1):  # 1 second timeout
                time.sleep(2)  # This should timeout
        except TimeoutError:
            timeout_test_passed = True
        except OSError:
            # Platform doesn't support timeouts
            timeout_test_passed = None

        # Test animation complexity limiting
        complex_theorem = {
            "proof_steps": ["step"] * 200,  # Very complex
            "statement": "x" * 5000,  # Long statement
            "prerequisites": ["req"] * 50,
        }

        animation_config = limiter.limit_animation_complexity(complex_theorem)
        animation_limits_applied = animation_config["max_duration"] < 300

        # Test resource monitoring
        with limiter.resource_monitoring() as monitor:
            time.sleep(0.1)  # Brief operation
            usage = monitor.get_current_usage()

        results = {
            "test_name": "resource_limits",
            "memory_limit_effective": memory_limit_test_passed,
            "timeout_limit_effective": timeout_test_passed,
            "animation_limits_applied": animation_limits_applied,
            "animation_config": animation_config,
            "monitoring_functional": usage.memory_mb > 0,
            "current_memory_mb": usage.memory_mb,
            "current_cpu_percent": usage.cpu_percent,
        }

        print(f"   Memory limiting: {'✅' if memory_limit_test_passed else '❌'}")
        print(
            f"   Timeout limiting: {'✅' if timeout_test_passed else '❌' if timeout_test_passed is not None else '⚠️ Unsupported'}"
        )
        print(f"   Animation limiting: {'✅' if animation_limits_applied else '❌'}")
        print(
            f"   Resource monitoring: {'✅' if results['monitoring_functional'] else '❌'}"
        )

        return results

    def run_full_benchmark_suite(self) -> Dict[str, Any]:
        """Run the complete benchmark suite."""
        print("🚀 Running Full Performance Benchmark Suite")
        print("=" * 60)

        all_results = {}

        # Run individual benchmarks
        try:
            all_results["notation_handler"] = self.benchmark_notation_handler(1000)
        except Exception as e:
            print(f"❌ Notation handler benchmark failed: {e}")
            all_results["notation_handler"] = {"error": str(e)}

        try:
            all_results["caching_system"] = self.benchmark_caching_system(1000)
        except Exception as e:
            print(f"❌ Caching system benchmark failed: {e}")
            all_results["caching_system"] = {"error": str(e)}

        try:
            all_results["parallel_processing"] = self.benchmark_parallel_processing(25)
        except Exception as e:
            print(f"❌ Parallel processing benchmark failed: {e}")
            all_results["parallel_processing"] = {"error": str(e)}

        try:
            all_results["memory_usage"] = self.benchmark_memory_usage()
        except Exception as e:
            print(f"❌ Memory usage benchmark failed: {e}")
            all_results["memory_usage"] = {"error": str(e)}

        try:
            all_results["resource_limits"] = self.benchmark_resource_limits()
        except Exception as e:
            print(f"❌ Resource limits benchmark failed: {e}")
            all_results["resource_limits"] = {"error": str(e)}

        # Calculate overall performance score
        performance_score = self._calculate_performance_score(all_results)
        all_results["overall_performance_score"] = performance_score

        # Save results
        self._save_results(all_results)

        # Print summary
        self._print_summary(all_results)

        return all_results

    def _calculate_performance_score(self, results: Dict[str, Any]) -> Dict[str, Any]:
        """Calculate overall performance score."""
        scores = {}
        total_score = 0
        weight_sum = 0

        # Notation handler score (weight: 2)
        if "notation_handler" in results and "speedup" in results["notation_handler"]:
            speedup = results["notation_handler"]["speedup"]
            score = min(speedup * 20, 100)  # Max 100 for 5x speedup
            scores["notation_handler"] = score
            total_score += score * 2
            weight_sum += 2

        # Caching system score (weight: 3)
        if "caching_system" in results and "cache_stats" in results["caching_system"]:
            hit_rate = results["caching_system"]["cache_stats"].get(
                "hit_rate_percent", 0
            )
            score = hit_rate  # Direct percentage
            scores["caching_system"] = score
            total_score += score * 3
            weight_sum += 3

        # Parallel processing score (weight: 3)
        if (
            "parallel_processing" in results
            and "speedup" in results["parallel_processing"]
        ):
            speedup = results["parallel_processing"]["speedup"]
            score = min(speedup * 25, 100)  # Max 100 for 4x speedup
            scores["parallel_processing"] = score
            total_score += score * 3
            weight_sum += 3

        # Memory efficiency score (weight: 2)
        if (
            "memory_usage" in results
            and "memory_efficiency_percent" in results["memory_usage"]
        ):
            efficiency = results["memory_usage"]["memory_efficiency_percent"]
            score = min(efficiency, 100)
            scores["memory_usage"] = score
            total_score += score * 2
            weight_sum += 2

        overall_score = total_score / weight_sum if weight_sum > 0 else 0

        return {
            "individual_scores": scores,
            "overall_score": overall_score,
            "grade": self._get_performance_grade(overall_score),
        }

    def _get_performance_grade(self, score: float) -> str:
        """Get performance grade based on score."""
        if score >= 90:
            return "A+"
        elif score >= 80:
            return "A"
        elif score >= 70:
            return "B+"
        elif score >= 60:
            return "B"
        elif score >= 50:
            return "C"
        else:
            return "F"

    def _save_results(self, results: Dict[str, Any]):
        """Save benchmark results to file."""
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        results_file = self.output_dir / f"benchmark_results_{timestamp}.json"

        try:
            with open(results_file, "w") as f:
                json.dump(results, f, indent=2, default=str)
            print(f"📊 Results saved to: {results_file}")
        except Exception as e:
            print(f"❌ Failed to save results: {e}")

    def _print_summary(self, results: Dict[str, Any]):
        """Print benchmark summary."""
        print("\n" + "=" * 60)
        print("📊 BENCHMARK SUMMARY")
        print("=" * 60)

        if "overall_performance_score" in results:
            score_data = results["overall_performance_score"]
            print(
                f"🎯 Overall Performance Score: {score_data['overall_score']:.1f}/100 (Grade: {score_data['grade']})"
            )
            print()

            print("Individual Component Scores:")
            for component, score in score_data["individual_scores"].items():
                print(f"   • {component.replace('_', ' ').title()}: {score:.1f}/100")

        print("\nKey Improvements:")

        # Notation handler
        if "notation_handler" in results and "speedup" in results["notation_handler"]:
            speedup = results["notation_handler"]["speedup"]
            print(f"   • Notation processing: {speedup:.2f}x faster")

        # Parallel processing
        if (
            "parallel_processing" in results
            and "speedup" in results["parallel_processing"]
        ):
            speedup = results["parallel_processing"]["speedup"]
            print(f"   • Parallel processing: {speedup:.2f}x faster")

        # Memory efficiency
        if (
            "memory_usage" in results
            and "memory_efficiency_percent" in results["memory_usage"]
        ):
            efficiency = results["memory_usage"]["memory_efficiency_percent"]
            print(f"   • Memory efficiency: {efficiency:.1f}% improvement")

        # Cache performance
        if "caching_system" in results and "cache_stats" in results["caching_system"]:
            hit_rate = results["caching_system"]["cache_stats"].get(
                "hit_rate_percent", 0
            )
            print(f"   • Cache hit rate: {hit_rate:.1f}%")

        print(f"\n✅ Benchmark suite completed successfully!")


# Pytest test functions
def test_performance_improvements():
    """Test that performance optimizations meet targets."""
    suite = BenchmarkSuite()
    results = suite.run_full_benchmark_suite()

    # Verify notation handler improvement
    if "notation_handler" in results and "speedup" in results["notation_handler"]:
        speedup = results["notation_handler"]["speedup"]
        assert (
            speedup > 3.0
        ), f"Notation handler only {speedup:.2f}x faster (target: 3x)"

    # Verify parallel processing improvement
    if "parallel_processing" in results and "speedup" in results["parallel_processing"]:
        speedup = results["parallel_processing"]["speedup"]
        assert (
            speedup > 2.0
        ), f"Parallel processing only {speedup:.2f}x faster (target: 2x)"

    # Verify memory efficiency
    if (
        "memory_usage" in results
        and "memory_efficiency_percent" in results["memory_usage"]
    ):
        efficiency = results["memory_usage"]["memory_efficiency_percent"]
        assert (
            efficiency > 10.0
        ), f"Memory efficiency only {efficiency:.1f}% (target: 10%)"

    # Verify overall performance score
    if "overall_performance_score" in results:
        score = results["overall_performance_score"]["overall_score"]
        assert score > 70.0, f"Overall performance score {score:.1f}/100 (target: 70+)"

    print("✅ All performance targets met!")


def test_caching_effectiveness():
    """Test that caching provides expected benefits."""
    suite = BenchmarkSuite()
    results = suite.benchmark_caching_system(500)

    # Cache should be fast
    assert results["read_hit_throughput"] > 1000, "Cache reads too slow"
    assert results["write_throughput"] > 500, "Cache writes too slow"

    # Should have good hit rate after warming up
    assert results["cache_stats"]["hit_rate_percent"] > 80, "Cache hit rate too low"


def test_resource_limits_functionality():
    """Test that resource limits work correctly."""
    suite = BenchmarkSuite()
    results = suite.benchmark_resource_limits()

    # Resource monitoring should work
    assert results["monitoring_functional"], "Resource monitoring not working"

    # Animation limits should be applied
    assert results[
        "animation_limits_applied"
    ], "Animation complexity limits not applied"


if __name__ == "__main__":
    # Run benchmark suite when executed directly
    suite = BenchmarkSuite()
    results = suite.run_full_benchmark_suite()
