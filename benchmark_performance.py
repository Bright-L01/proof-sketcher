#!/usr/bin/env python3
"""Performance benchmarking script for Proof Sketcher.

This script tests the performance optimizations and generates before/after metrics.
"""

import asyncio
import json
import logging
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List

import matplotlib.pyplot as plt
import numpy as np

# Setup logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)

# Test data
SAMPLE_THEOREMS = [
    """theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]""",
    """theorem mul_comm (m n : Nat) : m * n = n * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_mul, ih, mul_succ]""",
    """theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [succ_add, succ_add, succ_add, ih]""",
    """theorem zero_add (n : Nat) : 0 + n = n := by
  rfl""",
    """theorem succ_add (m n : Nat) : (m + 1) + n = (m + n) + 1 := by
  rw [Nat.add_succ]""",
]


class PerformanceBenchmark:
    """Comprehensive performance benchmarking."""

    def __init__(self, output_dir: Path):
        """Initialize benchmark.

        Args:
            output_dir: Directory for benchmark results
        """
        self.output_dir = output_dir
        self.output_dir.mkdir(parents=True, exist_ok=True)

        self.results: Dict[str, List[Dict[str, Any]]] = {
            "baseline": [],
            "optimized": [],
        }

    async def run_all_benchmarks(self):
        """Run all performance benchmarks."""
        logger.info("Starting performance benchmarks...")

        # Run baseline benchmarks (without optimizations)
        logger.info("Running baseline benchmarks...")
        await self._run_baseline_benchmarks()

        # Apply optimizations
        logger.info("Applying optimizations...")
        self._apply_optimizations()

        # Run optimized benchmarks
        logger.info("Running optimized benchmarks...")
        await self._run_optimized_benchmarks()

        # Generate reports
        logger.info("Generating performance reports...")
        self._generate_reports()

        logger.info("Benchmarks completed!")

    async def _run_baseline_benchmarks(self):
        """Run baseline performance tests."""
        from src.proof_sketcher.config.config import ProofSketcherConfig
        from src.proof_sketcher.core.batch_processor import BatchProcessor

        config = ProofSketcherConfig()
        config.cache_dir = self.output_dir / "baseline_cache"
        config.cache_dir.mkdir(exist_ok=True)

        processor = BatchProcessor(config)

        # Test different scales
        for scale in [1, 5, 10, 20]:
            result = await self._benchmark_batch_processing(
                processor, scale, "baseline"
            )
            self.results["baseline"].append(result)

    async def _run_optimized_benchmarks(self):
        """Run optimized performance tests."""
        from src.proof_sketcher.config.config import ProofSketcherConfig
        from src.proof_sketcher.core.batch_processor import BatchProcessor

        config = ProofSketcherConfig()
        config.cache_dir = self.output_dir / "optimized_cache"
        config.cache_dir.mkdir(exist_ok=True)

        processor = BatchProcessor(config)

        # Test different scales with optimizations
        for scale in [1, 5, 10, 20]:
            result = await self._benchmark_batch_processing(
                processor, scale, "optimized"
            )
            self.results["optimized"].append(result)

    def _apply_optimizations(self):
        """Apply performance optimizations."""
        from src.proof_sketcher.core.optimization import optimize_batch_processor

        optimize_batch_processor()

    async def _benchmark_batch_processing(
        self, processor: Any, scale: int, version: str
    ) -> Dict[str, Any]:
        """Benchmark batch processing at given scale.

        Args:
            processor: Batch processor instance
            scale: Number of theorems to process
            version: Version identifier (baseline/optimized)

        Returns:
            Benchmark results
        """
        # Create test files
        test_dir = self.output_dir / f"{version}_test_{scale}"
        test_dir.mkdir(exist_ok=True)

        for i in range(scale):
            theorem_file = test_dir / f"theorem_{i}.lean"
            theorem_content = SAMPLE_THEOREMS[i % len(SAMPLE_THEOREMS)]
            theorem_file.write_text(theorem_content)

        # Benchmark processing
        start_time = time.perf_counter()
        start_memory = self._get_memory_usage()

        try:
            output_dir = self.output_dir / f"{version}_output_{scale}"
            output_dir.mkdir(exist_ok=True)

            stats = await processor.process_directory(
                input_dir=test_dir, output_dir=output_dir, pattern="*.lean"
            )

            end_time = time.perf_counter()
            end_memory = self._get_memory_usage()

            return {
                "version": version,
                "scale": scale,
                "duration": end_time - start_time,
                "memory_usage": end_memory - start_memory,
                "theorems_processed": stats.total_theorems,
                "files_processed": stats.total_files,
                "success_rate": (
                    stats.successful_files / stats.total_files
                    if stats.total_files > 0
                    else 0
                ),
                "throughput": (
                    stats.total_theorems / (end_time - start_time)
                    if end_time > start_time
                    else 0
                ),
                "cache_stats": (
                    self._get_cache_stats() if version == "optimized" else None
                ),
            }

        except Exception as e:
            logger.error(f"Benchmark failed for {version} scale {scale}: {e}")
            return {
                "version": version,
                "scale": scale,
                "error": str(e),
                "duration": 0,
                "memory_usage": 0,
                "theorems_processed": 0,
                "files_processed": 0,
                "success_rate": 0,
                "throughput": 0,
            }

    def _get_memory_usage(self) -> int:
        """Get current memory usage in bytes."""
        import psutil

        process = psutil.Process()
        return process.memory_info().rss

    def _get_cache_stats(self) -> Dict[str, Any]:
        """Get cache statistics if available."""
        try:
            from src.proof_sketcher.core.optimization import get_optimization_stats

            return get_optimization_stats()
        except Exception:
            return {}

    def _generate_reports(self):
        """Generate comprehensive performance reports."""
        # Save raw data
        results_file = self.output_dir / "benchmark_results.json"
        with open(results_file, "w") as f:
            json.dump(self.results, f, indent=2, default=str)

        # Generate comparison report
        self._generate_comparison_report()

        # Generate performance charts
        self._generate_performance_charts()

        # Generate summary report
        self._generate_summary_report()

    def _generate_comparison_report(self):
        """Generate before/after comparison report."""
        report = []
        report.append("# Performance Benchmark Report")
        report.append(f"Generated: {time.strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("")

        # Compare results by scale
        scales = sorted(set(r["scale"] for r in self.results["baseline"]))

        report.append("## Performance Comparison by Scale")
        report.append("")
        report.append(
            "| Scale | Baseline Time (s) | Optimized Time (s) | Improvement | Baseline Throughput | Optimized Throughput | Memory Improvement |"
        )
        report.append(
            "|-------|-------------------|-------------------|-------------|---------------------|----------------------|-------------------|"
        )

        for scale in scales:
            baseline = next(
                (r for r in self.results["baseline"] if r["scale"] == scale), None
            )
            optimized = next(
                (r for r in self.results["optimized"] if r["scale"] == scale), None
            )

            if (
                baseline
                and optimized
                and "error" not in baseline
                and "error" not in optimized
            ):
                time_improvement = (
                    (baseline["duration"] - optimized["duration"])
                    / baseline["duration"]
                ) * 100
                throughput_improvement = (
                    (
                        (optimized["throughput"] - baseline["throughput"])
                        / baseline["throughput"]
                    )
                    * 100
                    if baseline["throughput"] > 0
                    else 0
                )
                memory_improvement = (
                    (
                        (baseline["memory_usage"] - optimized["memory_usage"])
                        / baseline["memory_usage"]
                    )
                    * 100
                    if baseline["memory_usage"] > 0
                    else 0
                )

                report.append(
                    f"| {scale} | {baseline['duration']:.2f} | {optimized['duration']:.2f} | {time_improvement:+.1f}% | {baseline['throughput']:.2f} | {optimized['throughput']:.2f} | {memory_improvement:+.1f}% |"
                )

        report.append("")
        report.append("## Key Improvements")
        report.append("")

        # Calculate overall improvements
        total_baseline_time = sum(
            r["duration"] for r in self.results["baseline"] if "error" not in r
        )
        total_optimized_time = sum(
            r["duration"] for r in self.results["optimized"] if "error" not in r
        )

        if total_baseline_time > 0:
            overall_improvement = (
                (total_baseline_time - total_optimized_time) / total_baseline_time
            ) * 100
            report.append(
                f"- **Overall Processing Time**: {overall_improvement:.1f}% improvement"
            )

        avg_baseline_throughput = np.mean(
            [
                r["throughput"]
                for r in self.results["baseline"]
                if "error" not in r and r["throughput"] > 0
            ]
        )
        avg_optimized_throughput = np.mean(
            [
                r["throughput"]
                for r in self.results["optimized"]
                if "error" not in r and r["throughput"] > 0
            ]
        )

        if avg_baseline_throughput > 0:
            throughput_improvement = (
                (avg_optimized_throughput - avg_baseline_throughput)
                / avg_baseline_throughput
            ) * 100
            report.append(
                f"- **Average Throughput**: {throughput_improvement:.1f}% improvement"
            )

        # Write report
        report_file = self.output_dir / "performance_report.md"
        with open(report_file, "w") as f:
            f.write("\n".join(report))

    def _generate_performance_charts(self):
        """Generate performance visualization charts."""
        try:
            # Extract data for plotting
            baseline_scales = [
                r["scale"] for r in self.results["baseline"] if "error" not in r
            ]
            baseline_times = [
                r["duration"] for r in self.results["baseline"] if "error" not in r
            ]
            baseline_throughput = [
                r["throughput"] for r in self.results["baseline"] if "error" not in r
            ]

            optimized_scales = [
                r["scale"] for r in self.results["optimized"] if "error" not in r
            ]
            optimized_times = [
                r["duration"] for r in self.results["optimized"] if "error" not in r
            ]
            optimized_throughput = [
                r["throughput"] for r in self.results["optimized"] if "error" not in r
            ]

            # Create subplots
            fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(15, 10))
            fig.suptitle("Proof Sketcher Performance Benchmarks", fontsize=16)

            # Processing time comparison
            ax1.plot(
                baseline_scales, baseline_times, "o-", label="Baseline", color="red"
            )
            ax1.plot(
                optimized_scales,
                optimized_times,
                "o-",
                label="Optimized",
                color="green",
            )
            ax1.set_xlabel("Number of Theorems")
            ax1.set_ylabel("Processing Time (seconds)")
            ax1.set_title("Processing Time Comparison")
            ax1.legend()
            ax1.grid(True, alpha=0.3)

            # Throughput comparison
            ax2.plot(
                baseline_scales,
                baseline_throughput,
                "o-",
                label="Baseline",
                color="red",
            )
            ax2.plot(
                optimized_scales,
                optimized_throughput,
                "o-",
                label="Optimized",
                color="green",
            )
            ax2.set_xlabel("Number of Theorems")
            ax2.set_ylabel("Throughput (theorems/second)")
            ax2.set_title("Throughput Comparison")
            ax2.legend()
            ax2.grid(True, alpha=0.3)

            # Performance improvement bar chart
            improvements = []
            scales_with_improvements = []
            for scale in baseline_scales:
                baseline = next(
                    (r for r in self.results["baseline"] if r["scale"] == scale), None
                )
                optimized = next(
                    (r for r in self.results["optimized"] if r["scale"] == scale), None
                )

                if baseline and optimized and baseline["duration"] > 0:
                    improvement = (
                        (baseline["duration"] - optimized["duration"])
                        / baseline["duration"]
                    ) * 100
                    improvements.append(improvement)
                    scales_with_improvements.append(scale)

            bars = ax3.bar(
                scales_with_improvements, improvements, color="skyblue", alpha=0.7
            )
            ax3.set_xlabel("Number of Theorems")
            ax3.set_ylabel("Time Improvement (%)")
            ax3.set_title("Performance Improvement by Scale")
            ax3.grid(True, alpha=0.3)

            # Add value labels on bars
            for bar, improvement in zip(bars, improvements):
                height = bar.get_height()
                ax3.text(
                    bar.get_x() + bar.get_width() / 2.0,
                    height,
                    f"{improvement:.1f}%",
                    ha="center",
                    va="bottom",
                )

            # Memory usage comparison
            baseline_memory = [
                r["memory_usage"] / 1024 / 1024
                for r in self.results["baseline"]
                if "error" not in r
            ]  # Convert to MB
            optimized_memory = [
                r["memory_usage"] / 1024 / 1024
                for r in self.results["optimized"]
                if "error" not in r
            ]

            ax4.plot(
                baseline_scales, baseline_memory, "o-", label="Baseline", color="red"
            )
            ax4.plot(
                optimized_scales,
                optimized_memory,
                "o-",
                label="Optimized",
                color="green",
            )
            ax4.set_xlabel("Number of Theorems")
            ax4.set_ylabel("Memory Usage (MB)")
            ax4.set_title("Memory Usage Comparison")
            ax4.legend()
            ax4.grid(True, alpha=0.3)

            plt.tight_layout()
            chart_file = self.output_dir / "performance_charts.png"
            plt.savefig(chart_file, dpi=300, bbox_inches="tight")
            plt.close()

            logger.info(f"Performance charts saved to {chart_file}")

        except Exception as e:
            logger.error(f"Failed to generate charts: {e}")

    def _generate_summary_report(self):
        """Generate executive summary report."""
        summary = {
            "benchmark_timestamp": time.time(),
            "total_tests_run": len(self.results["baseline"])
            + len(self.results["optimized"]),
            "baseline_results": len(self.results["baseline"]),
            "optimized_results": len(self.results["optimized"]),
            "optimizations_applied": [
                "Batch processing optimization",
                "Advanced caching with TTL",
                "Lazy loading for templates",
                "Parallel export processing",
                "Resource limiting and monitoring",
                "Connection pooling for subprocesses",
            ],
            "key_metrics": self._calculate_key_metrics(),
            "recommendations": self._generate_recommendations(),
        }

        summary_file = self.output_dir / "performance_summary.json"
        with open(summary_file, "w") as f:
            json.dump(summary, f, indent=2, default=str)

    def _calculate_key_metrics(self) -> Dict[str, Any]:
        """Calculate key performance metrics."""
        baseline_valid = [r for r in self.results["baseline"] if "error" not in r]
        optimized_valid = [r for r in self.results["optimized"] if "error" not in r]

        if not baseline_valid or not optimized_valid:
            return {"error": "Insufficient valid data for metrics calculation"}

        # Calculate average improvements
        avg_time_improvement = 0
        avg_throughput_improvement = 0
        avg_memory_improvement = 0
        valid_comparisons = 0

        for scale in set(r["scale"] for r in baseline_valid):
            baseline = next((r for r in baseline_valid if r["scale"] == scale), None)
            optimized = next((r for r in optimized_valid if r["scale"] == scale), None)

            if baseline and optimized:
                if baseline["duration"] > 0:
                    time_imp = (
                        (baseline["duration"] - optimized["duration"])
                        / baseline["duration"]
                    ) * 100
                    avg_time_improvement += time_imp

                if baseline["throughput"] > 0:
                    throughput_imp = (
                        (optimized["throughput"] - baseline["throughput"])
                        / baseline["throughput"]
                    ) * 100
                    avg_throughput_improvement += throughput_imp

                if baseline["memory_usage"] > 0:
                    memory_imp = (
                        (baseline["memory_usage"] - optimized["memory_usage"])
                        / baseline["memory_usage"]
                    ) * 100
                    avg_memory_improvement += memory_imp

                valid_comparisons += 1

        if valid_comparisons > 0:
            avg_time_improvement /= valid_comparisons
            avg_throughput_improvement /= valid_comparisons
            avg_memory_improvement /= valid_comparisons

        return {
            "average_time_improvement_percent": round(avg_time_improvement, 2),
            "average_throughput_improvement_percent": round(
                avg_throughput_improvement, 2
            ),
            "average_memory_improvement_percent": round(avg_memory_improvement, 2),
            "max_baseline_throughput": max(r["throughput"] for r in baseline_valid),
            "max_optimized_throughput": max(r["throughput"] for r in optimized_valid),
            "total_baseline_time": sum(r["duration"] for r in baseline_valid),
            "total_optimized_time": sum(r["duration"] for r in optimized_valid),
            "valid_test_comparisons": valid_comparisons,
        }

    def _generate_recommendations(self) -> List[str]:
        """Generate performance recommendations."""
        recommendations = [
            "Enable caching for production workloads to improve repeat processing performance",
            "Use batch processing for multiple theorems to leverage optimizations",
            "Configure resource limits based on available system resources",
            "Monitor performance metrics in production using the built-in monitoring system",
            "Consider using parallel export for large documentation generation tasks",
        ]

        # Add specific recommendations based on results
        key_metrics = self._calculate_key_metrics()
        if isinstance(key_metrics, dict) and "error" not in key_metrics:
            if key_metrics.get("average_memory_improvement_percent", 0) < 10:
                recommendations.append(
                    "Consider tuning cache size limits for better memory efficiency"
                )

            if key_metrics.get("average_throughput_improvement_percent", 0) > 50:
                recommendations.append(
                    "Significant throughput improvements observed - optimizations are highly effective"
                )

        return recommendations


async def main():
    """Main benchmark execution."""
    output_dir = Path("benchmark_results")

    benchmark = PerformanceBenchmark(output_dir)
    await benchmark.run_all_benchmarks()

    print(f"\nBenchmark completed! Results saved to: {output_dir.absolute()}")
    print(f"Performance report: {output_dir / 'performance_report.md'}")
    print(f"Performance charts: {output_dir / 'performance_charts.png'}")
    print(f"Summary data: {output_dir / 'performance_summary.json'}")


if __name__ == "__main__":
    asyncio.run(main())
