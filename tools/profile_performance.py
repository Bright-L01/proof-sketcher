#!/usr/bin/env python3
"""
Performance profiler for Proof Sketcher - Milestone 3.2.1

This module provides comprehensive performance profiling capabilities including:
- CPU profiling with cProfile
- Memory profiling with tracemalloc
- Bottleneck identification
- Performance regression detection
- Resource usage monitoring
"""

import cProfile
import io
import json
import logging
import pstats
import statistics
import sys
import time
import tracemalloc
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import psutil

# Add project root to path for imports
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root / "src"))

from proof_sketcher.batch.parallel_processor import ParallelProcessor
from proof_sketcher.batch.project_scanner import ProjectScanner
from proof_sketcher.exporter.html import HTMLExporter
from proof_sketcher.exporter.models import ExportContext, ExportOptions
from proof_sketcher.generator.offline import OfflineGenerator
from proof_sketcher.parser.lean_parser import LeanParser
from proof_sketcher.parser.mathlib_notation import MathlibNotationHandler


@dataclass
class PerformanceMetrics:
    """Performance metrics for a single operation."""

    operation_name: str
    execution_time: float
    memory_peak_mb: float
    memory_current_mb: float
    cpu_percent: float
    function_calls: int
    profile_data: str
    bottlenecks: List[Dict[str, Any]] = field(default_factory=list)
    timestamp: datetime = field(default_factory=datetime.now)


@dataclass
class SystemMetrics:
    """System-wide performance metrics."""

    cpu_count: int
    total_memory_gb: float
    available_memory_gb: float
    disk_usage_percent: float
    load_average: Optional[Tuple[float, float, float]]
    timestamp: datetime = field(default_factory=datetime.now)


class PerformanceProfiler:
    """Comprehensive performance profiler for Proof Sketcher."""

    def __init__(self, output_dir: Path = None):
        """Initialize profiler.

        Args:
            output_dir: Directory to save profiling results
        """
        self.output_dir = output_dir or Path("performance_results")
        self.output_dir.mkdir(exist_ok=True)

        self.logger = logging.getLogger(__name__)
        self.system_metrics = self._collect_system_metrics()

        # Performance baseline (to detect regressions)
        self.baseline_file = self.output_dir / "baseline_metrics.json"
        self.baseline_metrics = self._load_baseline()

    def _collect_system_metrics(self) -> SystemMetrics:
        """Collect current system metrics."""
        memory = psutil.virtual_memory()
        disk = psutil.disk_usage("/")

        load_avg = None
        if hasattr(psutil, "getloadavg"):
            try:
                load_avg = psutil.getloadavg()
            except (AttributeError, OSError):
                pass

        return SystemMetrics(
            cpu_count=psutil.cpu_count(),
            total_memory_gb=memory.total / (1024**3),
            available_memory_gb=memory.available / (1024**3),
            disk_usage_percent=disk.percent,
            load_average=load_avg,
        )

    def _load_baseline(self) -> Dict[str, float]:
        """Load baseline performance metrics."""
        if self.baseline_file.exists():
            try:
                with open(self.baseline_file, "r") as f:
                    return json.load(f)
            except Exception as e:
                self.logger.warning(f"Failed to load baseline: {e}")
        return {}

    def _save_baseline(self, metrics: Dict[str, float]):
        """Save baseline performance metrics."""
        try:
            with open(self.baseline_file, "w") as f:
                json.dump(metrics, f, indent=2)
        except Exception as e:
            self.logger.error(f"Failed to save baseline: {e}")

    def profile_theorem_processing(
        self, theorem_file: Path, theorem_name: str = None
    ) -> PerformanceMetrics:
        """Profile single theorem processing end-to-end.

        Args:
            theorem_file: Path to Lean file containing theorem
            theorem_name: Specific theorem to process (optional)

        Returns:
            Performance metrics for the operation
        """
        self.logger.info(f"Profiling theorem processing: {theorem_file}")

        # Setup profiler
        pr = cProfile.Profile()
        pr.enable()

        # Track memory
        tracemalloc.start()
        initial_memory = self._get_memory_usage()

        # Track CPU
        process = psutil.Process()
        cpu_start = process.cpu_percent()

        start_time = time.time()

        try:
            # Process theorem
            result = self._process_single_theorem(theorem_file, theorem_name)
            success = True
        except Exception as e:
            self.logger.error(f"Processing failed: {e}")
            result = None
            success = False

        end_time = time.time()
        execution_time = end_time - start_time

        # Get memory peak
        current_memory, peak_memory = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        # Get CPU usage
        cpu_end = process.cpu_percent()
        avg_cpu = (cpu_start + cpu_end) / 2

        pr.disable()

        # Analyze profiling results
        s = io.StringIO()
        ps = pstats.Stats(pr, stream=s).sort_stats("cumulative")
        ps.print_stats(30)  # Top 30 functions

        bottlenecks = self._identify_bottlenecks(ps)

        metrics = PerformanceMetrics(
            operation_name=f"theorem_processing_{theorem_file.stem}",
            execution_time=execution_time,
            memory_peak_mb=peak_memory / 1024 / 1024,
            memory_current_mb=current_memory / 1024 / 1024,
            cpu_percent=avg_cpu,
            function_calls=ps.total_calls,
            profile_data=s.getvalue(),
            bottlenecks=bottlenecks,
        )

        # Save detailed results
        self._save_metrics(metrics)

        return metrics

    def profile_batch_processing(
        self, project_dir: Path, max_theorems: int = 10
    ) -> PerformanceMetrics:
        """Profile batch processing performance.

        Args:
            project_dir: Directory containing Lean project
            max_theorems: Maximum number of theorems to process

        Returns:
            Performance metrics for batch operation
        """
        self.logger.info(f"Profiling batch processing: {project_dir}")

        # Setup profiler
        pr = cProfile.Profile()
        pr.enable()

        # Track memory
        tracemalloc.start()

        # Track CPU
        process = psutil.Process()
        cpu_start = process.cpu_percent()

        start_time = time.time()

        try:
            # Process batch
            result = self._process_batch(project_dir, max_theorems)
            success = True
        except Exception as e:
            self.logger.error(f"Batch processing failed: {e}")
            result = None
            success = False

        end_time = time.time()
        execution_time = end_time - start_time

        # Get memory peak
        current_memory, peak_memory = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        # Get CPU usage
        cpu_end = process.cpu_percent()
        avg_cpu = (cpu_start + cpu_end) / 2

        pr.disable()

        # Analyze profiling results
        s = io.StringIO()
        ps = pstats.Stats(pr, stream=s).sort_stats("cumulative")
        ps.print_stats(30)

        bottlenecks = self._identify_bottlenecks(ps)

        metrics = PerformanceMetrics(
            operation_name=f"batch_processing_{project_dir.name}",
            execution_time=execution_time,
            memory_peak_mb=peak_memory / 1024 / 1024,
            memory_current_mb=current_memory / 1024 / 1024,
            cpu_percent=avg_cpu,
            function_calls=ps.total_calls,
            profile_data=s.getvalue(),
            bottlenecks=bottlenecks,
        )

        self._save_metrics(metrics)
        return metrics

    def profile_notation_handler(self, test_size: int = 1000) -> PerformanceMetrics:
        """Profile mathematical notation handler performance.

        Args:
            test_size: Number of notation conversions to perform

        Returns:
            Performance metrics for notation handling
        """
        self.logger.info(f"Profiling notation handler with {test_size} conversions")

        # Create test data
        test_expressions = [
            "∀ x ∈ ℕ, x + 0 = x",
            "∃ f : ℝ → ℝ, ∀ x y, f(x + y) = f(x) + f(y)",
            "⊢ A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C",
            "∫₀¹ f(x) dx = ∑_{n=0}^∞ aₙ",
            "F ⊣ G ⇒ ∀ X Y, Hom(F(X), Y) ≅ Hom(X, G(Y))",
        ] * (test_size // 5)

        # Setup profiler
        pr = cProfile.Profile()
        pr.enable()

        # Track memory
        tracemalloc.start()

        start_time = time.time()

        # Test notation conversions
        handler = MathlibNotationHandler()
        results = []

        for expr in test_expressions:
            latex = handler.convert_to_latex(expr)
            html = handler.convert_to_html(expr)
            table = handler.get_notation_table(expr)
            areas = handler.detect_mathematical_areas(expr)
            results.append((latex, html, table, areas))

        end_time = time.time()
        execution_time = end_time - start_time

        # Get memory peak
        current_memory, peak_memory = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        pr.disable()

        # Analyze results
        s = io.StringIO()
        ps = pstats.Stats(pr, stream=s).sort_stats("cumulative")
        ps.print_stats(20)

        bottlenecks = self._identify_bottlenecks(ps)

        metrics = PerformanceMetrics(
            operation_name=f"notation_handler_{test_size}",
            execution_time=execution_time,
            memory_peak_mb=peak_memory / 1024 / 1024,
            memory_current_mb=current_memory / 1024 / 1024,
            cpu_percent=0,  # Not measured for this test
            function_calls=ps.total_calls,
            profile_data=s.getvalue(),
            bottlenecks=bottlenecks,
        )

        self._save_metrics(metrics)
        return metrics

    def _process_single_theorem(
        self, theorem_file: Path, theorem_name: str = None
    ) -> Dict:
        """Process a single theorem for profiling."""
        # Parse theorem
        parser = LeanParser()
        theorems = parser.parse_file(theorem_file)

        if not theorems:
            raise ValueError(f"No theorems found in {theorem_file}")

        # Select theorem
        theorem = (
            theorems[0]
            if not theorem_name
            else next((t for t in theorems if t.name == theorem_name), theorems[0])
        )

        # Generate explanation
        generator = OfflineGenerator()
        sketch = generator.generate_proof_sketch(theorem)

        if not sketch:
            raise ValueError(f"Failed to generate sketch for {theorem.name}")

        # Export
        output_dir = self.output_dir / "test_exports"
        output_dir.mkdir(exist_ok=True)

        options = ExportOptions(output_dir=output_dir)
        exporter = HTMLExporter(options)
        context = ExportContext(
            format=exporter.format, output_dir=output_dir, sketches=[sketch]
        )

        result = exporter.export_single(sketch, context)

        return {"theorem": theorem, "sketch": sketch, "export_result": result}

    def _process_batch(self, project_dir: Path, max_theorems: int) -> Dict:
        """Process a batch of theorems for profiling."""
        import asyncio

        # Scan project
        scanner = ProjectScanner()
        project_data = scanner.scan_project(project_dir)

        # Limit theorems
        total_theorems = min(project_data["statistics"]["total_theorems"], max_theorems)

        # Process batch
        processor = ParallelProcessor(max_workers=2)  # Limited for profiling

        async def run_batch():
            options = {
                "use_claude": False,  # Use offline mode for consistent profiling
                "create_visualization": False,  # Skip for speed
                "export_formats": ["html"],
            }

            result = await processor.process_project(
                project_data, self.output_dir / "batch_test", options
            )
            return result

        return asyncio.run(run_batch())

    def _identify_bottlenecks(self, stats: pstats.Stats) -> List[Dict[str, Any]]:
        """Identify performance bottlenecks from profiling stats."""
        bottlenecks = []

        # Get function stats
        stats_dict = stats.get_stats_profile().func_profiles

        # Sort by cumulative time
        sorted_stats = sorted(
            stats_dict.items(), key=lambda x: x[1].cumtime, reverse=True
        )[
            :15
        ]  # Top 15 functions

        for func_info, profile in sorted_stats:
            filename, line_num, func_name = func_info

            # Skip built-in functions
            if filename.startswith("<"):
                continue

            # Calculate per-call time
            per_call_time = (
                profile.cumtime / profile.ncalls if profile.ncalls > 0 else 0
            )

            # Identify bottlenecks (functions taking >50ms cumulative or >10ms per call)
            if profile.cumtime > 0.05 or per_call_time > 0.01:
                bottlenecks.append(
                    {
                        "function": func_name,
                        "filename": filename,
                        "line_number": line_num,
                        "total_time": profile.cumtime,
                        "per_call_time": per_call_time,
                        "call_count": profile.ncalls,
                        "percentage": (
                            (profile.cumtime / stats.total_tt) * 100
                            if stats.total_tt > 0
                            else 0
                        ),
                    }
                )

        return bottlenecks

    def _get_memory_usage(self) -> float:
        """Get current memory usage in bytes."""
        process = psutil.Process()
        return process.memory_info().rss

    def _save_metrics(self, metrics: PerformanceMetrics):
        """Save performance metrics to file."""
        timestamp = metrics.timestamp.strftime("%Y%m%d_%H%M%S")
        filename = f"{metrics.operation_name}_{timestamp}.json"
        output_file = self.output_dir / filename

        # Convert to dict for JSON serialization
        metrics_dict = {
            "operation_name": metrics.operation_name,
            "execution_time": metrics.execution_time,
            "memory_peak_mb": metrics.memory_peak_mb,
            "memory_current_mb": metrics.memory_current_mb,
            "cpu_percent": metrics.cpu_percent,
            "function_calls": metrics.function_calls,
            "bottlenecks": metrics.bottlenecks,
            "timestamp": metrics.timestamp.isoformat(),
            "system_metrics": {
                "cpu_count": self.system_metrics.cpu_count,
                "total_memory_gb": self.system_metrics.total_memory_gb,
                "available_memory_gb": self.system_metrics.available_memory_gb,
                "disk_usage_percent": self.system_metrics.disk_usage_percent,
                "load_average": self.system_metrics.load_average,
            },
        }

        try:
            with open(output_file, "w") as f:
                json.dump(metrics_dict, f, indent=2)

            # Also save detailed profile
            profile_file = (
                self.output_dir / f"{metrics.operation_name}_{timestamp}_profile.txt"
            )
            with open(profile_file, "w") as f:
                f.write(metrics.profile_data)

        except Exception as e:
            self.logger.error(f"Failed to save metrics: {e}")

    def compare_with_baseline(self, metrics: PerformanceMetrics) -> Dict[str, Any]:
        """Compare current metrics with baseline performance.

        Args:
            metrics: Current performance metrics

        Returns:
            Comparison report
        """
        baseline_key = metrics.operation_name.split("_")[
            0
        ]  # e.g., "theorem_processing"
        baseline_time = self.baseline_metrics.get(f"{baseline_key}_time", 0)
        baseline_memory = self.baseline_metrics.get(f"{baseline_key}_memory", 0)

        if baseline_time == 0:
            # No baseline yet, save current as baseline
            self.baseline_metrics[f"{baseline_key}_time"] = metrics.execution_time
            self.baseline_metrics[f"{baseline_key}_memory"] = metrics.memory_peak_mb
            self._save_baseline(self.baseline_metrics)

            return {
                "status": "baseline_set",
                "message": f"Set new baseline for {baseline_key}",
                "time_regression": 0,
                "memory_regression": 0,
            }

        # Calculate regressions
        time_regression = (
            (metrics.execution_time - baseline_time) / baseline_time
        ) * 100
        memory_regression = (
            (metrics.memory_peak_mb - baseline_memory) / baseline_memory
        ) * 100

        # Determine status
        status = "improved"
        if time_regression > 20 or memory_regression > 20:
            status = "regressed"
        elif time_regression > 5 or memory_regression > 5:
            status = "degraded"

        return {
            "status": status,
            "time_regression_percent": time_regression,
            "memory_regression_percent": memory_regression,
            "baseline_time": baseline_time,
            "current_time": metrics.execution_time,
            "baseline_memory": baseline_memory,
            "current_memory": metrics.memory_peak_mb,
        }

    def generate_performance_report(self) -> str:
        """Generate a comprehensive performance report."""
        report_lines = [
            "# Proof Sketcher Performance Report",
            f"Generated: {datetime.now().isoformat()}",
            "",
            "## System Information",
            f"- CPU Cores: {self.system_metrics.cpu_count}",
            f"- Total Memory: {self.system_metrics.total_memory_gb:.1f} GB",
            f"- Available Memory: {self.system_metrics.available_memory_gb:.1f} GB",
            f"- Disk Usage: {self.system_metrics.disk_usage_percent:.1f}%",
        ]

        if self.system_metrics.load_average:
            load_1, load_5, load_15 = self.system_metrics.load_average
            report_lines.append(
                f"- Load Average: {load_1:.2f}, {load_5:.2f}, {load_15:.2f}"
            )

        report_lines.extend(["", "## Performance Metrics", ""])

        # Load recent metrics
        metric_files = list(self.output_dir.glob("*.json"))
        if metric_files:
            report_lines.append("### Recent Performance Results")
            report_lines.append("")

            for metric_file in sorted(metric_files)[-5:]:  # Last 5 results
                try:
                    with open(metric_file, "r") as f:
                        data = json.load(f)

                    report_lines.extend(
                        [
                            f"**{data['operation_name']}**",
                            f"- Execution Time: {data['execution_time']:.3f}s",
                            f"- Memory Peak: {data['memory_peak_mb']:.1f} MB",
                            f"- Function Calls: {data['function_calls']:,}",
                            f"- Top Bottlenecks: {len(data['bottlenecks'])}",
                            "",
                        ]
                    )

                except Exception as e:
                    self.logger.warning(f"Failed to read {metric_file}: {e}")

        # Baseline comparison
        if self.baseline_metrics:
            report_lines.extend(["## Baseline Comparison", ""])

            for key, value in self.baseline_metrics.items():
                if key.endswith("_time"):
                    operation = key.replace("_time", "")
                    report_lines.append(f"- {operation} baseline: {value:.3f}s")
                elif key.endswith("_memory"):
                    operation = key.replace("_memory", "")
                    report_lines.append(
                        f"- {operation} memory baseline: {value:.1f} MB"
                    )

        return "\n".join(report_lines)


def main():
    """Run comprehensive performance profiling."""
    # Setup logging
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    )

    # Create profiler
    profiler = PerformanceProfiler()

    print("🚀 Proof Sketcher Performance Profiler - Milestone 3.2.1")
    print("=" * 60)

    # Test files
    project_root = Path(__file__).parent.parent
    test_files = [
        project_root / "examples" / "simple_proof.lean",
        project_root / "examples" / "induction_proof.lean",
    ]

    # Find actual test files
    existing_files = [f for f in test_files if f.exists()]
    if not existing_files:
        # Look for any .lean files
        example_dir = project_root / "examples"
        if example_dir.exists():
            existing_files = list(example_dir.rglob("*.lean"))[:2]

    results = []

    # Profile theorem processing
    if existing_files:
        print(f"\n📊 Profiling theorem processing...")
        for test_file in existing_files[:1]:  # Profile first file
            try:
                metrics = profiler.profile_theorem_processing(test_file)
                results.append(metrics)

                comparison = profiler.compare_with_baseline(metrics)

                print(f"✅ {test_file.name}:")
                print(f"   Time: {metrics.execution_time:.3f}s")
                print(f"   Memory Peak: {metrics.memory_peak_mb:.1f} MB")
                print(f"   Bottlenecks: {len(metrics.bottlenecks)}")
                print(f"   Status: {comparison['status']}")

                if comparison["status"] != "baseline_set":
                    print(
                        f"   Time Change: {comparison['time_regression_percent']:+.1f}%"
                    )
                    print(
                        f"   Memory Change: {comparison['memory_regression_percent']:+.1f}%"
                    )

            except Exception as e:
                print(f"❌ Failed to profile {test_file}: {e}")

    # Profile notation handler
    print(f"\n🔤 Profiling notation handler...")
    try:
        metrics = profiler.profile_notation_handler(1000)
        results.append(metrics)

        comparison = profiler.compare_with_baseline(metrics)

        print(f"✅ Notation Handler:")
        print(f"   Time: {metrics.execution_time:.3f}s")
        print(f"   Memory Peak: {metrics.memory_peak_mb:.1f} MB")
        print(f"   Rate: {1000/metrics.execution_time:.0f} conversions/sec")
        print(f"   Status: {comparison['status']}")

    except Exception as e:
        print(f"❌ Failed to profile notation handler: {e}")

    # Profile batch processing (if test project available)
    demo_project = project_root / "demo_batch_output" / "demo_lean_project"
    if demo_project.exists():
        print(f"\n📦 Profiling batch processing...")
        try:
            metrics = profiler.profile_batch_processing(demo_project, max_theorems=5)
            results.append(metrics)

            comparison = profiler.compare_with_baseline(metrics)

            print(f"✅ Batch Processing:")
            print(f"   Time: {metrics.execution_time:.3f}s")
            print(f"   Memory Peak: {metrics.memory_peak_mb:.1f} MB")
            print(f"   Status: {comparison['status']}")

        except Exception as e:
            print(f"❌ Failed to profile batch processing: {e}")

    # Generate report
    print(f"\n📋 Generating performance report...")
    report = profiler.generate_performance_report()
    report_file = profiler.output_dir / "performance_report.md"

    try:
        with open(report_file, "w") as f:
            f.write(report)
        print(f"✅ Report saved to: {report_file}")
    except Exception as e:
        print(f"❌ Failed to save report: {e}")

    # Summary
    print(f"\n📊 Performance Summary:")
    print(f"   Profiled Operations: {len(results)}")
    print(f"   Results Saved: {profiler.output_dir}")
    print(
        f"   System: {profiler.system_metrics.cpu_count} cores, {profiler.system_metrics.total_memory_gb:.1f}GB RAM"
    )

    if results:
        avg_time = statistics.mean([m.execution_time for m in results])
        avg_memory = statistics.mean([m.memory_peak_mb for m in results])
        print(f"   Average Time: {avg_time:.3f}s")
        print(f"   Average Memory: {avg_memory:.1f} MB")

    print(f"\n🎯 Profiling Complete! Check {profiler.output_dir} for detailed results.")


if __name__ == "__main__":
    main()
