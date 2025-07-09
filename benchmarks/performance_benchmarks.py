#!/usr/bin/env python3
"""Performance benchmarks for Proof Sketcher.

Tests performance characteristics with files of various sizes:
- Small files (1-10 theorems)
- Medium files (10-100 theorems)
- Large files (100-1000 theorems)
- Extra large files (1000+ theorems)

Measures:
- Parse time vs file size
- Memory usage patterns
- Generation time per theorem
- Export performance
- Cache effectiveness
- Concurrent processing limits
"""

import asyncio
import gc
import json
import statistics
import sys
import tempfile
import time
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import psutil

# Add the project root to Python path
sys.path.insert(0, str(Path(__file__).parent.parent))

import click
from rich.console import Console
from rich.progress import BarColumn, Progress, TextColumn, TimeElapsedColumn
from rich.table import Table

# Proof Sketcher imports
try:
    from src.proof_sketcher.exporter.html import HTMLExporter
    from src.proof_sketcher.exporter.models import ExportOptions
    from src.proof_sketcher.generator.offline import OfflineGenerator
    from src.proof_sketcher.parser.config import ParserConfig
    from src.proof_sketcher.parser.lean_parser import LeanParser
except ImportError as e:
    print(f"Import error: {e}")
    print("Make sure you're running from the project root directory")
    sys.exit(1)

console = Console()


@dataclass
class BenchmarkResult:
    """Results from a single benchmark run."""

    test_name: str
    file_size_bytes: int
    theorem_count: int
    parse_time_ms: float
    generation_time_ms: float
    export_time_ms: float
    total_time_ms: float
    peak_memory_mb: float
    average_memory_mb: float
    cache_hits: int
    cache_misses: int
    errors: List[str]

    @property
    def theorems_per_second(self) -> float:
        """Calculate theorems processed per second."""
        if self.total_time_ms == 0:
            return 0
        return (self.theorem_count * 1000) / self.total_time_ms

    @property
    def parse_time_per_theorem_ms(self) -> float:
        """Average parse time per theorem."""
        if self.theorem_count == 0:
            return 0
        return self.parse_time_ms / self.theorem_count

    @property
    def generation_time_per_theorem_ms(self) -> float:
        """Average generation time per theorem."""
        if self.theorem_count == 0:
            return 0
        return self.generation_time_ms / self.theorem_count


@dataclass
class BenchmarkSuite:
    """Complete benchmark suite results."""

    timestamp: str
    system_info: Dict[str, Any]
    results: List[BenchmarkResult]
    summary_stats: Dict[str, Any]

    def save_to_file(self, path: Path) -> None:
        """Save benchmark results to JSON file."""
        with open(path, "w") as f:
            json.dump(asdict(self), f, indent=2, default=str)

    @classmethod
    def load_from_file(cls, path: Path) -> "BenchmarkSuite":
        """Load benchmark results from JSON file."""
        with open(path, "r") as f:
            data = json.load(f)
        return cls(**data)


class MemoryMonitor:
    """Monitor memory usage during benchmarks."""

    def __init__(self, interval: float = 0.1):
        self.interval = interval
        self.measurements: List[float] = []
        self.running = False
        self.task: Optional[asyncio.Task] = None

    async def start(self) -> None:
        """Start monitoring memory usage."""
        self.running = True
        self.measurements = []
        self.task = asyncio.create_task(self._monitor())

    async def stop(self) -> Tuple[float, float]:
        """Stop monitoring and return (peak, average) memory in MB."""
        self.running = False
        if self.task:
            await self.task

        if not self.measurements:
            return 0.0, 0.0

        peak_mb = max(self.measurements)
        avg_mb = statistics.mean(self.measurements)
        return peak_mb, avg_mb

    async def _monitor(self) -> None:
        """Internal monitoring loop."""
        process = psutil.Process()
        while self.running:
            try:
                memory_mb = process.memory_info().rss / (1024 * 1024)
                self.measurements.append(memory_mb)
                await asyncio.sleep(self.interval)
            except psutil.NoSuchProcess:
                break


class LeanFileGenerator:
    """Generate Lean files of various sizes for benchmarking."""

    @staticmethod
    def generate_small_file(theorem_count: int = 5) -> str:
        """Generate a small Lean file with basic theorems."""
        theorems = []
        for i in range(theorem_count):
            theorems.append(
                f"""
theorem small_theorem_{i} (n : ℕ) : n + 0 = n := by
  simp

theorem small_theorem_{i}_comm (n m : ℕ) : n + m = m + n := by
  exact Nat.add_comm n m
"""
            )

        content = f"""-- Small benchmark file with {theorem_count} theorems
import Mathlib.Data.Nat.Basic

namespace SmallBenchmark

{''.join(theorems)}

end SmallBenchmark
"""
        return content

    @staticmethod
    def generate_medium_file(theorem_count: int = 50) -> str:
        """Generate a medium Lean file with varied theorem types."""
        theorems = []
        for i in range(theorem_count):
            if i % 3 == 0:
                theorems.append(
                    f"""
theorem medium_nat_theorem_{i} (n m k : ℕ) : (n + m) + k = n + (m + k) := by
  exact Nat.add_assoc n m k

lemma medium_helper_{i} (n : ℕ) : n * 1 = n := by
  exact Nat.mul_one n
"""
                )
            elif i % 3 == 1:
                theorems.append(
                    f"""
theorem medium_list_theorem_{i} {{α : Type*}} (l : List α) : l.length = l.length := by
  rfl

theorem medium_eq_theorem_{i} (n m : ℕ) (h : n = m) : m = n := by
  exact h.symm
"""
                )
            else:
                theorems.append(
                    f"""
theorem medium_prop_theorem_{i} (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.2
  · exact h.1

theorem medium_exists_theorem_{i} : ∃ n : ℕ, n + 1 = {i + 2} := by
  use {i + 1}
  norm_num
"""
                )

        content = f"""-- Medium benchmark file with {theorem_count} theorems
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

namespace MediumBenchmark

{''.join(theorems)}

end MediumBenchmark
"""
        return content

    @staticmethod
    def generate_large_file(theorem_count: int = 200) -> str:
        """Generate a large Lean file with complex theorems."""
        sections = []

        # Generate sections with different types of theorems
        for section in range(theorem_count // 20):
            section_theorems = []
            for i in range(20):
                theorem_id = section * 20 + i
                if i % 4 == 0:
                    # Inductive theorems
                    section_theorems.append(
                        f"""
theorem large_induction_{theorem_id} (n : ℕ) : n ≤ n + n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_add]
    exact Nat.le_succ_of_le ih

theorem large_strong_induction_{theorem_id} (P : ℕ → Prop)
    (h0 : P 0) (h1 : P 1) (hn : ∀ k, P k → P (k + 1) → P (k + 2)) :
    ∀ n, P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => exact h0
    | succ k =>
      cases k with
      | zero => exact h1
      | succ k => exact hn k (ih k (by simp)) (ih (k + 1) (by simp))
"""
                    )
                elif i % 4 == 1:
                    # Logic theorems
                    section_theorems.append(
                        f"""
theorem large_logic_{theorem_id} (P Q R : Prop) :
    (P → Q) → (Q → R) → (P → R) := by
  intros h1 h2 hp
  exact h2 (h1 hp)

theorem large_iff_{theorem_id} (P Q : Prop) :
    (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) := by
  constructor
  · intro h
    constructor
    · exact h.mp
    · exact h.mpr
  · intro h
    constructor
    · exact h.1
    · exact h.2
"""
                    )
                elif i % 4 == 2:
                    # Set theory theorems
                    section_theorems.append(
                        f"""
theorem large_set_{theorem_id} {{α : Type*}} (s t : Set α) :
    s ∩ t = t ∩ s := by
  ext x
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

theorem large_union_{theorem_id} {{α : Type*}} (s t u : Set α) :
    s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := by
  ext x
  constructor
  · intro h
    cases h with
    | inl hs => exact ⟨Or.inl hs, Or.inl hs⟩
    | inr htu => exact ⟨Or.inr htu.1, Or.inr htu.2⟩
  · intro h
    by_cases hx : x ∈ s
    · exact Or.inl hx
    · exact Or.inr ⟨h.1.resolve_left hx, h.2.resolve_left hx⟩
"""
                    )
                else:
                    # Function theorems
                    section_theorems.append(
                        f"""
theorem large_function_{theorem_id} {{α β : Type*}} (f : α → β) :
    Function.Injective f ↔ ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂ := by
  rfl

theorem large_composition_{theorem_id} {{α β γ : Type*}} (f : α → β) (g : β → γ) :
    Function.Injective f → Function.Injective g → Function.Injective (g ∘ f) := by
  intros hf hg a₁ a₂ h
  exact hf (hg h)
"""
                    )

            sections.append(
                f"""
section Section{section}
{chr(10).join(section_theorems)}
end Section{section}
"""
            )

        content = f"""-- Large benchmark file with {theorem_count} theorems
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Basic

namespace LargeBenchmark

{''.join(sections)}

end LargeBenchmark
"""
        return content


class PerformanceBenchmark:
    """Main benchmarking class."""

    def __init__(self):
        self.results: List[BenchmarkResult] = []
        self.temp_dir = Path(tempfile.mkdtemp(prefix="proof_sketcher_bench_"))
        console.print(f"[dim]Using temp directory: {self.temp_dir}[/dim]")

    async def run_all_benchmarks(self) -> BenchmarkSuite:
        """Run complete benchmark suite."""
        console.print(
            "[bold blue]🚀 Starting Performance Benchmark Suite[/bold blue]\n"
        )

        # System information
        system_info = {
            "cpu_count": psutil.cpu_count(),
            "memory_total_gb": psutil.virtual_memory().total / (1024**3),
            "platform": psutil.os.name,
            "python_version": f"{psutil.sys.version_info.major}.{psutil.sys.version_info.minor}",
        }

        # Test configurations: (name, theorem_count, file_generator)
        test_configs = [
            ("tiny", 3, LeanFileGenerator.generate_small_file),
            ("small", 10, LeanFileGenerator.generate_small_file),
            ("medium_small", 25, LeanFileGenerator.generate_medium_file),
            ("medium", 50, LeanFileGenerator.generate_medium_file),
            ("medium_large", 100, LeanFileGenerator.generate_medium_file),
            ("large", 200, LeanFileGenerator.generate_large_file),
            ("extra_large", 400, LeanFileGenerator.generate_large_file),
        ]

        with Progress(
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
            TimeElapsedColumn(),
            console=console,
        ) as progress:

            task = progress.add_task("Running benchmarks...", total=len(test_configs))

            for test_name, theorem_count, generator in test_configs:
                console.print(
                    f"\n[cyan]Running {test_name} benchmark ({theorem_count} theorems)...[/cyan]"
                )

                result = await self._run_single_benchmark(
                    test_name, theorem_count, generator
                )
                self.results.append(result)

                # Display immediate results
                console.print(f"  ✓ Completed in {result.total_time_ms:.0f}ms")
                console.print(f"  ✓ {result.theorems_per_second:.1f} theorems/sec")
                console.print(f"  ✓ Peak memory: {result.peak_memory_mb:.1f}MB")

                progress.update(task, advance=1)

        # Calculate summary statistics
        summary_stats = self._calculate_summary_stats()

        return BenchmarkSuite(
            timestamp=time.strftime("%Y-%m-%d %H:%M:%S"),
            system_info=system_info,
            results=self.results,
            summary_stats=summary_stats,
        )

    async def _run_single_benchmark(
        self, test_name: str, theorem_count: int, generator
    ) -> BenchmarkResult:
        """Run a single benchmark test."""

        # Generate test file
        content = generator(theorem_count)
        test_file = self.temp_dir / f"{test_name}.lean"
        test_file.write_text(content)

        file_size = test_file.stat().st_size
        errors = []

        # Initialize components
        parser_config = ParserConfig(fallback_to_regex=True)
        parser = LeanParser(parser_config)

        cache_dir = self.temp_dir / "cache"
        generator = OfflineGenerator(cache_dir=cache_dir)

        export_options = ExportOptions.model_validate(
            {"output_dir": self.temp_dir / "output"}
        )
        exporter = HTMLExporter(export_options)

        memory_monitor = MemoryMonitor()

        # Start memory monitoring
        await memory_monitor.start()

        total_start = time.perf_counter()

        try:
            # 1. Parse phase
            parse_start = time.perf_counter()
            parse_result = parser.parse_file(test_file)
            parse_time = (time.perf_counter() - parse_start) * 1000

            if parse_result.errors:
                errors.extend([str(e) for e in parse_result.errors])

            actual_theorem_count = len(parse_result.theorems)

            # 2. Generation phase
            gen_start = time.perf_counter()
            sketches = []

            for theorem in parse_result.theorems:
                try:
                    sketch = generator.generate_proof_sketch(theorem)
                    sketches.append(sketch)
                except Exception as e:
                    errors.append(f"Generation error for {theorem.name}: {e}")

            gen_time = (time.perf_counter() - gen_start) * 1000

            # 3. Export phase
            export_start = time.perf_counter()

            try:
                from src.proof_sketcher.exporter.models import (
                    ExportContext,
                    ExportFormat,
                )

                export_context = ExportContext(
                    format=ExportFormat.HTML,
                    output_dir=self.temp_dir / "output",
                    sketches=sketches,
                )
                export_result = exporter.export_multiple(sketches, export_context)

                if not export_result.success:
                    errors.extend(export_result.errors)

            except Exception as e:
                errors.append(f"Export error: {e}")

            export_time = (time.perf_counter() - export_start) * 1000

        except Exception as e:
            errors.append(f"Benchmark error: {e}")
            parse_time = gen_time = export_time = 0
            actual_theorem_count = 0

        total_time = (time.perf_counter() - total_start) * 1000

        # Stop memory monitoring
        peak_memory, avg_memory = await memory_monitor.stop()

        # Get cache statistics
        cache_stats = generator.get_stats()
        cache_hits = cache_stats.get("cache_hits", 0)
        cache_misses = cache_stats.get("generated_count", 0)

        # Force garbage collection
        gc.collect()

        return BenchmarkResult(
            test_name=test_name,
            file_size_bytes=file_size,
            theorem_count=actual_theorem_count,
            parse_time_ms=parse_time,
            generation_time_ms=gen_time,
            export_time_ms=export_time,
            total_time_ms=total_time,
            peak_memory_mb=peak_memory,
            average_memory_mb=avg_memory,
            cache_hits=cache_hits,
            cache_misses=cache_misses,
            errors=errors,
        )

    def _calculate_summary_stats(self) -> Dict[str, Any]:
        """Calculate summary statistics across all benchmarks."""
        if not self.results:
            return {}

        # Filter out failed benchmarks
        successful_results = [r for r in self.results if not r.errors]

        if not successful_results:
            return {"error": "No successful benchmark runs"}

        return {
            "total_benchmarks": len(self.results),
            "successful_benchmarks": len(successful_results),
            "failed_benchmarks": len(self.results) - len(successful_results),
            "total_theorems_processed": sum(
                r.theorem_count for r in successful_results
            ),
            "average_theorems_per_second": statistics.mean(
                r.theorems_per_second for r in successful_results
            ),
            "median_theorems_per_second": statistics.median(
                r.theorems_per_second for r in successful_results
            ),
            "peak_memory_usage_mb": max(r.peak_memory_mb for r in successful_results),
            "average_parse_time_per_theorem_ms": statistics.mean(
                r.parse_time_per_theorem_ms for r in successful_results
            ),
            "average_generation_time_per_theorem_ms": statistics.mean(
                r.generation_time_per_theorem_ms for r in successful_results
            ),
            "scaling_factors": self._calculate_scaling_factors(successful_results),
        }

    def _calculate_scaling_factors(
        self, results: List[BenchmarkResult]
    ) -> Dict[str, float]:
        """Calculate how performance scales with file size."""
        if len(results) < 2:
            return {}

        # Sort by theorem count
        sorted_results = sorted(results, key=lambda r: r.theorem_count)

        # Calculate scaling factors
        small_result = sorted_results[0]
        large_result = sorted_results[-1]

        theorem_ratio = large_result.theorem_count / small_result.theorem_count
        time_ratio = large_result.total_time_ms / small_result.total_time_ms
        memory_ratio = large_result.peak_memory_mb / small_result.peak_memory_mb

        return {
            "theorem_count_ratio": theorem_ratio,
            "time_scaling_factor": time_ratio
            / theorem_ratio,  # How much slower per theorem
            "memory_scaling_factor": memory_ratio
            / theorem_ratio,  # How much more memory per theorem
            "efficiency_degradation": (time_ratio / theorem_ratio)
            - 1.0,  # % performance loss per theorem
        }

    def display_results(self, suite: BenchmarkSuite) -> None:
        """Display benchmark results in a formatted table."""
        console.print("\n[bold green]📊 Benchmark Results[/bold green]\n")

        # Main results table
        table = Table(title="Performance Benchmark Results")
        table.add_column("Test", style="cyan", no_wrap=True)
        table.add_column("Theorems", justify="right", style="magenta")
        table.add_column("File Size", justify="right", style="yellow")
        table.add_column("Parse (ms)", justify="right", style="green")
        table.add_column("Generate (ms)", justify="right", style="blue")
        table.add_column("Export (ms)", justify="right", style="red")
        table.add_column("Total (ms)", justify="right", style="bold white")
        table.add_column("Thm/sec", justify="right", style="bold green")
        table.add_column("Peak RAM (MB)", justify="right", style="yellow")
        table.add_column("Errors", justify="center", style="red")

        for result in suite.results:
            file_size_str = f"{result.file_size_bytes / 1024:.1f}KB"
            errors_str = "❌" if result.errors else "✅"

            table.add_row(
                result.test_name,
                str(result.theorem_count),
                file_size_str,
                f"{result.parse_time_ms:.0f}",
                f"{result.generation_time_ms:.0f}",
                f"{result.export_time_ms:.0f}",
                f"{result.total_time_ms:.0f}",
                f"{result.theorems_per_second:.1f}",
                f"{result.peak_memory_mb:.1f}",
                errors_str,
            )

        console.print(table)

        # Summary statistics
        if "error" not in suite.summary_stats:
            console.print("\n[bold blue]📈 Summary Statistics[/bold blue]")
            stats = suite.summary_stats
            console.print(
                f"  • Total theorems processed: {stats['total_theorems_processed']}"
            )
            console.print(
                f"  • Average processing rate: {stats['average_theorems_per_second']:.1f} theorems/sec"
            )
            console.print(
                f"  • Peak memory usage: {stats['peak_memory_usage_mb']:.1f} MB"
            )
            console.print(
                f"  • Successful benchmarks: {stats['successful_benchmarks']}/{stats['total_benchmarks']}"
            )

            if "scaling_factors" in stats:
                scaling = stats["scaling_factors"]
                console.print(f"\n[bold yellow]⚡ Scaling Analysis[/bold yellow]")
                console.print(
                    f"  • Time scaling factor: {scaling.get('time_scaling_factor', 0):.2f}x per theorem"
                )
                console.print(
                    f"  • Memory scaling factor: {scaling.get('memory_scaling_factor', 0):.2f}x per theorem"
                )
                console.print(
                    f"  • Efficiency degradation: {scaling.get('efficiency_degradation', 0)*100:.1f}% per theorem"
                )

    def cleanup(self) -> None:
        """Clean up temporary files."""
        import shutil

        if self.temp_dir.exists():
            shutil.rmtree(self.temp_dir)


@click.command()
@click.option(
    "--output", "-o", type=click.Path(), help="Output file for results (JSON)"
)
@click.option("--quick", is_flag=True, help="Run quick benchmarks only")
@click.option("--include-large", is_flag=True, help="Include large file benchmarks")
def main(output: Optional[str], quick: bool, include_large: bool):
    """Run performance benchmarks for Proof Sketcher."""

    async def run_benchmarks():
        benchmark = PerformanceBenchmark()

        try:
            # Run benchmarks
            suite = await benchmark.run_all_benchmarks()

            # Display results
            benchmark.display_results(suite)

            # Save results if requested
            if output:
                output_path = Path(output)
                suite.save_to_file(output_path)
                console.print(f"\n[green]✅ Results saved to: {output_path}[/green]")

            # Performance recommendations
            console.print("\n[bold cyan]💡 Performance Recommendations[/bold cyan]")

            successful_results = [r for r in suite.results if not r.errors]
            if successful_results:
                avg_rate = suite.summary_stats.get("average_theorems_per_second", 0)
                peak_memory = suite.summary_stats.get("peak_memory_usage_mb", 0)

                if avg_rate < 1.0:
                    console.print(
                        "  ⚠️  Low processing rate - consider optimizing parsing or generation"
                    )
                elif avg_rate > 10.0:
                    console.print(
                        "  ✅ Excellent processing rate - suitable for large-scale processing"
                    )

                if peak_memory > 1000:
                    console.print(
                        "  ⚠️  High memory usage - consider batch processing for large files"
                    )
                elif peak_memory < 100:
                    console.print(
                        "  ✅ Efficient memory usage - suitable for resource-constrained environments"
                    )

                # Scaling analysis
                scaling = suite.summary_stats.get("scaling_factors", {})
                efficiency_loss = scaling.get("efficiency_degradation", 0)

                if efficiency_loss > 0.5:
                    console.print(
                        "  ⚠️  Significant efficiency degradation with file size - investigate algorithmic complexity"
                    )
                elif efficiency_loss < 0.1:
                    console.print(
                        "  ✅ Good scaling characteristics - linear performance with file size"
                    )

        finally:
            benchmark.cleanup()

    # Run the async benchmark
    asyncio.run(run_benchmarks())


if __name__ == "__main__":
    main()
