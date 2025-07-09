#!/usr/bin/env python3
"""Quick benchmark runner for development testing.

This is a simplified version of the full benchmark suite for quick performance testing
during development. It tests basic functionality without the full overhead.
"""

import sys
import tempfile
import time
from pathlib import Path

# Add the project root to Python path
sys.path.insert(0, str(Path(__file__).parent.parent))

from rich.console import Console
from rich.table import Table

# Proof Sketcher imports
try:
    from src.proof_sketcher.generator.offline import OfflineGenerator
    from src.proof_sketcher.parser.config import ParserConfig
    from src.proof_sketcher.parser.lean_parser import LeanParser
except ImportError as e:
    print(f"Import error: {e}")
    print("Make sure you're running from the project root directory")
    sys.exit(1)

console = Console()


def create_test_file(theorem_count: int = 5) -> str:
    """Create a simple test file with the specified number of theorems."""
    theorems = []
    for i in range(theorem_count):
        theorems.append(
            f"""
theorem test_theorem_{i} (n : ℕ) : n + 0 = n := by simp

theorem test_theorem_{i}_comm (n m : ℕ) : n + m = m + n := by
  exact Nat.add_comm n m
"""
        )

    return f"""-- Quick benchmark test file
import Mathlib.Data.Nat.Basic

namespace QuickBenchmark
{''.join(theorems)}
end QuickBenchmark
"""


def run_quick_benchmark():
    """Run a quick performance test."""
    console.print("[bold blue]🚀 Quick Performance Benchmark[/bold blue]\n")

    # Test configurations
    test_sizes = [3, 10, 25, 50]
    results = []

    with tempfile.TemporaryDirectory(prefix="proof_sketcher_quick_") as temp_dir:
        temp_path = Path(temp_dir)

        for size in test_sizes:
            console.print(f"[cyan]Testing with {size} theorems...[/cyan]")

            # Create test file
            content = create_test_file(size)
            test_file = temp_path / f"test_{size}.lean"
            test_file.write_text(content)

            # Initialize components
            parser_config = ParserConfig(fallback_to_regex=True)
            parser = LeanParser(parser_config)
            generator = OfflineGenerator(cache_dir=temp_path / "cache")

            # Measure performance
            total_start = time.perf_counter()

            # Parse
            parse_start = time.perf_counter()
            parse_result = parser.parse_file(test_file)
            parse_time = (time.perf_counter() - parse_start) * 1000

            # Generate
            gen_start = time.perf_counter()
            sketches = []
            for theorem in parse_result.theorems:
                try:
                    sketch = generator.generate_proof_sketch(theorem)
                    sketches.append(sketch)
                except Exception as e:
                    console.print(
                        f"  [red]Error generating sketch for {theorem.name}: {e}[/red]"
                    )

            gen_time = (time.perf_counter() - gen_start) * 1000
            total_time = (time.perf_counter() - total_start) * 1000

            # Calculate rate
            actual_count = len(parse_result.theorems)
            rate = (actual_count * 1000) / total_time if total_time > 0 else 0

            results.append(
                {
                    "theorems": actual_count,
                    "parse_time": parse_time,
                    "gen_time": gen_time,
                    "total_time": total_time,
                    "rate": rate,
                    "errors": len(parse_result.errors),
                }
            )

            console.print(
                f"  ✓ Processed {actual_count} theorems in {total_time:.0f}ms ({rate:.1f} thm/s)"
            )

    # Display results table
    console.print("\n[bold green]📊 Quick Benchmark Results[/bold green]")

    table = Table()
    table.add_column("Theorems", justify="right", style="cyan")
    table.add_column("Parse (ms)", justify="right", style="green")
    table.add_column("Generate (ms)", justify="right", style="blue")
    table.add_column("Total (ms)", justify="right", style="bold white")
    table.add_column("Rate (thm/s)", justify="right", style="bold green")
    table.add_column("Errors", justify="right", style="red")

    for result in results:
        table.add_row(
            str(result["theorems"]),
            f"{result['parse_time']:.0f}",
            f"{result['gen_time']:.0f}",
            f"{result['total_time']:.0f}",
            f"{result['rate']:.1f}",
            str(result["errors"]),
        )

    console.print(table)

    # Performance assessment
    if results:
        avg_rate = sum(r["rate"] for r in results) / len(results)
        max_errors = max(r["errors"] for r in results)

        console.print(f"\n[bold cyan]📈 Performance Summary[/bold cyan]")
        console.print(f"  • Average processing rate: {avg_rate:.1f} theorems/second")
        console.print(f"  • Total errors: {max_errors}")

        if avg_rate > 10:
            console.print(
                "  ✅ [green]Excellent performance - ready for large files[/green]"
            )
        elif avg_rate > 5:
            console.print(
                "  ✅ [green]Good performance - suitable for medium files[/green]"
            )
        elif avg_rate > 1:
            console.print(
                "  ⚠️ [yellow]Moderate performance - may be slow on large files[/yellow]"
            )
        else:
            console.print("  ❌ [red]Poor performance - optimization needed[/red]")

        if max_errors == 0:
            console.print("  ✅ [green]No parsing errors - good stability[/green]")
        else:
            console.print(
                f"  ⚠️ [yellow]Found {max_errors} parsing errors - check file format[/yellow]"
            )


if __name__ == "__main__":
    run_quick_benchmark()
