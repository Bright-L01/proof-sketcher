"""Performance profiling command."""

from __future__ import annotations

import time
from pathlib import Path

import click
from rich.console import Console
from rich.table import Table

from ...exporter.simple_html import SimpleHTMLExporter
from ...generator.simple_generator import SimpleGenerator
from ...parser.simple_parser import SimpleLeanParser

console = Console()


@click.command()
@click.argument("file_path", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--iterations",
    "-i",
    default=5,
    help="Number of iterations to run",
)
@click.option(
    "--profile-parsing",
    is_flag=True,
    help="Profile parsing performance",
)
@click.option(
    "--profile-generation",
    is_flag=True,
    help="Profile generation performance",
)
@click.option(
    "--profile-export",
    is_flag=True,
    help="Profile export performance",
)
def performance(
    file_path: Path,
    iterations: int,
    profile_parsing: bool,
    profile_generation: bool,
    profile_export: bool,
) -> None:
    """Profile performance of Proof Sketcher components.

    \b
    Examples:
      # Profile all components
      proof-sketcher performance examples/simple_proof.lean

      # Profile just parsing
      proof-sketcher performance file.lean --profile-parsing

      # Run more iterations
      proof-sketcher performance file.lean --iterations 10
    """
    # If no specific profile requested, profile all
    if not (profile_parsing or profile_generation or profile_export):
        profile_parsing = profile_generation = profile_export = True

    console.print(f"[green]Performance profiling of {file_path}[/green]")
    console.print(f"[dim]Running {iterations} iterations...[/dim]")

    results = {}

    # Profile parsing
    if profile_parsing:
        with console.status("Profiling parsing..."):
            parser = SimpleLeanParser()
            times = []

            for _ in range(iterations):
                start = time.time()
                result = parser.parse_file(file_path)
                end = time.time()
                times.append(end - start)

            results["parsing"] = {
                "avg": sum(times) / len(times),
                "min": min(times),
                "max": max(times),
                "total": sum(times),
                "success": result.success,
                "theorems": len(result.theorems) if result.success else 0,
            }

    # Profile generation
    if profile_generation and "parsing" in results and results["parsing"]["success"]:
        with console.status("Profiling generation..."):
            generator = SimpleGenerator()
            theorem = result.theorems[0] if result.theorems else None

            if theorem:
                times = []

                for _ in range(iterations):
                    start = time.time()
                    sketch = generator.generate_offline(theorem)
                    end = time.time()
                    times.append(end - start)

                results["generation"] = {
                    "avg": sum(times) / len(times),
                    "min": min(times),
                    "max": max(times),
                    "total": sum(times),
                }

    # Profile export
    if profile_export and "generation" in results:
        with console.status("Profiling export..."):
            exporter = SimpleHTMLExporter()
            times = []

            for _ in range(iterations):
                start = time.time()
                _ = exporter.export(sketch)
                end = time.time()
                times.append(end - start)

            results["export"] = {
                "avg": sum(times) / len(times),
                "min": min(times),
                "max": max(times),
                "total": sum(times),
            }

    # Display results
    console.print("\n[bold green]Performance Results:[/bold green]")

    table = Table(show_header=True, header_style="bold magenta")
    table.add_column("Component", style="cyan")
    table.add_column("Avg Time", style="yellow")
    table.add_column("Min Time", style="green")
    table.add_column("Max Time", style="red")
    table.add_column("Total Time", style="blue")

    for component, data in results.items():
        table.add_row(
            component.title(),
            f"{data['avg']:.4f}s",
            f"{data['min']:.4f}s",
            f"{data['max']:.4f}s",
            f"{data['total']:.4f}s",
        )

    console.print(table)

    # Additional info
    if "parsing" in results:
        console.print(
            f"\n[dim]Parsed {results['parsing']['theorems']} theorem(s)[/dim]"
        )

    total_time = sum(data["total"] for data in results.values())
    console.print(f"[dim]Total profiling time: {total_time:.4f}s[/dim]")
