"""Info commands - version and format information."""

from __future__ import annotations

import click
from rich.console import Console
from rich.table import Table

from ... import __version__

console = Console()


@click.command()
def version() -> None:
    """Show version information."""
    console.print(f"[bold green]Proof Sketcher[/bold green] version {__version__}")
    console.print("[yellow]⚠️  ALPHA SOFTWARE - LIMITED FUNCTIONALITY[/yellow]")
    console.print("\n[dim]For more information:[/dim]")
    console.print("  Repository: https://github.com/Bright-L01/proof-sketcher")
    console.print("  Issues: https://github.com/Bright-L01/proof-sketcher/issues")


@click.command()
def formats() -> None:
    """Show supported input and output formats."""
    console.print("[bold green]Supported Formats[/bold green]")

    # Input formats
    console.print("\n[yellow]Input Formats:[/yellow]")
    input_table = Table(show_header=True, header_style="bold magenta")
    input_table.add_column("Format", style="cyan")
    input_table.add_column("Extension", style="yellow")
    input_table.add_column("Description", style="dim")

    input_table.add_row(
        "Lean 4", ".lean", "Lean 4 source files with theorems and proofs"
    )

    console.print(input_table)

    # Output formats
    console.print("\n[yellow]Output Formats:[/yellow]")
    output_table = Table(show_header=True, header_style="bold magenta")
    output_table.add_column("Format", style="cyan")
    output_table.add_column("Extension", style="yellow")
    output_table.add_column("Description", style="dim")
    output_table.add_column("Features", style="green")

    output_table.add_row(
        "HTML",
        ".html",
        "Web-ready HTML with MathJax 4.0",
        "Math rendering, responsive design",
    )
    output_table.add_row(
        "Markdown", ".md", "GitHub-flavored Markdown", "LaTeX math, code blocks"
    )

    console.print(output_table)

    # Parsing features
    console.print("\n[yellow]Parsing Features:[/yellow]")
    features_table = Table(show_header=True, header_style="bold magenta")
    features_table.add_column("Feature", style="cyan")
    features_table.add_column("Status", style="yellow")
    features_table.add_column("Description", style="dim")

    features_table.add_row(
        "Theorem Extraction", "✅ Working", "Extract theorem names and statements"
    )
    features_table.add_row("Proof Parsing", "✅ Working", "Basic proof text extraction")
    features_table.add_row(
        "Dependency Analysis", "❌ Limited", "Simple dependency detection"
    )
    features_table.add_row(
        "LSP Integration", "❌ Not Available", "Full semantic analysis"
    )

    console.print(features_table)

    console.print(
        "\n[dim]Note: This is alpha software with limited functionality.[/dim]"
    )
