"""Information and utility commands."""

from pathlib import Path

import click
from rich.console import Console
from rich.table import Table

from ...config.config import ProofSketcherConfig
from ...parser.lean_parser import LeanParser

console = Console()


@click.command()
@click.argument("lean_file", type=click.Path(exists=True, path_type=Path))
@click.pass_context
def list_theorems(ctx: click.Context, lean_file: Path) -> None:
    """List all theorems found in a Lean file with their statements and locations.

    This command parses a Lean 4 file and extracts all theorem declarations,
    displaying them in a formatted table with their statements and line numbers.
    Useful for exploring unfamiliar Lean files or selecting specific theorems.

    \b
    Examples:
      # List all theorems in a file
      python -m proof_sketcher list-theorems examples/group_theory.lean

      # Explore classical mathematics examples
      python -m proof_sketcher list-theorems examples/classical/real_analysis.lean

      # Check a file before processing
      python -m proof_sketcher list-theorems my_theorems.lean

    \b
    Output Format:
      • Name: Theorem identifier
      • Statement: Theorem statement (truncated if long)
      • Line: Line number in source file

    \b
    Troubleshooting:
      • File must have .lean extension
      • File must contain valid Lean 4 syntax
      • Use --verbose flag for detailed parsing information
    """
    config: ProofSketcherConfig = ctx.obj["config"]

    # Validate file extension with helpful error message
    if not lean_file.suffix == ".lean":
        console.print(f"[red]Error: Invalid file extension '{lean_file.suffix}'[/red]")
        console.print(
            "[yellow]Proof Sketcher only processes Lean 4 files with .lean extension[/yellow]"
        )
        console.print(
            f"[dim]Suggestion: Rename '{lean_file}' to '{lean_file.stem}.lean'[/dim]"
        )
        raise click.Abort()

    console.print(f"[bold blue]Parsing {lean_file.name}...[/bold blue]\n")

    # Parse the Lean file
    parser = LeanParser(config.parser)
    result = parser.parse_file(lean_file)

    if result.errors:
        console.print("[bold red]⚠️  Parsing errors:[/bold red]")
        for error in result.errors:
            console.print(f"  • {error}")
        console.print()

    if not result.theorems:
        console.print("[red]❌ No theorems found in file[/red]")
        console.print("\n[yellow]This might mean:[/yellow]")
        console.print("  • File contains no theorem declarations")
        console.print("  • File has syntax errors preventing parsing")
        console.print("  • File is missing required imports")
        console.print("\n[yellow]Example valid theorem:[/yellow]")
        console.print("[dim]  theorem add_zero (n : ℕ) : n + 0 = n := by simp[/dim]")
        console.print(
            "\n[dim]For more examples, see: examples/classical/simple_examples.lean[/dim]"
        )
        return

    # Create table for theorems
    table = Table(title=f"Theorems in {lean_file.name}")
    table.add_column("Name", style="cyan", no_wrap=True)
    table.add_column("Statement", style="green")
    table.add_column("Line", style="yellow", justify="right")

    for theorem in result.theorems:
        # Truncate long statements
        statement = theorem.statement
        if len(statement) > 60:
            statement = statement[:57] + "..."

        line_info = f"line {theorem.line_number}" if theorem.line_number else "N/A"
        table.add_row(theorem.name, statement, line_info)

    console.print(table)
    console.print(f"\n[dim]Total: {len(result.theorems)} theorems[/dim]")


@click.command()
def formats() -> None:
    """Show supported export formats and their features."""
    table = Table(title="Supported Export Formats")
    table.add_column("Format", style="cyan", no_wrap=True)
    table.add_column("Extension", style="magenta")
    table.add_column("Features", style="green")
    table.add_column("Best For", style="yellow")

    formats_info = [
        (
            "HTML",
            ".html",
            "Interactive, animations, syntax highlighting",
            "Web documentation",
        ),
        (
            "Markdown",
            ".md",
            "GitHub compatible, collapsible sections",
            "Repository docs",
        ),
        ("PDF", ".pdf", "Professional formatting, print-ready", "Publications"),
        (
            "Jupyter",
            ".ipynb",
            "Interactive notebooks, code cells",
            "Education & exploration",
        ),
    ]

    for fmt, ext, features, best_for in formats_info:
        table.add_row(fmt, ext, features, best_for)

    console.print(table)
    console.print(
        "\n[dim]Use --format/-f option with 'prove' command to select format[/dim]"
    )
    console.print("[dim]Use --format all to export to all formats[/dim]")


@click.command()
def version() -> None:
    """Show Proof Sketcher version information."""
    from ... import __version__

    console.print(f"[bold]Proof Sketcher[/bold] v{__version__}")
    console.print("\nComponents:")
    console.print("  • Parser: Lean 4 AST extraction")
    console.print("  • Generator: Claude AI integration")
    console.print("  • Animator: Manim via MCP")
    console.print("  • Exporters: HTML, Markdown, PDF, Jupyter")
    console.print("\nFor updates: https://github.com/your-org/proof-sketcher")
