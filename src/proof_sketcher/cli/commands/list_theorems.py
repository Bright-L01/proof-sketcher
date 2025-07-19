"""List theorems command - show theorems in a Lean file."""

from pathlib import Path

import click
from rich.console import Console
from rich.table import Table

from ...parser.simple_parser import SimpleLeanParser

console = Console()


@click.command("list-theorems")
@click.argument("file_path", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--verbose",
    "-v",
    is_flag=True,
    help="Show full theorem statements",
)
@click.option(
    "--filter",
    "-f",
    help="Filter theorems by name pattern",
)
def list_theorems(
    file_path: Path,
    verbose: bool,
    filter: str,
) -> None:
    """List all theorems and lemmas in a Lean file.

    \b
    Examples:
      # List all theorems
      proof-sketcher list-theorems examples/simple_proof.lean

      # Show full statements
      proof-sketcher list-theorems file.lean --verbose

      # Filter by name
      proof-sketcher list-theorems file.lean --filter "add_*"
    """
    with console.status("[bold green]Parsing Lean file..."):
        # Parse the file
        parser = SimpleLeanParser()
        result = parser.parse_file(file_path)

        if not result.success:
            console.print("[red]Failed to parse file:[/red]")
            for error in result.errors:
                console.print(f"  • {error.message}")
            raise SystemExit(1)

        if not result.theorems:
            console.print("[yellow]No theorems found in file[/yellow]")
            raise SystemExit(0)

    # Filter theorems if requested
    theorems = result.theorems
    if filter:
        import fnmatch

        theorems = [t for t in theorems if fnmatch.fnmatch(t.name, filter)]
        if not theorems:
            console.print(f"[yellow]No theorems match pattern '{filter}'[/yellow]")
            raise SystemExit(0)

    # Display theorems
    console.print(f"\n[green]Found {len(theorems)} theorem(s) in {file_path}:[/green]")

    if verbose:
        # Detailed table
        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Name", style="cyan")
        table.add_column("Statement", style="yellow")
        table.add_column("Proof Preview", style="dim")

        for theorem in theorems:
            proof_preview = (
                theorem.proof[:50] + "..." if len(theorem.proof) > 50 else theorem.proof
            )
            table.add_row(theorem.name, theorem.statement, proof_preview)

        console.print(table)
    else:
        # Simple list
        for i, theorem in enumerate(theorems, 1):
            console.print(f"  {i}. [cyan]{theorem.name}[/cyan]")
            console.print(f"     [dim]{theorem.statement}[/dim]")

    console.print(f"\n[dim]Total: {len(theorems)} theorem(s)[/dim]")
