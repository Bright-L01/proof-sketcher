"""Command to enhance doc-gen4 documentation."""

from pathlib import Path
from typing import Optional

import click
from rich.console import Console
from rich.panel import Panel
from rich.table import Table

from ...core.exceptions import ProofSketcherError
from ...docgen4.integration import DocGen4Integration

console = Console()


@click.command()
@click.argument(
    "project_path",
    type=click.Path(exists=True, file_okay=False, path_type=Path),
    default=".",
)
@click.option(
    "--output",
    "-o",
    type=click.Path(path_type=Path),
    help="Output directory for enhanced docs (default: build/doc)",
)
@click.option("--module", "-m", help="Filter by module name pattern")
@click.option("--limit", "-l", type=int, help="Maximum number of theorems to process")
@click.option("--offline", is_flag=True, help="Use offline mode (no Claude API calls)")
@click.option("--no-backup", is_flag=True, help="Don't create backup files")
def enhance(
    project_path: Path,
    output: Optional[Path],
    module: Optional[str],
    limit: Optional[int],
    offline: bool,
    no_backup: bool,
) -> None:
    """Enhance doc-gen4 documentation with natural language explanations.

    This command integrates with doc-gen4's output and adds natural language
    explanations to theorems and definitions. It reads doc-gen4's JSON output
    and modifies the HTML files to include explanations.

    \b
    Examples:
      # Enhance all documentation
      proof-sketcher enhance .

      # Enhance specific module
      proof-sketcher enhance . --module Mathlib.Data.Nat

      # Test with offline mode (no API calls)
      proof-sketcher enhance . --offline --limit 5
    """
    console.print(
        Panel.fit(
            "[bold blue]Enhancing doc-gen4 documentation[/bold blue]\n"
            f"Project: {project_path.absolute()}",
            title="🚀 Proof Sketcher Enhancer",
        )
    )

    # Create integration instance
    integration = DocGen4Integration()

    try:
        # Run enhancement
        stats = integration.enhance_project(
            project_path=project_path,
            output_dir=output,
            module_filter=module,
            limit=limit,
            offline=offline,
        )

        # Display results
        table = Table(title="Enhancement Results")
        table.add_column("Metric", style="cyan")
        table.add_column("Count", style="green")

        table.add_row("Files Processed", str(stats.get("files_processed", 0)))
        table.add_row(
            "Declarations Enhanced", str(stats.get("declarations_enhanced", 0))
        )
        table.add_row("Errors", str(stats.get("errors", 0)))

        console.print(table)

        if offline:
            console.print(
                "\n[yellow]Note: Running in offline mode. "
                "Explanations are placeholders.[/yellow]"
            )

        console.print(
            "\n[green]✓ Enhancement complete![/green]\n"
            f"View enhanced docs at: {output or project_path / 'build/doc'}"
        )

    except ProofSketcherError as e:
        console.print(f"[red]Error: {e}[/red]")
        raise click.Exit(1)
