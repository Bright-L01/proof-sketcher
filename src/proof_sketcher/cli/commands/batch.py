"""Batch processing command - process multiple Lean files."""

from __future__ import annotations

from pathlib import Path

import click
from rich.console import Console
from rich.progress import Progress

from ...exporter.simple_html import SimpleHTMLExporter
from ...exporter.simple_markdown import SimpleMarkdownExporter
from ...generator.simple_generator import SimpleGenerator
from ...parser.simple_parser import SimpleLeanParser

console = Console()


@click.command()
@click.argument("input_dir", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--output",
    "-o",
    type=click.Path(path_type=Path),
    default="output",
    help="Output directory",
)
@click.option(
    "--format",
    "-f",
    type=click.Choice(["html", "markdown", "all"]),
    default="html",
    help="Output format",
)
@click.option(
    "--pattern",
    "-p",
    default="*.lean",
    help="File pattern to match",
)
@click.option(
    "--recursive/--no-recursive",
    default=True,
    help="Process directories recursively",
)
def batch(
    input_dir: Path,
    output: Path,
    format: str,
    pattern: str,
    recursive: bool,
) -> None:
    """Process multiple Lean files in batch.

    \b
    Examples:
      # Process all .lean files in directory
      proof-sketcher batch examples/

      # Process with specific pattern
      proof-sketcher batch src/ --pattern "*.lean"

      # Export to markdown
      proof-sketcher batch src/ --format markdown
    """
    # Find all Lean files
    search_pattern = "**/" + pattern if recursive else pattern
    lean_files = list(input_dir.glob(search_pattern))

    if not lean_files:
        console.print(f"[yellow]No files found matching pattern '{pattern}'[/yellow]")
        raise SystemExit(0)

    console.print(f"[green]Found {len(lean_files)} file(s) to process[/green]")

    # Create output directory
    output.mkdir(parents=True, exist_ok=True)

    # Process files
    parser = SimpleLeanParser()
    generator = SimpleGenerator()

    formats_to_export = ["html", "markdown"] if format == "all" else [format]

    with Progress() as progress:
        task = progress.add_task("[green]Processing files...", total=len(lean_files))

        for file_path in lean_files:
            progress.update(task, description=f"Processing {file_path.name}")

            # Parse file
            result = parser.parse_file(file_path)

            if not result.success:
                console.print(
                    f"[red]Failed to parse {file_path}: {result.errors[0].message}[/red]"
                )
                progress.advance(task)
                continue

            if not result.theorems:
                console.print(f"[yellow]No theorems found in {file_path}[/yellow]")
                progress.advance(task)
                continue

            # Process each theorem
            for theorem in result.theorems:
                sketch = generator.generate_offline(theorem)

                # Export in requested formats
                for fmt in formats_to_export:
                    # Create output path
                    relative_path = file_path.relative_to(input_dir)
                    output_subdir = output / relative_path.parent
                    output_subdir.mkdir(parents=True, exist_ok=True)

                    extension = "html" if fmt == "html" else "md"
                    output_file = output_subdir / f"{theorem.name}.{extension}"

                    # Export
                    if fmt == "html":
                        exporter = SimpleHTMLExporter()
                    else:
                        exporter = SimpleMarkdownExporter()

                    exporter.export(sketch, output_file)

            progress.advance(task)

    console.print("\n✅ [green]Batch processing complete![/green]")
    console.print(f"[dim]Output saved to: {output}[/dim]")
