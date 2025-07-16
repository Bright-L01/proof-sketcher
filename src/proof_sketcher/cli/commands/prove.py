"""Prove command - generate explanations for Lean theorems."""

from pathlib import Path
from typing import Optional

import click
from rich.console import Console

from ...exporter.simple_html import SimpleHTMLExporter
from ...exporter.simple_markdown import SimpleMarkdownExporter
from ...generator.simple_generator import SimpleGenerator
from ...parser.simple_parser import SimpleLeanParser

console = Console()


@click.command()
@click.argument("file_path", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--theorem",
    "-t",
    help="Specific theorem name to explain (default: first theorem found)",
)
@click.option(
    "--format",
    "-f",
    type=click.Choice(["html", "markdown", "all"]),
    default="html",
    help="Output format",
)
@click.option(
    "--output",
    "-o",
    type=click.Path(path_type=Path),
    help="Output file path (default: theorem_name.format)",
)
@click.option(
    "--show-proof/--no-show-proof",
    default=True,
    help="Include proof in output",
)
def prove(
    file_path: Path,
    theorem: Optional[str],
    format: str,
    output: Optional[Path],
    show_proof: bool,
) -> None:
    """Generate natural language explanation for a Lean theorem.

    \b
    Examples:
      # Explain first theorem in file
      proof-sketcher prove examples/simple_proof.lean

      # Explain specific theorem
      proof-sketcher prove file.lean --theorem add_comm

      # Generate markdown output
      proof-sketcher prove file.lean --format markdown

      # Save to specific file
      proof-sketcher prove file.lean --output docs/theorem.html
    """
    with console.status("[bold green]Parsing Lean file..."):
        # Parse the file
        parser = SimpleLeanParser()
        result = parser.parse_file(file_path)

        if not result.success:
            console.print("[red]Failed to parse file:[/red]")
            for error in result.errors:
                console.print(f"  • {error.message}")
            raise click.Exit(1)

        if not result.theorems:
            console.print("[yellow]No theorems found in file[/yellow]")
            raise click.Exit(0)

    # Find the theorem to explain
    if theorem:
        selected = next((t for t in result.theorems if t.name == theorem), None)
        if not selected:
            console.print(f"[red]Theorem '{theorem}' not found[/red]")
            console.print("\n[yellow]Available theorems:[/yellow]")
            for t in result.theorems:
                console.print(f"  • {t.name}")
            raise click.Exit(1)
    else:
        selected = result.theorems[0]
        if len(result.theorems) > 1:
            console.print(
                f"[yellow]Multiple theorems found, using first: {selected.name}[/yellow]"
            )

    console.print(f"\n[green]Selected theorem:[/green] {selected.name}")
    console.print(f"[dim]Statement:[/dim] {selected.statement}")

    with console.status("[bold green]Generating explanation..."):
        # Generate explanation
        generator = SimpleGenerator()
        sketch = generator.generate_offline(selected)

    # Export to requested format(s)
    formats_to_export = ["html", "markdown"] if format == "all" else [format]

    for fmt in formats_to_export:
        with console.status(f"[bold green]Exporting to {fmt.upper()}..."):
            # Determine output path
            if output and len(formats_to_export) == 1:
                output_path = output
            else:
                # Auto-generate filename
                base_name = selected.name.lower().replace(".", "_")
                extension = "html" if fmt == "html" else "md"
                output_path = Path(f"{base_name}.{extension}")

            # Export
            if fmt == "html":
                exporter = SimpleHTMLExporter()
            else:
                exporter = SimpleMarkdownExporter()

            content = exporter.export(sketch, output_path)

            console.print(
                f"✅ [green]Generated {fmt.upper()} explanation:[/green] {output_path}"
            )

    # Show preview if single format
    if len(formats_to_export) == 1 and output_path.stat().st_size < 10000:
        console.print(f"\n[dim]Preview of {output_path}:[/dim]")
        preview = output_path.read_text()[:500] + "..."
        console.print(preview)
