"""Prove command - main theorem processing functionality."""

from pathlib import Path
from typing import Any, Optional, Tuple, Union

import click
from rich.console import Console
from rich.progress import BarColumn, Progress, SpinnerColumn, TextColumn

from ...config.config import ProofSketcherConfig
from ...exporter import (
    ExportContext,
    ExportFormat,
    ExportOptions,
    HTMLExporter,
    JupyterExporter,
    MarkdownExporter,
    PDFExporter,
)
from ...generator import AIGenerator as ClaudeGenerator
from ...generator.offline import OfflineGenerator
from ...parser.lean_parser import LeanParser

console = Console()


@click.command()
@click.argument("lean_file", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--output",
    "-o",
    type=click.Path(path_type=Path),
    help="Output directory (default: ./output)",
)
@click.option(
    "--format",
    "-f",
    type=click.Choice(["html", "markdown", "pdf", "jupyter", "all"]),
    default="html",
    help="Export format: html (interactive), markdown (GitHub), pdf (print), jupyter (notebooks), all (everything)",
)
@click.option(
    "--theorem",
    "-t",
    multiple=True,
    help="Process only specific theorems by name (can be used multiple times)",
)
@click.option(
    "--offline",
    is_flag=True,
    help="Use offline mode - generate explanations from AST only, no AI required",
)
@click.pass_context
def prove(
    ctx: click.Context,
    lean_file: Path,
    output: Optional[Path],
    format: str,
    theorem: Tuple[str, ...],
    offline: bool,
) -> None:
    """Process a Lean file and generate natural language explanations.

    Parses Lean 4 theorems and generates accessible explanations using Claude AI.
    Supports multiple export formats and offline mode.

    \b
    Examples:
      # Basic usage - generate HTML explanation with AI
      python -m proof_sketcher prove theorems.lean

      # Generate explanation for specific theorem in Markdown
      python -m proof_sketcher prove file.lean --theorem "add_comm" --format markdown

      # Offline mode - no AI required, uses AST analysis only
      python -m proof_sketcher prove file.lean --offline --format markdown

      # Generate all formats
      python -m proof_sketcher prove file.lean --format all --output docs/

      # Process multiple specific theorems
      python -m proof_sketcher prove file.lean -t "theorem1" -t "theorem2" -f pdf

    \b
    Prerequisites:
      • Claude CLI must be installed and configured
      • For PDF: LaTeX distribution (TeX Live, MiKTeX)

    \b
    Supported File Types:
      • .lean files with valid Lean 4 syntax
      • Files must contain theorem declarations
      • Supports mathlib4 imports and dependencies

    The generated explanations include:
      • Natural language proof sketches
      • Step-by-step breakdowns
      • Mathematical context and intuition
      • Cross-references to dependencies
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

    # Set output directory
    if output is None:
        output = Path(config.export.output_dir)
    output.mkdir(parents=True, exist_ok=True)

    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        BarColumn(),
        TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
        console=console,
    ) as progress:

        # Parse Lean file
        parse_task = progress.add_task("[cyan]Parsing Lean file...", total=1)
        parser = LeanParser(config.parser)
        parse_result = parser.parse_file(lean_file)
        progress.update(parse_task, completed=1)

        if parse_result.errors:
            console.print("[bold red]⚠️  Parsing errors:[/bold red]")
            for error in parse_result.errors:
                console.print(f"  • {error}")

        if not parse_result.theorems:
            _show_no_theorems_help(lean_file)
            return

        # Filter theorems if specific ones requested
        theorems_to_process = _filter_theorems(
            parse_result.theorems, theorem, lean_file
        )
        if not theorems_to_process:
            return

        console.print(
            f"[bold green]✓ Found {len(theorems_to_process)} theorems to process[/bold green]"
        )

        # Choose generator based on offline mode
        generator = _setup_generator(offline, config, output)
        gen_mode_text = (
            "[cyan]Generating offline explanations..."
            if offline
            else "[cyan]Generating explanations..."
        )

        # Generate explanations
        sketches = _generate_explanations(
            theorems_to_process,
            generator,
            offline,
            config,
            output,
            progress,
            gen_mode_text,
        )

        if not sketches:
            _show_generation_failure_help(offline)
            return

        # Export results
        _export_results(
            sketches, format, output, lean_file, progress
        )

    console.print(f"\n[bold green]✨ Success![/bold green] Output saved to: {output}")


def _show_no_theorems_help(lean_file: Path) -> None:
    """Show helpful message when no theorems are found."""
    console.print("[red]❌ No theorems found in file[/red]")
    console.print("\n[yellow]Possible causes:[/yellow]")
    console.print("  • File contains no theorem declarations")
    console.print("  • Syntax errors preventing parsing")
    console.print("  • Missing required imports (e.g., import Mathlib.Data.Nat.Basic)")
    console.print(
        "\n[dim]Try: python -m proof_sketcher list-theorems path/to/working_file.lean[/dim]"
    )
    console.print("[dim]See: docs/TROUBLESHOOTING.md for more help[/dim]")


def _filter_theorems(theorems, theorem_names, lean_file):
    """Filter theorems if specific ones are requested."""
    if not theorem_names:
        return theorems

    filtered = [t for t in theorems if t.name in theorem_names]
    if not filtered:
        console.print(
            f"[red]❌ None of the specified theorems found: {', '.join(theorem_names)}[/red]"
        )
        console.print("\n[yellow]Available theorems in this file:[/yellow]")
        for i, thm in enumerate(theorems[:10], 1):
            console.print(f"  {i}. {thm.name}")
        if len(theorems) > 10:
            console.print(f"  ... and {len(theorems) - 10} more")
        console.print(
            f"\n[dim]Use: python -m proof_sketcher list-theorems {lean_file} to see all theorems[/dim]"
        )

    return filtered


def _setup_generator(
    offline: bool, config: ProofSketcherConfig, output: Path
) -> Union[OfflineGenerator, ClaudeGenerator]:
    """Setup the appropriate generator based on mode."""
    if offline:
        console.print(
            "[bold yellow]🔧 Using offline mode - no AI required[/bold yellow]"
        )
        cache_dir = output / ".cache" if output else Path(".cache")
        return OfflineGenerator(cache_dir=cache_dir)
    else:
        return ClaudeGenerator(default_config=config.generator)


def _generate_explanations(
    theorems, generator, offline, config, output, progress, gen_mode_text
):
    """Generate explanations for theorems."""
    gen_task = progress.add_task(gen_mode_text, total=len(theorems))
    sketches = []

    for thm in theorems:
        try:
            # Generate explanation
            sketch = generator.generate_proof_sketch(thm)
            sketches.append(sketch)
            progress.update(gen_task, advance=1)

        except Exception as e:
            if offline:
                console.print(
                    f"[red]Failed to process {thm.name} in offline mode: {e}[/red]"
                )
            else:
                console.print(f"[red]Failed to process {thm.name}: {e}[/red]")
                console.print(
                    "[yellow]💡 Try using --offline flag for basic explanations without AI[/yellow]"
                )
            progress.update(gen_task, advance=1)

    return sketches


def _show_generation_failure_help(offline: bool) -> None:
    """Show helpful message when generation fails."""
    console.print("[red]❌ No theorems were successfully processed[/red]")
    if not offline:
        console.print("\n[yellow]Common issues:[/yellow]")
        console.print("  • Claude CLI not installed or configured")
        console.print("  • Network connectivity issues")
        console.print("  • Invalid theorem syntax")
        console.print("\n[yellow]Quick fixes:[/yellow]")
        console.print("  1. Check Claude CLI: claude --version")
        console.print("  2. Test connection: claude 'Hello, world!'")
        console.print("  3. Try offline mode: --offline flag")
        console.print("  4. See troubleshooting: docs/TROUBLESHOOTING.md")
    else:
        console.print("\n[yellow]Offline mode issues:[/yellow]")
        console.print("  • Lean file parsing failed")
        console.print("  • Invalid theorem declarations")
        console.print("  • Insufficient AST information")


def _export_results(sketches, format, output, lean_file, progress):
    """Export results in the requested format(s)."""
    export_task = progress.add_task("[cyan]Exporting results...", total=1)

    # Create export context
    export_context = ExportContext(
        format=ExportFormat(format if format != "all" else "html"),
        output_dir=output,
        sketches=sketches,
        animations={},
        project_name=f"Proof Sketcher: {lean_file.stem}",
        include_animations=False,
    )

    # Export based on format
    export_options = ExportOptions.model_validate(
        {
            "output_dir": output,
            "include_animations": False,
            "create_index": len(sketches) > 1,
        }
    )

    if format == "all":
        formats = ["html", "markdown", "pdf", "jupyter"]
    else:
        formats = [format]

    for fmt in formats:
        try:
            exporter: Union[
                HTMLExporter, MarkdownExporter, PDFExporter, JupyterExporter
            ]
            if fmt == "html":
                exporter = HTMLExporter(export_options)
            elif fmt == "markdown":
                exporter = MarkdownExporter(export_options)
            elif fmt == "pdf":
                exporter = PDFExporter(export_options)
            elif fmt == "jupyter":
                exporter = JupyterExporter(export_options)
            else:
                continue

            result = exporter.export_multiple(sketches, export_context)

            if result.success:
                console.print(f"[green]✓ Exported to {fmt.upper()}[/green]")
            else:
                console.print(f"[red]✗ Failed to export {fmt}: {result.errors}[/red]")

        except Exception as e:
            console.print(f"[red]Export error ({fmt}): {e}[/red]")

    progress.update(export_task, completed=1)


