"""Click CLI entry point for Proof Sketcher."""

import asyncio
import logging
import sys
import time
from pathlib import Path
from typing import Optional

import click
from rich.console import Console
from rich.logging import RichHandler
from rich.progress import BarColumn, Progress, SpinnerColumn, TextColumn
from rich.table import Table

from . import __version__
from .animator.manim_mcp import ManimMCPClient
from .animator.models import AnimationRequest
from .config.config import ProofSketcherConfig, set_config
from .exporter import (
    ExportContext,
    ExportFormat,
    ExportOptions,
    HTMLExporter,
    JupyterExporter,
    MarkdownExporter,
    PDFExporter,
)
from .generator import AIGenerator as ClaudeGenerator
from .generator.cache import CacheManager
from .parser.lean_parser import LeanParser

# Set up rich console and logging
console = Console()


def setup_logging(config: ProofSketcherConfig) -> None:
    """Configure logging with rich formatting."""
    level = getattr(logging, config.log_level.upper(), logging.INFO)
    if config.debug:
        level = logging.DEBUG

    logging.basicConfig(
        level=level,
        format="%(message)s",
        datefmt="[%X]",
        handlers=[RichHandler(console=console, rich_tracebacks=True)],
    )


@click.group()
@click.version_option(version=__version__, prog_name="Proof Sketcher")
@click.option(
    "--verbose", 
    "-v", 
    is_flag=True, 
    help="Enable verbose logging for detailed debugging information"
)
@click.option(
    "--config",
    "-c",
    type=click.Path(exists=True, path_type=Path),
    help="Path to configuration file (default: .proof-sketcher.yaml)",
)
@click.pass_context
def cli(ctx: click.Context, verbose: bool, config: Optional[Path]) -> None:
    """Proof Sketcher: Transform Lean 4 theorems into natural language explanations.
    
    Transform formal mathematical proofs into accessible explanations with beautiful
    visualizations. Supports multiple output formats and classical mathematics.
    
    \b
    Quick Examples:
      # List theorems in a file
      python -m proof_sketcher list-theorems examples/group_theory.lean
      
      # Generate explanation for a specific theorem
      python -m proof_sketcher prove file.lean --theorem add_comm --format markdown
      
      # Generate all formats with animations
      python -m proof_sketcher prove file.lean --format all --animate
    
    \b
    Getting Started:
      1. Install Claude CLI: curl -fsSL https://claude.ai/install.sh | sh
      2. Try examples: python -m proof_sketcher list-theorems examples/classical/simple_examples.lean
      3. Read docs: See docs/QUICKSTART_GUIDE.md
    
    For more help: https://github.com/Bright-L01/proof-sketcher/docs
    """
    ctx.ensure_object(dict)

    # Load configuration
    proof_config = ProofSketcherConfig.load(config)
    if verbose:
        proof_config.debug = True
        proof_config.log_level = "DEBUG"

    # Store config in context
    ctx.obj["config"] = proof_config
    set_config(proof_config)

    setup_logging(proof_config)


@cli.command()
@click.argument("lean_file", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--output", 
    "-o", 
    type=click.Path(path_type=Path), 
    help="Output directory (default: ./output)"
)
@click.option(
    "--format",
    "-f",
    type=click.Choice(["html", "markdown", "pdf", "jupyter", "all"]),
    default="html",
    help="Export format: html (interactive), markdown (GitHub), pdf (print), jupyter (notebooks), all (everything)",
)
@click.option(
    "--animate", 
    is_flag=True, 
    help="Generate mathematical animations using Manim (requires Node.js and MCP server)"
)
@click.option(
    "--theorem", 
    "-t", 
    multiple=True, 
    help="Process only specific theorems by name (can be used multiple times)"
)
@click.pass_context
def prove(
    ctx: click.Context,
    lean_file: Path,
    output: Optional[Path],
    format: str,
    animate: bool,
    theorem: tuple,
) -> None:
    """Process a Lean file and generate natural language explanations.
    
    Parses Lean 4 theorems and generates accessible explanations using Claude AI.
    Supports multiple export formats and optional mathematical animations.
    
    \b
    Examples:
      # Basic usage - generate HTML explanation
      python -m proof_sketcher prove theorems.lean
      
      # Generate explanation for specific theorem in Markdown
      python -m proof_sketcher prove file.lean --theorem "add_comm" --format markdown
      
      # Generate all formats with animations
      python -m proof_sketcher prove file.lean --format all --animate --output docs/
      
      # Process multiple specific theorems
      python -m proof_sketcher prove file.lean -t "theorem1" -t "theorem2" -f pdf
    
    \b
    Prerequisites:
      • Claude CLI must be installed and configured
      • For animations: Node.js and Manim MCP server
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
    logging.getLogger(__name__)
    config: ProofSketcherConfig = ctx.obj["config"]

    # Validate file extension with helpful error message
    if not lean_file.suffix == ".lean":
        console.print(f"[red]Error: Invalid file extension '{lean_file.suffix}'[/red]")
        console.print("[yellow]Proof Sketcher only processes Lean 4 files with .lean extension[/yellow]")
        console.print(f"[dim]Suggestion: Rename '{lean_file}' to '{lean_file.stem}.lean'[/dim]")
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
        result = parser.parse_file(lean_file)
        progress.update(parse_task, completed=1)

        if result.errors:
            console.print("[bold red]⚠️  Parsing errors:[/bold red]")
            for error in result.errors:
                console.print(f"  • {error}")

        if not result.theorems:
            console.print("[red]❌ No theorems found in file[/red]")
            console.print("\n[yellow]Possible causes:[/yellow]")
            console.print("  • File contains no theorem declarations")
            console.print("  • Syntax errors preventing parsing")
            console.print("  • Missing required imports (e.g., import Mathlib.Data.Nat.Basic)")
            console.print("\n[dim]Try: python -m proof_sketcher list-theorems path/to/working_file.lean[/dim]")
            console.print("[dim]See: docs/TROUBLESHOOTING.md for more help[/dim]")
            return

        # Filter theorems if specific ones requested
        theorems_to_process = result.theorems
        if theorem:
            theorems_to_process = [t for t in result.theorems if t.name in theorem]
            if not theorems_to_process:
                console.print(f"[red]❌ None of the specified theorems found: {', '.join(theorem)}[/red]")
                console.print("\n[yellow]Available theorems in this file:[/yellow]")
                for i, thm in enumerate(result.theorems[:10], 1):
                    console.print(f"  {i}. {thm.name}")
                if len(result.theorems) > 10:
                    console.print(f"  ... and {len(result.theorems) - 10} more")
                console.print(f"\n[dim]Use: python -m proof_sketcher list-theorems {lean_file} to see all theorems[/dim]")
                return

        console.print(
            f"[bold green]✓ Found {len(theorems_to_process)} theorems to process[/bold green]"
        )

        # Generate explanations
        gen_task = progress.add_task(
            "[cyan]Generating explanations...", total=len(theorems_to_process)
        )

        generator = ClaudeGenerator(default_config=config.generator)
        sketches = []
        animations = {}

        for thm in theorems_to_process:
            try:
                # Generate explanation
                sketch = generator.generate_proof_sketch(thm)
                sketches.append(sketch)
                progress.update(gen_task, advance=1)

                # Generate animation if requested
                if animate:
                    anim_path = asyncio.run(
                        _generate_animation(thm.name, sketch, config, output)
                    )
                    if anim_path:
                        animations[thm.name] = anim_path

            except Exception as e:
                console.print(f"[red]Failed to process {thm.name}: {e}[/red]")
                progress.update(gen_task, advance=1)

        if not sketches:
            console.print("[red]❌ No theorems were successfully processed[/red]")
            console.print("\n[yellow]Common issues:[/yellow]")
            console.print("  • Claude CLI not installed or configured")
            console.print("  • Network connectivity issues")
            console.print("  • Invalid theorem syntax")
            console.print("\n[yellow]Quick fixes:[/yellow]")
            console.print("  1. Check Claude CLI: claude --version")
            console.print("  2. Test connection: claude 'Hello, world!'")
            console.print("  3. See troubleshooting: docs/TROUBLESHOOTING.md")
            return

        # Export results
        export_task = progress.add_task("[cyan]Exporting results...", total=1)

        # Create export context
        export_context = ExportContext(
            format=ExportFormat(format if format != "all" else "html"),
            output_dir=output,
            sketches=sketches,
            animations=animations,
            project_name=f"Proof Sketcher: {lean_file.stem}",
            include_animations=animate,
        )

        # Export based on format
        export_options = ExportOptions(
            output_dir=output,
            include_animations=animate,
            create_index=len(sketches) > 1,
        )

        if format == "all":
            formats = ["html", "markdown", "pdf", "jupyter"]
        else:
            formats = [format]

        for fmt in formats:
            try:
                if fmt == "html":
                    exporter = HTMLExporter(export_options)
                elif fmt == "markdown":
                    exporter = MarkdownExporter(export_options)
                elif fmt == "pdf":
                    exporter = PDFExporter(export_options)
                elif fmt == "jupyter":
                    exporter = JupyterExporter(export_options)

                result = exporter.export_multiple(sketches, export_context)

                if result.success:
                    console.print(f"[green]✓ Exported to {fmt.upper()}[/green]")
                else:
                    console.print(
                        f"[red]✗ Failed to export {fmt}: {result.errors}[/red]"
                    )

            except Exception as e:
                console.print(f"[red]Export error ({fmt}): {e}[/red]")

        progress.update(export_task, completed=1)

    console.print(f"\n[bold green]✨ Success![/bold green] Output saved to: {output}")


async def _generate_animation(
    theorem_name: str, sketch, config, output_dir: Path
) -> Optional[Path]:
    """Generate animation for a theorem."""
    try:
        client = ManimMCPClient(config.manim)
        await client.start_server()

        request = AnimationRequest(
            theorem_name=theorem_name,
            explanation=sketch.explanation,
            proof_steps=[step.description for step in sketch.steps],
            config=config.animator,
        )

        response = await client.render_animation(request)
        await client.stop_server()

        if response.success and response.video_path:
            return Path(response.video_path)
    except Exception as e:
        console.print(f"[yellow]Animation failed for {theorem_name}: {e}[/yellow]")

    return None


@cli.group()
def config() -> None:
    """Manage Proof Sketcher configuration settings.
    
    Configure how Proof Sketcher processes files, generates explanations,
    creates animations, and exports results. Settings can be managed through
    configuration files, environment variables, or command-line options.
    
    \b
    Configuration Sources (in priority order):
      1. Command-line options (highest priority)
      2. Environment variables (PROOF_SKETCHER_*)
      3. Configuration file (.proof-sketcher.yaml)
      4. Default values (lowest priority)
    
    \b
    Quick Commands:
      # View current configuration
      python -m proof_sketcher config show
      
      # Save current settings to file
      python -m proof_sketcher config save
      
      # Save to specific location
      python -m proof_sketcher config save -o my-config.yaml
    """
    pass


@config.command()
@click.pass_context
def show(ctx: click.Context) -> None:
    """Display current configuration settings in a formatted table.
    
    Shows all active configuration values including parser settings,
    generator options, animation preferences, and export configurations.
    Useful for debugging and verifying your setup.
    
    \b
    Categories Displayed:
      • Global: Project name, version, debug settings
      • Parser: Lean executable, timeouts, build options
      • Generator: AI model, temperature, token limits
      • Animation: Quality, FPS, style preferences
      • Export: Output directories, themes, engines
    
    Configuration values are resolved from all sources (CLI, env, files).
    """
    config: ProofSketcherConfig = ctx.obj["config"]

    # Create configuration table
    table = Table(title="Current Configuration", show_header=True)
    table.add_column("Category", style="cyan", no_wrap=True)
    table.add_column("Setting", style="magenta")
    table.add_column("Value", style="green")

    # Global settings
    table.add_row("Global", "Project Name", config.project_name)
    table.add_row("Global", "Version", config.version)
    table.add_row("Global", "Debug Mode", str(config.debug))
    table.add_row("Global", "Log Level", config.log_level)
    table.add_row("Global", "Cache Directory", str(config.cache_dir))

    # Parser settings
    table.add_row("Parser", "Lean Executable", str(config.parser.lean_executable))
    table.add_row(
        "Parser", "Lake Build on Parse", str(config.parser.lake_build_on_parse)
    )
    table.add_row("Parser", "Timeout", f"{config.parser.lean_timeout}s")

    # Generator settings
    table.add_row("Generator", "Model", config.generator.model.value)
    table.add_row("Generator", "Temperature", str(config.generator.temperature))
    table.add_row("Generator", "Max Tokens", str(config.generator.max_tokens))

    # Animation settings
    # AnimationConfig doesn't have 'enabled' field - animation is controlled by CLI flag
    table.add_row("Animation", "Quality", config.animator.quality.value)
    table.add_row("Animation", "FPS", str(config.animator.fps))

    # Export settings
    table.add_row("Export", "Output Directory", str(config.export.output_dir))
    table.add_row("Export", "HTML Theme", config.export.html_theme)
    table.add_row("Export", "Markdown Flavor", config.export.markdown_flavor)
    table.add_row("Export", "PDF Engine", config.export.pdf_engine)

    console.print(table)


@config.command()
@click.option(
    "--output",
    "-o",
    type=click.Path(path_type=Path),
    help="Path to save configuration file",
)
@click.pass_context
def save(ctx: click.Context, output: Optional[Path]) -> None:
    """Save current configuration to file."""
    config: ProofSketcherConfig = ctx.obj["config"]

    if output is None:
        output = Path(".proof-sketcher.yaml")

    try:
        config.save(output)
        console.print(f"[green]✓ Configuration saved to:[/green] {output}")
    except Exception as e:
        console.print(f"[red]Failed to save configuration:[/red] {e}")
        sys.exit(1)


@cli.group()
def cache() -> None:
    """Manage theorem and animation cache for improved performance.
    
    Proof Sketcher caches generated explanations and animations to avoid
    regenerating identical content. Use these commands to monitor and
    manage the cache system.
    
    \b
    Cache Benefits:
      • Faster repeated explanations
      • Reduced API usage and costs
      • Offline access to previously generated content
      • Consistent results across runs
    
    \b
    Quick Commands:
      # Check cache usage
      python -m proof_sketcher cache status
      
      # Clear all cached data
      python -m proof_sketcher cache clear
      
      # List cached theorems
      python -m proof_sketcher cache list
    """
    pass


@cache.command()
@click.option(
    "--force", 
    "-f", 
    is_flag=True, 
    help="Skip confirmation prompt and clear immediately"
)
@click.pass_context
def clear(ctx: click.Context, force: bool) -> None:
    """Clear all cached explanations and animations.
    
    Removes all cached theorem explanations, animations, and related data.
    This will free up disk space but means previously generated content
    will need to be regenerated on next use.
    
    \b
    Examples:
      # Clear with confirmation prompt
      python -m proof_sketcher cache clear
      
      # Clear without confirmation (use with caution)
      python -m proof_sketcher cache clear --force
    
    \b
    What Gets Cleared:
      • Generated theorem explanations
      • Cached animations and videos
      • Temporary files and metadata
      • All cached response data
    
    Use 'cache status' before clearing to see what will be removed.
    """
    config: ProofSketcherConfig = ctx.obj["config"]
    cache_dir = config.cache_dir

    if cache_dir.exists():
        if not force:
            console.print(
                f"[yellow]Warning: This will clear all cached data at {cache_dir}[/yellow]"
            )
            if not click.confirm("Are you sure you want to continue?"):
                console.print("[yellow]Cache clear cancelled[/yellow]")
                return

        console.print(f"[yellow]Clearing cache at {cache_dir}...[/yellow]")

        # Clear generator cache
        generator_cache = CacheManager(cache_dir / "generator")
        generator_count = generator_cache.clear()

        # Clear animation cache if it exists
        animation_count = 0
        animation_cache_dir = cache_dir / "animations"
        if animation_cache_dir.exists():
            for file in animation_cache_dir.glob("**/*"):
                if file.is_file():
                    file.unlink()
                    animation_count += 1

        total_count = generator_count + animation_count
        console.print(
            f"[green]✓ Cache cleared successfully ({total_count} entries removed)[/green]"
        )
    else:
        console.print("[yellow]No cache directory found[/yellow]")


@cache.command()
@click.pass_context
def status(ctx: click.Context) -> None:
    """Display comprehensive cache status and storage statistics.
    
    Shows detailed information about cached content including:
    storage usage, number of cached items, cache health, and
    recommendations for cache management.
    
    \b
    Information Displayed:
      • Cache directory location and size
      • Number of cached explanations by type
      • Animation cache statistics
      • Total storage usage
      • Cache configuration settings
    
    Use this command to monitor cache growth and decide when to clear.
    """
    config: ProofSketcherConfig = ctx.obj["config"]
    cache_dir = config.cache_dir

    console.print("[bold blue]Cache Status:[/bold blue]")
    console.print(f"  • Cache directory: {cache_dir}")
    console.print(f"  • Directory exists: {cache_dir.exists()}")

    if cache_dir.exists():
        # Get generator cache stats
        generator_cache = CacheManager(cache_dir / "generator")
        gen_stats = generator_cache.get_cache_stats()

        # Get animation cache stats
        animation_count = 0
        animation_size_mb = 0.0
        animation_cache_dir = cache_dir / "animations"
        if animation_cache_dir.exists():
            for file in animation_cache_dir.glob("**/*"):
                if file.is_file():
                    animation_count += 1
                    animation_size_mb += file.stat().st_size / (1024 * 1024)

        # Display statistics
        console.print("\n[bold]Generator Cache:[/bold]")
        console.print(f"  • Theorem sketches cached: {gen_stats['total_entries']}")
        console.print(f"  • Cache size: {gen_stats['size_mb']} MB")
        console.print(f"  • Maximum size: {gen_stats['max_size_mb']} MB")

        if gen_stats.get("by_type"):
            console.print("  • Cached by type:")
            for gen_type, count in gen_stats["by_type"].items():
                console.print(f"    - {gen_type}: {count}")

        console.print("\n[bold]Animation Cache:[/bold]")
        console.print(f"  • Animations cached: {animation_count}")
        console.print(f"  • Cache size: {animation_size_mb:.2f} MB")

        total_size_mb = gen_stats["size_mb"] + animation_size_mb
        console.print("\n[bold]Total:[/bold]")
        console.print(
            f"  • Total entries: {gen_stats['total_entries'] + animation_count}"
        )
        console.print(f"  • Total size: {total_size_mb:.2f} MB")


@cache.command()
@click.argument("pattern", required=False)
@click.pass_context
def list(ctx: click.Context, pattern: Optional[str]) -> None:
    """List cached items, optionally filtered by pattern."""
    config: ProofSketcherConfig = ctx.obj["config"]
    cache_dir = config.cache_dir

    console.print("[bold blue]Cached Items:[/bold blue]")

    if not cache_dir.exists():
        console.print("[yellow]No cache directory found[/yellow]")
        return

    # List cache contents
    generator_files = []
    animation_files = []
    other_files = []

    for item in cache_dir.rglob("*"):
        if item.is_file():
            if pattern is None or pattern in str(item):
                rel_path = item.relative_to(cache_dir)
                if str(rel_path).startswith("generator/"):
                    generator_files.append(item)
                elif str(rel_path).startswith("animations/"):
                    animation_files.append(item)
                else:
                    other_files.append(item)

    total_files = len(generator_files) + len(animation_files) + len(other_files)

    if total_files > 0:
        table = Table(
            title=f"Cached Files{f' (filtered by: {pattern})' if pattern else ''}"
        )
        table.add_column("Type", style="magenta")
        table.add_column("File", style="cyan")
        table.add_column("Size", style="green")
        table.add_column("Modified", style="yellow")

        # Add generator cache files
        for file in sorted(generator_files)[:10]:  # Limit to 10 most recent
            size = f"{file.stat().st_size / 1024:.1f} KB"
            modified = time.strftime(
                "%Y-%m-%d %H:%M", time.localtime(file.stat().st_mtime)
            )
            table.add_row("Generator", str(file.relative_to(cache_dir)), size, modified)

        if len(generator_files) > 10:
            table.add_row(
                "...", f"and {len(generator_files) - 10} more generator files", "", ""
            )

        # Add animation cache files
        for file in sorted(animation_files)[:10]:  # Limit to 10 most recent
            size = f"{file.stat().st_size / 1024:.1f} KB"
            modified = time.strftime(
                "%Y-%m-%d %H:%M", time.localtime(file.stat().st_mtime)
            )
            table.add_row("Animation", str(file.relative_to(cache_dir)), size, modified)

        if len(animation_files) > 10:
            table.add_row(
                "...", f"and {len(animation_files) - 10} more animation files", "", ""
            )

        # Add other files
        for file in sorted(other_files):
            size = f"{file.stat().st_size / 1024:.1f} KB"
            modified = time.strftime(
                "%Y-%m-%d %H:%M", time.localtime(file.stat().st_mtime)
            )
            table.add_row("Other", str(file.relative_to(cache_dir)), size, modified)

        console.print(table)
        console.print(f"\n[dim]Total: {total_files} files[/dim]")
    else:
        console.print("[yellow]No cached items found[/yellow]")


@cli.command()
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
        console.print("[yellow]Proof Sketcher only processes Lean 4 files with .lean extension[/yellow]")
        console.print(f"[dim]Suggestion: Rename '{lean_file}' to '{lean_file.stem}.lean'[/dim]")
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
        console.print("\n[dim]For more examples, see: examples/classical/simple_examples.lean[/dim]")
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


@cli.command()
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


@cli.command()
def version() -> None:
    """Show Proof Sketcher version information."""
    from . import __version__

    console.print(f"[bold]Proof Sketcher[/bold] v{__version__}")
    console.print("\nComponents:")
    console.print("  • Parser: Lean 4 AST extraction")
    console.print("  • Generator: Claude AI integration")
    console.print("  • Animator: Manim via MCP")
    console.print("  • Exporters: HTML, Markdown, PDF, Jupyter")
    console.print("\nFor updates: https://github.com/your-org/proof-sketcher")


def main():
    """Main entry point for the CLI."""
    cli()


if __name__ == "__main__":
    main()
