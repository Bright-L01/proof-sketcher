"""Configuration management commands."""

import sys
from pathlib import Path
from typing import Optional

import click
from rich.console import Console
from rich.table import Table

from ...config.config import ProofSketcherConfig

console = Console()


@click.group()
def config() -> None:
    """Manage Proof Sketcher configuration settings.

    Configure how Proof Sketcher processes files, generates explanations,
    and exports results. Settings can be managed through configuration files,
    environment variables, or command-line options.

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
