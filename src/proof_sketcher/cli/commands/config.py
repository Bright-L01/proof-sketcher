"""Configuration management command."""

import click
from rich.console import Console

from ...config.config import ProofSketcherConfig

console = Console()


@click.command()
@click.option(
    "--show",
    is_flag=True,
    help="Show current configuration",
)
@click.option(
    "--reset",
    is_flag=True,
    help="Reset to default configuration",
)
def config(show: bool, reset: bool) -> None:
    """Manage Proof Sketcher configuration.

    \b
    Examples:
      # Show current config
      proof-sketcher config --show

      # Reset to defaults
      proof-sketcher config --reset
    """
    if reset:
        # Reset to default config
        default_config = ProofSketcherConfig()
        default_config.save()
        console.print("✅ [green]Configuration reset to defaults[/green]")
        return

    if show:
        # Show current configuration
        config_obj = ProofSketcherConfig.load()
        console.print("[bold green]Current Configuration:[/bold green]")
        console.print(f"  Debug: {config_obj.debug}")
        console.print(f"  Log Level: {config_obj.log_level}")
        console.print(f"  Output Directory: {config_obj.output_dir}")
        console.print(f"  Default Format: {config_obj.default_format}")
        console.print(f"  Include Proofs: {config_obj.include_proofs}")
        return

    # Interactive configuration (future feature)
    console.print("[yellow]Interactive configuration not yet implemented[/yellow]")
    console.print("Use --show to view current settings or --reset to restore defaults")
