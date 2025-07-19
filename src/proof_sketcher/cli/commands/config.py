"""Configuration management command."""

from pathlib import Path

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
        config_path = Path(".proof-sketcher.yaml")
        default_config.save(config_path)
        console.print(f"✅ [green]Configuration reset to defaults and saved to {config_path}[/green]")
        return

    if show:
        # Show current configuration
        config_obj = ProofSketcherConfig.load()
        console.print("[bold green]Current Configuration:[/bold green]")
        console.print()
        
        # Global settings
        console.print("[bold]Global Settings:[/bold]")
        console.print(f"  Project Name: {config_obj.project_name}")
        console.print(f"  Version: {config_obj.version}")
        console.print(f"  Debug: {config_obj.debug}")
        console.print(f"  Log Level: {config_obj.log_level}")
        console.print(f"  Cache Directory: {config_obj.cache_dir}")
        console.print(f"  Data Directory: {config_obj.data_dir}")
        console.print()
        
        # Parser settings
        console.print("[bold]Parser Settings:[/bold]")
        console.print(f"  Lean Executable: {config_obj.parser.lean_executable}")
        console.print(f"  Lake Executable: {config_obj.parser.lake_executable}")
        console.print(f"  Use LSP: {config_obj.parser.use_lsp}")
        console.print(f"  Extract Proofs: {config_obj.parser.extract_proofs}")
        console.print(f"  Timeout: {config_obj.parser.timeout}s")
        console.print()
        
        # Generator settings
        console.print("[bold]Generator Settings:[/bold]")
        console.print(f"  Model: {config_obj.generator.model.value}")
        console.print(f"  Temperature: {config_obj.generator.temperature}")
        console.print(f"  Max Tokens: {config_obj.generator.max_tokens}")
        console.print(f"  Verbosity: {config_obj.generator.verbosity}")
        console.print(f"  Include Reasoning: {config_obj.generator.include_reasoning}")
        console.print()
        
        # Export settings
        console.print("[bold]Export Settings:[/bold]")
        console.print(f"  Output Directory: {config_obj.export.output_dir}")
        console.print(f"  HTML Theme: {config_obj.export.html_theme}")
        console.print(f"  Markdown Flavor: {config_obj.export.markdown_flavor}")
        console.print(f"  Parallel Exports: {config_obj.export.parallel_exports}")
        console.print(f"  Cache Exports: {config_obj.export.cache_exports}")
        return

    # Interactive configuration (future feature)
    console.print("[yellow]Interactive configuration not yet implemented[/yellow]")
    console.print("Use --show to view current settings or --reset to restore defaults")
