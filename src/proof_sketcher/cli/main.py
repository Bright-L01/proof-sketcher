"""Main CLI entry point and configuration."""

import logging
from pathlib import Path
from typing import Optional

import click
from rich.console import Console
from rich.logging import RichHandler

from .. import __version__
from ..config.config import ProofSketcherConfig, set_config

# Commands
from .commands.batch import batch
from .commands.cache import cache
from .commands.config import config
from .commands.info import formats, list_theorems, version
from .commands.optimize import optimize
from .commands.performance import performance
from .commands.prove import prove

# Set up rich console
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


# Register commands
cli.add_command(prove)
cli.add_command(config)
cli.add_command(cache)
cli.add_command(list_theorems)
cli.add_command(formats)
cli.add_command(version)
cli.add_command(batch)
cli.add_command(performance)
cli.add_command(optimize)


def main() -> None:
    """Main entry point for the CLI."""
    cli()


if __name__ == "__main__":
    main()