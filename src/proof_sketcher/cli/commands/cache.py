"""Cache management commands."""

import time
from typing import Optional

import click
from rich.console import Console
from rich.table import Table

from ...config.config import ProofSketcherConfig
from ...generator.cache import CacheManager

console = Console()


@click.group()
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

        by_type = gen_stats.get("by_type")
        if by_type and isinstance(by_type, dict):
            console.print("  • Cached by type:")
            for gen_type, count in by_type.items():
                console.print(f"    - {gen_type}: {count}")

        console.print("\n[bold]Animation Cache:[/bold]")
        console.print(f"  • Animations cached: {animation_count}")
        console.print(f"  • Cache size: {animation_size_mb:.2f} MB")

        size_mb = gen_stats.get("size_mb", 0)
        total_entries = gen_stats.get("total_entries", 0)
        if isinstance(size_mb, (int, float)) and isinstance(total_entries, (int, float)):
            total_size_mb = float(size_mb) + animation_size_mb
            total_entries_count = int(total_entries) + animation_count
            console.print("\n[bold]Total:[/bold]")
            console.print(f"  • Total entries: {total_entries_count}")
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