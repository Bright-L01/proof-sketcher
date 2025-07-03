"""Batch processing command for multiple files."""

import asyncio
import sys
from pathlib import Path
from typing import Optional, Tuple

import click
from rich.console import Console

from ...config.config import ProofSketcherConfig
from ...core.batch_processor import BatchProcessor
from ...exporter import ExportFormat

console = Console()


@click.command()
@click.argument("input_path", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--output-dir", "-o",
    type=click.Path(path_type=Path),
    default="./batch_output",
    help="Output directory for batch results"
)
@click.option(
    "--recursive/--no-recursive", "-r",
    default=True,
    help="Search for Lean files recursively"
)
@click.option(
    "--workers", "-w",
    type=int,
    default=4,
    help="Number of parallel workers"
)
@click.option(
    "--memory-limit",
    type=int,
    default=1024,
    help="Memory limit in MB"
)
@click.option(
    "--formats", "-f",
    type=click.Choice(["html", "markdown", "all"]),
    multiple=True,
    default=["html"],
    help="Export formats (can specify multiple)"
)
@click.option(
    "--exclude",
    multiple=True,
    help="Exclude patterns (e.g., '**/test/**')"
)
@click.option(
    "--enhanced/--basic",
    default=True,
    help="Use enhanced parser (recommended)"
)
@click.option(
    "--report",
    type=click.Path(path_type=Path),
    help="Save detailed report to JSON file"
)
@click.pass_context
def batch(
    ctx: click.Context,
    input_path: Path,
    output_dir: Path,
    recursive: bool,
    workers: int,
    memory_limit: int,
    formats: Tuple[str, ...],
    exclude: Tuple[str, ...],
    enhanced: bool,
    report: Optional[Path]
) -> None:
    """Process multiple Lean files in batch mode.
    
    INPUT_PATH can be either a directory containing Lean files or a single Lean file.
    
    Examples:
    
      # Process all files in a directory
      proof-sketcher batch ./my_project/ -o ./output/
      
      # Process with specific settings
      proof-sketcher batch ./mathlib/ -w 8 --memory-limit 2048 -f html -f markdown
      
      # Exclude test files
      proof-sketcher batch ./src/ --exclude "**/test/**" --exclude "**/temp/**"
    """
    config: ProofSketcherConfig = ctx.obj["config"]
    
    console.print(f"[bold blue]🔄 Starting Batch Processing[/bold blue]")
    console.print(f"Input: {input_path}")
    console.print(f"Output: {output_dir}")
    console.print(f"Workers: {workers}")
    console.print(f"Memory limit: {memory_limit}MB")
    console.print(f"Enhanced parser: {'Yes' if enhanced else 'No'}")
    
    # Parse format options
    export_formats = []
    if "all" in formats:
        export_formats = [ExportFormat.HTML, ExportFormat.MARKDOWN]
    else:
        for fmt in formats:
            if fmt == "html":
                export_formats.append(ExportFormat.HTML)
            elif fmt == "markdown":
                export_formats.append(ExportFormat.MARKDOWN)
    
    # Initialize batch processor
    processor = BatchProcessor(
        max_workers=workers,
        memory_limit_mb=memory_limit,
        use_enhanced_parser=enhanced,
        export_formats=export_formats
    )
    
    try:
        # Add files to the batch queue
        if input_path.is_file():
            processor.add_files([input_path])
            console.print(f"Added 1 file to batch queue")
        else:
            processor.add_directory(
                input_path,
                recursive=recursive,
                exclude_patterns=list(exclude) if exclude else None
            )
            file_count = len(processor.jobs)
            console.print(f"Added {file_count} files to batch queue")
            
        if not processor.jobs:
            console.print("[yellow]⚠️  No Lean files found to process[/yellow]")
            return
        
        # Process the batch
        async def run_batch():
            stats = await processor.process_batch(output_dir)
            return stats
        
        # Run the batch processing
        stats = asyncio.run(run_batch())
        
        # Display results
        stats.display(console)
        
        # Save detailed report if requested
        if report:
            processor.save_detailed_report(report)
        
        # Performance recommendations
        console.print("\n[bold cyan]💡 Performance Insights[/bold cyan]")
        
        if stats.theorems_per_second > 5.0:
            console.print("  ✅ Excellent processing rate - ready for large-scale batch processing")
        elif stats.theorems_per_second > 1.0:
            console.print("  ✅ Good processing rate - suitable for regular batch jobs")
        else:
            console.print("  ⚠️  Consider increasing workers or optimizing for better performance")
            
        if stats.failed_files > 0:
            failure_rate = (stats.failed_files / stats.total_files) * 100
            if failure_rate > 20:
                console.print(f"  ⚠️  High failure rate ({failure_rate:.1f}%) - check file formats and dependencies")
            else:
                console.print(f"  ℹ️  Some files failed ({failure_rate:.1f}%) - see error summary above")
        
        console.print(f"\n[green]✅ Batch processing completed! Results saved to: {output_dir}[/green]")
        
    except Exception as e:
        console.print(f"[red]❌ Batch processing failed: {e}[/red]")
        if config.debug:
            console.print_exception()
        sys.exit(1)