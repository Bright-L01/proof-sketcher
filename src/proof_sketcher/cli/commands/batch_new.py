"""Enhanced batch processing command for Lean projects with caching and dependency analysis."""

import asyncio
import json
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import click
from rich.console import Console
from rich.panel import Panel
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn, TaskProgressColumn
from rich.table import Table

from ...batch import CacheManager, ParallelProcessor, ProjectScanner
from ...config.config import ProofSketcherConfig

console = Console()


@click.command()
@click.argument("project_dir", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--output", "-o",
    type=click.Path(path_type=Path),
    default="./proof_docs",
    help="Output directory for generated documentation"
)
@click.option(
    "--parallel", "-p",
    type=int,
    default=None,
    help="Number of parallel workers (default: CPU count)"
)
@click.option(
    "--format", "-f",
    type=click.Choice(["html", "markdown", "pdf", "all"]),
    multiple=True,
    default=["html"],
    help="Export formats (can specify multiple)"
)
@click.option(
    "--use-cache/--no-cache",
    default=True,
    help="Enable/disable caching of processed theorems"
)
@click.option(
    "--cache-dir",
    type=click.Path(path_type=Path),
    default=".proof_sketcher_cache",
    help="Cache directory location"
)
@click.option(
    "--ignore",
    multiple=True,
    help="Additional patterns to ignore (e.g., '**/test/**')"
)
@click.option(
    "--claude/--offline",
    default=True,
    help="Use Claude API (if available) or offline mode"
)
@click.option(
    "--visualize/--no-visualize",
    default=True,
    help="Generate visualizations for proofs"
)
@click.option(
    "--report",
    type=click.Path(path_type=Path),
    help="Save detailed processing report"
)
@click.option(
    "--dry-run",
    is_flag=True,
    help="Analyze project without processing"
)
@click.option(
    "--clean-cache",
    is_flag=True,
    help="Clean cache before processing"
)
def batch(
    project_dir: Path,
    output: Path,
    parallel: Optional[int],
    format: Tuple[str, ...],
    use_cache: bool,
    cache_dir: Path,
    ignore: Tuple[str, ...],
    claude: bool,
    visualize: bool,
    report: Optional[Path],
    dry_run: bool,
    clean_cache: bool,
) -> None:
    """Process entire Lean project with intelligent dependency analysis.
    
    This command scans a Lean project, analyzes dependencies, and processes
    all theorems in optimal order with caching and parallel execution.
    
    Examples:
    
      # Process a Lean project
      proof-sketcher batch ./my_lean_project/
      
      # Process with 8 parallel workers and multiple formats
      proof-sketcher batch ./mathlib/ -p 8 -f html -f markdown
      
      # Dry run to analyze project structure
      proof-sketcher batch ./src/ --dry-run
      
      # Process without cache
      proof-sketcher batch ./project/ --no-cache
    """
    start_time = time.time()
    
    console.print(Panel.fit(
        "[bold blue]🚀 Proof Sketcher Batch Processing[/bold blue]\n"
        f"Project: {project_dir}\n"
        f"Output: {output}",
        title="Batch Processing"
    ))
    
    # Initialize cache manager if enabled
    cache_manager = None
    if use_cache:
        cache_manager = CacheManager(
            cache_dir=Path(cache_dir),
            ttl_days=30,
            compress=True
        )
        
        if clean_cache:
            console.print("🧹 Cleaning cache...")
            cleared = cache_manager.clear_all()
            console.print(f"✅ Cleared {cleared} cache entries")
        else:
            stats = cache_manager.get_statistics()
            console.print(f"📦 Cache: {stats['total_entries']} entries ({stats['total_size_mb']:.1f} MB)")
    
    # Scan project
    console.print("\n🔍 Scanning project structure...")
    scanner = ProjectScanner(ignore_patterns=list(ignore))
    
    try:
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            console=console
        ) as progress:
            scan_task = progress.add_task("Analyzing Lean files...", total=None)
            project_data = scanner.scan_project(project_dir)
            progress.update(scan_task, completed=True)
    
    except Exception as e:
        console.print(f"[red]❌ Failed to scan project: {e}[/red]")
        sys.exit(1)
    
    # Display project statistics
    stats = project_data["statistics"]
    
    stats_table = Table(title="Project Statistics", show_header=False)
    stats_table.add_column("Metric", style="cyan")
    stats_table.add_column("Value", style="green")
    
    stats_table.add_row("Total Files", str(stats["total_files"]))
    stats_table.add_row("Total Theorems", str(stats["total_theorems"]))
    stats_table.add_row("Total Lines", f"{stats['total_lines']:,}")
    stats_table.add_row("Avg Theorems/File", f"{stats['avg_theorems_per_file']:.1f}")
    stats_table.add_row("Dependency Graph", f"{stats['dependency_graph']['nodes']} nodes, {stats['dependency_graph']['edges']} edges")
    stats_table.add_row("Is DAG", "✅ Yes" if stats["dependency_graph"]["is_dag"] else "❌ No (has cycles)")
    
    console.print(stats_table)
    
    # Show most connected files
    if stats["most_imported_files"]:
        console.print("\n📊 Most Imported Files:")
        for file, count in stats["most_imported_files"][:3]:
            console.print(f"  • {file}: {count} imports")
    
    if dry_run:
        console.print("\n[yellow]🏃 Dry run complete - no processing performed[/yellow]")
        
        # Save project analysis if report requested
        if report:
            report_data = {
                "project_dir": str(project_dir),
                "scan_time": time.time() - start_time,
                "statistics": stats,
                "files": project_data["files"],
                "process_order": project_data["process_order"],
                "file_theorems": project_data["file_theorems"],
                "dependency_info": {
                    "most_imported": stats["most_imported_files"],
                    "most_importing": stats["most_importing_files"],
                }
            }
            with open(report, 'w') as f:
                json.dump(report_data, f, indent=2)
            console.print(f"📄 Project analysis saved to: {report}")
        
        return
    
    # Prepare processing options
    export_formats = []
    if "all" in format:
        export_formats = ["html", "markdown", "pdf"]
    else:
        export_formats = list(format)
    
    processing_options = {
        "use_claude": claude,
        "create_visualization": visualize,
        "try_animation": visualize,
        "export_formats": export_formats,
        "project_name": project_dir.name,
        "author": "Proof Sketcher",
        "version": "1.0.0",
        "cache_manager": cache_manager,
    }
    
    # Initialize parallel processor
    processor = ParallelProcessor(
        max_workers=parallel,
        use_processes=True  # Use processes for better parallelism
    )
    
    # Progress callback
    processed_count = 0
    total_theorems = stats["total_theorems"]
    
    def progress_callback(file_path: str, theorem_name: str, result: Dict):
        nonlocal processed_count
        processed_count += 1
        
        status_icon = {
            "success": "✅",
            "skipped": "⏭️",
            "error": "❌"
        }.get(result["status"], "❓")
        
        console.print(
            f"{status_icon} [{processed_count}/{total_theorems}] "
            f"{theorem_name} ({result.get('time', 0):.1f}s)"
        )
    
    # Process project
    console.print(f"\n🚀 Processing {total_theorems} theorems with {processor.max_workers} workers...")
    
    try:
        # Run async processing
        process_results = asyncio.run(
            processor.process_project(
                project_data,
                output,
                processing_options,
                progress_callback
            )
        )
        
        total_time = time.time() - start_time
        
        # Display results summary
        console.print("\n" + "="*60)
        
        results_table = Table(title="Processing Results")
        results_table.add_column("Status", style="bold")
        results_table.add_column("Count", justify="right")
        results_table.add_column("Percentage", justify="right")
        
        total = process_results["total_theorems"]
        results_table.add_row(
            "✅ Successful",
            str(process_results["processed"]),
            f"{(process_results['processed']/total*100):.1f}%"
        )
        results_table.add_row(
            "⏭️ Skipped",
            str(process_results["skipped"]),
            f"{(process_results['skipped']/total*100):.1f}%"
        )
        results_table.add_row(
            "❌ Failed",
            str(process_results["errors"]),
            f"{(process_results['errors']/total*100):.1f}%"
        )
        
        console.print(results_table)
        
        # Performance statistics
        perf_stats = process_results["statistics"]
        console.print("\n⚡ Performance Statistics:")
        console.print(f"  • Total time: {total_time:.1f}s")
        console.print(f"  • Processing time: {perf_stats['total_time']:.1f}s")
        console.print(f"  • Average per theorem: {perf_stats['average_time']:.2f}s")
        console.print(f"  • Throughput: {perf_stats['theorems_per_second']:.2f} theorems/second")
        
        # Generator usage
        if perf_stats["generator_usage"]:
            console.print("\n🤖 Generator Usage:")
            for gen, count in perf_stats["generator_usage"].items():
                console.print(f"  • {gen}: {count} theorems")
        
        # Error summary
        if process_results["errors"] > 0:
            error_summary = process_results["error_summary"]
            console.print(f"\n❌ Error Summary ({error_summary['total_errors']} errors):")
            for error_type, errors in list(error_summary["by_type"].items())[:3]:
                console.print(f"  • {error_type}: {len(errors)} occurrences")
                if errors:
                    console.print(f"    Example: {errors[0]['theorem']} - {errors[0]['message'][:50]}...")
        
        # Cache statistics
        if cache_manager:
            cache_stats = cache_manager.get_statistics()
            console.print("\n📦 Cache Statistics:")
            console.print(f"  • Total entries: {cache_stats['total_entries']}")
            console.print(f"  • Cache size: {cache_stats['total_size_mb']:.1f} MB")
            console.print(f"  • Cache hits: {processing_options.get('cache_hits', 0)}")
        
        # Save detailed report
        if report:
            report_data = {
                "project_dir": str(project_dir),
                "output_dir": str(output),
                "processing_time": total_time,
                "options": {
                    "parallel_workers": processor.max_workers,
                    "export_formats": export_formats,
                    "use_cache": use_cache,
                    "use_claude": claude,
                    "visualize": visualize,
                },
                "results": process_results,
                "project_statistics": stats,
            }
            
            with open(report, 'w') as f:
                json.dump(report_data, f, indent=2)
            console.print(f"\n📄 Detailed report saved to: {report}")
        
        # Final summary
        if process_results["processed"] > 0:
            console.print(f"\n[green]✅ Successfully processed {process_results['processed']} theorems![/green]")
            console.print(f"📁 Documentation generated in: {output}")
            
            # Suggest next steps
            console.print("\n💡 Next steps:")
            console.print(f"  1. View generated documentation: open {output}/index.html")
            console.print(f"  2. Check individual theorems in: {output}/exports/")
            if visualize:
                console.print(f"  3. View visualizations in: {output}/visualizations/")
        else:
            console.print("\n[yellow]⚠️  No theorems were successfully processed[/yellow]")
        
    except KeyboardInterrupt:
        console.print("\n[yellow]⚠️  Processing interrupted by user[/yellow]")
        sys.exit(1)
    except Exception as e:
        console.print(f"\n[red]❌ Processing failed: {e}[/red]")
        import traceback
        if ProofSketcherConfig().debug:
            console.print_exception()
        sys.exit(1)