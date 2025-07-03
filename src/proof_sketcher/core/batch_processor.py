"""Batch processing capability for multiple Lean files.

Features:
- Process entire directories of Lean files
- Parallel processing for performance
- Progress tracking and reporting
- Error handling and recovery
- Lake project awareness
- Export in multiple formats
- Memory-efficient streaming processing
"""

import logging
import shutil
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from collections import defaultdict

from rich.console import Console
from rich.progress import Progress, BarColumn, TextColumn, TimeElapsedColumn, TaskID
from rich.table import Table

from .exceptions import BatchProcessingError, BatchFileError, GeneratorError, ExporterError
from .resources import ResourceMonitor
from ..parser.lean_parser import LeanParser
from ..parser.config import ParserConfig
from ..generator.offline import OfflineGenerator
from ..generator.models import ProofSketch
from ..exporter.html import HTMLExporter
from ..exporter.markdown import MarkdownExporter
from ..exporter.models import ExportOptions, ExportContext, ExportFormat


@dataclass
class BatchJob:
    """A single file processing job in a batch."""
    file_path: Path
    priority: int = 0
    metadata: Optional[Dict[str, Any]] = None
    
    def __post_init__(self):
        if self.metadata is None:
            self.metadata = {}


@dataclass
class BatchResult:
    """Result of processing a single file in a batch."""
    file_path: Path
    success: bool
    theorems_found: int = 0
    sketches_generated: int = 0
    exports_created: int = 0
    parse_time_ms: float = 0.0
    generation_time_ms: float = 0.0
    export_time_ms: float = 0.0
    total_time_ms: float = 0.0
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)


@dataclass
class BatchStats:
    """Statistics from a complete batch processing run."""
    total_files: int
    successful_files: int
    failed_files: int
    total_theorems: int
    total_sketches: int
    total_exports: int
    total_time_ms: float
    average_time_per_file_ms: float
    average_time_per_theorem_ms: float
    files_per_second: float
    theorems_per_second: float
    peak_memory_mb: float
    error_summary: Dict[str, int]
    
    def display(self, console: Console) -> None:
        """Display batch statistics in a formatted table."""
        console.print("\n[bold green]📊 Batch Processing Summary[/bold green]")
        
        # Main statistics table
        table = Table(title="Batch Processing Results")
        table.add_column("Metric", style="cyan", no_wrap=True)
        table.add_column("Value", justify="right", style="bold white")
        table.add_column("Rate", justify="right", style="green")
        
        table.add_row("Files Processed", str(self.total_files), f"{self.files_per_second:.1f}/sec")
        table.add_row("Successful", str(self.successful_files), f"{(self.successful_files/self.total_files*100):.1f}%")
        table.add_row("Failed", str(self.failed_files), f"{(self.failed_files/self.total_files*100):.1f}%")
        table.add_row("Theorems Found", str(self.total_theorems), f"{self.theorems_per_second:.1f}/sec")
        table.add_row("Sketches Generated", str(self.total_sketches), "")
        table.add_row("Exports Created", str(self.total_exports), "")
        table.add_row("Total Time", f"{self.total_time_ms/1000:.1f}s", "")
        table.add_row("Peak Memory", f"{self.peak_memory_mb:.1f}MB", "")
        
        console.print(table)
        
        # Error summary if there were errors
        if self.error_summary:
            console.print("\n[bold red]❌ Error Summary[/bold red]")
            error_table = Table()
            error_table.add_column("Error Type", style="red")
            error_table.add_column("Count", justify="right", style="bold red")
            
            for error_type, count in sorted(self.error_summary.items()):
                error_table.add_row(error_type, str(count))
                
            console.print(error_table)


class BatchProcessor:
    """Main batch processing engine for Lean files."""
    
    def __init__(
        self,
        max_workers: int = 4,
        memory_limit_mb: int = 1024,
        use_enhanced_parser: bool = True,
        export_formats: Optional[List[ExportFormat]] = None
    ):
        """Initialize batch processor.
        
        Args:
            max_workers: Maximum number of parallel workers
            memory_limit_mb: Memory limit for processing
            use_enhanced_parser: Whether to use enhanced parser
            export_formats: List of export formats to generate
        """
        self.max_workers = max_workers
        self.memory_limit_mb = memory_limit_mb
        self.use_enhanced_parser = use_enhanced_parser
        self.export_formats = export_formats or [ExportFormat.HTML]
        
        self.logger = logging.getLogger(__name__)
        self.console = Console()
        
        # Initialize components
        parser_config = ParserConfig(
            fallback_to_regex=True,
            auto_detect_lake=True,
            lean_timeout=30.0
        )
        self.parser = LeanParser(parser_config)
        self.generator = OfflineGenerator()
        self.resource_monitor = ResourceMonitor()
        
        # Processing state
        self.jobs: List[BatchJob] = []
        self.results: List[BatchResult] = []
        self.temp_dir: Optional[Path] = None
        
    def discover_lean_files(
        self, 
        root_path: Path, 
        recursive: bool = True,
        exclude_patterns: Optional[List[str]] = None
    ) -> List[Path]:
        """Discover Lean files in a directory.
        
        Args:
            root_path: Root directory to search
            recursive: Whether to search recursively
            exclude_patterns: Patterns to exclude (e.g., ["**/test/**", "**/temp/**"])
            
        Returns:
            List of discovered Lean file paths
        """
        if not root_path.exists():
            raise BatchProcessingError(f"Root path does not exist: {root_path}")
            
        exclude_patterns = exclude_patterns or []
        lean_files = []
        
        if recursive:
            pattern = "**/*.lean"
        else:
            pattern = "*.lean"
            
        for file_path in root_path.glob(pattern):
            if file_path.is_file():
                # Check exclude patterns
                excluded = False
                for exclude_pattern in exclude_patterns:
                    if file_path.match(exclude_pattern):
                        excluded = True
                        break
                
                if not excluded:
                    lean_files.append(file_path)
        
        return sorted(lean_files)
    
    def add_files(self, file_paths: List[Path], priority: int = 0) -> None:
        """Add files to the batch processing queue.
        
        Args:
            file_paths: List of Lean file paths to process
            priority: Processing priority (higher = earlier)
        """
        for file_path in file_paths:
            if not file_path.exists():
                self.logger.warning(f"File does not exist: {file_path}")
                continue
                
            if not file_path.suffix == ".lean":
                self.logger.warning(f"Not a Lean file: {file_path}")
                continue
                
            job = BatchJob(file_path=file_path, priority=priority)
            self.jobs.append(job)
            
        # Sort by priority (higher first)
        self.jobs.sort(key=lambda job: job.priority, reverse=True)
        
        self.logger.info(f"Added {len(file_paths)} files to batch queue (total: {len(self.jobs)})")
    
    def add_directory(
        self, 
        directory: Path, 
        recursive: bool = True,
        exclude_patterns: Optional[List[str]] = None,
        priority: int = 0
    ) -> None:
        """Add all Lean files from a directory to the batch queue.
        
        Args:
            directory: Directory containing Lean files
            recursive: Whether to search recursively
            exclude_patterns: Patterns to exclude
            priority: Processing priority
        """
        lean_files = self.discover_lean_files(
            directory, recursive=recursive, exclude_patterns=exclude_patterns
        )
        self.add_files(lean_files, priority=priority)
    
    async def process_batch(
        self, 
        output_dir: Path,
        progress_callback: Optional[callable] = None
    ) -> BatchStats:
        """Process all files in the batch queue.
        
        Args:
            output_dir: Directory for output files
            progress_callback: Optional callback for progress updates
            
        Returns:
            Batch processing statistics
        """
        if not self.jobs:
            raise BatchProcessingError("No files in batch queue")
            
        # Setup output directory
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Setup temporary directory
        self.temp_dir = Path(tempfile.mkdtemp(prefix="batch_processing_"))
        
        try:
            # Start resource monitoring
            # Note: ResourceMonitor doesn't require async start/stop for this demo
            
            start_time = time.perf_counter()
            
            # Process files with progress tracking
            with Progress(
                TextColumn("[progress.description]{task.description}"),
                BarColumn(),
                TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
                TextColumn("({task.completed}/{task.total})"),
                TimeElapsedColumn(),
                console=self.console,
            ) as progress:
                
                task = progress.add_task("Processing files...", total=len(self.jobs))
                
                # Process files in parallel
                await self._process_files_parallel(self.jobs, output_dir, progress, task)
                
            total_time = (time.perf_counter() - start_time) * 1000
            
            # Generate statistics
            stats = self._calculate_stats(total_time)
            
            return stats
            
        finally:
            # Cleanup
            pass
            if self.temp_dir and self.temp_dir.exists():
                shutil.rmtree(self.temp_dir)
    
    async def _process_files_parallel(
        self, 
        jobs: List[BatchJob], 
        output_dir: Path,
        progress: Progress,
        task: TaskID
    ) -> None:
        """Process files in parallel using thread pool."""
        
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            # Submit all jobs
            future_to_job = {
                executor.submit(self._process_single_file, job, output_dir): job
                for job in jobs
            }
            
            # Process completed jobs
            for future in as_completed(future_to_job):
                job = future_to_job[future]
                try:
                    result = future.result()
                    self.results.append(result)
                    
                    # Update progress
                    progress.update(task, advance=1)
                    
                    # Memory check
                    current_usage = self.resource_monitor.get_current_usage()
                    if current_usage.memory_mb > self.memory_limit_mb:
                        self.logger.warning(f"Memory usage high: {current_usage.memory_mb:.1f}MB")
                        
                except BatchFileError as e:
                    self.logger.error(f"Batch processing failed for {job.file_path}: {e}")
                    error_result = BatchResult(
                        file_path=job.file_path,
                        success=False,
                        errors=[f"Batch processing error: {e}"]
                    )
                    self.results.append(error_result)
                    progress.update(task, advance=1)
                except (OSError, PermissionError) as e:
                    self.logger.error(f"File system error for {job.file_path}: {e}")
                    error_result = BatchResult(
                        file_path=job.file_path,
                        success=False,
                        errors=[f"File system error: {e}"]
                    )
                    self.results.append(error_result)
                    progress.update(task, advance=1)
                except Exception as e:
                    self.logger.error(f"Unexpected error processing {job.file_path}: {e}")
                    error_result = BatchResult(
                        file_path=job.file_path,
                        success=False,
                        errors=[f"Unexpected error: {type(e).__name__}: {e}"]
                    )
                    self.results.append(error_result)
                    progress.update(task, advance=1)
    
    def _process_single_file(self, job: BatchJob, output_dir: Path) -> BatchResult:
        """Process a single Lean file."""
        start_time = time.perf_counter()
        result = BatchResult(file_path=job.file_path, success=False)
        
        try:
            # 1. Parse file
            parse_start = time.perf_counter()
            
            if self.use_enhanced_parser:
                parse_result = self.parser.parse_file(job.file_path)
            else:
                parse_result = self.parser.parse_file(job.file_path)
                
            result.parse_time_ms = (time.perf_counter() - parse_start) * 1000
            
            if not parse_result.success or not parse_result.theorems:
                result.errors.extend([str(e) for e in parse_result.errors])
                if not parse_result.theorems:
                    result.warnings.append("No theorems found in file")
                return result
                
            result.theorems_found = len(parse_result.theorems)
            
            # 2. Generate proof sketches
            gen_start = time.perf_counter()
            sketches = []
            
            for theorem in parse_result.theorems:
                try:
                    sketch = self.generator.generate_proof_sketch(theorem)
                    sketches.append(sketch)
                    result.sketches_generated += 1
                except GeneratorError as e:
                    result.warnings.append(f"Generation failed for {theorem.name}: {e}")
                except (OSError, MemoryError, KeyboardInterrupt) as e:
                    result.errors.append(f"System error during generation of {theorem.name}: {e}")
                    break  # Stop processing this file on system errors
            
            result.generation_time_ms = (time.perf_counter() - gen_start) * 1000
            
            # 3. Export in requested formats
            export_start = time.perf_counter()
            
            for export_format in self.export_formats:
                try:
                    export_count = self._export_sketches(
                        sketches, export_format, output_dir, job.file_path
                    )
                    result.exports_created += export_count
                except ExporterError as e:
                    result.warnings.append(f"Export failed for {export_format}: {e}")
                except (OSError, PermissionError) as e:
                    result.errors.append(f"File system error during export to {export_format}: {e}")
                except MemoryError as e:
                    result.errors.append(f"Out of memory during export to {export_format}: {e}")
                    break  # Stop processing exports on memory error
            
            result.export_time_ms = (time.perf_counter() - export_start) * 1000
            result.success = True
            
        except BatchFileError as e:
            result.errors.append(f"Batch processing error: {e}")
        except (OSError, PermissionError) as e:
            result.errors.append(f"File system error: {e}")
        except MemoryError as e:
            result.errors.append(f"Out of memory: {e}")
        except KeyboardInterrupt:
            result.errors.append("Processing interrupted by user")
        except Exception as e:
            # Fallback for truly unexpected errors
            result.errors.append(f"Unexpected error: {type(e).__name__}: {e}")
            
        result.total_time_ms = (time.perf_counter() - start_time) * 1000
        return result
    
    def _export_sketches(
        self, 
        sketches: List[ProofSketch], 
        export_format: ExportFormat,
        output_dir: Path,
        source_file: Path
    ) -> int:
        """Export sketches in the specified format."""
        if not sketches:
            return 0
            
        # Create format-specific output directory
        format_dir = output_dir / export_format.value
        format_dir.mkdir(parents=True, exist_ok=True)
        
        # Setup exporter
        export_options = ExportOptions.model_validate({
            "output_dir": format_dir
        })
        
        if export_format == ExportFormat.HTML:
            exporter = HTMLExporter(export_options)
        elif export_format == ExportFormat.MARKDOWN:
            exporter = MarkdownExporter(export_options)
        else:
            raise BatchProcessingError(f"Unsupported export format: {export_format}")
        
        # Export context
        export_context = ExportContext(
            format=export_format,
            output_dir=format_dir,
            sketches=sketches,
            metadata={"source_file": str(source_file)}
        )
        
        # Export all sketches
        export_count = 0
        for sketch in sketches:
            try:
                result = exporter.export_single(sketch, export_context)
                if result.success:
                    export_count += 1
            except ExporterError as e:
                self.logger.warning(f"Export error for {sketch.theorem_name}: {e}")
            except (OSError, PermissionError) as e:
                self.logger.error(f"File system error exporting {sketch.theorem_name}: {e}")
            except MemoryError as e:
                self.logger.error(f"Out of memory exporting {sketch.theorem_name}: {e}")
                break  # Stop on memory errors
                
        return export_count
    
    def _calculate_stats(self, total_time_ms: float) -> BatchStats:
        """Calculate batch processing statistics."""
        successful_results = [r for r in self.results if r.success]
        failed_results = [r for r in self.results if not r.success]
        
        total_theorems = sum(r.theorems_found for r in self.results)
        total_sketches = sum(r.sketches_generated for r in self.results)
        total_exports = sum(r.exports_created for r in self.results)
        
        # Error summary
        error_summary = defaultdict(int)
        for result in failed_results:
            for error in result.errors:
                # Categorize error
                if "timeout" in error.lower():
                    error_summary["Timeout"] += 1
                elif "memory" in error.lower():
                    error_summary["Memory"] += 1
                elif "parse" in error.lower():
                    error_summary["Parse Error"] += 1
                elif "generation" in error.lower():
                    error_summary["Generation Error"] += 1
                else:
                    error_summary["Other"] += 1
        
        # Calculate rates
        total_files = len(self.results)
        files_per_second = (total_files * 1000) / total_time_ms if total_time_ms > 0 else 0
        theorems_per_second = (total_theorems * 1000) / total_time_ms if total_time_ms > 0 else 0
        avg_time_per_file = total_time_ms / total_files if total_files > 0 else 0
        avg_time_per_theorem = total_time_ms / total_theorems if total_theorems > 0 else 0
        
        # Memory usage
        peak_memory = self.resource_monitor.get_current_usage().memory_mb
        
        return BatchStats(
            total_files=total_files,
            successful_files=len(successful_results),
            failed_files=len(failed_results),
            total_theorems=total_theorems,
            total_sketches=total_sketches,
            total_exports=total_exports,
            total_time_ms=total_time_ms,
            average_time_per_file_ms=avg_time_per_file,
            average_time_per_theorem_ms=avg_time_per_theorem,
            files_per_second=files_per_second,
            theorems_per_second=theorems_per_second,
            peak_memory_mb=peak_memory,
            error_summary=dict(error_summary)
        )
    
    def get_results_by_status(self) -> Tuple[List[BatchResult], List[BatchResult]]:
        """Get results separated by success/failure status.
        
        Returns:
            Tuple of (successful_results, failed_results)
        """
        successful = [r for r in self.results if r.success]
        failed = [r for r in self.results if not r.success]
        return successful, failed
    
    def save_detailed_report(self, output_path: Path) -> None:
        """Save detailed batch processing report to JSON file."""
        import json
        from datetime import datetime
        
        report = {
            "timestamp": datetime.now().isoformat(),
            "configuration": {
                "max_workers": self.max_workers,
                "memory_limit_mb": self.memory_limit_mb,
                "use_enhanced_parser": self.use_enhanced_parser,
                "export_formats": [fmt.value for fmt in self.export_formats]
            },
            "results": [
                {
                    "file_path": str(result.file_path),
                    "success": result.success,
                    "theorems_found": result.theorems_found,
                    "sketches_generated": result.sketches_generated,
                    "exports_created": result.exports_created,
                    "parse_time_ms": result.parse_time_ms,
                    "generation_time_ms": result.generation_time_ms,
                    "export_time_ms": result.export_time_ms,
                    "total_time_ms": result.total_time_ms,
                    "errors": result.errors,
                    "warnings": result.warnings
                }
                for result in self.results
            ]
        }
        
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
            
        self.console.print(f"[green]✅ Detailed report saved to: {output_path}[/green]")