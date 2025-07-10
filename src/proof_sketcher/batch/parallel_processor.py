"""Parallel processor for efficient theorem processing."""

import asyncio
import logging
import multiprocessing
import time
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

from tqdm import tqdm

from ..config.config import ProofSketcherConfig


class ProcessingError(Exception):
    """Error during parallel processing."""

    pass


def _process_single_theorem_worker(args: Tuple) -> Dict[str, Any]:
    """Worker function for processing a single theorem.

    This runs in a separate process to avoid GIL and memory issues.

    Args:
        args: Tuple of (file_path, theorem_name, output_dir, options)

    Returns:
        Processing result dictionary
    """
    file_path, theorem_name, output_dir, options = args

    # Import here to avoid pickling issues
    from pathlib import Path

    from ..exporter.html import HTMLExporter
    from ..exporter.markdown import MarkdownExporter
    from ..exporter.models import ExportContext, ExportFormat, ExportOptions
    from ..generator import AIGenerator
    from ..generator.models import ProofSketch, ProofStep
    from ..generator.offline import OfflineGenerator
    from ..parser.lean_parser import LeanParser

    start_time = time.time()

    try:
        # Parse theorem
        parser = LeanParser()
        theorem_info = None

        # Try to extract specific theorem
        theorems = parser.parse_file(Path(file_path))
        for theorem in theorems:
            if theorem.name == theorem_name:
                theorem_info = theorem
                break

        if not theorem_info:
            return {
                "status": "skipped",
                "theorem": theorem_name,
                "file": file_path,
                "reason": "Theorem not found in file",
                "time": time.time() - start_time,
            }

        # Convert to dict for processing
        theorem_dict = {
            "name": theorem_info.name,
            "statement": theorem_info.statement,
            "proo": theorem_info.proof,
            "docstring": theorem_info.docstring,
            "dependencies": [],  # Would need deeper analysis
        }

        # Generate explanation
        explanation = None
        generator_used = None

        if options.get("use_claude", True):
            try:
                generator = AIGenerator()
                result = generator.generate_proof_sketch(theorem_info)
                if result:
                    explanation = result
                    generator_used = "ai_generator"
            except Exception as e:
                # Fallback to offline
                pass

        if not explanation:
            # Use offline generator
            generator = OfflineGenerator()
            explanation = generator.generate_proof_sketch(theorem_info)
            generator_used = "offline"

        # Create visualization
        visualization_path = None
        visualizer_used = None

        if options.get("create_visualization", True):
            output_path = Path(output_dir) / "visualizations" / f"{theorem_name}.png"
            output_path.parent.mkdir(parents=True, exist_ok=True)

            # Static visualization is not available after removing animation system
            visualization_path = None
            visualizer_used = "none"

        # Export to requested formats
        exported_files = []
        export_formats = options.get("export_formats", ["html"])

        export_options = ExportOptions(
            output_dir=Path(output_dir) / "exports",
            create_subdirs=True,
            include_animations=bool(visualization_path),
            include_timestamps=True,
        )

        context = ExportContext(
            format=ExportFormat.HTML,
            output_dir=export_options.output_dir,
            sketches=[explanation],
            animations=(
                {theorem_name: Path(visualization_path)} if visualization_path else {}
            ),
            project_name=options.get("project_name", "Lean Project"),
            author=options.get("author", "Proof Sketcher"),
            version=options.get("version", "1.0.0"),
        )

        for format_name in export_formats:
            try:
                if format_name == "html":
                    exporter = HTMLExporter(export_options)
                    result = exporter.export_single(explanation, context)
                    if result.success:
                        exported_files.extend([str(f) for f in result.files_created])
                elif format_name == "markdown":
                    exporter = MarkdownExporter(export_options)
                    result = exporter.export_single(explanation, context)
                    if result.success:
                        exported_files.extend([str(f) for f in result.files_created])
            except Exception as e:
                # Log but don't fail the whole theorem
                pass

        return {
            "status": "success",
            "theorem": theorem_name,
            "file": file_path,
            "generator": generator_used,
            "visualizer": visualizer_used,
            "visualization": visualization_path,
            "exported_files": exported_files,
            "time": time.time() - start_time,
        }

    except Exception as e:
        return {
            "status": "error",
            "theorem": theorem_name,
            "file": file_path,
            "error": str(e),
            "error_type": type(e).__name__,
            "time": time.time() - start_time,
        }


class ParallelProcessor:
    """Process theorems in parallel with robust error handling."""

    def __init__(self, max_workers: Optional[int] = None, use_processes: bool = True):
        """Initialize parallel processor.

        Args:
            max_workers: Maximum number of parallel workers
            use_processes: Use process pool (True) or thread pool (False)
        """
        self.max_workers = max_workers or min(multiprocessing.cpu_count(), 8)
        self.use_processes = use_processes
        self.logger = logging.getLogger(__name__)

    async def process_project(
        self,
        project_data: Dict,
        output_dir: Path,
        options: Optional[Dict] = None,
        progress_callback: Optional[Callable] = None,
    ) -> Dict[str, Any]:
        """Process entire project in parallel.

        Args:
            project_data: Project scan data from ProjectScanner
            output_dir: Output directory for results
            options: Processing options
            progress_callback: Callback for progress updates

        Returns:
            Processing results dictionary
        """
        options = options or {}
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)

        # Collect all theorems to process
        all_theorems = []
        for file_path in project_data["process_order"]:
            theorems = project_data["file_theorems"].get(file_path, [])
            for theorem_name in theorems:
                all_theorems.append((file_path, theorem_name))

        total_theorems = len(all_theorems)
        self.logger.info(
            f"Processing {total_theorems} theorems with {self.max_workers} workers"
        )

        # Process theorems
        results = await self._process_theorems_batch(
            all_theorems, output_dir, options, progress_callback
        )

        # Aggregate results
        successful = [r for r in results if r["status"] == "success"]
        skipped = [r for r in results if r["status"] == "skipped"]
        errors = [r for r in results if r["status"] == "error"]

        # Compute statistics
        total_time = sum(r["time"] for r in results)
        avg_time = total_time / len(results) if results else 0

        return {
            "total_theorems": total_theorems,
            "processed": len(successful),
            "skipped": len(skipped),
            "errors": len(errors),
            "results": results,
            "statistics": {
                "total_time": total_time,
                "average_time": avg_time,
                "theorems_per_second": (
                    len(results) / total_time if total_time > 0 else 0
                ),
                "generator_usage": self._count_generator_usage(successful),
                "visualizer_usage": self._count_visualizer_usage(successful),
            },
            "error_summary": self._summarize_errors(errors),
        }

    async def _process_theorems_batch(
        self,
        theorems: List[Tuple[str, str]],
        output_dir: Path,
        options: Dict,
        progress_callback: Optional[Callable],
    ) -> List[Dict]:
        """Process a batch of theorems in parallel.

        Args:
            theorems: List of (file_path, theorem_name) tuples
            output_dir: Output directory
            options: Processing options
            progress_callback: Progress callback

        Returns:
            List of processing results
        """
        results = []

        # Prepare arguments for workers
        worker_args = [
            (file_path, theorem_name, str(output_dir), options)
            for file_path, theorem_name in theorems
        ]

        # Choose executor based on configuration
        if self.use_processes:
            executor_class = ProcessPoolExecutor
        else:
            executor_class = ThreadPoolExecutor

        with executor_class(max_workers=self.max_workers) as executor:
            # Submit all tasks
            future_to_theorem = {
                executor.submit(_process_single_theorem_worker, args): (
                    args[0],
                    args[1],
                )
                for args in worker_args
            }

            # Process results as they complete
            with tqdm(total=len(theorems), desc="Processing theorems") as pbar:
                for future in as_completed(future_to_theorem):
                    file_path, theorem_name = future_to_theorem[future]

                    try:
                        result = future.result(timeout=300)  # 5 minute timeout
                        results.append(result)

                        if progress_callback:
                            await self._run_callback_async(
                                progress_callback, file_path, theorem_name, result
                            )

                    except Exception as e:
                        # Handle timeout or other errors
                        error_result = {
                            "status": "error",
                            "theorem": theorem_name,
                            "file": file_path,
                            "error": f"Processing failed: {str(e)}",
                            "error_type": type(e).__name__,
                            "time": 0,
                        }
                        results.append(error_result)

                        if progress_callback:
                            await self._run_callback_async(
                                progress_callback, file_path, theorem_name, error_result
                            )

                    pbar.update(1)

        return results

    async def _run_callback_async(self, callback: Callable, *args):
        """Run callback asynchronously if needed."""
        if asyncio.iscoroutinefunction(callback):
            await callback(*args)
        else:
            callback(*args)

    def _count_generator_usage(self, results: List[Dict]) -> Dict[str, int]:
        """Count generator usage statistics."""
        usage = {}
        for result in results:
            generator = result.get("generator", "unknown")
            usage[generator] = usage.get(generator, 0) + 1
        return usage

    def _count_visualizer_usage(self, results: List[Dict]) -> Dict[str, int]:
        """Count visualizer usage statistics."""
        usage = {}
        for result in results:
            visualizer = result.get("visualizer", "none")
            usage[visualizer] = usage.get(visualizer, 0) + 1
        return usage

    def _summarize_errors(self, errors: List[Dict]) -> Dict[str, Any]:
        """Summarize errors by type."""
        error_types = {}
        for error in errors:
            error_type = error.get("error_type", "Unknown")
            if error_type not in error_types:
                error_types[error_type] = []
            error_types[error_type].append(
                {
                    "theorem": error["theorem"],
                    "file": error["file"],
                    "message": error.get("error", ""),
                }
            )

        return {
            "total_errors": len(errors),
            "by_type": error_types,
            "most_common": (
                max(error_types.items(), key=lambda x: len(x[1]))[0]
                if error_types
                else None
            ),
        }

    def process_single_file(
        self, file_path: Path, output_dir: Path, options: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """Process a single file synchronously.

        Args:
            file_path: Path to Lean file
            output_dir: Output directory
            options: Processing options

        Returns:
            Processing results
        """
        # Use asyncio.run for synchronous interface
        from ..batch.project_scanner import ProjectScanner

        scanner = ProjectScanner()

        # Create minimal project data for single file
        project_data = {
            "process_order": [str(file_path)],
            "file_theorems": {str(file_path): []},  # Will be populated by scanner
        }

        # Extract theorems from file
        theorems = scanner._extract_theorem_names(file_path)
        project_data["file_theorems"][str(file_path)] = theorems

        # Process using async method
        return asyncio.run(self.process_project(project_data, output_dir, options))
