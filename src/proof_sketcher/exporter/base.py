"""Base exporter implementation with common functionality."""

import logging
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional, Set

from ..generator.models import ProofSketch
from .models import ExportContext, ExportFormat, ExportOptions, ExportResult
from .template_manager import TemplateManager


class BaseExporterImpl:
    """Base implementation with common functionality for exporters."""

    def __init__(
        self,
        format: ExportFormat,
        options: Optional[ExportOptions] = None,
        template_manager: Optional[TemplateManager] = None,
    ):
        """Initialize base exporter.

        Args:
            format: Export format
            options: Export options
            template_manager: Template manager instance
        """
        self.format = format
        self.options = options or ExportOptions()
        self.template_manager = template_manager or TemplateManager()
        self.logger = logging.getLogger(f"{__name__}.{format.value}")

        # Ensure output directory exists
        self._ensure_output_dir()

    def export_single(
        self, sketch: ProofSketch, context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export a single proof sketch.

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            Export result
        """
        start_time = time.time()
        context = context or self._create_default_context([sketch])

        try:
            # Export the sketch
            files = self._export_sketch(sketch, context)

            return ExportResult(
                success=True,
                format=self.format,
                output_path=self.options.output_dir,
                files_created=files,
                export_time=time.time() - start_time,
            )

        except Exception as e:
            self.logger.error(f"Failed to export {sketch.theorem_name}: {e}")
            return ExportResult(
                success=False,
                format=self.format,
                output_path=self.options.output_dir,
                errors=[str(e)],
                export_time=time.time() - start_time,
            )

    def export_multiple(
        self, sketches: List[ProofSketch], context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export multiple proof sketches.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Export result
        """
        start_time = time.time()
        context = context or self._create_default_context(sketches)

        all_files = []
        all_warnings = []
        all_errors = []

        if self.options.parallel_export and len(sketches) > 1:
            # Parallel export
            with ThreadPoolExecutor(max_workers=4) as executor:
                futures = {
                    executor.submit(self._export_sketch, sketch, context): sketch
                    for sketch in sketches
                }

                for future in as_completed(futures):
                    sketch = futures[future]
                    try:
                        files = future.result()
                        all_files.extend(files)
                    except Exception as e:
                        error_msg = f"Failed to export {sketch.theorem_name}: {e}"
                        self.logger.error(error_msg)
                        all_errors.append(error_msg)
        else:
            # Sequential export
            for sketch in sketches:
                try:
                    files = self._export_sketch(sketch, context)
                    all_files.extend(files)
                except Exception as e:
                    error_msg = f"Failed to export {sketch.theorem_name}: {e}"
                    self.logger.error(error_msg)
                    all_errors.append(error_msg)

        # Create index if requested
        if self.options.create_index and len(sketches) > 1:
            try:
                index_file = self._create_index(sketches, context)
                if index_file:
                    all_files.append(index_file)
            except Exception as e:
                all_warnings.append(f"Failed to create index: {e}")

        return ExportResult(
            success=len(all_errors) == 0,
            format=self.format,
            output_path=self.options.output_dir,
            files_created=all_files,
            warnings=all_warnings,
            errors=all_errors,
            export_time=time.time() - start_time,
        )

    def _export_sketch(self, sketch: ProofSketch, context: ExportContext) -> List[Path]:
        """Export a single sketch (to be implemented by subclasses).

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            List of created files
        """
        raise NotImplementedError("Subclasses must implement _export_sketch")

    def _create_index(
        self, sketches: List[ProofSketch], context: ExportContext
    ) -> Optional[Path]:
        """Create an index file (to be implemented by subclasses).

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Path to index file if created
        """
        # Default implementation does nothing
        return None

    def _ensure_output_dir(self) -> None:
        """Ensure output directory exists."""
        self.options.output_dir.mkdir(parents=True, exist_ok=True)

        # Create subdirectories if needed
        if self.options.create_subdirs:
            for subdir in ["css", "js", "images", "animations"]:
                (self.options.output_dir / subdir).mkdir(exist_ok=True)

    def _create_default_context(self, sketches: List[ProofSketch]) -> ExportContext:
        """Create default export context.

        Args:
            sketches: List of proof sketches

        Returns:
            Export context
        """
        # Build theorem links
        theorem_links = {
            sketch.theorem_name: self._get_output_url(sketch) for sketch in sketches
        }

        # Build dependency graph
        dependency_graph = self._build_dependency_graph(sketches)

        return ExportContext(
            format=self.format,
            output_dir=self.options.output_dir,
            sketches=sketches,
            theorem_links=theorem_links,
            dependency_graph=dependency_graph,
            include_animations=self.options.include_animations,
            include_index=self.options.create_index,
            include_timestamps=self.options.include_timestamps,
            create_subdirs=self.options.create_subdirs,
        )

    def _get_output_url(self, sketch: ProofSketch) -> str:
        """Get output URL for a sketch.

        Args:
            sketch: Proof sketch

        Returns:
            Relative URL to output file
        """
        extension = self._get_file_extension()
        filename = self.options.filename_pattern.format(
            theorem_name=sketch.theorem_name
        )
        filename = self._sanitize_filename(filename)
        return f"{filename}.{extension}"

    def _get_file_extension(self) -> str:
        """Get file extension for format."""
        extensions = {
            ExportFormat.HTML: "html",
            ExportFormat.MARKDOWN: "md",
            ExportFormat.PDF: "pdf",
            ExportFormat.JUPYTER: "ipynb",
        }
        return extensions.get(self.format, "txt")

    def _sanitize_filename(self, filename: str) -> str:
        """Sanitize filename for filesystem.

        Args:
            filename: Raw filename

        Returns:
            Sanitized filename
        """
        # Replace spaces with underscores
        filename = filename.replace(" ", "_")
        # Keep only alphanumeric, underscore, and hyphen
        return "".join(c for c in filename if c.isalnum() or c in "_-")

    def _build_dependency_graph(
        self, sketches: List[ProofSketch]
    ) -> Dict[str, Set[str]]:
        """Build dependency graph from sketches.

        Args:
            sketches: List of proof sketches

        Returns:
            Dependency graph mapping theorem names to dependencies
        """
        graph = {}

        for sketch in sketches:
            dependencies = set()

            # Extract dependencies from proof steps
            for step in sketch.steps:
                for prereq in step.prerequisites:
                    # Check if prerequisite is another theorem
                    if any(s.theorem_name == prereq for s in sketches):
                        dependencies.add(prereq)

            graph[sketch.theorem_name] = dependencies

        return graph

    def _copy_assets(self) -> List[Path]:
        """Copy static assets to output directory.

        Returns:
            List of copied files
        """
        copied_files = []

        if not self.options.create_subdirs:
            return copied_files

        # Copy CSS, JS, and other assets based on format
        asset_dirs = {
            ExportFormat.HTML: ["css", "js", "images"],
            ExportFormat.PDF: ["images"],
            ExportFormat.JUPYTER: ["images"],
        }

        for asset_dir in asset_dirs.get(self.format, []):
            src_dir = self.template_manager.get_asset_dir(self.format, asset_dir)
            if src_dir and src_dir.exists():
                dst_dir = self.options.output_dir / asset_dir
                copied = self._copy_directory(src_dir, dst_dir)
                copied_files.extend(copied)

        return copied_files

    def _copy_directory(self, src: Path, dst: Path) -> List[Path]:
        """Copy directory recursively.

        Args:
            src: Source directory
            dst: Destination directory

        Returns:
            List of copied files
        """
        import shutil

        copied = []
        dst.mkdir(parents=True, exist_ok=True)

        for item in src.iterdir():
            if item.is_file():
                dst_file = dst / item.name
                shutil.copy2(item, dst_file)
                copied.append(dst_file)
            elif item.is_dir():
                sub_copied = self._copy_directory(item, dst / item.name)
                copied.extend(sub_copied)

        return copied
