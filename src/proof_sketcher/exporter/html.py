"""HTML exporter for generating web documentation."""

import json
import logging
import shutil
from pathlib import Path
from typing import List, Optional

from ..generator.models import ProofSketch
from .base import BaseExporterImpl
from .models import (ExportContext, ExportFormat, ExportOptions, ExportResult,
                     TemplateContext, TemplateType)
from .template_manager import TemplateManager


class HTMLExporter(BaseExporterImpl):
    """Exporter for HTML format with doc-gen4 compatibility."""

    def __init__(
        self,
        options: Optional[ExportOptions] = None,
        template_manager: Optional[TemplateManager] = None,
    ):
        """Initialize HTML exporter.

        Args:
            options: Export options
            template_manager: Template manager
        """
        super().__init__(ExportFormat.HTML, options, template_manager)
        self.logger = logging.getLogger(__name__)

    def _export_sketch(self, sketch: ProofSketch, context: ExportContext) -> List[Path]:
        """Export a single proof sketch to HTML.

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            List of created files
        """
        created_files = []

        # Generate output filename
        output_file = self._generate_filename(sketch.theorem_name, "html")

        # Create template context
        template_context = self._create_template_context(sketch, context)

        # Check for animation
        if context.include_animations and sketch.theorem_name in context.animations:
            animation_path = context.animations[sketch.theorem_name]

            # Copy animation to output directory
            if animation_path.exists():
                animation_dest = self._copy_animation(
                    animation_path, sketch.theorem_name
                )
                template_context["animation_path"] = animation_dest.name
                created_files.append(animation_dest)

        # Render theorem template
        html_content = self.template_manager.render_template(
            ExportFormat.HTML, TemplateType.THEOREM, template_context.dict()
        )

        # Write output file
        output_file.write_text(html_content, encoding="utf-8")
        created_files.append(output_file)

        self.logger.info(f"Exported {sketch.theorem_name} to {output_file}")

        return created_files

    def _create_index(
        self, sketches: List[ProofSketch], context: ExportContext
    ) -> Optional[Path]:
        """Create an index HTML file.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Path to index file
        """
        index_file = self.options.output_dir / "index.html"

        # Prepare theorem list for index
        theorem_list = []
        for sketch in sketches:
            theorem_data = {
                "name": sketch.theorem_name,
                "statement": sketch.theorem_statement,
                "url": context.theorem_links.get(sketch.theorem_name, "#"),
                "summary": (
                    sketch.explanation[:200] + "..."
                    if len(sketch.explanation) > 200
                    else sketch.explanation
                ),
                "step_count": len(sketch.steps),
                "has_animation": sketch.theorem_name in context.animations,
            }
            theorem_list.append(theorem_data)

        # Sort by name
        theorem_list.sort(key=lambda x: x["name"])

        # Create index context
        index_context = {
            "project_name": context.project_name,
            "theorem_count": len(sketches),
            "theorems": theorem_list,
            "timestamp": (
                context.timestamp.isoformat() if context.include_timestamps else None
            ),
            "has_animations": bool(context.animations),
            "author": context.author,
            "version": context.version,
        }

        # Render index template
        index_html = self.template_manager.render_template(
            ExportFormat.HTML, TemplateType.INDEX, index_context
        )

        # Write index file
        index_file.write_text(index_html, encoding="utf-8")

        self.logger.info(f"Created index at {index_file}")

        return index_file

    def export_multiple(
        self, sketches: List[ProofSketch], context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export multiple sketches with additional HTML features.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Export result
        """
        # Call parent implementation
        result = super().export_multiple(sketches, context)

        # Copy static assets
        if result.success and self.options.create_subdirs:
            try:
                asset_files = self._copy_assets()
                result.files_created.extend(asset_files)
            except Exception as e:
                result.warnings.append(f"Failed to copy assets: {e}")

        # Generate search index
        if result.success and len(sketches) > 5:
            try:
                search_file = self._generate_search_index(sketches)
                if search_file:
                    result.files_created.append(search_file)
            except Exception as e:
                result.warnings.append(f"Failed to generate search index: {e}")

        return result

    def _create_template_context(
        self, sketch: ProofSketch, context: ExportContext
    ) -> TemplateContext:
        """Create template context with HTML-specific additions.

        Args:
            sketch: Proof sketch
            context: Export context

        Returns:
            Template context
        """
        base_context = super()._create_context(sketch)

        # Add HTML-specific fields
        base_context.syntax_theme = (
            self.options.syntax_highlighting and "monokai" or "none"
        )
        base_context.math_renderer = "katex"  # or "mathjax"

        # Add navigation
        all_names = [s.theorem_name for s in context.sketches]
        current_index = (
            all_names.index(sketch.theorem_name)
            if sketch.theorem_name in all_names
            else -1
        )

        if current_index > 0:
            prev_sketch = context.sketches[current_index - 1]
            base_context.prev_theorem = {
                "name": prev_sketch.theorem_name,
                "url": context.theorem_links.get(prev_sketch.theorem_name),
            }

        if 0 <= current_index < len(all_names) - 1:
            next_sketch = context.sketches[current_index + 1]
            base_context.next_theorem = {
                "name": next_sketch.theorem_name,
                "url": context.theorem_links.get(next_sketch.theorem_name),
            }

        base_context.index_url = "index.html"

        # Add dependencies with links
        if self.options.generate_links:
            base_context.dependencies = [
                {"name": dep, "url": context.theorem_links.get(dep, f"#{dep}")}
                for dep in sketch.dependencies
            ]

        return base_context

    def _copy_animation(self, source: Path, theorem_name: str) -> Path:
        """Copy animation file to output directory.

        Args:
            source: Source animation file
            theorem_name: Theorem name for naming

        Returns:
            Destination path
        """
        animations_dir = self.options.output_dir / "animations"
        animations_dir.mkdir(exist_ok=True)

        # Generate unique filename
        extension = source.suffix
        dest_filename = f"{self._sanitize_filename(theorem_name)}_animation{extension}"
        dest_path = animations_dir / dest_filename

        # Copy file
        shutil.copy2(source, dest_path)

        return dest_path

    def _generate_search_index(self, sketches: List[ProofSketch]) -> Optional[Path]:
        """Generate search index for client-side search.

        Args:
            sketches: List of proof sketches

        Returns:
            Path to search index file
        """
        search_data = []

        for sketch in sketches:
            # Create search entry
            entry = {
                "id": sketch.theorem_name,
                "title": sketch.theorem_name,
                "statement": sketch.theorem_statement,
                "content": sketch.explanation,
                "url": self._get_output_url(sketch),
                "keywords": sketch.key_insights,
            }

            # Add step descriptions to searchable content
            step_text = " ".join(step.description for step in sketch.steps)
            entry["content"] += " " + step_text

            search_data.append(entry)

        # Write search index
        search_file = self.options.output_dir / "search-index.json"
        search_file.write_text(
            json.dumps(search_data, indent=2, ensure_ascii=False), encoding="utf-8"
        )

        return search_file

    def _copy_assets(self) -> List[Path]:
        """Copy HTML-specific assets.

        Returns:
            List of copied files
        """
        copied = super()._copy_assets()

        # Copy additional HTML resources
        resources = [
            ("css/doc-gen4.css", "css/doc-gen4.css"),
            ("css/theorem.css", "css/theorem.css"),
            ("js/navigation.js", "js/navigation.js"),
            ("js/search.js", "js/search.js"),
            ("js/katex-auto-render.js", "js/katex-auto-render.js"),
        ]

        for src_rel, dst_rel in resources:
            src = self.template_manager.template_dir / "html" / "assets" / src_rel
            if src.exists():
                dst = self.options.output_dir / dst_rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
                copied.append(dst)

        return copied
