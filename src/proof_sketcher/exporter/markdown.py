"""Markdown exporter for generating GitHub-compatible documentation."""

import logging
from pathlib import Path
from typing import List, Optional

from ..generator.models import ProofSketch
from .base import BaseExporterImpl
from .models import (ExportContext, ExportFormat, ExportOptions, ExportResult,
                     TemplateContext, TemplateType)
from .template_manager import TemplateManager


class MarkdownExporter(BaseExporterImpl):
    """Exporter for Markdown format."""

    def __init__(
        self,
        options: Optional[ExportOptions] = None,
        template_manager: Optional[TemplateManager] = None,
    ):
        """Initialize Markdown exporter.

        Args:
            options: Export options
            template_manager: Template manager
        """
        super().__init__(ExportFormat.MARKDOWN, options, template_manager)
        self.logger = logging.getLogger(__name__)

    def _export_sketch(self, sketch: ProofSketch, context: ExportContext) -> List[Path]:
        """Export a single proof sketch to Markdown.

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            List of created files
        """
        created_files = []

        # Generate output filename
        output_file = self._generate_filename(sketch.theorem_name, "md")

        # Create template context
        template_context = self._create_template_context(sketch, context)

        # Render markdown template
        markdown_content = self.template_manager.render_template(
            ExportFormat.MARKDOWN, TemplateType.THEOREM, template_context.dict()
        )

        # Write output file
        output_file.write_text(markdown_content, encoding="utf-8")
        created_files.append(output_file)

        self.logger.info(f"Exported {sketch.theorem_name} to {output_file}")

        return created_files

    def _create_index(
        self, sketches: List[ProofSketch], context: ExportContext
    ) -> Optional[Path]:
        """Create an index Markdown file (README.md).

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Path to index file
        """
        index_file = self.options.output_dir / "README.md"

        # Prepare theorem list
        theorem_list = []
        for sketch in sketches:
            theorem_data = {
                "name": sketch.theorem_name,
                "statement": sketch.theorem_statement,
                "url": context.theorem_links.get(sketch.theorem_name, "#"),
                "summary": self._truncate_text(sketch.explanation, 150),
                "step_count": len(sketch.steps),
                "has_animation": sketch.theorem_name in context.animations,
            }
            theorem_list.append(theorem_data)

        # Group by first letter for TOC
        grouped = {}
        for theorem in sorted(theorem_list, key=lambda x: x["name"]):
            first_letter = theorem["name"][0].upper()
            if first_letter not in grouped:
                grouped[first_letter] = []
            grouped[first_letter].append(theorem)

        # Create index context
        index_context = {
            "project_name": context.project_name,
            "theorem_count": len(sketches),
            "theorems": theorem_list,
            "grouped_theorems": grouped,
            "timestamp": (
                context.timestamp.isoformat() if context.include_timestamps else None
            ),
            "has_animations": bool(context.animations),
            "author": context.author,
            "version": context.version,
        }

        # Render index template
        index_md = self.template_manager.render_template(
            ExportFormat.MARKDOWN, TemplateType.INDEX, index_context
        )

        # Write index file
        index_file.write_text(index_md, encoding="utf-8")

        self.logger.info(f"Created index at {index_file}")

        return index_file

    def _create_template_context(
        self, sketch: ProofSketch, context: ExportContext
    ) -> TemplateContext:
        """Create template context with Markdown-specific additions.

        Args:
            sketch: Proof sketch
            context: Export context

        Returns:
            Template context
        """
        base_context = super()._create_context(sketch)

        # Markdown-specific settings
        base_context.math_renderer = (
            "katex" if self.options.markdown_flavor == "github" else "mathjax"
        )

        # Format animation path as relative link
        if sketch.theorem_name in context.animations:
            animation_path = context.animations[sketch.theorem_name]
            # Make path relative to output directory
            try:
                rel_path = animation_path.relative_to(self.options.output_dir)
                base_context.animation_path = str(rel_path)
            except ValueError:
                # If not relative, use absolute path
                base_context.animation_path = str(animation_path)

        # Add navigation links as Markdown
        all_names = [s.theorem_name for s in context.sketches]
        current_index = (
            all_names.index(sketch.theorem_name)
            if sketch.theorem_name in all_names
            else -1
        )

        nav_links = []
        if current_index > 0:
            prev_sketch = context.sketches[current_index - 1]
            prev_url = context.theorem_links.get(prev_sketch.theorem_name, "#")
            nav_links.append(f"[← {prev_sketch.theorem_name}]({prev_url})")

        nav_links.append("[Index](README.md)")

        if 0 <= current_index < len(all_names) - 1:
            next_sketch = context.sketches[current_index + 1]
            next_url = context.theorem_links.get(next_sketch.theorem_name, "#")
            nav_links.append(f"[{next_sketch.theorem_name} →]({next_url})")

        base_context.custom_metadata["navigation"] = " | ".join(nav_links)

        return base_context

    def _truncate_text(self, text: str, max_length: int) -> str:
        """Truncate text to maximum length with ellipsis.

        Args:
            text: Text to truncate
            max_length: Maximum length

        Returns:
            Truncated text
        """
        if len(text) <= max_length:
            return text
        return text[: max_length - 3] + "..."

    def export_multiple(
        self, sketches: List[ProofSketch], context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export multiple sketches with Markdown-specific features.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Export result
        """
        # Call parent implementation
        result = super().export_multiple(sketches, context)

        # Generate table of contents file
        if result.success and len(sketches) > 10:
            try:
                toc_file = self._generate_toc(
                    sketches, context or self._create_default_context(sketches)
                )
                if toc_file:
                    result.files_created.append(toc_file)
            except Exception as e:
                result.warnings.append(f"Failed to generate TOC: {e}")

        return result

    def _generate_toc(
        self, sketches: List[ProofSketch], context: ExportContext
    ) -> Optional[Path]:
        """Generate table of contents file.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Path to TOC file
        """
        toc_file = self.options.output_dir / "TOC.md"

        toc_content = ["# Table of Contents\n"]
        toc_content.append(f"Total theorems: {len(sketches)}\n")

        # Group by dependencies
        root_theorems = []
        dependent_theorems = {}

        for sketch in sketches:
            has_deps = False
            for dep in sketch.dependencies:
                if any(s.theorem_name == dep for s in sketches):
                    has_deps = True
                    if dep not in dependent_theorems:
                        dependent_theorems[dep] = []
                    dependent_theorems[dep].append(sketch)

            if not has_deps:
                root_theorems.append(sketch)

        # Write root theorems
        if root_theorems:
            toc_content.append("\n## Foundation Theorems\n")
            for theorem in sorted(root_theorems, key=lambda x: x.theorem_name):
                url = context.theorem_links.get(theorem.theorem_name, "#")
                toc_content.append(f"- [{theorem.theorem_name}]({url})")

                # List dependents
                if theorem.theorem_name in dependent_theorems:
                    for dep in dependent_theorems[theorem.theorem_name]:
                        dep_url = context.theorem_links.get(dep.theorem_name, "#")
                        toc_content.append(f"  - [{dep.theorem_name}]({dep_url})")

        # Write orphaned theorems
        all_listed = set()
        for t in root_theorems:
            all_listed.add(t.theorem_name)
            if t.theorem_name in dependent_theorems:
                for d in dependent_theorems[t.theorem_name]:
                    all_listed.add(d.theorem_name)

        orphaned = [s for s in sketches if s.theorem_name not in all_listed]
        if orphaned:
            toc_content.append("\n## Other Theorems\n")
            for theorem in sorted(orphaned, key=lambda x: x.theorem_name):
                url = context.theorem_links.get(theorem.theorem_name, "#")
                toc_content.append(f"- [{theorem.theorem_name}]({url})")

        toc_file.write_text("\n".join(toc_content), encoding="utf-8")

        return toc_file
