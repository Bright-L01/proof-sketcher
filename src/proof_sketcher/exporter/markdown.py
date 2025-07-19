"""Markdown exporter for generating GitHub-compatible documentation.

Features:
- GitHub-flavored markdown with collapsible sections
- Table of contents generation
- Math rendering with $ notation
- Animated GIF previews with video links
- Relative/absolute link modes
- Mermaid diagram support
"""

import logging
import re
from pathlib import Path

from ..generator.models import ProofSketch
from .models import BaseExporter as BaseExporterImpl
from .models import (
    ExportContext,
    ExportFormat,
    ExportOptions,
    ExportResult,
    TemplateContext,
    TemplateType,
)
from .models import TemplateContext as TemplateManager


class MarkdownExporter(BaseExporterImpl):
    """Exporter for GitHub-flavored Markdown format.

    Supports:
    - Collapsible details sections
    - Math rendering with $ notation
    - Table of contents with anchors
    - Video embedding with GIF previews
    - Relative/absolute link modes
    """

    def __init__(
        self,
        options: ExportOptions | None = None,
        template_manager: TemplateManager | None = None,
    ):
        """Initialize Markdown exporter.

        Args:
            options: Export options
            template_manager: Template manager
        """
        super().__init__(ExportFormat.MARKDOWN, options, template_manager)
        self.logger = logging.getLogger(__name__)

        # GitHub-flavored markdown settings
        self._use_github_features = getattr(options, "github_features", True)
        self._link_mode = getattr(
            options, "link_mode", "relative"
        )  # 'relative' or 'absolute'
        self._generate_toc = getattr(options, "generate_toc", True)
        self._use_collapsible = getattr(options, "use_collapsible", True)
        self._math_notation = getattr(
            options, "math_notation", "dollars"
        )  # 'dollars' or 'latex'

    def _export_sketch(self, sketch: ProofSketch, context: ExportContext) -> list[Path]:
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

        # Create template context with GitHub features
        template_context = self._create_template_context_github(sketch, context)

        # Render markdown template
        markdown_content = self.template_manager.render_template(
            ExportFormat.MARKDOWN, TemplateType.THEOREM, template_context
        )

        # Write output file
        output_file.write_text(markdown_content, encoding="utf-8")
        created_files.append(output_file)

        self.logger.info(f"Exported {sketch.theorem_name} to {output_file}")

        return created_files

    def _create_index(
        self, sketches: list[ProofSketch], context: ExportContext
    ) -> Path | None:
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
                "statement": "",  # ProofSketch doesn't have theorem_statement
                "url": context.theorem_links.get(sketch.theorem_name, "#"),
                "summary": self._truncate_text(sketch.introduction, 150),
                "step_count": len(sketch.key_steps),
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
        base_context = super()._create_template_context(sketch, context)

        # Markdown-specific settings
        # Convert to dict to modify
        context_dict = base_context
        context_dict["math_renderer"] = (
            "katex" if self.options.markdown_flavor == "github" else "mathjax"
        )

        # Format animation path as relative link
        if sketch.theorem_name in context.animations:
            animation_path = context.animations[sketch.theorem_name]
            # Make path relative to output directory
            try:
                rel_path = animation_path.relative_to(self.options.output_dir)
                context_dict["animation_path"] = str(rel_path)
            except ValueError:
                # If not relative, use absolute path
                context_dict["animation_path"] = str(animation_path)

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

        # Add navigation to context
        if "custom_metadata" not in context_dict:
            context_dict["custom_metadata"] = {}
        context_dict["custom_metadata"]["navigation"] = " | ".join(nav_links)

        return context_dict

    def _create_template_context_github(
        self, sketch: ProofSketch, context: ExportContext
    ) -> TemplateContext:
        """Create template context with GitHub-specific features.

        Args:
            sketch: Proof sketch
            context: Export context

        Returns:
            Enhanced template context
        """
        base_context = self._create_template_context(sketch, context)

        # Add GitHub-specific features
        base_context["github_features"] = {
            "use_collapsible": self._use_collapsible,
            "math_notation": self._math_notation,
            "mermaid_diagrams": True,
            "task_lists": True,
            "tables": True,
            "link_mode": self._link_mode,
        }

        # Process animation for GitHub display
        if sketch.theorem_name in context.animations:
            animation_assets = self._process_animation_for_github(
                context.animations[sketch.theorem_name], sketch.theorem_name
            )
            base_context["animation_github"] = animation_assets

        # Generate theorem TOC for current file
        base_context["theorem_toc"] = self._generate_theorem_toc(sketch)

        # Add collapsible sections data
        if self._use_collapsible:
            base_context["collapsible_sections"] = self._create_collapsible_sections(
                sketch
            )

        # Convert math notation if needed
        if self._math_notation == "dollars":
            base_context = self._convert_math_to_dollars(base_context)

        return base_context

    def _process_animation_for_github(
        self, animation_path: Path, theorem_name: str
    ) -> dict:
        """Process animation for GitHub markdown display.

        Args:
            animation_path: Path to animation file
            theorem_name: Theorem name

        Returns:
            Dictionary with animation display options
        """
        assets = {
            "video_url": self._format_link(animation_path),
            "has_gif": False,
            "gif_url": None,
            "poster_url": None,
        }

        # Look for GIF version
        gif_path = animation_path.with_suffix(".gif")
        if gif_path.exists():
            assets["has_gif"] = True
            assets["gif_url"] = self._format_link(gif_path)

        # Look for poster frame
        poster_path = animation_path.parent / f"{animation_path.stem}_poster.jpg"
        if poster_path.exists():
            assets["poster_url"] = self._format_link(poster_path)

        return assets

    def _format_link(self, path: Path) -> str:
        """Format link according to link mode.

        Args:
            path: File path

        Returns:
            Formatted link
        """
        if self._link_mode == "absolute":
            return str(path.absolute())
        else:
            try:
                return str(path.relative_to(self.options.output_dir))
            except ValueError:
                return str(path)

    def _generate_theorem_toc(self, sketch: ProofSketch) -> list[dict]:
        """Generate table of contents for current theorem.

        Args:
            sketch: Proof sketch

        Returns:
            List of TOC entries
        """
        toc_entries = []

        # Add main sections
        toc_entries.append({"title": "Statement", "anchor": "#statement", "level": 2})

        if sketch.introduction:
            toc_entries.append(
                {"title": "Introduction", "anchor": "#introduction", "level": 2}
            )

        if sketch.key_steps:
            toc_entries.append(
                {"title": "Proof Steps", "anchor": "#proof-steps", "level": 2}
            )

            # Add individual steps
            for i, step in enumerate(sketch.key_steps, 1):
                step_title = f"Step {i}: {step.description[:50]}..."
                toc_entries.append(
                    {"title": step_title, "anchor": f"#step-{i}", "level": 3}
                )

        if sketch.conclusion:
            toc_entries.append(
                {"title": "Conclusion", "anchor": "#conclusion", "level": 2}
            )

        return toc_entries

    def _create_collapsible_sections(self, sketch: ProofSketch) -> dict:
        """Create collapsible sections for GitHub.

        Args:
            sketch: Proof sketch

        Returns:
            Dictionary of collapsible section configurations
        """
        sections = {}

        # Make proof steps collapsible if many steps
        if len(sketch.key_steps) > 3:
            sections["proof_steps"] = {
                "summary": f"Proof Steps ({len(sketch.key_steps)} steps)",
                "open": False,
            }

        # Make detailed explanations collapsible
        if len(sketch.introduction) > 500:
            sections["detailed_explanation"] = {
                "summary": "Detailed Explanation",
                "open": False,
            }

        return sections

    def _convert_math_to_dollars(self, context: TemplateContext) -> TemplateContext:
        """Convert LaTeX math notation to GitHub-compatible dollar notation.

        Args:
            context: Template context

        Returns:
            Updated context with converted math
        """

        def convert_latex_to_dollars(text: str) -> str:
            if not isinstance(text, str):
                return text

            # Convert \\[ ... \\] to $$ ... $$
            text = re.sub(r"\\\[(.+?)\\\]", r"$$\1$$", text, flags=re.DOTALL)

            # Convert \\( ... \\) to $ ... $
            text = re.sub(r"\\\((.+?)\\\)", r"$\1$", text, flags=re.DOTALL)

            # Convert \begin{equation} ... \end{equation} to $$ ... $$
            text = re.sub(
                r"\\begin\{equation\}(.+?)\\end\{equation\}",
                r"$$\1$$",
                text,
                flags=re.DOTALL,
            )

            return text

        # Apply conversion to text fields
        for key, value in context.items():
            if isinstance(value, str):
                context[key] = convert_latex_to_dollars(value)
            elif isinstance(value, dict):
                for subkey, subvalue in value.items():
                    if isinstance(subvalue, str):
                        value[subkey] = convert_latex_to_dollars(subvalue)

        return context

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
        self, sketches: list[ProofSketch], context: ExportContext | None = None
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

        # Generate table of contents file if enabled
        if result.success and self._generate_toc:
            try:
                toc_file = self._generate_enhanced_toc(
                    sketches, context or self._create_default_context(sketches)
                )
                if toc_file:
                    result.files_created.append(toc_file)
            except Exception as e:
                result.warnings.append(f"Failed to generate TOC: {e}")

        # Generate animation previews as GIF
        if result.success and context and context.animations:
            try:
                preview_files = self._generate_animation_previews(sketches, context)
                result.files_created.extend(preview_files)
            except Exception as e:
                result.warnings.append(f"Failed to generate animation previews: {e}")

        return result

    def _generate_toc(
        self, sketches: list[ProofSketch], context: ExportContext
    ) -> Path | None:
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

        # ProofSketch doesn't have dependencies, so all theorems are root theorems
        root_theorems = sketches[:]

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

    def _generate_enhanced_toc(
        self, sketches: list[ProofSketch], context: ExportContext
    ) -> Path | None:
        """Generate enhanced table of contents with GitHub features.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Path to enhanced TOC file
        """
        toc_file = self.options.output_dir / "TOC.md"

        toc_content = []

        # Header with badges and stats
        toc_content.extend(
            [
                "# 📚 Table of Contents",
                "",
                f"![Theorems](https://img.shields.io/badge/theorems-{len(sketches)}-blue)",
                f"![Generated](https://img.shields.io/badge/generated-{context.timestamp.strftime('%Y%m%d') if context.timestamp else 'unknown'}-green)",
                "",
                f"> **{len(sketches)} theorems** documented with interactive proofs and animations",
                "",
            ]
        )

        # Quick navigation
        toc_content.extend(
            [
                "## 🧭 Quick Navigation",
                "",
                "- [📖 All Theorems](#-all-theorems)",
                (
                    "- [🎥 Animated Proofs](#-animated-proofs)"
                    if context.animations
                    else ""
                ),
                "- [🔤 Alphabetical Index](#-alphabetical-index)",
                "- [📊 Statistics](#-statistics)",
                "",
            ]
        )

        # All theorems section
        toc_content.extend(["## 📖 All Theorems", ""])

        # Group by difficulty or category
        difficulty_groups = self._group_by_difficulty(sketches)

        for difficulty, theorems in difficulty_groups.items():
            if theorems:
                toc_content.extend(
                    [f"### {difficulty.title()} Level ({len(theorems)} theorems)", ""]
                )

                for theorem in sorted(theorems, key=lambda x: x.theorem_name):
                    url = self._format_link(Path(f"{theorem.theorem_name}.md"))
                    step_count = len(theorem.key_steps)
                    has_animation = theorem.theorem_name in context.animations

                    # Create theorem entry with metadata
                    entry_parts = [f"- **[{theorem.theorem_name}]({url})**"]

                    if step_count > 0:
                        entry_parts.append(f"📝 {step_count} steps")
                    if has_animation:
                        entry_parts.append("🎥 animated")

                    if len(entry_parts) > 1:
                        entry_parts[0] += " — " + " · ".join(entry_parts[1:])

                    if theorem.introduction:
                        entry_parts[0] += (
                            f"  \n  _{self._truncate_text(theorem.introduction, 100)}_"
                        )

                    toc_content.append(entry_parts[0])

                toc_content.append("")

        # Animated proofs section
        if context.animations:
            animated_theorems = [
                s for s in sketches if s.theorem_name in context.animations
            ]
            toc_content.extend(
                [
                    "## 🎥 Animated Proofs",
                    "",
                    f"**{len(animated_theorems)} theorems** have interactive animations:",
                    "",
                ]
            )

            for theorem in sorted(animated_theorems, key=lambda x: x.theorem_name):
                url = self._format_link(Path(f"{theorem.theorem_name}.md"))
                gif_path = context.animations[theorem.theorem_name].with_suffix(".gif")

                if gif_path.exists():
                    gif_url = self._format_link(gif_path)
                    toc_content.extend(
                        [
                            f"### [{theorem.theorem_name}]({url})",
                            f"![{theorem.theorem_name} Animation]({gif_url})",
                            "",
                        ]
                    )
                else:
                    toc_content.append(f"- **[{theorem.theorem_name}]({url})** 🎥")

            toc_content.append("")

        # Alphabetical index
        toc_content.extend(["## 🔤 Alphabetical Index", ""])

        # Group by first letter
        alpha_groups = {}
        for theorem in sketches:
            first_letter = theorem.theorem_name[0].upper()
            if first_letter not in alpha_groups:
                alpha_groups[first_letter] = []
            alpha_groups[first_letter].append(theorem)

        for letter in sorted(alpha_groups.keys()):
            theorems = sorted(alpha_groups[letter], key=lambda x: x.theorem_name)

            # Create collapsible section for each letter
            if self._use_collapsible:
                toc_content.extend(
                    [
                        "<details>",
                        f"<summary><strong>{letter}</strong> ({len(theorems)} theorems)</summary>",
                        "",
                    ]
                )
            else:
                toc_content.extend([f"### {letter} ({len(theorems)} theorems)", ""])

            for theorem in theorems:
                url = self._format_link(Path(f"{theorem.theorem_name}.md"))
                toc_content.append(f"- [{theorem.theorem_name}]({url})")

            if self._use_collapsible:
                toc_content.extend(["", "</details>", ""])
            else:
                toc_content.append("")

        # Statistics section
        toc_content.extend(
            [
                "## 📊 Statistics",
                "",
                "| Metric | Value |",
                "|--------|-------|",
                f"| Total Theorems | {len(sketches)} |",
                f"| With Animations | {len(context.animations) if context.animations else 0} |",
                f"| Total Proof Steps | {sum(len(s.key_steps) for s in sketches)} |",
                f"| Average Steps per Theorem | {sum(len(s.key_steps) for s in sketches) / len(sketches):.1f} |",
            ]
        )

        # Add difficulty breakdown
        for difficulty, theorems in difficulty_groups.items():
            if theorems:
                toc_content.append(f"| {difficulty.title()} Level | {len(theorems)} |")

        toc_content.extend(
            [
                "",
                "---",
                "",
                f"*Generated on {context.timestamp.isoformat() if context.timestamp else 'unknown date'}*",
            ]
        )

        toc_file.write_text("\n".join(toc_content), encoding="utf-8")
        self.logger.info(f"Generated enhanced TOC: {toc_file}")

        return toc_file

    def _group_by_difficulty(
        self, sketches: list[ProofSketch]
    ) -> dict[str, list[ProofSketch]]:
        """Group theorems by difficulty level.

        Args:
            sketches: List of proof sketches

        Returns:
            Dictionary mapping difficulty levels to theorem lists
        """
        groups = {"beginner": [], "intermediate": [], "advanced": [], "expert": []}

        for sketch in sketches:
            difficulty = getattr(sketch, "difficulty_level", "intermediate")
            if difficulty in groups:
                groups[difficulty].append(sketch)
            else:
                groups["intermediate"].append(sketch)  # Default fallback

        return groups

    def _generate_animation_previews(
        self, sketches: list[ProofSketch], context: ExportContext
    ) -> list[Path]:
        """Generate animation preview files for GitHub.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            List of created preview files
        """
        preview_files = []

        if not context.animations:
            return preview_files

        preview_dir = self.options.output_dir / "previews"
        preview_dir.mkdir(exist_ok=True)

        # Create animations index
        animations_md = preview_dir / "animations.md"
        content = [
            "# 🎥 Animation Previews",
            "",
            "Click on any animation to view the full proof video:",
            "",
        ]

        for sketch in sketches:
            if sketch.theorem_name in context.animations:
                animation_path = context.animations[sketch.theorem_name]
                gif_path = animation_path.with_suffix(".gif")

                theorem_url = self._format_link(Path(f"../{sketch.theorem_name}.md"))

                content.extend([f"## [{sketch.theorem_name}]({theorem_url})", ""])

                if gif_path.exists():
                    gif_url = self._format_link(gif_path)
                    video_url = self._format_link(animation_path)

                    content.extend(
                        [
                            f"[![{sketch.theorem_name}]({gif_url})]({video_url})",
                            "",
                            f"*Click to view full video: [{animation_path.name}]({video_url})*",
                            "",
                        ]
                    )
                else:
                    video_url = self._format_link(animation_path)
                    content.extend([f"[📹 View Animation]({video_url})", ""])

        animations_md.write_text("\n".join(content), encoding="utf-8")
        preview_files.append(animations_md)

        return preview_files
