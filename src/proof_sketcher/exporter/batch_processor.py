"""Batch processor for exporting multiple theorems."""

import logging
from pathlib import Path
from typing import Dict, List

from ..generator.models import ProofSketch
from ..parser.models import TheoremInfo
from .simple_html import SimpleHTMLExporter
from .simple_markdown import SimpleMarkdownExporter


class BatchExporter:
    """Batch processor for exporting multiple theorems to various formats."""

    def __init__(self, output_dir: Path = Path("output")):
        """Initialize batch exporter.

        Args:
            output_dir: Directory to export files to
        """
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)

        self.markdown_exporter = SimpleMarkdownExporter()
        self.html_exporter = SimpleHTMLExporter()

        self.logger = logging.getLogger(__name__)

    def export_multiple(
        self,
        sketches: List[ProofSketch],
        formats: List[str] = None,
        create_index: bool = True,
    ) -> Dict[str, List[Path]]:
        """Export multiple proof sketches to various formats.

        Args:
            sketches: List of proof sketches to export
            formats: List of formats to export to ("markdown", "html")
            create_index: Whether to create an index file

        Returns:
            Dictionary mapping format names to lists of generated files
        """
        if formats is None:
            formats = ["markdown", "html"]
        results = {}

        for format_name in formats:
            if format_name == "markdown":
                results[format_name] = self._export_markdown_batch(sketches)
            elif format_name == "html":
                results[format_name] = self._export_html_batch(sketches)
            else:
                self.logger.warning(f"Unknown format: {format_name}")

        # Create index files if requested
        if create_index:
            self._create_index_files(sketches, formats)

        return results

    def _export_markdown_batch(self, sketches: List[ProofSketch]) -> List[Path]:
        """Export all sketches to markdown format."""
        markdown_dir = self.output_dir / "markdown"
        markdown_dir.mkdir(exist_ok=True)

        files = []
        for sketch in sketches:
            filename = f"{sketch.theorem_name}.md"
            output_path = markdown_dir / filename

            try:
                self.markdown_exporter.export(sketch, output_path)
                files.append(output_path)
                self.logger.info(f"Exported {sketch.theorem_name} to markdown")
            except Exception as e:
                self.logger.error(
                    f"Failed to export {sketch.theorem_name} to markdown: {e}"
                )

        return files

    def _export_html_batch(self, sketches: List[ProofSketch]) -> List[Path]:
        """Export all sketches to HTML format."""
        html_dir = self.output_dir / "html"
        html_dir.mkdir(exist_ok=True)

        files = []
        for sketch in sketches:
            filename = f"{sketch.theorem_name}.html"
            output_path = html_dir / filename

            try:
                self.html_exporter.export(sketch, output_path)
                files.append(output_path)
                self.logger.info(f"Exported {sketch.theorem_name} to HTML")
            except Exception as e:
                self.logger.error(
                    f"Failed to export {sketch.theorem_name} to HTML: {e}"
                )

        return files

    def _create_index_files(
        self, sketches: List[ProofSketch], formats: List[str]
    ) -> None:
        """Create index files for easy navigation."""
        # Create markdown index
        if "markdown" in formats:
            self._create_markdown_index(sketches)

        # Create HTML index
        if "html" in formats:
            self._create_html_index(sketches)

    def _create_markdown_index(self, sketches: List[ProofSketch]) -> None:
        """Create a markdown index file."""
        index_content = [
            "# Proof Sketcher - Theorem Index",
            "",
            "This directory contains natural language explanations of Lean 4 theorems.",
            "",
            "## Theorems",
            "",
        ]

        for sketch in sketches:
            difficulty_emoji = {
                "beginner": "🟢",
                "intermediate": "🟡",
                "advanced": "🔴",
            }.get(sketch.difficulty_level, "⚪")

            areas = ", ".join(sketch.mathematical_areas[:3])  # Limit to first 3 areas
            if len(sketch.mathematical_areas) > 3:
                areas += "..."

            index_content.append(
                f"- [{sketch.theorem_name}](markdown/{sketch.theorem_name}.md) "
                f"{difficulty_emoji} *{areas}*"
            )

        index_content.extend(
            [
                "",
                "## Legend",
                "- 🟢 Beginner",
                "- 🟡 Intermediate",
                "- 🔴 Advanced",
                "",
                f"Generated with Proof Sketcher - {len(sketches)} theorems processed",
            ]
        )

        index_path = self.output_dir / "README.md"
        index_path.write_text("\n".join(index_content), encoding="utf-8")
        self.logger.info(f"Created markdown index: {index_path}")

    def _create_html_index(self, sketches: List[ProofSketch]) -> None:
        """Create an HTML index file."""
        theorem_rows = ""
        for sketch in sketches:
            difficulty_color = {
                "beginner": "#28a745",
                "intermediate": "#ffc107",
                "advanced": "#dc3545",
            }.get(sketch.difficulty_level, "#6c757d")

            areas = ", ".join(sketch.mathematical_areas[:3])
            if len(sketch.mathematical_areas) > 3:
                areas += "..."

            theorem_rows += f"""
            <tr>
                <td><a href="html/{sketch.theorem_name}.html">{sketch.theorem_name}</a></td>
                <td><span style="color: {difficulty_color}">●</span> {sketch.difficulty_level.title()}</td>
                <td>{areas}</td>
                <td>{sketch.introduction[:100]}...</td>
            </tr>
            """

        html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Proof Sketcher - Theorem Index</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', 'Roboto', sans-serif;
            line-height: 1.6;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background-color: #fafafa;
        }}

        .header {{
            text-align: center;
            margin-bottom: 40px;
        }}

        .header h1 {{
            color: #2c3e50;
            margin-bottom: 10px;
        }}

        .header p {{
            color: #6c757d;
            font-size: 1.1em;
        }}

        .theorem-table {{
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
            overflow: hidden;
        }}

        table {{
            width: 100%;
            border-collapse: collapse;
        }}

        th, td {{
            padding: 12px;
            text-align: left;
            border-bottom: 1px solid #dee2e6;
        }}

        th {{
            background-color: #f8f9fa;
            font-weight: 600;
            color: #495057;
        }}

        tr:hover {{
            background-color: #f8f9fa;
        }}

        a {{
            color: #007bff;
            text-decoration: none;
        }}

        a:hover {{
            text-decoration: underline;
        }}

        .footer {{
            text-align: center;
            margin-top: 40px;
            padding-top: 20px;
            border-top: 1px solid #dee2e6;
            color: #6c757d;
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>Proof Sketcher - Theorem Index</h1>
        <p>Natural language explanations of Lean 4 theorems</p>
    </div>

    <div class="theorem-table">
        <table>
            <thead>
                <tr>
                    <th>Theorem</th>
                    <th>Difficulty</th>
                    <th>Mathematical Areas</th>
                    <th>Description</th>
                </tr>
            </thead>
            <tbody>
                {theorem_rows}
            </tbody>
        </table>
    </div>

    <div class="footer">
        <p>Generated with <strong>Proof Sketcher</strong> - {len(sketches)} theorems processed</p>
    </div>
</body>
</html>"""

        index_path = self.output_dir / "index.html"
        index_path.write_text(html_content, encoding="utf-8")
        self.logger.info(f"Created HTML index: {index_path}")

    def export_from_theorems(
        self,
        theorems: List[TheoremInfo],
        generator,
        formats: List[str] = None,
        create_index: bool = True,
    ) -> Dict[str, List[Path]]:
        """Export theorems by generating sketches first.

        Args:
            theorems: List of theorem info objects
            generator: Generator to use for creating sketches
            formats: List of formats to export to
            create_index: Whether to create index files

        Returns:
            Dictionary mapping format names to lists of generated files
        """
        if formats is None:
            formats = ["markdown", "html"]
        sketches = []

        for theorem in theorems:
            try:
                sketch = generator.generate_offline(theorem)
                sketches.append(sketch)
                self.logger.info(f"Generated sketch for {theorem.name}")
            except Exception as e:
                self.logger.error(f"Failed to generate sketch for {theorem.name}: {e}")

        return self.export_multiple(sketches, formats, create_index)
