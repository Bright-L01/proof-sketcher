"""Jupyter notebook exporter for interactive exploration."""

import json
import logging
from pathlib import Path
from typing import Any, Dict, List, Optional

from ..generator.models import ProofSketch
from .base import BaseExporterImpl
from .models import ExportContext, ExportFormat, ExportOptions, ExportResult
from .template_manager import TemplateManager


class JupyterExporter(BaseExporterImpl):
    """Exporter for Jupyter notebook format."""

    def __init__(
        self,
        options: Optional[ExportOptions] = None,
        template_manager: Optional[TemplateManager] = None,
    ):
        """Initialize Jupyter exporter.

        Args:
            options: Export options
            template_manager: Template manager
        """
        super().__init__(ExportFormat.JUPYTER, options, template_manager)
        self.logger = logging.getLogger(__name__)

    def _export_sketch(self, sketch: ProofSketch, context: ExportContext) -> List[Path]:
        """Export a single proof sketch to Jupyter notebook.

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            List of created files
        """
        created_files = []

        # Generate notebook structure
        notebook = self._create_notebook(sketch, context)

        # Write notebook file
        output_file = self._generate_filename(sketch.theorem_name, "ipynb")
        output_file.write_text(json.dumps(notebook, indent=2), encoding="utf-8")
        created_files.append(output_file)

        self.logger.info(f"Exported {sketch.theorem_name} to {output_file}")

        return created_files

    def export_multiple(
        self, sketches: List[ProofSketch], context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export multiple sketches as a single notebook with sections.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Export result
        """
        context = context or self._create_default_context(sketches)

        # Create combined notebook
        notebook = self._create_combined_notebook(sketches, context)

        # Write notebook
        output_file = self.options.output_dir / "proof_sketcher_notebook.ipynb"
        output_file.write_text(json.dumps(notebook, indent=2), encoding="utf-8")

        return ExportResult(
            success=True,
            format=ExportFormat.JUPYTER,
            output_path=self.options.output_dir,
            files_created=[output_file],
        )

    def _create_notebook(
        self, sketch: ProofSketch, context: ExportContext
    ) -> Dict[str, Any]:
        """Create notebook structure for a single sketch.

        Args:
            sketch: Proof sketch
            context: Export context

        Returns:
            Notebook dictionary
        """
        cells = []

        # Title cell
        cells.append(self._create_markdown_cell(f"# {sketch.theorem_name}"))

        # Statement cell
        cells.append(
            self._create_markdown_cell(
                "## Statement\n\n" f"```lean\n{sketch.theorem_statement}\n```"
            )
        )

        # Explanation cell
        cells.append(
            self._create_markdown_cell(f"## Explanation\n\n{sketch.explanation}")
        )

        # Interactive exploration cell
        cells.append(
            self._create_code_cell(
                "# Interactive exploration\n"
                "# You can use this cell to experiment with the concepts\n\n"
                f"theorem_name = '{sketch.theorem_name}'\n"
                f"step_count = {len(sketch.steps)}\n\n"
                "print(f'Theorem {theorem_name} has {step_count} steps')"
            )
        )

        # Animation cell if available
        if sketch.theorem_name in context.animations:
            animation_path = context.animations[sketch.theorem_name]
            cells.append(
                self._create_markdown_cell(
                    "## Animation\n\n" f"![Animation]({animation_path})"
                )
            )

            # Video player code cell
            cells.append(
                self._create_code_cell(
                    "from IPython.display import Video\n" f"Video('{animation_path}')"
                )
            )

        # Proof steps
        cells.append(self._create_markdown_cell("## Proof Steps"))

        for i, step in enumerate(sketch.steps, 1):
            step_md = f"### Step {i}: {step.description}\n\n"

            if step.mathematical_content:
                step_md += f"$$\n{step.mathematical_content}\n$$\n\n"

            if step.reasoning:
                step_md += f"**Reasoning:** {step.reasoning}\n\n"

            cells.append(self._create_markdown_cell(step_md))

            # Add interactive cell for mathematical exploration
            if step.mathematical_content:
                cells.append(
                    self._create_code_cell(
                        f"# Explore step {i} mathematically\n"
                        "# You can use SymPy or other libraries here\n"
                        f"# Mathematical content: {step.mathematical_content}\n"
                    )
                )

        # Key insights
        if sketch.key_insights:
            insights_md = "## Key Insights\n\n"
            for insight in sketch.key_insights:
                insights_md += f"- {insight}\n"
            cells.append(self._create_markdown_cell(insights_md))

        # Summary code cell
        cells.append(
            self._create_code_cell(
                "# Summary and further exploration\n"
                f"summary = {{\n"
                f"    'theorem': '{sketch.theorem_name}',\n"
                f"    'steps': {len(sketch.steps)},\n"
                f"    'insights': {len(sketch.key_insights)},\n"
                f"}}\n\n"
                "print('Proof Summary:')\n"
                "for key, value in summary.items():\n"
                "    print(f'{key}: {value}')"
            )
        )

        return self._create_notebook_structure(cells)

    def _create_combined_notebook(
        self, sketches: List[ProofSketch], context: ExportContext
    ) -> Dict[str, Any]:
        """Create a combined notebook for multiple sketches.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Notebook dictionary
        """
        cells = []

        # Title and introduction
        cells.append(
            self._create_markdown_cell(
                f"# {context.project_name}\n\n"
                f"This notebook contains {len(sketches)} theorems with natural language explanations.\n\n"
                "Generated by Proof Sketcher"
            )
        )

        # Table of contents
        toc_md = "## Table of Contents\n\n"
        for i, sketch in enumerate(sketches, 1):
            toc_md += f"{i}. [{sketch.theorem_name}](#{sketch.theorem_name.replace(' ', '-')})\n"
        cells.append(self._create_markdown_cell(toc_md))

        # Setup cell
        cells.append(
            self._create_code_cell(
                "# Setup and imports\n"
                "import json\n"
                "from IPython.display import display, Markdown, Video\n\n"
                "# Helper functions\n"
                "def show_theorem(name, statement):\n"
                "    display(Markdown(f'### {name}\\n\\n```lean\\n{statement}\\n```'))\n\n"
                "def show_step(step_num, description, math=None):\n"
                "    content = f'**Step {step_num}:** {description}'\n"
                "    if math:\n"
                "        content += f'\\n\\n$${math}$$'\n"
                "    display(Markdown(content))"
            )
        )

        # Add each theorem as a section
        for sketch in sketches:
            # Section header
            cells.append(self._create_markdown_cell(f"## {sketch.theorem_name}"))

            # Theorem info
            cells.append(
                self._create_code_cell(
                    f"# Theorem: {sketch.theorem_name}\n"
                    f"show_theorem('{sketch.theorem_name}', '''{sketch.theorem_statement}''')"
                )
            )

            # Explanation
            cells.append(self._create_markdown_cell(sketch.explanation))

            # Interactive steps
            steps_code = f"# Proof steps for {sketch.theorem_name}\n"
            for i, step in enumerate(sketch.steps, 1):
                math_content = step.mathematical_content or ""
                steps_code += (
                    f"show_step({i}, '{step.description}', '{math_content}')\n"
                )

            cells.append(self._create_code_cell(steps_code))

        # Summary statistics
        cells.append(
            self._create_code_cell(
                "# Summary statistics\n"
                f"total_theorems = {len(sketches)}\n"
                f"total_steps = {sum(len(s.steps) for s in sketches)}\n"
                f"avg_steps = total_steps / total_theorems\n\n"
                "print(f'Total theorems: {total_theorems}')\n"
                "print(f'Total proof steps: {total_steps}')\n"
                "print(f'Average steps per proof: {avg_steps:.1f}')"
            )
        )

        return self._create_notebook_structure(cells)

    def _create_notebook_structure(self, cells: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Create the notebook JSON structure.

        Args:
            cells: List of cell dictionaries

        Returns:
            Complete notebook structure
        """
        return {
            "cells": cells,
            "metadata": {
                "kernelspec": {
                    "display_name": "Python 3",
                    "language": "python",
                    "name": "python3",
                },
                "language_info": {
                    "codemirror_mode": {"name": "ipython", "version": 3},
                    "file_extension": ".py",
                    "mimetype": "text/x-python",
                    "name": "python",
                    "nbconvert_exporter": "python",
                    "pygments_lexer": "ipython3",
                    "version": "3.11.0",
                },
            },
            "nbformat": 4,
            "nbformat_minor": 5,
        }

    def _create_markdown_cell(self, content: str) -> Dict[str, Any]:
        """Create a markdown cell.

        Args:
            content: Markdown content

        Returns:
            Cell dictionary
        """
        return {"cell_type": "markdown", "metadata": {}, "source": content.split("\n")}

    def _create_code_cell(
        self, content: str, outputs: List[Any] = None
    ) -> Dict[str, Any]:
        """Create a code cell.

        Args:
            content: Python code
            outputs: Optional outputs

        Returns:
            Cell dictionary
        """
        return {
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": outputs or [],
            "source": content.split("\n"),
        }
