"""PDF exporter using LaTeX."""

import logging
import subprocess
import tempfile
from pathlib import Path
from typing import List, Optional

from ..generator.models import ProofSketch
from .base import BaseExporterImpl
from .models import (
    ExportContext,
    ExportFormat,
    ExportOptions,
    ExportResult,
    TemplateContext,
    TemplateType,
)
from .template_manager import TemplateManager


class PDFExporter(BaseExporterImpl):
    """Exporter for PDF format via LaTeX."""

    def __init__(
        self,
        options: Optional[ExportOptions] = None,
        template_manager: Optional[TemplateManager] = None,
    ):
        """Initialize PDF exporter.

        Args:
            options: Export options
            template_manager: Template manager
        """
        super().__init__(ExportFormat.PDF, options, template_manager)
        self.logger = logging.getLogger(__name__)
        self.latex_engine = (
            getattr(options, "pdf_engine", "pdflatex") if options else "pdflatex"
        )

    def _export_sketch(self, sketch: ProofSketch, context: ExportContext) -> List[Path]:
        """Export a single proof sketch to PDF.

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            List of created files
        """
        created_files = []

        # Generate LaTeX content
        template_context = self._create_template_context(sketch, context)
        latex_content = self.template_manager.render_template(
            ExportFormat.PDF, TemplateType.THEOREM, template_context.dict()
        )

        # Compile LaTeX to PDF
        pdf_file = self._compile_latex(latex_content, sketch.theorem_name)
        if pdf_file:
            created_files.append(pdf_file)
            self.logger.info(f"Exported {sketch.theorem_name} to {pdf_file}")

        return created_files

    def export_multiple(
        self, sketches: List[ProofSketch], context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export multiple sketches as a single PDF document.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Export result
        """
        context = context or self._create_default_context(sketches)

        # For PDF, we create a single document with all theorems
        template_context = {
            "project_name": context.project_name,
            "author": context.author,
            "version": context.version,
            "timestamp": (
                context.timestamp.isoformat() if context.include_timestamps else None
            ),
            "theorems": [],
        }

        # Add all theorems to context
        for sketch in sketches:
            theorem_ctx = self._create_template_context(sketch, context)
            template_context["theorems"].append(theorem_ctx.dict())

        # Render complete document
        latex_content = self.template_manager.render_template(
            ExportFormat.PDF,
            TemplateType.LAYOUT,
            template_context,
            custom_name="document.tex.jinja2",
        )

        # Compile to PDF
        pdf_file = self._compile_latex(latex_content, "proof_sketcher_output")

        if pdf_file:
            return ExportResult(
                success=True,
                format=ExportFormat.PDF,
                output_path=self.options.output_dir,
                files_created=[pdf_file],
            )
        else:
            return ExportResult(
                success=False,
                format=ExportFormat.PDF,
                output_path=self.options.output_dir,
                errors=["Failed to compile LaTeX to PDF"],
            )

    def _compile_latex(self, latex_content: str, name: str) -> Optional[Path]:
        """Compile LaTeX content to PDF.

        Args:
            latex_content: LaTeX source code
            name: Base name for output file

        Returns:
            Path to PDF file if successful
        """
        # Use temporary directory for compilation
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_path = Path(tmpdir)

            # Write LaTeX file
            tex_file = tmp_path / f"{name}.tex"
            tex_file.write_text(latex_content, encoding="utf-8")

            # Copy any required assets
            self._copy_latex_assets(tmp_path)

            # Run LaTeX compiler twice for references
            for i in range(2):
                try:
                    result = subprocess.run(
                        [self.latex_engine, "-interaction=nonstopmode", tex_file.name],
                        cwd=tmp_path,
                        capture_output=True,
                        text=True,
                        timeout=60,
                    )

                    if result.returncode != 0 and i == 1:
                        self.logger.error(
                            f"LaTeX compilation failed:\n{result.stdout}\n{result.stderr}"
                        )
                        return None

                except subprocess.TimeoutExpired:
                    self.logger.error("LaTeX compilation timed out")
                    return None
                except FileNotFoundError:
                    self.logger.error(f"LaTeX engine '{self.latex_engine}' not found")
                    return None

            # Move PDF to output directory
            pdf_src = tmp_path / f"{name}.pdf"
            if pdf_src.exists():
                pdf_dst = self._generate_filename(name, "pdf")
                pdf_src.rename(pdf_dst)
                return pdf_dst
            else:
                self.logger.error(f"PDF file not generated: {pdf_src}")
                return None

    def _create_template_context(
        self, sketch: ProofSketch, context: ExportContext
    ) -> TemplateContext:
        """Create template context with LaTeX-specific formatting.

        Args:
            sketch: Proof sketch
            context: Export context

        Returns:
            Template context
        """
        # Get base context as dict and convert to TemplateContext
        base_dict = super()._create_template_context(sketch, context)
        base_context = TemplateContext(**base_dict)

        # Escape LaTeX special characters in text fields
        base_context.explanation = self.template_manager._latex_escape(
            base_context.explanation
        )

        # Format mathematical content for LaTeX
        for step in base_context.proof_steps:
            if isinstance(step, dict) and "mathematical_content" in step:
                # Already in LaTeX format, no escaping needed
                pass

        return base_context

    def _copy_latex_assets(self, target_dir: Path) -> None:
        """Copy LaTeX assets to compilation directory.

        Args:
            target_dir: Target directory
        """
        # Copy any custom LaTeX packages or styles
        assets_dir = self.template_manager.get_asset_dir(ExportFormat.PDF, "latex")
        if assets_dir and assets_dir.exists():
            import shutil

            for item in assets_dir.iterdir():
                if item.suffix in [".sty", ".cls", ".tex"]:
                    shutil.copy2(item, target_dir / item.name)
