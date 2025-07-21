"""Unit tests for exporter modules."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, Mock, patch

import pytest

from proof_sketcher.exporter import HTMLExporter, MarkdownExporter, TemplateManager
from proof_sketcher.exporter.models import (
    BaseExporter,
    ExportFormat,
    ExportOptions,
    ExportResult,
    TemplateContext,
)
from proof_sketcher.generator.models import ProofSketch, ProofStep, ProofStrategy


@pytest.fixture
def sample_proof_sketch():
    """Create a sample proof sketch for testing."""
    from proof_sketcher.generator.models import ProofStrategy

    return ProofSketch(
        theorem_name="test_theorem",
        theorem_statement="∀ n : ℕ, n + 0 = n",
        intuitive_overview="This theorem shows that zero is the right identity for addition.",
        conceptual_overview="We use the definition of natural number addition to prove this identity.",
        bridging_overview="The proof connects our intuitive understanding with formal definitions.",
        formal_overview="This theorem is proven using Lean's definition of natural number addition.",
        key_steps=[
            ProofStep(
                step_number=1,
                intuitive_explanation="Zero doesn't change the value when added",
                conceptual_explanation="Apply the definition of addition",
                bridging_explanation="Use formal definitions to prove the identity",
                formal_explanation="By the definition of natural number addition",
                tactics=["simp"],
                mathematical_content="n + 0 = n",
                lean_code="by simp",
            )
        ],
        intuitive_conclusion="Therefore, zero is the right identity for addition.",
        conceptual_conclusion="This completes our proof of the identity property.",
        bridging_conclusion="We have connected intuitive and formal reasoning.",
        formal_conclusion="The theorem is proven using Lean's type system.",
        proof_strategy=ProofStrategy.DIRECT,
        discrete_math_topic="arithmetic",
        difficulty_level="beginner",
        mathematical_areas=["arithmetic", "number_theory"],
        prerequisites=["basic_arithmetic"],
    )


@pytest.fixture
def export_options(tmp_path):
    """Create export options for testing."""
    return ExportOptions(
        output_dir=tmp_path,
        include_animations=True,
    )


class TestBaseExporterBase:
    """Test the base exporter class."""

    def test_base_exporter_initialization(self, export_options):
        """Test base exporter initialization."""

        class TestBaseExporter(BaseExporter):
            @property
            def format(self):
                return ExportFormat.HTML

            def export_single(self, proof_sketch, animation_path=None):
                return ExportResult(
                    success=True,
                    format=ExportFormat.HTML,
                    output_files=[Path("test.html")],
                    metadata={},
                )

            def export_multiple(self, proof_sketches):
                return [self.export_single(sketch) for sketch in proof_sketches]

        exporter = TestBaseExporter(export_options)
        assert exporter.options == export_options
        assert exporter.options.output_dir == export_options.output_dir

    def test_base_exporter_setup_output_dir(self, tmp_path):
        """Test output directory setup."""
        options = ExportOptions(output_dir=tmp_path / "new_dir")

        class TestBaseExporter(BaseExporter):
            @property
            def format(self):
                return ExportFormat.HTML

            def export_single(self, proof_sketch, animation_path=None):
                return ExportResult(
                    success=True, format=ExportFormat.HTML, output_files=[], metadata={}
                )

            def export_multiple(self, proof_sketches):
                return [self.export_single(sketch) for sketch in proof_sketches]

        exporter = TestBaseExporter(options)
        exporter._ensure_output_dir()
        assert (tmp_path / "new_dir").exists()

    # def test_base_exporter_validation(self, export_options):
    #     """Test input validation."""
    #
    #     class TestBaseExporter(BaseExporter):
    #         def export_single(self, proof_sketch, animation_path=None):
    #             return ExportResult(
    #                 success=True, format=ExportFormat.HTML, output_files=[], metadata={}
    #             )
    #
    #     exporter = TestBaseExporter(ExportFormat.HTML, export_options)
    #
    #     # Valid proof sketch should not raise
    #     valid_sketch = ProofSketch(
    #         theorem_name="test",
    #         theorem_statement="True",
    #         introduction="Test",
    #         key_steps=[],
    #         conclusion="Done",
    #         difficulty_level="easy",
    #     )
    #     exporter._validate_input(valid_sketch)
    #
    #     # Invalid input should raise
    #     with pytest.raises(ValueError):
    #         exporter._validate_input(None)


class TestHTMLExporter:
    """Test HTML exporter."""

    def test_html_exporter_initialization(self, export_options):
        """Test HTML exporter initialization."""
        exporter = HTMLExporter(export_options)
        assert exporter.options == export_options
        assert exporter.template_manager is not None

    def test_html_export_single(self, sample_proof_sketch, export_options):
        """Test single HTML export."""
        exporter = HTMLExporter(export_options)

        with patch.object(exporter.template_manager, "render_template") as mock_render:
            mock_render.return_value = "<html><body>Test theorem</body></html>"

            result = exporter.export_single(sample_proof_sketch)

            assert result.success
            assert result.format == ExportFormat.HTML
            assert len(result.files_created) == 1
            assert result.files_created[0].suffix == ".html"
            mock_render.assert_called_once()

    def test_html_export_with_animations(
        self, sample_proof_sketch, export_options, tmp_path
    ):
        """Test HTML export with animations."""
        animation_path = tmp_path / "animation.mp4"
        animation_path.write_text("fake video")

        exporter = HTMLExporter(export_options)

        with patch.object(exporter.template_manager, "render_template") as mock_render:
            mock_render.return_value = "<html><body>With animation</body></html>"

            result = exporter.export_single(sample_proof_sketch, animation_path)

            assert result.success
            assert "animation_path" in result.metadata

    def test_html_export_batch(self, export_options, tmp_path):
        """Test batch HTML export."""
        sketches = [
            ProofSketch(
                theorem_name=f"theorem_{i}",
                theorem_statement=f"Statement {i}",
                intuitive_overview=f"Introduction {i}",
                conceptual_overview=f"Conceptual overview {i}",
                bridging_overview=f"Bridging overview {i}",
                formal_overview=f"Formal overview {i}",
                key_steps=[],
                intuitive_conclusion=f"Conclusion {i}",
                conceptual_conclusion=f"Conceptual conclusion {i}",
                bridging_conclusion=f"Bridging conclusion {i}",
                formal_conclusion=f"Formal conclusion {i}",
                proof_strategy=ProofStrategy.DIRECT,
                difficulty_level="beginner",
                mathematical_areas=["test"],
                prerequisites=["basic_logic"],
            )
            for i in range(3)
        ]

        exporter = HTMLExporter(export_options)

        with patch.object(exporter, "export_single") as mock_export:
            mock_export.return_value = ExportResult(
                success=True,
                format=ExportFormat.HTML,
                output_path=Path("test.html"),
                files_created=[Path("test.html")],
                warnings=[],
                errors=[],
                metadata={},
            )

            results = exporter.export_batch(sketches)

            assert len(results) == 3
            assert all(r.success for r in results)
            assert mock_export.call_count == 3


class TestMarkdownExporter:
    """Test Markdown exporter."""

    def test_markdown_exporter_initialization(self, export_options):
        """Test Markdown exporter initialization."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.MARKDOWN
        )
        exporter = MarkdownExporter(options)
        assert exporter.options.format == ExportFormat.MARKDOWN

    def test_markdown_export_single(self, sample_proof_sketch, export_options):
        """Test single Markdown export."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.MARKDOWN
        )
        exporter = MarkdownExporter(options)

        with patch.object(exporter.template_manager, "render_template") as mock_render:
            mock_render.return_value = "# Test Theorem\n\nThis is a test."

            result = exporter.export_single(sample_proof_sketch)

            assert result.success
            assert result.format == ExportFormat.MARKDOWN
            assert len(result.output_files) == 1
            assert result.output_files[0].suffix == ".md"

    def test_markdown_github_flavor(self, sample_proof_sketch, export_options):
        """Test GitHub-flavored Markdown export."""
        options = ExportOptions(
            output_dir=export_options.output_dir,
            format=ExportFormat.MARKDOWN,
            markdown_flavor="github",
        )
        exporter = MarkdownExporter(options)

        with patch.object(exporter.template_manager, "render_template") as mock_render:
            mock_render.return_value = "```lean\ntheorem test\n```"

            result = exporter.export_single(sample_proof_sketch)
            assert result.success

    def test_markdown_with_math(self, sample_proof_sketch, export_options):
        """Test Markdown export with mathematical notation."""
        options = ExportOptions(
            output_dir=export_options.output_dir,
            format=ExportFormat.MARKDOWN,
            include_mathjax=True,
        )
        exporter = MarkdownExporter(options)

        with patch.object(exporter.template_manager, "render_template") as mock_render:
            mock_render.return_value = "$$\\forall n \\in \\mathbb{N}, n + 0 = n$$"

            result = exporter.export_single(sample_proof_sketch)
            assert result.success


class TestBaseExporter:
    """Test PDF exporter."""

    def test_pdf_exporter_initialization(self, export_options):
        """Test PDF exporter initialization."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.PDF
        )
        exporter = BaseExporter(options)
        assert exporter.options.format == ExportFormat.PDF

    def test_pdf_export_latex_generation(self, sample_proof_sketch, export_options):
        """Test LaTeX generation for PDF export."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.PDF
        )
        exporter = BaseExporter(options)

        with patch.object(exporter.template_manager, "render_template") as mock_render:
            mock_render.return_value = (
                "\\documentclass{article}\\begin{document}Test\\end{document}"
            )

            latex_content = exporter._generate_latex(sample_proof_sketch)

            assert "\\documentclass" in latex_content
            assert "\\begin{document}" in latex_content
            assert "\\end{document}" in latex_content

    def test_pdf_export_single(self, sample_proof_sketch, export_options):
        """Test single PDF export."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.PDF
        )
        exporter = BaseExporter(options)

        with patch.object(exporter, "_generate_latex") as mock_latex:
            mock_latex.return_value = (
                "\\documentclass{article}\\begin{document}Test\\end{document}"
            )

            with patch.object(exporter, "_compile_latex") as mock_compile:
                mock_compile.return_value = True

                result = exporter.export_single(sample_proof_sketch)

                assert result.success
                assert result.format == ExportFormat.PDF

    def test_pdf_latex_compilation(self, export_options, tmp_path):
        """Test LaTeX compilation."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.PDF
        )
        exporter = BaseExporter(options)

        latex_file = tmp_path / "test.tex"
        latex_file.write_text(
            "\\documentclass{article}\\begin{document}Test\\end{document}"
        )

        with patch("subprocess.run") as mock_run:
            mock_run.return_value = Mock(returncode=0)

            success = exporter._compile_latex(latex_file)
            assert success


class TestBaseExporter:
    """Test Jupyter notebook exporter."""

    def test_jupyter_exporter_initialization(self, export_options):
        """Test Jupyter exporter initialization."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.JUPYTER
        )
        exporter = BaseExporter(options)
        assert exporter.options.format == ExportFormat.JUPYTER

    def test_jupyter_export_single(self, sample_proof_sketch, export_options):
        """Test single Jupyter notebook export."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.JUPYTER
        )
        exporter = BaseExporter(options)

        result = exporter.export_single(sample_proof_sketch)

        assert result.success
        assert result.format == ExportFormat.JUPYTER
        assert len(result.output_files) == 1
        assert result.output_files[0].suffix == ".ipynb"

    def test_jupyter_notebook_structure(self, sample_proof_sketch, export_options):
        """Test Jupyter notebook structure."""
        options = ExportOptions(
            output_dir=export_options.output_dir, format=ExportFormat.JUPYTER
        )
        exporter = BaseExporter(options)

        notebook = exporter._create_notebook(sample_proof_sketch)

        assert "cells" in notebook
        assert "metadata" in notebook
        assert "nbformat" in notebook
        assert len(notebook["cells"]) > 0

    def test_jupyter_with_code_cells(self, sample_proof_sketch, export_options):
        """Test Jupyter notebook with code cells."""
        options = ExportOptions(
            output_dir=export_options.output_dir,
            format=ExportFormat.JUPYTER,
            include_lean_code=True,
        )
        exporter = BaseExporter(options)

        notebook = exporter._create_notebook(sample_proof_sketch)

        # Check for code cells
        code_cells = [cell for cell in notebook["cells"] if cell["cell_type"] == "code"]
        assert len(code_cells) > 0


class TestMarkdownExporter:
    """Test Mathlib-specific exporter."""

    def test_mathlib_exporter_initialization(self, export_options):
        """Test Mathlib exporter initialization."""
        exporter = MarkdownExporter(export_options)
        assert exporter.notation_handler is not None

    def test_mathlib_notation_enhancement(self, sample_proof_sketch, export_options):
        """Test Mathlib notation enhancement."""
        exporter = MarkdownExporter(export_options)

        with patch.object(
            exporter.notation_handler, "enhance_proof_sketch"
        ) as mock_enhance:
            mock_enhance.return_value = sample_proof_sketch

            enhanced = exporter._enhance_with_mathlib_notation(sample_proof_sketch)

            assert enhanced == sample_proof_sketch
            mock_enhance.assert_called_once_with(sample_proof_sketch)

    def test_mathlib_complexity_assessment(self, sample_proof_sketch, export_options):
        """Test complexity assessment for Mathlib theorems."""
        exporter = MarkdownExporter(export_options)

        complexity = exporter._assess_complexity(sample_proof_sketch)

        assert isinstance(complexity, dict)
        assert "notation_complexity" in complexity
        assert "proof_complexity" in complexity
        assert "overall_score" in complexity

    def test_mathlib_export_single(self, sample_proof_sketch, export_options):
        """Test single Mathlib export."""
        exporter = MarkdownExporter(export_options)

        with patch.object(exporter, "_enhance_with_mathlib_notation") as mock_enhance:
            mock_enhance.return_value = sample_proof_sketch

            with patch.object(exporter.base_exporter, "export_single") as mock_export:
                mock_export.return_value = ExportResult(
                    success=True,
                    format=ExportFormat.HTML,
                    output_files=[Path("test.html")],
                    metadata={},
                )

                result = exporter.export_single(sample_proof_sketch)

                assert result.success
                mock_enhance.assert_called_once()
                mock_export.assert_called_once()


class TestTemplateManager:
    """Test template manager."""

    def test_template_manager_initialization(self):
        """Test template manager initialization."""
        manager = TemplateManager()
        assert manager.env is not None
        assert manager.template_dir.exists()

    def test_render_html_template(self, sample_proof_sketch):
        """Test HTML template rendering."""
        manager = TemplateManager()

        with patch.object(manager.env, "get_template") as mock_get:
            mock_template = Mock()
            mock_template.render.return_value = "<html>Test</html>"
            mock_get.return_value = mock_template

            result = manager.render_template(
                "theorem.html.jinja2", theorem=sample_proof_sketch
            )

            assert result == "<html>Test</html>"
            mock_get.assert_called_once_with("theorem.html.jinja2")

    def test_render_markdown_template(self, sample_proof_sketch):
        """Test Markdown template rendering."""
        manager = TemplateManager()

        with patch.object(manager.env, "get_template") as mock_get:
            mock_template = Mock()
            mock_template.render.return_value = "# Test\n\nContent"
            mock_get.return_value = mock_template

            result = manager.render_template(
                "theorem.md.jinja2", theorem=sample_proof_sketch
            )

            assert result == "# Test\n\nContent"

    def test_template_context_helpers(self):
        """Test template context helpers."""
        manager = TemplateManager()

        # Test math formatting helper
        assert hasattr(manager, "_format_math")
        assert hasattr(manager, "_escape_latex")
        assert hasattr(manager, "_format_code")

    def test_custom_template_filters(self):
        """Test custom Jinja2 filters."""
        manager = TemplateManager()

        # Check custom filters are registered
        assert "format_math" in manager.env.filters
        assert "escape_latex" in manager.env.filters
        assert "format_duration" in manager.env.filters

    def test_template_not_found_handling(self):
        """Test handling of missing templates."""
        manager = TemplateManager()

        with pytest.raises(Exception):
            manager.render_template("nonexistent.jinja2", data={})

    def test_template_inheritance(self, sample_proof_sketch):
        """Test template inheritance system."""
        manager = TemplateManager()

        with patch.object(manager.env, "get_template") as mock_get:
            # Mock a template that extends base
            mock_template = Mock()
            mock_template.render.return_value = "<!DOCTYPE html><html>Extended</html>"
            mock_get.return_value = mock_template

            result = manager.render_template(
                "theorem.html.jinja2", theorem=sample_proof_sketch
            )

            assert "<!DOCTYPE html>" in result
            assert "Extended" in result


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
