"""Comprehensive tests for the exporter module."""

import json
import tempfile
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.animator.models import AnimationResponse
from proof_sketcher.config.config import ExportConfig
from proof_sketcher.exporter import (HTMLExporter, JupyterExporter,
                                     MarkdownExporter, PDFExporter)
from proof_sketcher.exporter.models import ExportResult
from proof_sketcher.generator.models import ProofSketch, ProofStep


class TestHTMLExporter:
    """Test suite for HTMLExporter."""

    @pytest.fixture
    def html_exporter(self):
        """Create HTML exporter instance."""
        config = ExportConfig(
            html_theme="light", html_syntax_style="monokai", html_embed_videos=True
        )
        return HTMLExporter(config)

    @pytest.fixture
    def sample_proof_sketch(self):
        """Create sample proof sketch for testing."""
        return ProofSketch(
            theorem_name="test_theorem",
            explanation="This is a test explanation with $x^2 + y^2 = z^2$",
            steps=[
                ProofStep(description="Step 1", formula="x = y"),
                ProofStep(description="Step 2", formula="y = z"),
            ],
            key_insight="Test insight",
            prerequisites=["Basic math"],
        )

    def test_export_html_basic(self, html_exporter, sample_proof_sketch, tmp_path):
        """Test basic HTML export."""
        output_file = tmp_path / "test.html"

        result = html_exporter.export(
            proof_sketch=sample_proof_sketch, output_path=output_file
        )

        assert result.success
        assert output_file.exists()

        # Check content
        content = output_file.read_text()
        assert "test_theorem" in content
        assert "This is a test explanation" in content
        assert "MathJax" in content  # Should include MathJax

    def test_export_with_animation(self, html_exporter, sample_proof_sketch, tmp_path):
        """Test HTML export with animation."""
        output_file = tmp_path / "animated.html"
        animation_response = AnimationResponse(
            request=Mock(), video_path=Path("/tmp/video.mp4"), success=True
        )

        result = html_exporter.export(
            proof_sketch=sample_proof_sketch,
            animation=animation_response,
            output_path=output_file,
        )

        assert result.success
        content = output_file.read_text()
        assert "video" in content.lower()
        assert "mp4" in content

    def test_template_rendering(self, html_exporter):
        """Test template rendering system."""
        context = {"theorem_name": "Test", "content": "Test content"}

        html = html_exporter._render_template("base.html", context)
        assert isinstance(html, str)
        assert len(html) > 0

    def test_error_handling(self, html_exporter, sample_proof_sketch):
        """Test error handling in export."""
        # Invalid path
        result = html_exporter.export(
            proof_sketch=sample_proof_sketch,
            output_path=Path("/invalid/path/test.html"),
        )

        assert not result.success
        assert result.error_message is not None


class TestMarkdownExporter:
    """Test suite for MarkdownExporter."""

    @pytest.fixture
    def markdown_exporter(self):
        """Create Markdown exporter instance."""
        config = ExportConfig(include_toc=True, math_engine="katex")
        return MarkdownExporter(config)

    def test_export_markdown_basic(
        self, markdown_exporter, sample_proof_sketch, tmp_path
    ):
        """Test basic Markdown export."""
        output_file = tmp_path / "test.md"

        result = markdown_exporter.export(
            proof_sketch=sample_proof_sketch, output_path=output_file
        )

        assert result.success
        assert output_file.exists()

        content = output_file.read_text()
        assert "# test_theorem" in content
        assert "## Steps" in content
        assert "$x^2 + y^2 = z^2$" in content

    def test_collapsible_sections(self, markdown_exporter):
        """Test collapsible sections in Markdown."""
        sketch = ProofSketch(
            theorem_name="collapsible_test",
            explanation="Main text",
            steps=[ProofStep(description="Hidden step", formula="x=1")],
            prerequisites=["Prereq 1", "Prereq 2"],
        )

        content = markdown_exporter._format_proof_sketch(sketch)

        # Should have details/summary tags
        assert "<details>" in content
        assert "<summary>" in content
        assert "Prerequisites" in content

    def test_github_flavored_markdown(self, markdown_exporter):
        """Test GitHub-flavored Markdown features."""
        sketch = ProofSketch(
            theorem_name="gfm_test",
            explanation="Test with `code` and **bold**",
            steps=[],
        )

        content = markdown_exporter._format_proof_sketch(sketch)

        assert "`code`" in content
        assert "**bold**" in content


class TestPDFExporter:
    """Test suite for PDFExporter."""

    @pytest.fixture
    def pdf_exporter(self):
        """Create PDF exporter instance."""
        config = ExportConfig(
            paper_size="letter", font_size=11, latex_engine="pdflatex"
        )
        return PDFExporter(config)

    @patch("subprocess.run")
    def test_export_pdf_basic(
        self, mock_run, pdf_exporter, sample_proof_sketch, tmp_path
    ):
        """Test basic PDF export."""
        # Mock successful LaTeX compilation
        mock_run.return_value.returncode = 0

        output_file = tmp_path / "test.pdf"

        pdf_exporter.export(proof_sketch=sample_proof_sketch, output_path=output_file)

        # Should generate LaTeX and attempt compilation
        assert mock_run.called
        latex_file = tmp_path / "test.tex"
        assert latex_file.exists()

    def test_latex_generation(self, pdf_exporter, sample_proof_sketch):
        """Test LaTeX document generation."""
        latex = pdf_exporter._generate_latex(sample_proof_sketch)

        assert "\\documentclass" in latex
        assert "\\begin{document}" in latex
        assert "\\end{document}" in latex
        assert "test_theorem" in latex
        assert "\\section" in latex

    def test_latex_escaping(self, pdf_exporter):
        """Test LaTeX special character escaping."""
        sketch = ProofSketch(
            theorem_name="test_with_$pecial_chars",
            explanation="Text with & and % and _",
            steps=[],
        )

        latex = pdf_exporter._generate_latex(sketch)

        # Special chars should be escaped
        assert "\\$" in latex or "$" not in latex.replace("\\documentclass", "")
        assert "\\&" in latex
        assert "\\%" in latex


class TestJupyterExporter:
    """Test suite for JupyterExporter."""

    @pytest.fixture
    def jupyter_exporter(self):
        """Create Jupyter exporter instance."""
        config = ExportConfig(kernel_name="python3", include_outputs=True)
        return JupyterExporter(config)

    def test_export_notebook_basic(
        self, jupyter_exporter, sample_proof_sketch, tmp_path
    ):
        """Test basic Jupyter notebook export."""
        output_file = tmp_path / "test.ipynb"

        result = jupyter_exporter.export(
            proof_sketch=sample_proof_sketch, output_path=output_file
        )

        assert result.success
        assert output_file.exists()

        # Load and check notebook structure
        with open(output_file) as f:
            notebook = json.load(f)

        assert "cells" in notebook
        assert len(notebook["cells"]) > 0
        assert notebook["metadata"]["kernelspec"]["name"] == "python3"

    def test_cell_generation(self, jupyter_exporter, sample_proof_sketch):
        """Test notebook cell generation."""
        cells = jupyter_exporter._create_cells(sample_proof_sketch)

        assert len(cells) > 0

        # Should have markdown cells
        markdown_cells = [c for c in cells if c["cell_type"] == "markdown"]
        assert len(markdown_cells) > 0

        # Should have title cell
        title_cell = markdown_cells[0]
        assert "test_theorem" in title_cell["source"]

    def test_code_cell_generation(self, jupyter_exporter):
        """Test code cell generation for interactive content."""
        sketch = ProofSketch(
            theorem_name="interactive_test",
            explanation="Test with code",
            steps=[ProofStep(description="Compute", formula="2 + 2 = 4")],
        )

        cells = jupyter_exporter._create_cells(sketch, include_code=True)

        # Should have at least one code cell
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        assert len(code_cells) > 0


class TestExportModels:
    """Test suite for export data models."""

    def test_export_config(self):
        """Test ExportConfig model."""
        config = ExportConfig(
            format="html",
            include_mathjax=True,
            theme="dark",
            custom_css="body { color: red; }",
        )

        assert config.format == "html"
        assert config.include_mathjax is True
        assert config.theme == "dark"
        assert "color: red" in config.custom_css

    def test_export_result(self):
        """Test ExportResult model."""
        result = ExportResult(
            success=True,
            output_path=Path("/tmp/output.html"),
            file_size_mb=1.5,
            export_time_ms=1234.5,
            warnings=["Missing animation"],
        )

        assert result.success
        assert result.file_size_mb == 1.5
        assert len(result.warnings) == 1


@pytest.mark.integration
class TestExporterIntegration:
    """Integration tests for exporters."""

    def test_multi_format_export(self, tmp_path):
        """Test exporting to multiple formats."""
        from proof_sketcher.exporter import HTMLExporter, MarkdownExporter

        sketch = ProofSketch(
            theorem_name="multi_format_test", explanation="Test content", steps=[]
        )

        # Export to HTML
        html_exporter = HTMLExporter()
        html_result = html_exporter.export(sketch, output_path=tmp_path / "test.html")
        assert html_result.success

        # Export to Markdown
        md_exporter = MarkdownExporter()
        md_result = md_exporter.export(sketch, output_path=tmp_path / "test.md")
        assert md_result.success

        # Both files should exist
        assert (tmp_path / "test.html").exists()
        assert (tmp_path / "test.md").exists()

    def test_export_with_full_pipeline(self):
        """Test export with complete proof sketcher pipeline."""
        from proof_sketcher.exporter import HTMLExporter
        from proof_sketcher.generator.models import ProofSketch, ProofStep
        from proof_sketcher.parser.models import TheoremInfo

        # Create theorem
        theorem = TheoremInfo(
            name="pipeline_test", statement="∀x, P(x)", proof="by assumption"
        )

        # Create proof sketch
        sketch = ProofSketch(
            theorem_name=theorem.name,
            explanation="For all x, P holds",
            steps=[ProofStep(description="Assume x is arbitrary", formula="x : Type")],
        )

        # Export
        exporter = HTMLExporter()
        with tempfile.NamedTemporaryFile(suffix=".html", delete=False) as tmp:
            result = exporter.export(sketch, Path(tmp.name))
            assert result.success

            # Verify content
            content = Path(tmp.name).read_text()
            assert theorem.name in content
            assert "For all x, P holds" in content
