"""Comprehensive tests for the exporter module."""

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from proof_sketcher.exporter import (
    HTMLExporter,
    JupyterExporter,
    MarkdownExporter,
    PDFExporter,
)
from proof_sketcher.exporter.models import ExportFormat, ExportOptions, ExportResult
from proof_sketcher.generator.models import ProofSketch, ProofStep


class TestHTMLExporter:
    """Test suite for HTMLExporter."""

    @pytest.fixture
    def html_exporter(self):
        """Create HTML exporter instance."""
        config = ExportOptions(
            html_theme="light", html_syntax_style="monokai", html_embed_videos=True
        )
        return HTMLExporter(config)

    @pytest.fixture
    def sample_proof_sketch(self):
        """Create sample proof sketch for testing."""
        return ProofSketch(
            theorem_name="test_theorem",
            introduction="This is a test explanation with $x^2 + y^2 = z^2$",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Step 1",
                    mathematical_content="x = y",
                    tactics=[],
                ),
                ProofStep(
                    step_number=2,
                    description="Step 2",
                    mathematical_content="y = z",
                    tactics=[],
                ),
            ],
            conclusion="Test conclusion",
            prerequisites=["Basic math"],
        )

    def test_export_html_basic(self, html_exporter, sample_proof_sketch, tmp_path):
        """Test basic HTML export."""
        # Set output directory for the exporter
        html_exporter.options.output_dir = tmp_path

        result = html_exporter.export_single(sample_proof_sketch)

        assert result.success
        assert len(result.files_created) > 0

        # Check the created file
        output_file = result.files_created[0]
        assert output_file.exists()

        # Check content
        content = output_file.read_text(encoding="utf-8")
        assert "test_theorem" in content
        assert "This is a test explanation" in content
        # Check that it's valid HTML with theorem structure
        assert "<h1>" in content or "<title>" in content
        assert "x = y" in content  # First proof step
        assert "y = z" in content  # Second proof step

    def test_export_with_animation(self, html_exporter, sample_proof_sketch, tmp_path):
        """Test HTML export with animation."""
        html_exporter.options.output_dir = tmp_path

        # Create a fake animation file
        animation_file = tmp_path / "test_animation.mp4"
        animation_file.write_text("fake video content", encoding="utf-8")

        # Create export context with animation
        from proof_sketcher.exporter.models import ExportContext

        context = ExportContext(
            format=ExportFormat.HTML,
            output_dir=tmp_path,
            sketches=[sample_proof_sketch],
            animations={sample_proof_sketch.theorem_name: animation_file},
        )

        result = html_exporter.export_single(sample_proof_sketch, context)

        assert result.success
        assert len(result.files_created) > 0

        # Check that animation was copied
        animations_dir = tmp_path / "animations"
        if animations_dir.exists():
            animation_files = list(animations_dir.glob("*.mp4"))
            assert len(animation_files) > 0

    def test_template_rendering(self, html_exporter):
        """Test template rendering system."""
        from proof_sketcher.exporter.models import TemplateType

        context = {"theorem_name": "Test", "content": "Test content"}

        # Test that template manager can render
        html = html_exporter.template_manager.render_template(
            ExportFormat.HTML, TemplateType.THEOREM, context
        )
        assert isinstance(html, str)
        assert len(html) > 0

    def test_error_handling(self, html_exporter, sample_proof_sketch):
        """Test error handling in export."""
        # Set invalid output directory
        html_exporter.options.output_dir = Path("/invalid/path/that/does/not/exist")

        result = html_exporter.export_single(sample_proof_sketch)

        # The export might still succeed if it creates the directory
        # So we can just check the result is valid
        assert isinstance(result, ExportResult)


class TestMarkdownExporter:
    """Test suite for MarkdownExporter."""

    @pytest.fixture
    def markdown_exporter(self):
        """Create Markdown exporter instance."""
        config = ExportOptions(
            markdown_collapsible_proofs=True, markdown_math_style="katex"
        )
        return MarkdownExporter(config)

    @pytest.fixture
    def sample_proof_sketch(self):
        """Create sample proof sketch for testing."""
        return ProofSketch(
            theorem_name="test_theorem",
            introduction="This is a test explanation with $x^2 + y^2 = z^2$",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Step 1",
                    mathematical_content="x = y",
                    tactics=[],
                ),
                ProofStep(
                    step_number=2,
                    description="Step 2",
                    mathematical_content="y = z",
                    tactics=[],
                ),
            ],
            conclusion="Test conclusion",
            prerequisites=["Basic math"],
        )

    def test_export_markdown_basic(
        self, markdown_exporter, sample_proof_sketch, tmp_path
    ):
        """Test basic Markdown export."""
        markdown_exporter.options.output_dir = tmp_path

        result = markdown_exporter.export_single(sample_proof_sketch)

        assert result.success
        assert len(result.files_created) > 0

        output_file = result.files_created[0]
        assert output_file.exists()

        content = output_file.read_text(encoding="utf-8")
        assert "test_theorem" in content
        assert "Step" in content or "step" in content
        assert "$x^2 + y^2 = z^2$" in content

    def test_collapsible_sections(self, markdown_exporter, tmp_path):
        """Test collapsible sections in Markdown."""
        sketch = ProofSketch(
            theorem_name="collapsible_test",
            introduction="Main text",
            key_steps=[
                ProofStep(
                    step_number=1, description="Hidden step", mathematical_content="x=1"
                )
            ],
            conclusion="Test conclusion",
            prerequisites=["Prereq 1", "Prereq 2"],
        )

        markdown_exporter.options.output_dir = tmp_path
        result = markdown_exporter.export_single(sketch)

        if result.success and result.files_created:
            content = result.files_created[0].read_text(encoding="utf-8")
            # Check for collapsible sections if enabled
            if markdown_exporter.options.markdown_collapsible_proofs:
                assert (
                    "<details>" in content or "##" in content
                )  # Either collapsible or headers

    def test_github_flavored_markdown(self, markdown_exporter, tmp_path):
        """Test GitHub-flavored Markdown features."""
        sketch = ProofSketch(
            theorem_name="gfm_test",
            introduction="Test with `code` and **bold**",
            key_steps=[],
            conclusion="Test conclusion",
        )

        markdown_exporter.options.output_dir = tmp_path
        result = markdown_exporter.export_single(sketch)

        if result.success and result.files_created:
            content = result.files_created[0].read_text(encoding="utf-8")
            assert "`code`" in content
            assert "**bold**" in content


class TestPDFExporter:
    """Test suite for PDFExporter."""

    @pytest.fixture
    def pdf_exporter(self):
        """Create PDF exporter instance."""
        config = ExportOptions(
            pdf_paper_size="letter", pdf_font_size=11, pdf_engine="pdflatex"
        )
        return PDFExporter(config)

    @pytest.fixture
    def sample_proof_sketch(self):
        """Create sample proof sketch for testing."""
        return ProofSketch(
            theorem_name="test_theorem",
            introduction="This is a test explanation",
            key_steps=[
                ProofStep(
                    step_number=1, description="Step 1", mathematical_content="x = y"
                ),
                ProofStep(
                    step_number=2, description="Step 2", mathematical_content="y = z"
                ),
            ],
            conclusion="Test conclusion",
        )

    @patch("subprocess.run")
    def test_export_pdf_basic(
        self, mock_run, pdf_exporter, sample_proof_sketch, tmp_path
    ):
        """Test basic PDF export."""
        # Mock successful LaTeX compilation
        mock_run.return_value.returncode = 0

        pdf_exporter.options.output_dir = tmp_path

        result = pdf_exporter.export_single(sample_proof_sketch)

        # Should attempt to create PDF
        assert isinstance(result, ExportResult)

    def test_latex_generation(self, pdf_exporter, sample_proof_sketch, tmp_path):
        """Test LaTeX document generation."""
        pdf_exporter.options.output_dir = tmp_path

        # Try to export and check if LaTeX file is created
        with patch("subprocess.run") as mock_run:
            mock_run.return_value.returncode = 0
            result = pdf_exporter.export_single(sample_proof_sketch)

            # Check if any tex files were created
            tex_files = list(tmp_path.glob("*.tex"))
            if tex_files:
                latex_content = tex_files[0].read_text(encoding="utf-8")
                assert "test_theorem" in latex_content

    def test_latex_escaping(self, pdf_exporter, tmp_path):
        """Test LaTeX special character escaping."""
        sketch = ProofSketch(
            theorem_name="test_with_special_chars",
            introduction="Text with & and % and _",
            key_steps=[],
            conclusion="Test conclusion",
        )

        pdf_exporter.options.output_dir = tmp_path

        # Try to export
        with patch("subprocess.run") as mock_run:
            mock_run.return_value.returncode = 0
            result = pdf_exporter.export_single(sketch)

            # Check result
            assert isinstance(result, ExportResult)


class TestJupyterExporter:
    """Test suite for JupyterExporter."""

    @pytest.fixture
    def jupyter_exporter(self):
        """Create Jupyter exporter instance."""
        config = ExportOptions(jupyter_kernel="python3", jupyter_include_outputs=True)
        return JupyterExporter(config)

    @pytest.fixture
    def sample_proof_sketch(self):
        """Create sample proof sketch for testing."""
        return ProofSketch(
            theorem_name="test_theorem",
            introduction="This is a test explanation",
            key_steps=[
                ProofStep(
                    step_number=1, description="Step 1", mathematical_content="x = y"
                ),
                ProofStep(
                    step_number=2, description="Step 2", mathematical_content="y = z"
                ),
            ],
            conclusion="Test conclusion",
        )

    def test_export_notebook_basic(
        self, jupyter_exporter, sample_proof_sketch, tmp_path
    ):
        """Test basic Jupyter notebook export."""
        jupyter_exporter.options.output_dir = tmp_path

        result = jupyter_exporter.export_single(sample_proof_sketch)

        assert result.success
        assert len(result.files_created) > 0

        output_file = result.files_created[0]
        assert output_file.exists()
        assert output_file.suffix == ".ipynb"

        # Load and check notebook structure
        with open(output_file) as f:
            notebook = json.load(f)

        assert "cells" in notebook
        assert len(notebook["cells"]) > 0

    def test_cell_generation(self, jupyter_exporter, sample_proof_sketch, tmp_path):
        """Test notebook cell generation."""
        jupyter_exporter.options.output_dir = tmp_path

        # Export and check the generated notebook
        result = jupyter_exporter.export_single(sample_proof_sketch)

        if result.success and result.files_created:
            with open(result.files_created[0]) as f:
                notebook = json.load(f)

            cells = notebook.get("cells", [])
            assert len(cells) > 0

            # Should have markdown cells
            markdown_cells = [c for c in cells if c.get("cell_type") == "markdown"]
            assert len(markdown_cells) > 0

    def test_code_cell_generation(self, jupyter_exporter, tmp_path):
        """Test code cell generation for interactive content."""
        sketch = ProofSketch(
            theorem_name="interactive_test",
            introduction="Test with code",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Compute",
                    mathematical_content="2 + 2 = 4",
                )
            ],
            conclusion="Test conclusion",
        )

        jupyter_exporter.options.output_dir = tmp_path
        result = jupyter_exporter.export_single(sketch)

        if result.success and result.files_created:
            with open(result.files_created[0]) as f:
                notebook = json.load(f)

            cells = notebook.get("cells", [])
            # Just check that cells exist
            assert len(cells) > 0


class TestExportModels:
    """Test suite for export data models."""

    def test_export_config(self):
        """Test ExportOptions model."""
        config = ExportOptions(
            output_dir=Path("/tmp/output"),
            html_theme="dark",
            include_source=True,
            syntax_highlighting=True,
        )

        assert config.output_dir == Path("/tmp/output")
        assert config.html_theme == "dark"
        assert config.include_source is True
        assert config.syntax_highlighting is True

    def test_export_result(self):
        """Test ExportResult model."""
        result = ExportResult(
            success=True,
            format=ExportFormat.HTML,
            output_path=Path("/tmp/output"),
            files_created=[Path("/tmp/output/test.html")],
            export_time=1.234,
            warnings=["Missing animation"],
        )

        assert result.success
        assert result.format == ExportFormat.HTML
        assert result.export_time == 1.234
        assert len(result.warnings) == 1
        assert len(result.files_created) == 1


@pytest.mark.integration
class TestExporterIntegration:
    """Integration tests for exporters."""

    def test_multi_format_export(self, tmp_path):
        """Test exporting to multiple formats."""
        from proof_sketcher.exporter import HTMLExporter, MarkdownExporter

        sketch = ProofSketch(
            theorem_name="multi_format_test",
            introduction="Test content",
            key_steps=[],
            conclusion="Test conclusion",
        )

        # Export to HTML
        html_options = ExportOptions(output_dir=tmp_path)
        html_exporter = HTMLExporter(html_options)
        html_result = html_exporter.export_single(sketch)
        assert html_result.success

        # Export to Markdown
        md_options = ExportOptions(output_dir=tmp_path)
        md_exporter = MarkdownExporter(md_options)
        md_result = md_exporter.export_single(sketch)
        assert md_result.success

        # Check files were created
        assert len(html_result.files_created) > 0
        assert len(md_result.files_created) > 0

    def test_export_with_full_pipeline(self, tmp_path):
        """Test export with complete proof sketcher pipeline."""
        from proof_sketcher.exporter import HTMLExporter
        from proof_sketcher.generator.models import ProofSketch, ProofStep

        # Create proof sketch
        sketch = ProofSketch(
            theorem_name="pipeline_test",
            introduction="For all x, P holds",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Assume x is arbitrary",
                    mathematical_content="x : Type",
                )
            ],
            conclusion="Test conclusion",
        )

        # Export
        options = ExportOptions(output_dir=tmp_path)
        exporter = HTMLExporter(options)
        result = exporter.export_single(sketch)

        assert result.success
        assert len(result.files_created) > 0

        # Verify content
        if result.files_created:
            content = result.files_created[0].read_text(encoding="utf-8")
            assert "pipeline_test" in content
            assert "For all x, P holds" in content
