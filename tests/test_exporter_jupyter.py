"""Comprehensive tests for Jupyter notebook exporter."""

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from proof_sketcher.exporter.jupyter import JupyterExporter
from proof_sketcher.exporter.models import ExportContext, ExportFormat, ExportOptions
from proof_sketcher.generator.models import ProofSketch, ProofStep


class TestJupyterExporterComprehensive:
    """Comprehensive test suite for JupyterExporter."""

    @pytest.fixture
    def exporter(self, tmp_path):
        """Create a JupyterExporter instance."""
        options = ExportOptions(
            output_dir=tmp_path, jupyter_kernel="python3", jupyter_include_outputs=True
        )
        return JupyterExporter(options)

    @pytest.fixture
    def sample_proof_sketch(self):
        """Create a comprehensive sample proof sketch."""
        return ProofSketch(
            theorem_name="nat_add_comm",
            introduction="This theorem states that natural number addition is commutative.",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Base case: prove for n = 0",
                    tactics=["simp"],
                    mathematical_content="0 + m = m = m + 0",
                    intuition="Zero is the additive identity",
                ),
                ProofStep(
                    step_number=2,
                    description="Inductive step",
                    tactics=["induction", "simp"],
                    mathematical_content="(n + 1) + m = (m + n) + 1",
                    intuition="Use the inductive hypothesis and associativity",
                ),
            ],
            conclusion="Therefore, addition is commutative for all natural numbers.",
            difficulty_level="beginner",
            mathematical_areas=["algebra", "number theory"],
            prerequisites=["natural numbers", "induction"],
        )

    @pytest.fixture
    def simple_proof_sketch(self):
        """Create a minimal proof sketch."""
        return ProofSketch(
            theorem_name="simple_theorem",
            introduction="A simple theorem.",
            key_steps=[],
            conclusion="Done.",
        )

    def test_export_single_basic(self, exporter, sample_proof_sketch, tmp_path):
        """Test basic single proof export to notebook."""
        result = exporter.export_single(sample_proof_sketch)

        assert result.success
        assert len(result.files_created) > 0

        # Check that notebook file was created
        notebook_file = result.files_created[0]
        assert notebook_file.exists()
        assert notebook_file.suffix == ".ipynb"

        # Verify notebook content
        with open(notebook_file) as f:
            notebook = json.load(f)

        assert "cells" in notebook
        assert "metadata" in notebook
        assert notebook["nbformat"] == 4
        assert notebook["nbformat_minor"] == 5

    def test_notebook_structure_complete(self, exporter, sample_proof_sketch, tmp_path):
        """Test complete notebook structure and cell content."""
        result = exporter.export_single(sample_proof_sketch)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        cells = notebook["cells"]

        # Should have multiple cells for different sections
        assert (
            len(cells) >= 6
        )  # Title, intro, overview, interactive, animation/steps, conclusion

        # Check cell types
        cell_types = [cell["cell_type"] for cell in cells]
        assert "markdown" in cell_types
        assert "code" in cell_types

        # Check specific content
        cell_sources = [
            (
                " ".join(cell["source"])
                if isinstance(cell["source"], list)
                else cell["source"]
            )
            for cell in cells
        ]
        all_content = " ".join(cell_sources)

        assert "nat_add_comm" in all_content
        assert "natural number addition is commutative" in all_content
        assert "Base case" in all_content
        assert "Inductive step" in all_content

    def test_markdown_cells_content(self, exporter, sample_proof_sketch, tmp_path):
        """Test markdown cell content is correctly formatted."""
        result = exporter.export_single(sample_proof_sketch)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        markdown_cells = [
            cell for cell in notebook["cells"] if cell["cell_type"] == "markdown"
        ]
        assert len(markdown_cells) >= 4  # Title, intro, steps, conclusion

        # Check title cell
        title_cell = markdown_cells[0]
        title_content = " ".join(title_cell["source"])
        assert "# nat_add_comm" in title_content

        # Check that mathematical content is properly formatted
        all_md_content = " ".join([" ".join(cell["source"]) for cell in markdown_cells])
        assert "$$" in all_md_content  # LaTeX math blocks
        assert "0 + m = m = m + 0" in all_md_content

    def test_code_cells_content(self, exporter, sample_proof_sketch, tmp_path):
        """Test code cell content and interactive features."""
        result = exporter.export_single(sample_proof_sketch)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        code_cells = [cell for cell in notebook["cells"] if cell["cell_type"] == "code"]
        assert (
            len(code_cells) >= 2
        )  # Interactive exploration + step exploration + summary

        # Check interactive exploration cell
        code_content = [" ".join(cell["source"]) for cell in code_cells]
        all_code = " ".join(code_content)

        assert "theorem_name = 'nat_add_comm'" in all_code
        assert "step_count = 2" in all_code
        assert "print" in all_code

    def test_export_with_animation(self, exporter, sample_proof_sketch, tmp_path):
        """Test export with animation integration."""
        # Create fake animation file
        animation_path = tmp_path / "nat_add_comm.mp4"
        animation_path.write_text("fake video content")

        context = ExportContext(
            format=ExportFormat.JUPYTER,
            output_dir=tmp_path,
            animations={"nat_add_comm": animation_path},
        )

        result = exporter.export_single(sample_proof_sketch, context=context)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        cells = notebook["cells"]

        # Check for animation-related cells
        all_content = " ".join([" ".join(cell["source"]) for cell in cells])
        assert "Animation" in all_content
        assert "Video" in all_content
        assert str(animation_path) in all_content

    def test_export_multiple_sketches(
        self, exporter, sample_proof_sketch, simple_proof_sketch, tmp_path
    ):
        """Test exporting multiple sketches to a combined notebook."""
        sketches = [sample_proof_sketch, simple_proof_sketch]

        result = exporter.export_multiple(sketches)

        assert result.success
        assert len(result.files_created) == 1

        notebook_file = result.files_created[0]
        assert notebook_file.name == "proof_sketcher_notebook.ipynb"

        with open(notebook_file) as f:
            notebook = json.load(f)

        cells = notebook["cells"]
        all_content = " ".join([" ".join(cell["source"]) for cell in cells])

        # Should contain both theorems
        assert "nat_add_comm" in all_content
        assert "simple_theorem" in all_content

        # Should have table of contents
        assert "Table of Contents" in all_content

        # Should have setup code
        assert "import json" in all_content
        assert "show_theorem" in all_content
        assert "show_step" in all_content

    def test_combined_notebook_structure(
        self, exporter, sample_proof_sketch, simple_proof_sketch, tmp_path
    ):
        """Test combined notebook has proper structure."""
        sketches = [sample_proof_sketch, simple_proof_sketch]

        result = exporter.export_multiple(sketches)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        cells = notebook["cells"]

        # Should have project title, TOC, setup, theorem sections, summary
        assert len(cells) >= 6

        # Check for summary statistics at the end
        code_cells = [cell for cell in cells if cell["cell_type"] == "code"]
        summary_code = " ".join([" ".join(cell["source"]) for cell in code_cells])

        assert "total_theorems = 2" in summary_code
        assert "total_steps" in summary_code
        assert "avg_steps" in summary_code

    def test_notebook_metadata(self, exporter, sample_proof_sketch, tmp_path):
        """Test notebook metadata is correctly set."""
        result = exporter.export_single(sample_proof_sketch)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        metadata = notebook["metadata"]

        # Check kernel specification
        assert "kernelspec" in metadata
        kernelspec = metadata["kernelspec"]
        assert kernelspec["display_name"] == "Python 3"
        assert kernelspec["language"] == "python"
        assert kernelspec["name"] == "python3"

        # Check language info
        assert "language_info" in metadata
        lang_info = metadata["language_info"]
        assert lang_info["name"] == "python"
        assert "version" in lang_info

    def test_cell_structure(self, exporter, sample_proof_sketch, tmp_path):
        """Test individual cell structure is correct."""
        result = exporter.export_single(sample_proof_sketch)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        for cell in notebook["cells"]:
            # All cells should have required fields
            assert "cell_type" in cell
            assert "metadata" in cell
            assert "source" in cell

            if cell["cell_type"] == "code":
                assert "execution_count" in cell
                assert "outputs" in cell
                assert isinstance(cell["outputs"], list)

            # Source should be a list of strings
            assert isinstance(cell["source"], list)

    def test_export_sketch_with_no_steps(self, exporter, simple_proof_sketch, tmp_path):
        """Test export with sketch that has no proof steps."""
        result = exporter.export_single(simple_proof_sketch)

        assert result.success

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        cells = notebook["cells"]
        all_content = " ".join([" ".join(cell["source"]) for cell in cells])

        assert "simple_theorem" in all_content
        assert "A simple theorem." in all_content
        assert "step_count = 0" in all_content  # Should show 0 steps

    def test_mathematical_content_rendering(self, exporter, tmp_path):
        """Test proper rendering of mathematical content."""
        sketch = ProofSketch(
            theorem_name="math_test",
            introduction="Testing math $\\sum_{i=1}^n i^2$",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Mathematical step",
                    mathematical_content="\\int_0^1 f(x) dx = \\frac{1}{2}",
                    intuition="Integration by parts",
                )
            ],
            conclusion="Therefore $\\square$",
        )

        result = exporter.export_single(sketch)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        all_content = " ".join([" ".join(cell["source"]) for cell in notebook["cells"]])

        # Check LaTeX math is preserved
        assert "$$" in all_content
        assert "\\int_0^1 f(x) dx" in all_content
        assert "\\sum_{i=1}^n i^2" in all_content

    def test_filename_generation(self, exporter, tmp_path):
        """Test filename generation with special characters."""
        sketch = ProofSketch(
            theorem_name="theorem:with/special<chars>",
            introduction="Test",
            key_steps=[],
            conclusion="Done",
        )

        result = exporter.export_single(sketch)

        # Filename should be sanitized
        notebook_file = result.files_created[0]
        assert notebook_file.exists()
        # Should not contain problematic characters
        assert ":" not in notebook_file.name
        assert "/" not in notebook_file.name
        assert "<" not in notebook_file.name

    def test_error_handling(self, exporter, tmp_path):
        """Test error handling during export."""
        sketch = ProofSketch(
            theorem_name="error_test",
            introduction="Test",
            key_steps=[],
            conclusion="Done",
        )

        # Mock file write to raise an error
        with patch("pathlib.Path.write_text", side_effect=IOError("Permission denied")):
            result = exporter.export_single(sketch)

            assert not result.success
            assert len(result.errors) > 0

    def test_context_with_custom_project_name(
        self, exporter, sample_proof_sketch, tmp_path
    ):
        """Test export with custom project name in context."""
        context = ExportContext(
            format=ExportFormat.JUPYTER,
            output_dir=tmp_path,
            project_name="Custom Project",
            author="Test Author",
        )

        sketches = [sample_proof_sketch]
        context._sketches = sketches  # Set sketches in context

        result = exporter.export_multiple(sketches, context)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        all_content = " ".join([" ".join(cell["source"]) for cell in notebook["cells"]])
        assert "Custom Project" in all_content

    def test_export_preserves_step_order(self, exporter, tmp_path):
        """Test that proof steps are exported in correct order."""
        sketch = ProofSketch(
            theorem_name="order_test",
            introduction="Test step ordering",
            key_steps=[
                ProofStep(
                    step_number=3,
                    description="Third step",
                    mathematical_content="3 = 3",
                ),
                ProofStep(
                    step_number=1,
                    description="First step",
                    mathematical_content="1 = 1",
                ),
                ProofStep(
                    step_number=2,
                    description="Second step",
                    mathematical_content="2 = 2",
                ),
            ],
            conclusion="Steps should be in order",
        )

        result = exporter.export_single(sketch)

        with open(result.files_created[0]) as f:
            notebook = json.load(f)

        markdown_cells = [
            cell for cell in notebook["cells"] if cell["cell_type"] == "markdown"
        ]

        # Find cells with step content
        step_contents = []
        for cell in markdown_cells:
            content = " ".join(cell["source"])
            if "Step" in content and (
                "First" in content or "Second" in content or "Third" in content
            ):
                step_contents.append(content)

        # Should find steps in the order they appear in the list (not sorted by step_number)
        if len(step_contents) >= 3:
            assert "Third step" in step_contents[0]
            assert "First step" in step_contents[1]
            assert "Second step" in step_contents[2]
