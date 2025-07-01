"""Comprehensive tests for Markdown exporter."""

import tempfile
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.exporter.markdown import MarkdownExporter
from proof_sketcher.exporter.models import ExportContext, ExportFormat, ExportOptions, ExportResult
from proof_sketcher.generator.models import ProofSketch, ProofStep


class TestMarkdownExporter:
    """Test suite for Markdown exporter."""

    @pytest.fixture
    def exporter(self, tmp_path):
        """Create a MarkdownExporter instance."""
        options = ExportOptions(
            output_dir=tmp_path,
            include_metadata=True
        )
        return MarkdownExporter(options)

    @pytest.fixture
    def sample_proof_sketch(self):
        """Create a sample proof sketch."""
        return ProofSketch(
            theorem_name="nat_add_comm",
            introduction="This theorem states that natural number addition is commutative.",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Base case: prove for n = 0",
                    tactics=["simp"],
                    mathematical_content="0 + m = m = m + 0",
                    intuition="Zero is the additive identity"
                ),
                ProofStep(
                    step_number=2,
                    description="Inductive step: assume for n, prove for n + 1",
                    tactics=["induction", "simp"],
                    mathematical_content="(n + 1) + m = (m + n) + 1",
                    intuition="Use the inductive hypothesis and associativity"
                ),
            ],
            conclusion="Therefore, addition is commutative for all natural numbers.",
            difficulty_level="beginner",
            mathematical_areas=["algebra", "number theory"],
            prerequisites=["natural numbers", "induction"],
        )

    def test_exporter_initialization(self, tmp_path):
        """Test exporter initialization."""
        options = ExportOptions(output_dir=tmp_path)
        exporter = MarkdownExporter(options)
        
        assert exporter.options == options
        assert exporter.format == ExportFormat.MARKDOWN

    def test_export_single_basic(self, exporter, sample_proof_sketch, tmp_path):
        """Test basic single proof export."""
        result = exporter.export_single(sample_proof_sketch)
        
        assert result.success
        assert len(result.files_created) > 0
        
        # Check that at least one markdown file was created
        md_files = list(tmp_path.glob("*.md"))
        assert len(md_files) > 0
        
        # Check content of the first markdown file
        content = md_files[0].read_text()
        assert "nat_add_comm" in content
        assert "natural number addition is commutative" in content

    def test_export_single_with_context(self, exporter, sample_proof_sketch, tmp_path):
        """Test export with custom context."""
        context = ExportContext(
            format=ExportFormat.MARKDOWN,
            output_dir=tmp_path,
            author="Test Author",
            version="1.0.0",
            include_timestamps=True
        )
        
        result = exporter.export_single(sample_proof_sketch, context=context)
        
        assert result.success
        
        # Find the created markdown file
        md_files = list(tmp_path.glob("*.md"))
        assert len(md_files) > 0

    def test_export_multiple(self, exporter, sample_proof_sketch, tmp_path):
        """Test batch export of multiple proofs."""
        proof2 = ProofSketch(
            theorem_name="nat_mul_comm",
            introduction="Multiplication is also commutative.",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Similar proof structure",
                    tactics=["simp"],
                    mathematical_content="a * b = b * a",
                )
            ],
            conclusion="QED",
        )
        
        result = exporter.export_multiple([sample_proof_sketch, proof2])
        
        assert result.success
        assert len(result.files_created) >= 2  # At least 2 theorem files
        
        # Check files exist
        md_files = list(tmp_path.glob("*.md"))
        assert len(md_files) >= 2

    def test_export_with_animation(self, exporter, sample_proof_sketch, tmp_path):
        """Test export with animation link."""
        # Create context with animation
        animation_path = tmp_path / "animations" / "nat_add_comm.mp4"
        animation_path.parent.mkdir(exist_ok=True)
        animation_path.write_text("fake video")
        
        context = ExportContext(
            format=ExportFormat.MARKDOWN,
            output_dir=tmp_path,
            animations={"nat_add_comm": animation_path}
        )
        
        result = exporter.export_single(sample_proof_sketch, context=context)
        
        assert result.success

    def test_export_error_handling(self, exporter, sample_proof_sketch):
        """Test error handling during export."""
        # Mock the _export_sketch method to raise an error
        with patch.object(exporter, '_export_sketch', side_effect=Exception("Export failed")):
            result = exporter.export_single(sample_proof_sketch)
            
        assert not result.success
        assert len(result.errors) > 0
        assert "Export failed" in str(result.errors[0])

    def test_format_markdown_options(self, tmp_path):
        """Test markdown-specific formatting options."""
        options = ExportOptions(
            output_dir=tmp_path,
            markdown_flavor="github",
            markdown_math_style="katex",
            markdown_collapsible_proofs=True
        )
        exporter = MarkdownExporter(options)
        
        assert exporter.options.markdown_flavor == "github"
        assert exporter.options.markdown_math_style == "katex"
        assert exporter.options.markdown_collapsible_proofs is True

    def test_filename_generation(self, exporter, tmp_path):
        """Test filename generation with special characters."""
        sketch = ProofSketch(
            theorem_name="theorem:with/special<chars>",
            introduction="Test",
            key_steps=[],
            conclusion="QED"
        )
        
        result = exporter.export_single(sketch)
        
        assert result.success
        # Check that file was created with sanitized name
        md_files = list(tmp_path.glob("*.md"))
        assert len(md_files) > 0
        # Filename should not contain special characters
        for f in md_files:
            assert "/" not in f.name
            assert ":" not in f.name
            assert "<" not in f.name

    def test_parallel_export(self, tmp_path):
        """Test parallel export of multiple sketches."""
        options = ExportOptions(
            output_dir=tmp_path,
            parallel_export=True
        )
        exporter = MarkdownExporter(options)
        
        # Create multiple sketches
        sketches = []
        for i in range(5):
            sketch = ProofSketch(
                theorem_name=f"theorem_{i}",
                introduction=f"Theorem {i}",
                key_steps=[],
                conclusion="Done"
            )
            sketches.append(sketch)
        
        result = exporter.export_multiple(sketches)
        
        assert result.success
        assert len(result.files_created) >= 5

    def test_export_with_metadata(self, tmp_path):
        """Test export with metadata options."""
        options = ExportOptions(
            output_dir=tmp_path,
            include_source=True,
            include_dependencies=True,
            include_timestamps=True
        )
        exporter = MarkdownExporter(options)
        
        sketch = ProofSketch(
            theorem_name="test_theorem",
            introduction="Test with metadata",
            key_steps=[],
            conclusion="Done",
            mathematical_areas=["test"],
            prerequisites=["basics"]
        )
        
        result = exporter.export_single(sketch)
        assert result.success

    def test_export_minimal_sketch(self, exporter):
        """Test export of minimal proof sketch."""
        sketch = ProofSketch(
            theorem_name="minimal",
            introduction="",
            key_steps=[],
            conclusion=""
        )
        
        result = exporter.export_single(sketch)
        assert result.success

    def test_export_with_complex_content(self, exporter, tmp_path):
        """Test export with complex mathematical content."""
        sketch = ProofSketch(
            theorem_name="complex_theorem",
            introduction="Contains $\\LaTeX$ math: $\\int_0^1 f(x) dx$",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Step with inline $math$ and display $$\\sum_{i=1}^n i^2$$",
                    mathematical_content="$\\forall x \\in \\mathbb{R}: x^2 \\geq 0$",
                    tactics=["complex_tactic"]
                )
            ],
            conclusion="Thus $\\square$"
        )
        
        result = exporter.export_single(sketch)
        assert result.success
        
        # Check that LaTeX is preserved
        md_files = list(tmp_path.glob("*.md"))
        content = md_files[0].read_text()
        assert "$" in content
        assert "\\int" in content or "int" in content
        assert "\\forall" in content or "forall" in content