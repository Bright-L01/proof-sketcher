"""Tests for all export formats."""

import pytest
from pathlib import Path
from unittest.mock import Mock, patch

from proof_sketcher.export import HTMLExporter, MarkdownExporter, PDFExporter
from proof_sketcher.parser.models import TheoremInfo


@pytest.fixture
def theorem():
    """Create a test theorem."""
    return TheoremInfo(
        name="test_theorem",
        statement="For all x, P(x) → Q(x)",
        docstring="A test theorem for demonstration",
        file_path=Path("test.lean"),
        start_line=1,
        end_line=5,
    )


@pytest.fixture
def explanation():
    """Test explanation text."""
    return """This theorem states that for all x, if P(x) is true, then Q(x) is also true.

This is a basic logical implication that demonstrates the relationship between
two predicates P and Q across all elements in the domain."""


@pytest.fixture
def temp_visualization(tmp_path):
    """Create a temporary visualization file."""
    viz_path = tmp_path / "test_viz.png"
    viz_path.write_text("fake image content")
    return viz_path


class TestHTMLExporter:
    """Test HTML export functionality."""

    def test_export_without_visualization(self, theorem, explanation, tmp_path):
        """Test HTML export without visualization."""
        exporter = HTMLExporter()
        output_path = tmp_path / "test.html"
        
        result = exporter.export(
            theorem=theorem,
            explanation=explanation,
            visualization=None,
            output_path=output_path,
        )
        
        assert result == output_path
        assert output_path.exists()
        assert output_path.stat().st_size > 100
        
        content = output_path.read_text()
        assert theorem.name in content
        assert theorem.statement in content
        assert explanation in content
        assert "MathJax" in content
        assert "css" in content.lower()

    def test_export_with_visualization(self, theorem, explanation, temp_visualization, tmp_path):
        """Test HTML export with visualization."""
        exporter = HTMLExporter()
        output_path = tmp_path / "test.html"
        
        result = exporter.export(
            theorem=theorem,
            explanation=explanation,
            visualization=temp_visualization,
            output_path=output_path,
        )
        
        assert result == output_path
        assert output_path.exists()
        
        # Check that visualization was copied
        media_dir = tmp_path / "media"
        assert media_dir.exists()
        assert (media_dir / temp_visualization.name).exists()
        
        content = output_path.read_text()
        assert f"media/{temp_visualization.name}" in content
        assert "visualization" in content.lower()

    def test_assets_copied(self, theorem, explanation, tmp_path):
        """Test that CSS assets are copied."""
        exporter = HTMLExporter()
        output_path = tmp_path / "test.html"
        
        exporter.export(
            theorem=theorem,
            explanation=explanation,
            visualization=None,
            output_path=output_path,
        )
        
        assets_dir = tmp_path / "assets"
        assert assets_dir.exists()
        assert (assets_dir / "style.css").exists()


class TestMarkdownExporter:
    """Test Markdown export functionality."""

    def test_export_without_visualization(self, theorem, explanation, tmp_path):
        """Test Markdown export without visualization."""
        exporter = MarkdownExporter()
        output_path = tmp_path / "test.md"
        
        result = exporter.export(
            theorem=theorem,
            explanation=explanation,
            visualization=None,
            output_path=output_path,
        )
        
        assert result == output_path
        assert output_path.exists()
        assert output_path.stat().st_size > 100
        
        content = output_path.read_text()
        assert f"# {theorem.name}" in content
        assert theorem.statement in content
        assert explanation in content
        assert "```lean" in content
        assert "Generated on" in content

    def test_export_with_visualization(self, theorem, explanation, temp_visualization, tmp_path):
        """Test Markdown export with visualization."""
        exporter = MarkdownExporter()
        output_path = tmp_path / "test.md"
        
        result = exporter.export(
            theorem=theorem,
            explanation=explanation,
            visualization=temp_visualization,
            output_path=output_path,
        )
        
        assert result == output_path
        assert output_path.exists()
        
        # Check that visualization was copied
        media_dir = tmp_path / "media"
        assert media_dir.exists()
        assert (media_dir / temp_visualization.name).exists()
        
        content = output_path.read_text()
        assert f"![Proof diagram](media/{temp_visualization.name})" in content
        assert "## Visualization" in content

    def test_export_with_video_visualization(self, theorem, explanation, tmp_path):
        """Test Markdown export with video visualization."""
        # Create fake video file
        video_path = tmp_path / "test_viz.mp4"
        video_path.write_text("fake video content")
        
        exporter = MarkdownExporter()
        output_path = tmp_path / "test.md"
        
        result = exporter.export(
            theorem=theorem,
            explanation=explanation,
            visualization=video_path,
            output_path=output_path,
        )
        
        content = output_path.read_text()
        assert f"[View animation](media/{video_path.name})" in content
        assert "Click the link above" in content

    def test_export_index(self, tmp_path):
        """Test index export functionality."""
        theorems = [
            TheoremInfo(
                name="theorem1",
                statement="statement1",
                docstring="First theorem",
                file_path=Path("test1.lean"),
                start_line=1,
                end_line=5,
            ),
            TheoremInfo(
                name="theorem2",
                statement="statement2",
                docstring="Second theorem",
                file_path=Path("test2.lean"),
                start_line=10,
                end_line=15,
            ),
        ]
        
        exporter = MarkdownExporter()
        output_path = tmp_path / "index.md"
        
        result = exporter.export_index(theorems, output_path)
        
        assert result == output_path
        assert output_path.exists()
        
        content = output_path.read_text()
        assert "# Theorem Documentation Index" in content
        assert "theorem1" in content
        assert "theorem2" in content
        assert "| Theorem | Description | Source |" in content


class TestPDFExporter:
    """Test PDF export functionality."""

    def test_latex_not_available(self, theorem, explanation, tmp_path):
        """Test PDF export when LaTeX is not available."""
        with patch.object(PDFExporter, "_check_latex", return_value=False):
            exporter = PDFExporter()
            output_path = tmp_path / "test.pdf"
            
            with pytest.raises(RuntimeError, match="LaTeX is not available"):
                exporter.export(
                    theorem=theorem,
                    explanation=explanation,
                    visualization=None,
                    output_path=output_path,
                )

    def test_latex_available_but_compilation_fails(self, theorem, explanation, tmp_path):
        """Test PDF export when LaTeX is available but compilation fails."""
        with patch.object(PDFExporter, "_check_latex", return_value=True):
            with patch("subprocess.run") as mock_run:
                mock_run.return_value = Mock(returncode=1, stderr="LaTeX error")
                
                exporter = PDFExporter()
                output_path = tmp_path / "test.pdf"
                
                with pytest.raises(RuntimeError, match="PDF compilation failed"):
                    exporter.export(
                        theorem=theorem,
                        explanation=explanation,
                        visualization=None,
                        output_path=output_path,
                    )

    def test_create_latex_content(self, theorem, explanation):
        """Test LaTeX content creation."""
        exporter = PDFExporter()
        latex_content = exporter._create_latex(theorem, explanation, None)
        
        assert "\\documentclass" in latex_content
        assert theorem.name.replace("_", "\\_") in latex_content  # LaTeX escapes underscores
        assert theorem.statement in latex_content
        assert explanation in latex_content
        assert "\\begin{document}" in latex_content
        assert "\\end{document}" in latex_content

    def test_latex_escaping(self, tmp_path):
        """Test that special LaTeX characters are properly escaped."""
        theorem = TheoremInfo(
            name="test_theorem_with_$pecial_chars",
            statement="For all x: P(x) & Q(x) → R(x) % comment",
            file_path=Path("test.lean"),
            start_line=1,
            end_line=5,
        )
        
        exporter = PDFExporter()
        latex_content = exporter._create_latex(theorem, "Test & explanation", None)
        
        # Check that special characters are escaped
        assert "\\$" in latex_content
        assert "\\&" in latex_content
        assert "\\%" in latex_content


@pytest.mark.parametrize("exporter_class,extension", [
    (HTMLExporter, ".html"),
    (MarkdownExporter, ".md"),
])
def test_export_formats_consistency(exporter_class, extension, theorem, explanation, tmp_path):
    """Test that all export formats include required elements."""
    exporter = exporter_class()
    output_path = tmp_path / f"test{extension}"
    
    result = exporter.export(
        theorem=theorem,
        explanation=explanation,
        visualization=None,
        output_path=output_path,
    )
    
    assert result == output_path
    assert output_path.exists()
    assert output_path.stat().st_size > 100
    
    content = output_path.read_text()
    assert theorem.name in content
    assert theorem.statement in content
    assert explanation in content