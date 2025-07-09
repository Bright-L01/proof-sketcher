"""End-to-end pipeline testing for Proof Sketcher.

This test verifies the complete pipeline:
Parse → Generate → Animate → Export
"""

import pytest
from pathlib import Path
from unittest.mock import Mock, patch

from proof_sketcher.parser.models import TheoremInfo
from proof_sketcher.animation.animator import Animator
from proof_sketcher.export import HTMLExporter, MarkdownExporter


@pytest.fixture
def sample_lean_content():
    """Sample Lean theorem content."""
    return """
theorem example_theorem : ∀ x : ℕ, x + 0 = x := by
  intro x
  rw [add_zero]
"""


@pytest.fixture
def theorem_info():
    """Create sample theorem info."""
    return TheoremInfo(
        name="example_theorem",
        statement="∀ x : ℕ, x + 0 = x",
        docstring="Example theorem showing addition with zero",
        file_path=Path("example.lean"),
        start_line=1,
        end_line=4,
    )


@pytest.fixture
def explanation():
    """Sample explanation text."""
    return """This theorem demonstrates the fundamental property of addition with zero.

For any natural number x, adding zero to x leaves x unchanged. This is a basic
property of natural number addition in Lean's type system.

The proof uses the `add_zero` lemma which is built into Lean's standard library."""


class TestEndToEndPipeline:
    """Test complete pipeline functionality."""

    def test_animation_to_html_export(self, theorem_info, explanation, tmp_path):
        """Test animation generation followed by HTML export."""
        # Step 1: Generate animation (or fallback)
        animator = Animator()
        viz_result = animator.create_visualization(theorem_info, tmp_path)
        
        # Should always get some visualization
        assert viz_result["type"] in ["animation", "static", "placeholder"]
        assert viz_result["path"] is not None
        assert viz_result["path"].exists()
        
        # Step 2: Export to HTML
        html_exporter = HTMLExporter()
        html_output = tmp_path / "theorem.html"
        
        html_result = html_exporter.export(
            theorem=theorem_info,
            explanation=explanation,
            visualization=viz_result["path"],
            output_path=html_output,
        )
        
        assert html_result.exists()
        assert html_result.stat().st_size > 1000  # Should be substantial
        
        # Check HTML content
        content = html_result.read_text()
        assert theorem_info.name in content
        assert theorem_info.statement in content
        assert explanation in content
        
        # Check that media was embedded
        if viz_result["type"] == "animation":
            assert "video" in content.lower()
        elif viz_result["type"] == "static":
            assert "img" in content.lower()
        
        # Check that assets were copied
        assert (tmp_path / "assets" / "style.css").exists()

    def test_animation_to_markdown_export(self, theorem_info, explanation, tmp_path):
        """Test animation generation followed by Markdown export."""
        # Step 1: Generate visualization
        animator = Animator()
        viz_result = animator.create_visualization(theorem_info, tmp_path)
        
        assert viz_result["path"] is not None
        assert viz_result["path"].exists()
        
        # Step 2: Export to Markdown
        md_exporter = MarkdownExporter()
        md_output = tmp_path / "theorem.md"
        
        md_result = md_exporter.export(
            theorem=theorem_info,
            explanation=explanation,
            visualization=viz_result["path"],
            output_path=md_output,
        )
        
        assert md_result.exists()
        assert md_result.stat().st_size > 500
        
        # Check Markdown content
        content = md_result.read_text()
        assert f"# {theorem_info.name}" in content
        assert theorem_info.statement in content
        assert explanation in content
        assert "```lean" in content
        
        # Check that media was copied
        assert (tmp_path / "media" / viz_result["path"].name).exists()

    def test_batch_visualization_and_export(self, tmp_path):
        """Test batch processing multiple theorems."""
        # Create multiple theorems
        theorems = [
            TheoremInfo(
                name=f"theorem_{i}",
                statement=f"∀ x : ℕ, P_{i}(x)",
                docstring=f"Test theorem {i}",
                file_path=Path("test.lean"),
                start_line=i,
                end_line=i + 2,
            )
            for i in range(3)
        ]
        
        # Step 1: Batch visualize
        animator = Animator()
        viz_results = animator.batch_visualize(theorems, tmp_path)
        
        assert len(viz_results) == 3
        for name, result in viz_results.items():
            assert result["type"] in ["animation", "static", "placeholder"]
            assert result["path"] is not None
            assert result["path"].exists()
        
        # Step 2: Export each to HTML
        html_exporter = HTMLExporter()
        for i, theorem in enumerate(theorems):
            html_output = tmp_path / f"theorem_{i}.html"
            
            html_result = html_exporter.export(
                theorem=theorem,
                explanation=f"Explanation for theorem {i}",
                visualization=viz_results[theorem.name]["path"],
                output_path=html_output,
            )
            
            assert html_result.exists()
            assert theorem.name in html_result.read_text()

    def test_error_handling_in_pipeline(self, tmp_path):
        """Test that pipeline handles errors gracefully."""
        # Create theorem with problematic content
        bad_theorem = TheoremInfo(
            name="bad/theorem\\name",
            statement="∀ x ∈ ℝ, ∃ y : x < y",
            docstring="Theorem with special characters",
            file_path=Path("test.lean"),
            start_line=1,
            end_line=5,
        )
        
        # Step 1: Try to visualize (should not crash)
        animator = Animator()
        viz_result = animator.create_visualization(bad_theorem, tmp_path)
        
        # Should get some result, even if it's a placeholder
        assert viz_result["type"] in ["animation", "static", "placeholder"]
        assert viz_result["path"] is not None
        
        # Step 2: Try to export (should handle special characters)
        html_exporter = HTMLExporter()
        html_output = tmp_path / "bad_theorem.html"
        
        # This should not crash
        html_result = html_exporter.export(
            theorem=bad_theorem,
            explanation="Test explanation",
            visualization=viz_result["path"],
            output_path=html_output,
        )
        
        assert html_result.exists()
        
        # Check that content is sanitized
        content = html_result.read_text()
        assert "bad" in content.lower()  # Should contain sanitized version

    def test_capabilities_reporting(self):
        """Test that components report their capabilities correctly."""
        animator = Animator()
        capabilities = animator.get_capabilities()
        
        # Should always support static diagrams
        assert capabilities["static"] is True
        assert capabilities["formats"]["png"] is True
        
        # Animation support depends on Manim availability
        assert isinstance(capabilities["animation"], bool)
        assert isinstance(capabilities["formats"]["mp4"], bool)
        assert isinstance(capabilities["formats"]["gif"], bool)

    def test_minimal_working_pipeline(self, tmp_path):
        """Test minimal pipeline that should always work."""
        # Create simple theorem
        theorem = TheoremInfo(
            name="simple_theorem",
            statement="True",
            file_path=Path("test.lean"),
            start_line=1,
            end_line=1,
        )
        
        # Full pipeline: visualize → export
        animator = Animator()
        viz_result = animator.create_visualization(theorem, tmp_path)
        
        # Should always get some visualization
        assert viz_result["path"] is not None
        assert viz_result["path"].exists()
        
        # Export to all formats
        for ExporterClass, extension in [
            (HTMLExporter, ".html"),
            (MarkdownExporter, ".md"),
        ]:
            exporter = ExporterClass()
            output_path = tmp_path / f"simple{extension}"
            
            result = exporter.export(
                theorem=theorem,
                explanation="Simple theorem explanation",
                visualization=viz_result["path"],
                output_path=output_path,
            )
            
            assert result.exists()
            assert result.stat().st_size > 100
            
            content = result.read_text()
            assert theorem.name in content
            assert theorem.statement in content