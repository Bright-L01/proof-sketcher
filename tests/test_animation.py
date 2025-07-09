"""Tests for animation system with fallback."""

import pytest
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock
import subprocess

from proof_sketcher.animation.animator import Animator
from proof_sketcher.animation.manim_generator import ManimGenerator
from proof_sketcher.animation.static_generator import StaticDiagramGenerator
from proof_sketcher.parser.models import TheoremInfo


@pytest.fixture
def theorem():
    """Create a test theorem."""
    return TheoremInfo(
        name="test_theorem",
        statement="For all x, P(x) implies Q(x)",
        file_path=Path("test.lean"),
        start_line=1,
        end_line=5,
    )


@pytest.fixture
def temp_dir(tmp_path):
    """Create a temporary directory for tests."""
    return tmp_path / "test_animations"


class TestManimGenerator:
    """Test Manim generator functionality."""

    def test_check_manim_available(self, mocker):
        """Test Manim availability check when available."""
        mock_run = mocker.patch("subprocess.run")
        mock_run.return_value = Mock(returncode=0, stdout="Manim version 0.17.3")

        generator = ManimGenerator()
        assert generator.manim_available is True

    def test_check_manim_unavailable(self, mocker):
        """Test Manim availability check when unavailable."""
        mock_run = mocker.patch("subprocess.run")
        mock_run.side_effect = FileNotFoundError("manim not found")

        generator = ManimGenerator()
        assert generator.manim_available is False

    def test_generate_animation_success(self, mocker, theorem, temp_dir):
        """Test successful animation generation."""
        generator = ManimGenerator()
        generator.manim_available = True

        # Mock subprocess to simulate successful Manim run
        mock_run = mocker.patch("subprocess.run")
        mock_run.return_value = Mock(returncode=0)

        output_path = temp_dir / "test.mp4"
        
        # Create fake output file
        temp_dir.mkdir(parents=True, exist_ok=True)
        output_path.touch()

        result = generator.generate_animation(theorem, output_path)
        
        assert result == output_path
        assert mock_run.called

    def test_generate_animation_timeout(self, mocker, theorem, temp_dir):
        """Test animation generation with timeout."""
        generator = ManimGenerator()
        generator.manim_available = True

        # Mock subprocess to simulate timeout
        mock_run = mocker.patch("subprocess.run")
        mock_run.side_effect = subprocess.TimeoutExpired("manim", 30)

        output_path = temp_dir / "test.mp4"
        result = generator.generate_animation(theorem, output_path)
        
        assert result is None

    def test_escape_latex(self):
        """Test LaTeX escaping."""
        generator = ManimGenerator()
        
        test_cases = [
            ("simple text", "simple text"),
            ("text_with_underscore", "text\\_with\\_underscore"),
            ("math $x^2$", "math \\$x\\^2\\$"),
            ("braces {test}", "braces \\{test\\}"),
        ]
        
        for input_text, expected in test_cases:
            assert generator._escape_latex(input_text) == expected


class TestStaticDiagramGenerator:
    """Test static diagram generator functionality."""

    def test_generate_diagram_success(self, mocker, theorem, temp_dir):
        """Test successful static diagram generation."""
        # Mock matplotlib to avoid actual plotting
        mock_savefig = mocker.patch("matplotlib.pyplot.savefig")
        mock_close = mocker.patch("matplotlib.pyplot.close")

        generator = StaticDiagramGenerator()
        output_path = temp_dir / "test.png"
        
        # Create output file
        temp_dir.mkdir(parents=True, exist_ok=True)
        output_path.touch()

        result = generator.generate_diagram(theorem, output_path)
        
        assert result == output_path
        assert mock_savefig.called
        assert mock_close.called

    def test_wrap_text(self):
        """Test text wrapping functionality."""
        generator = StaticDiagramGenerator()
        
        # Test short text
        short_text = "Short text"
        assert generator._wrap_text(short_text, 20) == short_text
        
        # Test long text
        long_text = "This is a very long text that needs to be wrapped at the specified width"
        wrapped = generator._wrap_text(long_text, 20)
        lines = wrapped.split("\n")
        assert all(len(line) <= 20 for line in lines)
        
        # Test very long text (should be truncated)
        very_long = "x" * 500
        wrapped = generator._wrap_text(very_long, 50)
        assert wrapped.endswith("...")
        assert len(wrapped) <= 310  # 300 chars + ellipsis + newlines

    def test_truncate_text(self):
        """Test text truncation."""
        generator = StaticDiagramGenerator()
        
        assert generator._truncate_text("short", 10) == "short"
        assert generator._truncate_text("very long text", 10) == "very lo..."


class TestAnimator:
    """Test unified animator interface."""

    def test_animation_with_manim_available(self, mocker, theorem, temp_dir):
        """Test when Manim is available and works."""
        # Mock Manim generator
        mock_manim = Mock()
        mock_manim.manim_available = True
        mock_manim.generate_animation.return_value = temp_dir / "test.mp4"
        
        # Create the output file
        temp_dir.mkdir(parents=True, exist_ok=True)
        (temp_dir / "test.mp4").touch()

        animator = Animator()
        animator.manim = mock_manim

        result = animator.create_visualization(theorem, temp_dir)
        
        assert result["type"] == "animation"
        assert result["path"] == temp_dir / "test.mp4"
        assert result["error"] is None
        assert mock_manim.generate_animation.called

    def test_fallback_to_static(self, mocker, theorem, temp_dir):
        """Test fallback when Manim unavailable."""
        # Mock Manim as unavailable
        mock_manim = Mock()
        mock_manim.manim_available = False
        
        # Mock static generator
        mock_static = Mock()
        mock_static.generate_diagram.return_value = temp_dir / "test.png"

        animator = Animator()
        animator.manim = mock_manim
        animator.static = mock_static

        result = animator.create_visualization(theorem, temp_dir)
        
        assert result["type"] == "static"
        assert result["path"] == temp_dir / "test.png"
        assert not mock_manim.generate_animation.called
        assert mock_static.generate_diagram.called

    def test_animation_fails_fallback_to_static(self, mocker, theorem, temp_dir):
        """Test fallback when animation fails."""
        # Mock Manim that fails
        mock_manim = Mock()
        mock_manim.manim_available = True
        mock_manim.generate_animation.return_value = None
        
        # Mock static generator
        mock_static = Mock()
        mock_static.generate_diagram.return_value = temp_dir / "test.png"

        animator = Animator()
        animator.manim = mock_manim
        animator.static = mock_static

        result = animator.create_visualization(theorem, temp_dir)
        
        assert result["type"] == "static"
        assert result["path"] == temp_dir / "test.png"
        assert mock_manim.generate_animation.called
        assert mock_static.generate_diagram.called

    def test_both_fail_creates_placeholder(self, mocker, theorem, temp_dir):
        """Test placeholder creation when both methods fail."""
        # Mock both generators to fail
        mock_manim = Mock()
        mock_manim.manim_available = True
        mock_manim.generate_animation.side_effect = Exception("Manim error")
        
        mock_static = Mock()
        mock_static.generate_diagram.side_effect = Exception("Static error")

        animator = Animator()
        animator.manim = mock_manim
        animator.static = mock_static

        result = animator.create_visualization(theorem, temp_dir)
        
        assert result["type"] == "placeholder"
        assert result["path"].name == "test_theorem_placeholder.txt"
        assert result["error"] is not None
        assert result["path"].exists()

    def test_batch_visualize(self, mocker, temp_dir):
        """Test batch visualization."""
        theorems = [
            TheoremInfo(name=f"theorem_{i}", statement=f"Statement {i}", 
                       file_path=Path("test.lean"), start_line=i, end_line=i+1)
            for i in range(3)
        ]

        # Mock successful static generation
        mock_static = Mock()
        mock_static.generate_diagram.side_effect = [
            temp_dir / f"theorem_{i}.png" for i in range(3)
        ]

        animator = Animator()
        animator.manim.manim_available = False
        animator.static = mock_static

        results = animator.batch_visualize(theorems, temp_dir)
        
        assert len(results) == 3
        assert all(r["type"] == "static" for r in results.values())
        assert mock_static.generate_diagram.call_count == 3

    def test_get_capabilities(self):
        """Test capability reporting."""
        animator = Animator()
        
        # Mock Manim availability
        animator.manim.manim_available = True
        
        capabilities = animator.get_capabilities()
        
        assert capabilities["animation"] is True
        assert capabilities["static"] is True
        assert capabilities["formats"]["png"] is True
        assert capabilities["formats"]["mp4"] is True


@pytest.mark.integration
class TestAnimationIntegration:
    """Integration tests for the animation system."""

    def test_full_pipeline(self, theorem, temp_dir):
        """Test the full animation pipeline."""
        animator = Animator()
        
        # Create visualization
        result = animator.create_visualization(
            theorem, temp_dir, prefer_animation=True
        )
        
        # Should always get some visualization
        assert result["type"] in ["animation", "static", "placeholder"]
        assert result["path"] is not None
        assert result["path"].exists()

    def test_error_recovery(self, temp_dir):
        """Test error recovery in animation pipeline."""
        # Create theorem with problematic characters
        bad_theorem = TheoremInfo(
            name="bad/theorem\\name",
            statement="∀ x ∈ ℝ, ∃ y : x < y",
            file_path=Path("test.lean"),
            start_line=1,
            end_line=2,
        )
        
        animator = Animator()
        result = animator.create_visualization(bad_theorem, temp_dir)
        
        # Should handle the bad characters gracefully
        assert result["path"] is not None
        assert result["type"] in ["animation", "static", "placeholder"]