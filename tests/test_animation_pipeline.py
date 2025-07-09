"""
Tests for Animation Pipeline

This module tests the complete animation pipeline including Manim integration,
animation generation, and static fallback visualization.
"""

import asyncio
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, Mock, patch

import pytest

from src.proof_sketcher.animator.animation_generator import TheoremAnimator
from src.proof_sketcher.animator.manim_server import ManimMCPServer, get_manim_server
from src.proof_sketcher.animator.static_fallback import StaticVisualizer


class TestManimMCPServer:
    """Test Manim MCP server functionality."""

    def test_server_initialization(self):
        """Test MCP server initialization."""
        server = ManimMCPServer()
        assert server is not None
        assert server.temp_dir.exists()
        assert hasattr(server, "manim_available")

    def test_manim_availability_check(self):
        """Test Manim availability detection."""
        server = ManimMCPServer()
        # Should not crash regardless of Manim availability
        assert isinstance(server.manim_available, bool)

    @patch("subprocess.run")
    def test_manim_available_true(self, mock_run):
        """Test when Manim is available."""
        mock_run.return_value = Mock(returncode=0, stdout="Manim Community v0.17.3")

        server = ManimMCPServer()
        assert server._check_manim_available() is True

    @patch("subprocess.run")
    def test_manim_available_false(self, mock_run):
        """Test when Manim is not available."""
        mock_run.side_effect = FileNotFoundError()

        server = ManimMCPServer()
        assert server._check_manim_available() is False

    def test_sync_animation_creation_no_manim(self):
        """Test synchronous animation creation when Manim unavailable."""
        with patch.object(ManimMCPServer, "_check_manim_available", return_value=False):
            server = ManimMCPServer()

            result = server.create_animation_sync("test script", "output.mp4")

            assert result["success"] is False
            assert "Manim not available" in result["error"]
            assert result.get("fallback_recommended") is True

    @pytest.mark.asyncio
    async def test_async_animation_creation_no_manim(self):
        """Test async animation creation when Manim unavailable."""
        with patch.object(ManimMCPServer, "_check_manim_available", return_value=False):
            server = ManimMCPServer()

            result = await server._create_animation_impl("test script", "output.mp4")

            assert result["success"] is False
            assert "Manim not available" in result["error"]

    def test_cleanup(self):
        """Test server cleanup functionality."""
        server = ManimMCPServer()

        # Create some test files
        test_file = server.temp_dir / "manim_scene_test.py"
        test_file.write_text("test content")

        # Cleanup should not crash
        server.cleanup()
        # File should be cleaned up
        assert not test_file.exists()

    def test_global_server_instance(self):
        """Test global server instance getter."""
        server1 = get_manim_server()
        server2 = get_manim_server()

        # Should return same instance
        assert server1 is server2


class TestTheoremAnimator:
    """Test theorem animation generation."""

    def test_animator_initialization(self):
        """Test animator initialization."""
        animator = TheoremAnimator()
        assert animator is not None
        assert hasattr(animator, "default_timings")
        assert hasattr(animator, "colors")

    def test_safe_class_name_generation(self):
        """Test safe class name generation."""
        animator = TheoremAnimator()

        # Normal theorem name
        assert animator._safe_class_name("Nat.add_comm") == "NatAddComm"

        # Name with special characters
        assert animator._safe_class_name("test-theorem!@#") == "TestTheorem"

        # Name starting with number
        assert animator._safe_class_name("2_theorem") == "Theorem2Theorem"

        # Empty name
        assert animator._safe_class_name("") == "TheoremAnimation"

        # Very long name
        long_name = "a" * 100
        result = animator._safe_class_name(long_name)
        assert len(result) <= 50

    def test_latex_escaping(self):
        """Test LaTeX escaping for mathematical notation."""
        animator = TheoremAnimator()

        # Basic symbols
        assert "\\\\forall" in animator._escape_latex("∀")
        assert "\\\\exists" in animator._escape_latex("∃")
        assert "\\\\to" in animator._escape_latex("→")
        assert "\\\\mathbb{N}" in animator._escape_latex("ℕ")

        # Combined expression
        result = animator._escape_latex("∀ (n : ℕ), n + 0 = n")
        assert "\\\\forall" in result
        assert "\\\\mathbb{N}" in result

    def test_string_escaping(self):
        """Test string escaping for Python literals."""
        animator = TheoremAnimator()

        # Basic escaping
        assert animator._escape_string('test "quoted" text') == 'test \\"quoted\\" text'
        assert animator._escape_string("test 'quoted' text") == "test \\'quoted\\' text"
        assert animator._escape_string("test\\backslash") == "test\\\\backslash"

        # Newlines and tabs
        assert animator._escape_string("line1\nline2") == "line1\\nline2"
        assert animator._escape_string("tab\there") == "tab\\there"

    def test_simple_animation_generation(self):
        """Test simple animation script generation."""
        animator = TheoremAnimator()

        script = animator.generate_simple_animation(
            "test_theorem", "2 + 2 = 4", ["Start with 2 + 2", "Evaluate to get 4"]
        )

        assert "class TestTheorem(Scene):" in script
        assert "from manim import *" in script
        assert "def construct(self):" in script
        assert "2 + 2 = 4" in script
        assert "Start with 2 + 2" in script
        assert "∎" in script

    def test_full_animation_generation(self):
        """Test full animation script generation."""
        animator = TheoremAnimator()

        theorem = {"name": "Nat.add_comm", "statement": "∀ (a b : ℕ), a + b = b + a"}

        sketch = {
            "key_steps": [
                {
                    "description": "Apply commutativity of addition",
                    "mathematical_content": "a + b = b + a",
                    "tactics": ["rw", "add_comm"],
                },
                {
                    "description": "Conclude the proof",
                    "mathematical_content": "b + a",
                    "tactics": ["rfl"],
                },
            ]
        }

        script = animator.generate_animation_script(theorem, sketch)

        # Check script structure
        assert "class NatAddComm(Scene):" in script
        assert "from manim import *" in script
        assert "def construct(self):" in script
        assert "def setup_scene(self):" in script
        assert "def show_title(self):" in script
        assert "def show_statement(self):" in script
        assert "def animate_proof(self):" in script
        assert "def show_conclusion(self):" in script

        # Check content
        assert "Nat.add_comm" in script
        assert "\\\\forall" in script  # ∀ should be escaped
        assert "\\\\mathbb{N}" in script  # ℕ should be escaped
        assert "Apply commutativity" in script
        assert "rw" in script
        assert "∎" in script

    def test_script_validation(self):
        """Test script validation functionality."""
        animator = TheoremAnimator()

        # Valid script
        valid_script = """
from manim import *

class TestScene(Scene):
    def construct(self):
        text = Text("Hello")
        self.play(Write(text))
"""
        is_valid, error = animator.validate_script(valid_script)
        assert is_valid is True
        assert error is None

        # Invalid syntax
        invalid_script = "def invalid_syntax( :"
        is_valid, error = animator.validate_script(invalid_script)
        assert is_valid is False
        assert "Syntax error" in error

        # Missing required elements
        incomplete_script = "print('hello')"
        is_valid, error = animator.validate_script(incomplete_script)
        assert is_valid is False
        assert "Missing required element" in error

    def test_animation_with_empty_sketch(self):
        """Test animation generation with empty proof sketch."""
        animator = TheoremAnimator()

        theorem = {"name": "simple_theorem", "statement": "True"}

        # Empty sketch
        sketch = {}

        script = animator.generate_animation_script(theorem, sketch)
        assert "class SimpleTheorem(Scene):" in script
        assert "No proof steps available" in script


class TestStaticVisualizer:
    """Test static visualization fallback."""

    def test_visualizer_initialization(self):
        """Test visualizer initialization."""
        visualizer = StaticVisualizer()
        assert visualizer is not None
        assert hasattr(visualizer, "config")
        assert hasattr(visualizer, "colors")

    def test_availability_check(self):
        """Test matplotlib availability check."""
        visualizer = StaticVisualizer()
        # Should not crash regardless of matplotlib availability
        assert isinstance(visualizer.is_available(), bool)

    def test_supported_formats(self):
        """Test supported format listing."""
        visualizer = StaticVisualizer()
        formats = visualizer.get_supported_formats()

        if visualizer.is_available():
            assert ".png" in formats
            assert ".pdf" in formats
            assert ".svg" in formats
        else:
            assert formats == []

    @pytest.mark.skipif(
        not StaticVisualizer().is_available(), reason="Matplotlib not available"
    )
    def test_simple_diagram_creation(self):
        """Test simple diagram creation."""
        visualizer = StaticVisualizer()

        with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
            output_path = f.name

        try:
            success = visualizer.create_simple_diagram(
                "Test Theorem",
                "2 + 2 = 4",
                output_path,
                ["Start with 2 + 2", "Evaluate"],
            )

            assert success is True
            assert Path(output_path).exists()
            assert Path(output_path).stat().st_size > 0

        finally:
            Path(output_path).unlink(missing_ok=True)

    @pytest.mark.skipif(
        not StaticVisualizer().is_available(), reason="Matplotlib not available"
    )
    def test_full_proof_diagram(self):
        """Test full proof diagram creation."""
        visualizer = StaticVisualizer()

        theorem = {
            "name": "Addition Commutativity",
            "statement": "∀ (a b : ℕ), a + b = b + a",
        }

        sketch = {
            "key_steps": [
                {
                    "description": "Apply the commutativity property of natural number addition",
                    "mathematical_content": "a + b = b + a",
                    "tactics": ["rw", "Nat.add_comm"],
                },
                {
                    "description": "The equation holds by definition",
                    "mathematical_content": "b + a",
                    "tactics": ["rfl"],
                },
            ]
        }

        with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
            output_path = f.name

        try:
            success = visualizer.create_proof_diagram(theorem, sketch, output_path)

            assert success is True
            assert Path(output_path).exists()

            # Check file size (should be substantial for a detailed diagram)
            file_size = Path(output_path).stat().st_size
            assert file_size > 10000  # At least 10KB for quality diagram

        finally:
            Path(output_path).unlink(missing_ok=True)

    @pytest.mark.skipif(
        not StaticVisualizer().is_available(), reason="Matplotlib not available"
    )
    def test_error_diagram_creation(self):
        """Test error diagram creation."""
        visualizer = StaticVisualizer()

        with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
            output_path = f.name

        try:
            success = visualizer.create_error_diagram(
                "Animation generation failed",
                output_path,
                "Manim not available or script error",
            )

            assert success is True
            assert Path(output_path).exists()

        finally:
            Path(output_path).unlink(missing_ok=True)

    def test_diagram_creation_without_matplotlib(self):
        """Test diagram creation when matplotlib unavailable."""
        with patch(
            "src.proof_sketcher.animator.static_fallback.MATPLOTLIB_AVAILABLE", False
        ):
            visualizer = StaticVisualizer()

            success = visualizer.create_simple_diagram(
                "Test", "statement", "output.png"
            )

            assert success is False


class TestAnimationPipeline:
    """Test complete animation pipeline integration."""

    def test_full_pipeline_with_fallback(self):
        """Test complete animation pipeline with fallback."""
        # Create test data
        theorem = {"name": "Nat.add_zero", "statement": "∀ (n : ℕ), n + 0 = n"}

        sketch = {
            "key_steps": [
                {
                    "description": "Apply the right identity property of addition",
                    "mathematical_content": "n + 0 = n",
                    "tactics": ["rfl"],
                }
            ]
        }

        # Test animation generation
        animator = TheoremAnimator()
        script = animator.generate_animation_script(theorem, sketch)

        # Validate script
        is_valid, error = animator.validate_script(script)
        assert is_valid, f"Generated script invalid: {error}"

        # Test MCP server (without actual Manim)
        server = ManimMCPServer()

        with tempfile.NamedTemporaryFile(suffix=".mp4", delete=False) as f:
            video_path = f.name

        try:
            # This will likely fail without Manim, which is expected
            result = server.create_animation_sync(script, video_path)

            if not result["success"]:
                # Fallback to static visualization
                visualizer = StaticVisualizer()

                if visualizer.is_available():
                    static_path = video_path.replace(".mp4", ".png")

                    success = visualizer.create_proof_diagram(
                        theorem, sketch, static_path
                    )

                    if success:
                        assert Path(static_path).exists()
                        Path(static_path).unlink()

        finally:
            Path(video_path).unlink(missing_ok=True)

    def test_animation_script_compilation(self):
        """Test that generated scripts can be compiled."""
        animator = TheoremAnimator()

        # Test various theorem types
        test_cases = [
            {"theorem": {"name": "simple", "statement": "True"}, "sketch": {}},
            {
                "theorem": {"name": "with_steps", "statement": "2 + 2 = 4"},
                "sketch": {
                    "key_steps": [
                        {"description": "Evaluate", "mathematical_content": "4"}
                    ]
                },
            },
            {
                "theorem": {"name": "complex", "statement": "∀ (x : ℝ), x + 0 = x"},
                "sketch": {
                    "key_steps": [
                        {
                            "description": "Apply additive identity",
                            "mathematical_content": "x + 0 = x",
                            "tactics": ["ring"],
                        }
                    ]
                },
            },
        ]

        for test_case in test_cases:
            script = animator.generate_animation_script(
                test_case["theorem"], test_case["sketch"]
            )

            # Should compile without syntax errors
            try:
                compile(script, "<string>", "exec")
            except SyntaxError as e:
                pytest.fail(
                    f"Generated script has syntax error: {e}\nScript:\n{script}"
                )

    def test_error_handling_in_pipeline(self):
        """Test error handling throughout the pipeline."""
        # Test with invalid input
        animator = TheoremAnimator()

        # Should handle None inputs gracefully
        script = animator.generate_animation_script({}, {})
        assert "class Theorem(Scene):" in script

        # Should handle malformed data
        malformed_theorem = {"name": "", "statement": None}
        malformed_sketch = {"key_steps": None}

        script = animator.generate_animation_script(malformed_theorem, malformed_sketch)
        assert "from manim import *" in script

        # Should be valid Python
        is_valid, _ = animator.validate_script(script)
        assert is_valid


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
