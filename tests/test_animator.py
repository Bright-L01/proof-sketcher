"""Comprehensive tests for the animation module."""

from pathlib import Path
from unittest.mock import AsyncMock, Mock, patch

import pytest

from proof_sketcher.animator import ManimAnimator
from proof_sketcher.animator.formula_extractor import (FormulaExtractor,
                                                       LeanToLatexConverter)
from proof_sketcher.animator.models import (AnimationConfig, AnimationQuality,
                                            AnimationRequest,
                                            AnimationResponse, AnimationStyle,
                                            TransformationType)
from proof_sketcher.animator.scene_builder import ProofAnimationBuilder
from proof_sketcher.generator.models import ProofSketch, ProofStep


@pytest.fixture
def sample_proof_sketch():
    """Create sample proof sketch."""
    steps = [
        ProofStep(
            step_number=1,
            description="State the theorem",
            mathematical_content="∀ n : ℕ, n + 0 = n",
            tactics=["intro"],
            intuition="We need to prove this for all natural numbers",
        ),
        ProofStep(
            step_number=2,
            description="Apply induction",
            mathematical_content="P(0) ∧ (∀k, P(k) → P(k+1))",
            tactics=["induction", "simp"],
            intuition="Use mathematical induction on n",
        ),
    ]

    return ProofSketch(
        theorem_name="nat_add_zero",
        introduction="This theorem proves that adding zero to any natural number gives the same number",
        key_steps=steps,
        conclusion="Therefore, zero is the additive identity for natural numbers",
        difficulty_level="beginner",
        mathematical_areas=["Arithmetic", "Natural Numbers"],
        prerequisites=["Natural numbers", "Addition"],
    )


class TestManimAnimator:
    """Test suite for ManimAnimator."""

    @pytest.fixture
    def animator(self):
        """Create animator instance."""
        config = AnimationConfig(
            quality=AnimationQuality.MEDIUM, fps=30, style=AnimationStyle.MODERN
        )
        return ManimAnimator(animation_config=config)

    @pytest.mark.asyncio
    async def test_animate_proof_success(self, animator, sample_proof_sketch):
        """Test successful animation generation."""
        # Create a mock request
        import uuid
        from proof_sketcher.animator.models import AnimationSegment, AnimationScene
        
        mock_request = AnimationRequest(
            theorem_name="nat_add_zero",
            request_id=str(uuid.uuid4()),
            segments=[AnimationSegment(
                segment_id="seg1",
                title="Main",
                scenes=[AnimationScene(
                    scene_id="scene1",
                    title="Test",
                    duration=3.0,
                    initial_formula="",
                    final_formula="n + 0 = n",
                    transformation_type=TransformationType.EXPANSION
                )]
            )]
        )
        mock_request.estimated_duration = 13.0
        
        mock_response = AnimationResponse(
            request=mock_request,
            video_path=Path("/tmp/animation.mp4"),
            success=True,
            actual_duration=13.0,
        )
        
        # Mock all the necessary methods
        with patch.object(animator, '_validate_animation_request', return_value=True), \
             patch.object(animator.scene_builder, 'build_animation_request', return_value=mock_request), \
             patch.object(animator, '_post_process_animation', return_value=mock_response), \
             patch("proof_sketcher.animator.animator.ManimMCPManager") as mock_manager:
            
            # Mock MCP manager instance
            mock_instance = AsyncMock()
            mock_instance.render_animation.return_value = mock_response
            
            # Set up async context manager properly
            mock_context = AsyncMock()
            mock_context.__aenter__.return_value = mock_instance
            mock_context.__aexit__.return_value = None
            mock_manager.return_value = mock_context

            # Generate animation
            response = await animator.animate_proof(sample_proof_sketch)

            assert response.success
            assert response.video_path is not None
            assert response.actual_duration == 13.0

    @pytest.mark.asyncio
    async def test_animate_single_step(self, animator):
        """Test animating a single proof step."""
        step = ProofStep(
            step_number=1,
            description="Base case",
            mathematical_content="P(0)",
            tactics=["simp"],
            intuition="Check the base case",
        )

        with patch("proof_sketcher.animator.animator.ManimMCPManager") as mock_manager:
            mock_instance = AsyncMock()
            mock_response = AnimationResponse(
                request=Mock(), video_path=Path("/tmp/step.mp4"), success=True
            )
            mock_instance.render_animation.return_value = mock_response
            mock_manager.return_value.__aenter__.return_value = mock_instance

            response = await animator.animate_single_step(step, step_number=1)

            assert response.success

    def test_setup_output_directories(self, animator):
        """Test output directory setup."""
        # Should create directories
        assert animator.manim_config.output_dir.exists()
        assert animator.manim_config.temp_dir.exists()

    @pytest.mark.asyncio
    async def test_error_handling(self, animator, sample_proof_sketch):
        """Test error handling in animation."""
        with patch("proof_sketcher.animator.animator.ManimMCPManager") as mock_manager:
            # Mock MCP error
            mock_instance = AsyncMock()
            mock_instance.render_animation.side_effect = Exception("Render failed")
            mock_manager.return_value.__aenter__.return_value = mock_instance

            response = await animator.animate_proof(sample_proof_sketch)

            assert not response.success
            assert response.error_message is not None
            assert "Render failed" in response.error_message


class TestSceneBuilder:
    """Test suite for ProofAnimationBuilder."""

    @pytest.fixture
    def scene_builder(self):
        """Create scene builder instance."""
        config = AnimationConfig()
        return ProofAnimationBuilder(config)

    def test_build_animation_request(self, scene_builder, sample_proof_sketch):
        """Test building animation request from proof sketch."""
        request = scene_builder.build_animation_request(sample_proof_sketch)

        assert request.theorem_name == "nat_add_zero"
        assert len(request.segments) > 0
        assert request.estimated_duration > 0
        assert request.config is not None

    def test_scene_generation(self, scene_builder, sample_proof_sketch):
        """Test individual scene generation."""
        # Test the creation of segments
        segments = scene_builder._create_segments(sample_proof_sketch, AnimationConfig())
        
        assert len(segments) > 0
        # Check introduction segment
        intro_segment = segments[0]
        assert intro_segment.title == "Introduction"
        assert len(intro_segment.scenes) > 0
        
        # Check that scenes have proper structure
        first_scene = intro_segment.scenes[0]
        assert first_scene.scene_id is not None
        assert first_scene.title is not None
        assert first_scene.duration > 0

    def test_style_configuration(self, scene_builder):
        """Test animation style configuration."""
        config = AnimationConfig(style=AnimationStyle.MODERN)
        builder = ProofAnimationBuilder(config)
        
        # Create a minimal proof sketch
        proof_sketch = ProofSketch(
            theorem_name="test",
            introduction="Test introduction",
            key_steps=[],
            conclusion="Test conclusion"
        )

        request = builder.build_animation_request(proof_sketch)

        assert request.config.style == AnimationStyle.MODERN
        assert request.config.background_color == "#FFFFFF"
        assert request.config.text_color == "#000000"


class TestFormulaExtractor:
    """Test suite for formula extraction."""

    @pytest.fixture
    def extractor(self):
        """Create formula extractor instance."""
        return FormulaExtractor()

    def test_extract_formulas(self, extractor):
        """Test formula extraction from text."""
        text = (
            "Consider the equation $x^2 + y^2 = z^2$ and the formula $$\\int_0^1 x dx$$"
        )
        formulas = extractor.extract_formulas(text)

        assert len(formulas) == 2
        assert formulas[0].latex == "x^2 + y^2 = z^2"
        assert formulas[0].display_mode is False
        assert formulas[1].latex == "\\int_0^1 x dx"
        assert formulas[1].display_mode is True

    def test_lean_notation_extraction(self, extractor):
        """Test Lean notation extraction."""
        text = "The theorem states `∀ x : ℕ, x + 0 = x` which is fundamental"
        formulas = extractor.extract_lean_notation(text)

        assert len(formulas) == 1
        assert "∀ x : ℕ" in formulas[0]

    def test_process_mixed_content(self, extractor):
        """Test processing mixed mathematical content."""
        content = """
        We prove that `∀ n : ℕ, n + 0 = n` using induction.
        The base case is $P(0)$, and the inductive step shows
        $$P(k) \\implies P(k+1)$$
        """

        processed = extractor.process_proof_content(content)

        # Should identify multiple formula types
        assert len(processed.formulas) > 0
        assert len(processed.lean_code) > 0


class TestLeanToLatexConverter:
    """Test suite for Lean to LaTeX conversion."""

    @pytest.fixture
    def converter(self):
        """Create converter instance."""
        return LeanToLatexConverter()

    def test_basic_conversions(self, converter):
        """Test basic Lean to LaTeX conversions."""
        # Forall
        assert converter.convert("∀ x, P x") == "\\forall x, P(x)"

        # Exists
        assert converter.convert("∃ x, P x") == "\\exists x, P(x)"

        # Lambda
        assert converter.convert("λ x, x + 1") == "\\lambda x. x + 1"

        # Natural numbers
        assert converter.convert("ℕ") == "\\mathbb{N}"

    def test_type_annotations(self, converter):
        """Test type annotation conversions."""
        lean = "∀ (x : ℕ), x + 0 = x"
        latex = converter.convert(lean)
        assert "\\forall" in latex
        assert "\\mathbb{N}" in latex

    def test_complex_expressions(self, converter):
        """Test complex expression conversions."""
        lean = "∀ (f : ℕ → ℕ) (x : ℕ), f (x + 0) = f x"
        latex = converter.convert(lean)

        assert "\\to" in latex
        assert "\\forall" in latex
        assert "f(x + 0) = f(x)" in latex or "f(x+0)=f(x)" in latex.replace(" ", "")


class TestAnimationModels:
    """Test suite for animation data models."""

    def test_animation_config(self):
        """Test AnimationConfig model."""
        config = AnimationConfig(
            quality=AnimationQuality.HIGH,
            fps=60,
            style=AnimationStyle.ACCESSIBLE,
            background_color="#1a1a1a",
            step_duration=20,
        )

        assert config.quality == AnimationQuality.HIGH
        assert config.fps == 60
        assert config.width == 1280  # Default width
        assert config.height == 720  # Default height
        assert config.step_duration == 20

    def test_animation_request(self):
        """Test AnimationRequest model."""
        from proof_sketcher.animator.models import AnimationSegment, AnimationScene
        import uuid

        scenes = [
            AnimationScene(
                scene_id="scene1",
                title="Introduction", 
                duration=3.0,
                initial_formula="",
                final_formula="Test Theorem",
                transformation_type=TransformationType.EXPANSION
            )
        ]
        
        segments = [
            AnimationSegment(
                segment_id="seg1",
                title="Main Segment",
                scenes=scenes
            )
        ]

        request = AnimationRequest(
            theorem_name="test",
            request_id=str(uuid.uuid4()),
            segments=segments,
            config=AnimationConfig(),
        )

        assert request.theorem_name == "test"
        assert len(request.segments) == 1
        assert len(request.segments[0].scenes) == 1

    def test_animation_response(self):
        """Test AnimationResponse model."""
        # Create a mock request with necessary attributes
        mock_request = Mock()
        mock_request.theorem_name = "test"
        mock_request.segments = []
        
        response = AnimationResponse(
            request=mock_request,
            video_path=Path("/tmp/video.mp4"),
            preview_image_path=Path("/tmp/thumb.png"),
            success=True,
            actual_duration=10.5,
            file_size_mb=2.3,
        )

        assert response.success
        assert response.actual_duration == 10.5
        assert response.file_size_mb == 2.3


@pytest.mark.integration
class TestAnimatorIntegration:
    """Integration tests for the animator."""

    @pytest.mark.asyncio
    async def test_full_animation_pipeline(self):
        """Test complete animation pipeline."""
        from proof_sketcher.animator import ManimAnimator
        from proof_sketcher.generator.models import ProofSketch, ProofStep

        # Create proof sketch
        sketch = ProofSketch(
            theorem_name="integration_test",
            introduction="Test explanation",
            key_steps=[ProofStep(
                step_number=1,
                description="Step 1",
                mathematical_content="x = y",
                tactics=["rfl"]
            )],
            conclusion="Test complete"
        )

        # Create animator
        animator = ManimAnimator()

        # Mock MCP server
        with patch("proof_sketcher.animator.manim_mcp.ManimMCPManager") as mock_mcp:
            mock_instance = AsyncMock()
            mock_response = AnimationResponse(
                request=Mock(), video_path=Path("/tmp/test.mp4"), success=True
            )
            mock_instance.render_animation.return_value = mock_response
            mock_mcp.return_value.__aenter__.return_value = mock_instance

            # Generate animation
            response = await animator.animate_proof(sketch)

            assert response.success
            assert response.video_path is not None


class TestCachedAnimator:
    """Test suite for cached animator."""

    @pytest.mark.asyncio
    async def test_caching_behavior(self, tmp_path):
        """Test animation caching."""
        from proof_sketcher.animator.animator import CachedManimAnimator

        cache_dir = tmp_path / "animation_cache"
        animator = CachedManimAnimator(cache_directory=cache_dir)

        sketch = ProofSketch(
            theorem_name="cached_test",
            introduction="Test",
            key_steps=[],
            conclusion="Test complete"
        )

        with patch.object(animator, "_generate_animation") as mock_generate:
            mock_generate.return_value = AnimationResponse(
                request=Mock(), video_path=Path("/tmp/cached.mp4"), success=True
            )

            # First call should generate
            response1 = await animator.animate_proof(sketch)
            assert mock_generate.call_count == 1

            # Second call should use cache
            response2 = await animator.animate_proof(sketch)
            assert mock_generate.call_count == 1  # Not called again

            assert response1.video_path == response2.video_path
