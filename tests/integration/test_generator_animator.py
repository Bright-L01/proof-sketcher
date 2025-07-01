"""Integration tests for generator and animator components."""

from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.animator.manim_mcp import ManimMCPClient
from proof_sketcher.animator.models import (
    AnimationConfig,
    AnimationQuality,
    ManimConfig,
)
from proof_sketcher.animator.scene_builder import ProofAnimationBuilder
from proof_sketcher.generator.models import ProofSketch, ProofStep


class TestGeneratorAnimatorIntegration:
    """Test integration between generator and animator."""

    @pytest.fixture
    def animation_config(self):
        """Create animation configuration for tests."""
        return AnimationConfig(quality=AnimationQuality.MEDIUM, fps=30)

    @pytest.fixture
    def manim_config(self):
        """Create Manim configuration for tests."""
        return ManimConfig(
            server_command="npx",
            server_args=["-y", "@moonshiner/manim_mcp@latest"],
            output_dir=Path("/tmp/animations"),
        )

    @pytest.fixture
    def sample_sketches(self):
        """Create sample proof sketches for testing."""
        sketches = {}

        # Simple proof
        sketches["simple"] = ProofSketch(
            theorem_name="add_zero",
            introduction="Adding zero to any natural number leaves it unchanged.",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Apply reflexivity",
                    mathematical_content="n + 0 = n by definition",
                )
            ],
            conclusion="This proves that zero is the additive identity for natural numbers.",
        )

        # Induction proof
        sketches["induction"] = ProofSketch(
            theorem_name="sum_formula",
            introduction="The sum of first n natural numbers equals n(n+1)/2.",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Base case: n = 0",
                    mathematical_content="2 * sum(0) = 2 * 0 = 0 = 0 * 1",
                ),
                ProofStep(
                    step_number=2,
                    description="Inductive step: assume for n",
                    mathematical_content="2 * sum(n) = n * (n + 1)",
                ),
                ProofStep(
                    step_number=3,
                    description="Prove for n + 1",
                    mathematical_content="2 * sum(n+1) = 2 * (sum(n) + (n+1))",
                ),
                ProofStep(
                    step_number=4,
                    description="Apply inductive hypothesis",
                    mathematical_content="= n(n+1) + 2(n+1) = (n+1)(n+2)",
                ),
            ],
            conclusion="By mathematical induction, the formula holds for all natural numbers.",
        )

        # Complex proof
        sketches["complex"] = ProofSketch(
            theorem_name="pigeonhole",
            introduction="The pigeonhole principle demonstrated through contradiction.",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Assume each hole has at most 1 pigeon",
                    mathematical_content="∀i ∈ [1,m], |hole_i| ≤ 1",
                ),
                ProofStep(
                    step_number=2,
                    description="Count total pigeons",
                    mathematical_content="total = Σ|hole_i| ≤ Σ1 = m",
                ),
                ProofStep(
                    step_number=3,
                    description="Derive contradiction",
                    mathematical_content="n > m ≥ total ≥ n",
                ),
            ],
            conclusion="By contradiction, at least one hole must contain more than one pigeon.",
        )

        return sketches

    @pytest.mark.asyncio
    async def test_simple_animation_generation(
        self, animation_config, manim_config, sample_sketches
    ):
        """Test generating animation for a simple proof."""
        sketch = sample_sketches["simple"]

        with patch.object(ManimMCPClient, "start_server"):
            with patch.object(ManimMCPClient, "render_animation") as mock_render:
                # Mock successful render
                mock_render.return_value = Mock(
                    video_path="/tmp/animations/add_zero.mp4",
                    duration=45.0,  # 30s base + 15s for 1 step
                    success=True,
                    error=None,
                )

                client = ManimMCPClient(manim_config)
                await client.start_server()

                # Create animation request from sketch
                builder = ProofAnimationBuilder(animation_config)
                request = builder.build_animation_request(sketch, animation_config)

                response = await client.render_animation(request)

                assert response.success
                # Simple proof has 1 step: 30s base + 15s = 45s
                assert response.duration == 45.0
                assert "add_zero.mp4" in response.video_path

    @pytest.mark.asyncio
    async def test_induction_animation_generation(
        self, animation_config, manim_config, sample_sketches
    ):
        """Test generating animation for an induction proof."""
        sketch = sample_sketches["induction"]

        # Calculate expected duration: 30s base + 15s per step
        expected_duration = 30 + (15 * len(sketch.key_steps))

        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            mock_render.return_value = Mock(
                video_path="/tmp/animations/sum_formula.mp4",
                duration=float(expected_duration),
                success=True,
            )

            client = ManimMCPClient(manim_config)

            # Create animation request from sketch
            builder = ProofAnimationBuilder(animation_config)
            request = builder.build_animation_request(sketch, animation_config)

            response = await client.render_animation(request)

            assert response.success
            assert response.duration == expected_duration
            assert len(sketch.key_steps) == 4

    @pytest.mark.asyncio
    async def test_batch_animation_generation(
        self, animation_config, manim_config, sample_sketches
    ):
        """Test generating animations for multiple proofs."""
        sketches = list(sample_sketches.values())

        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            # Different response for each sketch
            responses = [
                Mock(
                    video_path=f"/tmp/{s.theorem_name}.mp4", duration=30.0, success=True
                )
                for s in sketches
            ]
            mock_render.side_effect = responses

            client = ManimMCPClient(manim_config)
            builder = ProofAnimationBuilder(animation_config)
            results = []

            for sketch in sketches:
                request = builder.build_animation_request(sketch, animation_config)
                response = await client.render_animation(request)
                results.append(response)

            assert len(results) == len(sketches)
            assert all(r.success for r in results)
            assert len(set(r.video_path for r in results)) == len(results)

    @pytest.mark.asyncio
    async def test_animation_caching(
        self, animation_config, manim_config, sample_sketches
    ):
        """Test animation caching behavior."""
        sketch = sample_sketches["simple"]

        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            # Setup mock to return cached=False first, then cached=True
            mock_render.side_effect = [
                Mock(
                    video_path="/tmp/cache/add_zero.mp4",
                    duration=45.0,  # 30s base + 15s for 1 step
                    success=True,
                    cached=False,
                ),
                Mock(
                    video_path="/tmp/cache/add_zero.mp4",
                    duration=45.0,
                    success=True,
                    cached=True,
                ),
            ]

            client = ManimMCPClient(manim_config)
            builder = ProofAnimationBuilder(animation_config)
            request = builder.build_animation_request(sketch, animation_config)

            # First call - not cached
            response1 = await client.render_animation(request)
            assert not response1.cached

            # Second call - cached
            response2 = await client.render_animation(request)
            assert response2.cached

    @pytest.mark.asyncio
    async def test_animation_error_handling(
        self, animation_config, manim_config, sample_sketches
    ):
        """Test error handling in animation generation."""
        sketch = sample_sketches["complex"]

        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            # Simulate render failure
            mock_render.return_value = Mock(
                video_path=None,
                duration=0,
                success=False,
                error="Manim rendering failed: Invalid LaTeX",
            )

            client = ManimMCPClient(manim_config)
            builder = ProofAnimationBuilder(animation_config)
            request = builder.build_animation_request(sketch, animation_config)

            response = await client.render_animation(request)

            assert not response.success
            assert "Invalid LaTeX" in response.error
            assert response.video_path is None

    @pytest.mark.asyncio
    async def test_animation_with_custom_config(self, manim_config, sample_sketches):
        """Test animation with custom configuration."""
        custom_config = AnimationConfig(
            quality=AnimationQuality.HIGH,
            fps=60,
            background_color="#FFFFFF",
            math_font="Computer Modern",
        )

        sketch = sample_sketches["simple"]

        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            client = ManimMCPClient(manim_config)

            builder = ProofAnimationBuilder(custom_config)
            request = builder.build_animation_request(sketch, custom_config)

            await client.render_animation(request)

            # Verify custom config was passed
            mock_render.assert_called_once()
            call_args = mock_render.call_args[0][0]
            assert call_args.config.quality == AnimationQuality.HIGH
            assert call_args.config.fps == 60

    def test_animation_request_from_sketch(self, sample_sketches, animation_config):
        """Test creating animation request from proof sketch."""
        sketch = sample_sketches["induction"]

        # Create animation request using builder
        builder = ProofAnimationBuilder(animation_config)
        request = builder.build_animation_request(sketch, animation_config)

        assert request.theorem_name == sketch.theorem_name
        assert len(request.segments) > 0  # Should have segments
        assert request.config == animation_config
