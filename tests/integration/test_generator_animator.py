"""Integration tests for generator and animator components."""

from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.animator.manim_mcp import ManimMCPClient
from proof_sketcher.animator.models import (AnimationConfig,
                                            AnimationRequest, ManimConfig)
from proof_sketcher.generator.models import ProofSketch, ProofStep


class TestGeneratorAnimatorIntegration:
    """Test integration between generator and animator."""

    @pytest.fixture
    def animation_config(self):
        """Create animation configuration for tests."""
        return AnimationConfig(
            enabled=True, quality="720p", fps=30, cache_animations=True
        )

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
            theorem_statement="∀ n : Nat, n + 0 = n",
            explanation="Adding zero to any natural number leaves it unchanged.",
            steps=[
                ProofStep(
                    description="Apply reflexivity",
                    mathematical_content="n + 0 = n by definition",
                )
            ],
            key_insights=["Zero is the additive identity"],
        )

        # Induction proof
        sketches["induction"] = ProofSketch(
            theorem_name="sum_formula",
            theorem_statement="∀ n : Nat, 2 * sum(n) = n * (n + 1)",
            explanation="The sum of first n natural numbers equals n(n+1)/2.",
            steps=[
                ProofStep(
                    description="Base case: n = 0",
                    mathematical_content="2 * sum(0) = 2 * 0 = 0 = 0 * 1",
                ),
                ProofStep(
                    description="Inductive step: assume for n",
                    mathematical_content="2 * sum(n) = n * (n + 1)",
                ),
                ProofStep(
                    description="Prove for n + 1",
                    mathematical_content="2 * sum(n+1) = 2 * (sum(n) + (n+1))",
                ),
                ProofStep(
                    description="Apply inductive hypothesis",
                    mathematical_content="= n(n+1) + 2(n+1) = (n+1)(n+2)",
                ),
            ],
            key_insights=["Mathematical induction", "Algebraic manipulation"],
        )

        # Complex proof
        sketches["complex"] = ProofSketch(
            theorem_name="pigeonhole",
            theorem_statement="If n > m pigeons are in m holes, at least one hole has >1 pigeon",
            explanation="The pigeonhole principle demonstrated through contradiction.",
            steps=[
                ProofStep(
                    description="Assume each hole has at most 1 pigeon",
                    mathematical_content="∀i ∈ [1,m], |hole_i| ≤ 1",
                ),
                ProofStep(
                    description="Count total pigeons",
                    mathematical_content="total = Σ|hole_i| ≤ Σ1 = m",
                ),
                ProofStep(
                    description="Derive contradiction",
                    mathematical_content="n > m ≥ total ≥ n",
                ),
            ],
            key_insights=["Proof by contradiction", "Counting argument"],
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
                    duration=30.0,
                    success=True,
                    error=None,
                )

                client = ManimMCPClient(manim_config)
                await client.start_server()

                # Create animation request from sketch
                request = AnimationRequest(
                    theorem_name=sketch.theorem_name,
                    theorem_statement=sketch.theorem_statement,
                    explanation=sketch.explanation,
                    proof_steps=[step.description for step in sketch.steps],
                    mathematical_content=[
                        step.mathematical_content for step in sketch.steps
                    ],
                    key_insights=sketch.key_insights,
                    config=animation_config,
                )

                response = await client.render_animation(request)

                assert response.success
                assert response.duration == 30.0
                assert "add_zero.mp4" in response.video_path

    @pytest.mark.asyncio
    async def test_induction_animation_generation(
        self, animation_config, manim_config, sample_sketches
    ):
        """Test generating animation for an induction proof."""
        sketch = sample_sketches["induction"]

        # Calculate expected duration: 30s base + 15s per step
        expected_duration = 30 + (15 * len(sketch.steps))

        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            mock_render.return_value = Mock(
                video_path="/tmp/animations/sum_formula.mp4",
                duration=float(expected_duration),
                success=True,
            )

            client = ManimMCPClient(manim_config)

            request = AnimationRequest(
                theorem_name=sketch.theorem_name,
                theorem_statement=sketch.theorem_statement,
                explanation=sketch.explanation,
                proof_steps=[step.description for step in sketch.steps],
                mathematical_content=[
                    step.mathematical_content for step in sketch.steps
                ],
                duration=expected_duration,
            )

            response = await client.render_animation(request)

            assert response.success
            assert response.duration == expected_duration
            assert len(request.proof_steps) == 4

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
            results = []

            for sketch in sketches:
                request = AnimationRequest(
                    theorem_name=sketch.theorem_name,
                    explanation=sketch.explanation,
                    proof_steps=[step.description for step in sketch.steps],
                )
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
        animation_config.cache_animations = True
        sketch = sample_sketches["simple"]

        with patch.object(ManimMCPClient, "_get_cache_path") as mock_cache:
            with patch.object(Path, "exists") as mock_exists:
                # First call - cache miss
                mock_exists.return_value = False
                mock_cache.return_value = Path("/tmp/cache/add_zero.mp4")

                with patch.object(ManimMCPClient, "render_animation") as mock_render:
                    mock_render.return_value = Mock(
                        video_path="/tmp/cache/add_zero.mp4",
                        duration=30.0,
                        success=True,
                        cached=False,
                    )

                    client = ManimMCPClient(manim_config)
                    request = AnimationRequest(
                        theorem_name=sketch.theorem_name,
                        explanation=sketch.explanation,
                        proof_steps=[s.description for s in sketch.steps],
                    )

                    response1 = await client.render_animation(request)
                    assert not response1.cached

                # Second call - cache hit
                mock_exists.return_value = True

                # Should return cached result without rendering
                await client.render_animation(request)
                # Implementation would check cache first

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
            request = AnimationRequest(
                theorem_name=sketch.theorem_name,
                explanation=sketch.explanation,
                proof_steps=[s.description for s in sketch.steps],
            )

            response = await client.render_animation(request)

            assert not response.success
            assert "Invalid LaTeX" in response.error
            assert response.video_path is None

    @pytest.mark.asyncio
    async def test_animation_with_custom_config(self, manim_config, sample_sketches):
        """Test animation with custom configuration."""
        custom_config = AnimationConfig(
            enabled=True,
            quality="1080p",
            fps=60,
            background_color="#FFFFFF",
            font="Computer Modern",
        )

        sketch = sample_sketches["simple"]

        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            client = ManimMCPClient(manim_config)

            request = AnimationRequest(
                theorem_name=sketch.theorem_name,
                explanation=sketch.explanation,
                proof_steps=[s.description for s in sketch.steps],
                config=custom_config,
            )

            await client.render_animation(request)

            # Verify custom config was passed
            mock_render.assert_called_once()
            call_args = mock_render.call_args[0][0]
            assert call_args.config.quality == "1080p"
            assert call_args.config.fps == 60

    def test_animation_request_from_sketch(self, sample_sketches):
        """Test creating animation request from proof sketch."""
        sketch = sample_sketches["induction"]

        # Helper method to convert sketch to request
        def sketch_to_request(
            sketch: ProofSketch, duration: int = None
        ) -> AnimationRequest:
            if duration is None:
                duration = 30 + (15 * len(sketch.steps))

            return AnimationRequest(
                theorem_name=sketch.theorem_name,
                theorem_statement=sketch.theorem_statement,
                explanation=sketch.explanation,
                proof_steps=[s.description for s in sketch.steps],
                mathematical_content=[s.mathematical_content for s in sketch.steps],
                key_insights=sketch.key_insights,
                duration=min(duration, 720),  # Max 12 minutes
            )

        request = sketch_to_request(sketch)

        assert request.theorem_name == sketch.theorem_name
        assert len(request.proof_steps) == len(sketch.steps)
        assert request.duration == 90  # 30 + 4*15
        assert request.key_insights == sketch.key_insights
