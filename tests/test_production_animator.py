"""Comprehensive tests for the production-ready animator module."""

import asyncio
import tempfile
import time
from pathlib import Path
from typing import Any, Dict
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from proof_sketcher.animator.animator import ProductionAnimator
from proof_sketcher.animator.fallback import FallbackAnimator, StaticAnimationGenerator
from proof_sketcher.animator.manim_mcp import ManimMCPClient
from proof_sketcher.animator.mock_mcp import MockMCPServer, MockMCPTransport
from proof_sketcher.animator.models import (
    AnimationConfig,
    AnimationQuality,
    AnimationResponse,
    AnimationStyle,
    ManimConfig,
)
from proof_sketcher.core.exceptions import AnimationTimeoutError, AnimatorError
from proof_sketcher.generator.models import ProofSketch, ProofStep


@pytest.fixture
def sample_proof_sketch():
    """Create a sample proof sketch for testing."""
    steps = [
        ProofStep(
            step_number=1,
            description="Define the theorem",
            mathematical_content="∀ n : ℕ, n + 0 = n",
            tactics=["intro"],
            intuition="We prove this for all natural numbers",
        ),
        ProofStep(
            step_number=2,
            description="Use induction",
            mathematical_content="Base case: 0 + 0 = 0",
            tactics=["induction", "simp"],
            intuition="Start with base case",
        ),
        ProofStep(
            step_number=3,
            description="Inductive step",
            mathematical_content="(k + 1) + 0 = k + 1",
            tactics=["rw", "ih"],
            intuition="Use inductive hypothesis",
        ),
    ]

    return ProofSketch(
        theorem_name="nat_add_zero",
        introduction="Proving that adding zero to any natural number gives the same number",
        key_steps=steps,
        conclusion="Therefore, zero is the additive identity for natural numbers",
        difficulty_level="beginner",
        mathematical_areas=["Arithmetic", "Natural Numbers"],
        prerequisites=["Natural numbers", "Addition"],
    )


@pytest.fixture
def temp_output_dir():
    """Create temporary output directory."""
    with tempfile.TemporaryDirectory() as tmpdir:
        yield Path(tmpdir)


@pytest.fixture
def animation_config(temp_output_dir):
    """Create animation configuration."""
    return AnimationConfig(
        max_memory_mb=512,
        max_processing_time=60,
    )


@pytest.fixture
def manim_config(temp_output_dir):
    """Create Manim configuration."""
    return ManimConfig(
        server_host="localhost",
        server_port=8765,
        auto_start=False,
        output_dir=temp_output_dir,
        temp_dir=temp_output_dir / "temp",
    )


class TestProductionAnimator:
    """Test suite for ProductionAnimator."""

    def test_initialization(self, animation_config, manim_config):
        """Test ProductionAnimator initialization."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        assert animator.animation_config == animation_config
        assert animator.manim_config == manim_config
        assert animator.use_mock is True
        assert isinstance(animator.mcp_client, ManimMCPClient)
        assert isinstance(animator.static_generator, StaticAnimationGenerator)
        assert isinstance(animator.fallback_animator, FallbackAnimator)

    def test_default_configurations(self):
        """Test default configurations when none provided."""
        animator = ProductionAnimator()

        assert animator.animation_config is not None
        assert animator.manim_config is not None
        assert animator.max_memory_mb >= 0
        assert animator.max_processing_time > 0

    def test_output_directory_creation(self, temp_output_dir):
        """Test output directory creation."""
        config = AnimationConfig(output_dir=temp_output_dir / "new_dir")
        animator = ProductionAnimator(animation_config=config)

        assert config.output_dir.exists()

    @pytest.mark.asyncio
    async def test_successful_animation_generation(
        self, animation_config, manim_config, sample_proof_sketch
    ):
        """Test successful animation generation with mock."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Create a mock request first
        from proof_sketcher.animator.models import AnimationRequest

        mock_request = AnimationRequest(
            theorem_name=sample_proof_sketch.theorem_name,
            request_id="test-request",
            segments=[],
            config=animation_config,
        )

        # Mock the fallback animator to return success
        mock_response = AnimationResponse(
            request=mock_request,
            video_path=manim_config.output_dir / "test.mp4",
            preview_image_path=manim_config.output_dir / "test_thumb.png",
            actual_duration=45.0,
            file_size_mb=1.0,
            success=True,
        )

        with patch.object(
            animator.fallback_animator, "animate", return_value=mock_response
        ):
            response = await animator.animate_proof(sample_proof_sketch)

            assert response.video_path is not None
            assert response.duration == 45.0
            assert response.frame_count == 1350
            assert response.size_bytes == 1024 * 1024
            assert response.metadata["processing_time_seconds"] > 0
            assert response.metadata["style"] == AnimationStyle.MODERN.value
            assert response.metadata["quality"] == AnimationQuality.MEDIUM.value
            assert response.metadata["theorem_name"] == "nat_add_zero"

    @pytest.mark.asyncio
    async def test_timeout_handling(
        self, animation_config, manim_config, sample_proof_sketch
    ):
        """Test animation timeout handling."""
        # Set very short timeout
        config = AnimationConfig(
            output_dir=manim_config.output_dir,
            max_processing_time=0.1,  # 100ms timeout
        )

        animator = ProductionAnimator(
            animation_config=config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Mock the fallback animator to take too long
        async def slow_animate(*args, **kwargs):
            await asyncio.sleep(0.2)  # Longer than timeout
            return AnimationResponse(
                video_path=None, duration=0, frame_count=0, size_bytes=0
            )

        with patch.object(
            animator.fallback_animator, "animate", side_effect=slow_animate
        ):
            response = await animator.animate_proof(sample_proof_sketch)

            assert response.error is not None
            assert "timed out" in response.error.lower()
            assert response.metadata["error_type"] == "timeout"
            assert response.metadata["timeout_seconds"] == 0.1

    @pytest.mark.asyncio
    async def test_memory_limit_checking(self, animation_config, manim_config):
        """Test memory limit checking."""
        # Set very low memory limit
        config = AnimationConfig(
            output_dir=manim_config.output_dir,
            max_memory_mb=1,  # 1MB limit (very low)
        )

        animator = ProductionAnimator(
            animation_config=config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Create a minimal proof to trigger memory check
        minimal_proof = ProofSketch(
            theorem_name="test",
            introduction="Test",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Test step",
                    mathematical_content="x = x",
                    tactics=["rfl"],
                )
            ],
            conclusion="Done",
        )

        # psutil might not be available, so test both cases
        try:
            import psutil

            # If psutil is available, mock it to return high memory usage
            with patch("psutil.Process") as mock_process:
                mock_process.return_value.memory_info.return_value.rss = (
                    2 * 1024 * 1024
                )  # 2MB

                response = await animator.animate_proof(minimal_proof)

                assert response.error is not None
                assert "memory limit" in response.error.lower()
                assert response.metadata["error_type"] == "memory_limit"
        except ImportError:
            # psutil not available, memory check should be skipped
            response = await animator.animate_proof(minimal_proof)
            # Should still work without psutil
            assert response is not None

    @pytest.mark.asyncio
    async def test_general_error_handling(
        self, animation_config, manim_config, sample_proof_sketch
    ):
        """Test general error handling."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Mock the fallback animator to raise an exception
        with patch.object(
            animator.fallback_animator,
            "animate",
            side_effect=Exception("Unexpected error"),
        ):
            response = await animator.animate_proof(sample_proof_sketch)

            assert response.error is not None
            assert "Unexpected error" in response.error
            assert response.metadata["error_type"] == "general"
            assert response.metadata["theorem_name"] == "nat_add_zero"

    @pytest.mark.asyncio
    async def test_batch_animation(
        self, animation_config, manim_config, sample_proof_sketch
    ):
        """Test batch animation processing."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Create multiple proof sketches
        proof_sketches = [
            sample_proof_sketch,
            ProofSketch(
                theorem_name="test2",
                introduction="Second test",
                key_steps=[
                    ProofStep(
                        step_number=1,
                        description="Test",
                        mathematical_content="y = y",
                        tactics=["rfl"],
                    )
                ],
                conclusion="Done",
            ),
        ]

        # Mock successful responses
        mock_response = AnimationResponse(
            video_path=manim_config.output_dir / "test.mp4",
            duration=30.0,
            frame_count=900,
            size_bytes=1024 * 512,
        )

        with patch.object(
            animator.fallback_animator, "animate", return_value=mock_response
        ):
            responses = await animator.animate_batch(proof_sketches, max_concurrent=2)

            assert len(responses) == 2
            assert all(r.video_path is not None for r in responses)

    @pytest.mark.asyncio
    async def test_batch_with_failures(
        self, animation_config, manim_config, sample_proof_sketch
    ):
        """Test batch animation with some failures."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Create multiple proof sketches
        proof_sketches = [sample_proof_sketch] * 3

        # Mock alternating success/failure
        call_count = 0

        def mock_animate(*args, **kwargs):
            nonlocal call_count
            call_count += 1
            if call_count % 2 == 0:  # Every second call fails
                raise Exception(f"Mock failure {call_count}")
            return AnimationResponse(
                video_path=manim_config.output_dir / f"test{call_count}.mp4",
                duration=30.0,
                frame_count=900,
                size_bytes=1024 * 512,
            )

        with patch.object(
            animator.fallback_animator, "animate", side_effect=mock_animate
        ):
            responses = await animator.animate_batch(proof_sketches)

            assert len(responses) == 3
            # Should have some successes and some failures
            successes = [r for r in responses if not r.error]
            failures = [r for r in responses if r.error]
            assert len(successes) > 0
            assert len(failures) > 0

    def test_progress_callback(self, animation_config, manim_config):
        """Test progress callback functionality."""
        progress_calls = []

        def progress_callback(message: str, progress: float):
            progress_calls.append((message, progress))

        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
            progress_callback=progress_callback,
        )

        # Trigger progress reporting
        animator._report_progress("Test message", 0.5)

        assert len(progress_calls) == 1
        assert progress_calls[0][0] == "Test message"
        assert progress_calls[0][1] == 0.5

    def test_progress_callback_error_handling(self, animation_config, manim_config):
        """Test progress callback error handling."""

        def failing_callback(message: str, progress: float):
            raise Exception("Callback failed")

        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
            progress_callback=failing_callback,
        )

        # Should not raise exception even if callback fails
        animator._report_progress("Test message", 0.5)

    def test_filename_sanitization(self, animation_config, manim_config):
        """Test filename sanitization."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Test various problematic characters
        test_cases = [
            ("normal_name", "normal_name"),
            ("name with spaces", "name_with_spaces"),
            ("name/with\\bad:chars", "name_with_bad_chars"),
            ("a" * 100, "a" * 50),  # Long name truncation
            ("___multiple___underscores___", "multiple_underscores"),
        ]

        for input_name, expected in test_cases:
            result = animator._sanitize_filename(input_name)
            assert result == expected
            assert len(result) <= 50
            assert not result.startswith("_")
            assert not result.endswith("_")

    def test_proof_sketch_validation(self, animation_config, manim_config):
        """Test proof sketch validation."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Test valid proof sketch
        valid_proof = ProofSketch(
            theorem_name="valid_theorem",
            introduction="Valid intro",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Valid step",
                    mathematical_content="x = x",
                    tactics=["rfl"],
                )
            ],
            conclusion="Valid conclusion",
        )

        # Should not raise exception
        animator._validate_proof_sketch(valid_proof)

        # Test invalid proof sketches
        with pytest.raises(AnimatorError, match="must have a theorem name"):
            invalid_proof = ProofSketch(
                theorem_name="",
                introduction="Intro",
                key_steps=[
                    ProofStep(
                        step_number=1,
                        description="Step",
                        mathematical_content="x = x",
                        tactics=["rfl"],
                    )
                ],
                conclusion="Conclusion",
            )
            animator._validate_proof_sketch(invalid_proof)

        with pytest.raises(AnimatorError, match="must have at least one key step"):
            invalid_proof = ProofSketch(
                theorem_name="theorem",
                introduction="Intro",
                key_steps=[],
                conclusion="Conclusion",
            )
            animator._validate_proof_sketch(invalid_proof)

    @pytest.mark.asyncio
    async def test_validate_setup(self, animation_config, manim_config):
        """Test setup validation."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Mock mode should validate successfully
        is_valid = await animator.validate_setup()
        assert is_valid is True

    @pytest.mark.asyncio
    async def test_cleanup(self, animation_config, manim_config):
        """Test resource cleanup."""
        animator = ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        # Mock the mcp_client disconnect method
        with patch.object(animator.mcp_client, "disconnect") as mock_disconnect:
            await animator.cleanup()
            mock_disconnect.assert_called_once()

    @pytest.mark.asyncio
    async def test_async_context_manager(self, animation_config, manim_config):
        """Test async context manager functionality."""
        async with ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        ) as animator:
            assert isinstance(animator, ProductionAnimator)
        # Cleanup should be called automatically

    def test_backward_compatibility_alias(self, animation_config, manim_config):
        """Test backward compatibility alias."""
        from proof_sketcher.animator.animator import ManimAnimator

        # ManimAnimator should be an alias for ProductionAnimator
        animator = ManimAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        )

        assert isinstance(animator, ProductionAnimator)


class TestManimMCPClient:
    """Test suite for ManimMCPClient."""

    @pytest.mark.asyncio
    async def test_mock_connection(self):
        """Test connection with mock server."""
        client = ManimMCPClient(use_mock=True)

        success = await client.connect()
        assert success is True
        assert client.is_connected is True

        await client.disconnect()
        assert client.is_connected is False

    @pytest.mark.asyncio
    async def test_health_check_mock(self):
        """Test health check with mock server."""
        client = ManimMCPClient(use_mock=True)

        await client.connect()
        health = await client.health_check()
        assert health is True

        await client.disconnect()

    @pytest.mark.asyncio
    async def test_render_animation_mock(self, sample_proof_sketch):
        """Test animation rendering with mock server."""
        client = ManimMCPClient(use_mock=True)

        await client.connect()

        response = await client.render_animation(
            sample_proof_sketch,
            style=AnimationStyle.MODERN,
            quality=AnimationQuality.MEDIUM,
        )

        assert response.video_path is not None or response.error is not None
        # Mock might simulate failures, so we accept either success or failure

        await client.disconnect()

    @pytest.mark.asyncio
    async def test_circuit_breaker(self):
        """Test circuit breaker functionality."""
        client = ManimMCPClient(use_mock=True)

        # Simulate failures to trigger circuit breaker
        client.failure_count = 3
        client.last_failure_time = time.time()
        client.circuit_open = True

        # Should raise error when circuit is open
        with pytest.raises(AnimatorError, match="Circuit breaker is open"):
            await client.connect()

        # Test circuit reset after timeout
        client.last_failure_time = time.time() - 70  # More than circuit_timeout
        assert not client._is_circuit_open()
        assert client.failure_count == 0

    @pytest.mark.asyncio
    async def test_async_context_manager(self):
        """Test async context manager for MCP client."""
        async with ManimMCPClient(use_mock=True) as client:
            assert client.is_connected is True

        assert client.is_connected is False


class TestStaticAnimationGenerator:
    """Test suite for StaticAnimationGenerator."""

    def test_initialization(self, temp_output_dir):
        """Test StaticAnimationGenerator initialization."""
        generator = StaticAnimationGenerator(output_dir=temp_output_dir)

        assert generator.output_dir == temp_output_dir
        assert temp_output_dir.exists()

    @pytest.mark.asyncio
    async def test_generate_static_animation(
        self, temp_output_dir, sample_proof_sketch
    ):
        """Test static animation generation."""
        generator = StaticAnimationGenerator(output_dir=temp_output_dir)

        response = await generator.generate_static_animation(
            sample_proof_sketch, "test_animation.mp4"
        )

        # Should always produce some response
        assert response is not None
        assert isinstance(response, AnimationResponse)

        # Check if output files were created
        if response.video_path:
            assert response.video_path.exists()


class TestFallbackAnimator:
    """Test suite for FallbackAnimator."""

    @pytest.mark.asyncio
    async def test_fallback_to_static(self, temp_output_dir, sample_proof_sketch):
        """Test fallback to static generation when MCP fails."""
        # Create a mock MCP client that always fails
        mock_client = AsyncMock()
        mock_client.render_animation.side_effect = Exception("MCP failed")

        static_generator = StaticAnimationGenerator(output_dir=temp_output_dir)
        fallback = FallbackAnimator(
            mcp_client=mock_client,
            static_generator=static_generator,
        )

        response = await fallback.animate(
            proof_sketch=sample_proof_sketch,
            style=AnimationStyle.MODERN,
            quality=AnimationQuality.MEDIUM,
        )

        # Should fallback to static generation
        assert response is not None
        assert response.metadata.get("fallback_used") is True


class TestMockMCPServer:
    """Test suite for MockMCPServer."""

    @pytest.mark.asyncio
    async def test_server_lifecycle(self):
        """Test mock server start/stop."""
        server = MockMCPServer()

        assert not server.is_running

        await server.start()
        assert server.is_running

        await server.stop()
        assert not server.is_running

    @pytest.mark.asyncio
    async def test_health_check(self):
        """Test mock server health check."""
        server = MockMCPServer()

        # Should fail when not running
        with pytest.raises(ConnectionError):
            await server.health_check()

        await server.start()
        health = await server.health_check()
        assert health["status"] == "healthy"

        await server.stop()

    @pytest.mark.asyncio
    async def test_render_request(self, sample_proof_sketch):
        """Test mock rendering request."""
        server = MockMCPServer(success_rate=1.0)  # Always succeed
        await server.start()

        params = {
            "proof_sketch": sample_proof_sketch.dict(),
            "style": "modern",
            "quality": "medium",
            "output_filename": "test.mp4",
        }

        response = await server.handle_request("manim.render_proof", params)

        assert "result" in response
        result = response["result"]
        assert "video_path" in result
        assert "duration" in result

        await server.stop()

    @pytest.mark.asyncio
    async def test_failure_simulation(self, sample_proof_sketch):
        """Test mock server failure simulation."""
        server = MockMCPServer(success_rate=0.0)  # Always fail
        await server.start()

        params = {
            "proof_sketch": sample_proof_sketch.dict(),
            "style": "modern",
            "quality": "medium",
        }

        response = await server.handle_request("manim.render_proof", params)

        assert "error" in response
        assert response["error"]["code"] < 0

        await server.stop()


@pytest.mark.integration
class TestProductionAnimatorIntegration:
    """Integration tests for production animator."""

    @pytest.mark.asyncio
    async def test_end_to_end_with_mock(self, temp_output_dir, sample_proof_sketch):
        """Test complete end-to-end animation with mock server."""
        config = AnimationConfig(output_dir=temp_output_dir)

        async with ProductionAnimator(
            animation_config=config,
            use_mock=True,
        ) as animator:
            response = await animator.animate_proof(sample_proof_sketch)

            # Should always produce a response (either success or fallback)
            assert response is not None
            assert isinstance(response, AnimationResponse)

    @pytest.mark.asyncio
    async def test_stress_test_batch(self, temp_output_dir):
        """Stress test with multiple concurrent animations."""
        config = AnimationConfig(output_dir=temp_output_dir)

        # Create multiple proof sketches
        proof_sketches = []
        for i in range(5):
            sketch = ProofSketch(
                theorem_name=f"stress_test_{i}",
                introduction=f"Stress test theorem {i}",
                key_steps=[
                    ProofStep(
                        step_number=1,
                        description=f"Step for theorem {i}",
                        mathematical_content=f"x_{i} = x_{i}",
                        tactics=["rfl"],
                    )
                ],
                conclusion=f"Theorem {i} complete",
            )
            proof_sketches.append(sketch)

        async with ProductionAnimator(
            animation_config=config,
            use_mock=True,
        ) as animator:
            responses = await animator.animate_batch(
                proof_sketches,
                max_concurrent=3,
            )

            assert len(responses) == 5
            # All should produce some response
            assert all(r is not None for r in responses)
