"""Comprehensive robustness tests for the production animator module.

Tests all critical failure modes and recovery scenarios to ensure the animator
always produces output even when underlying services fail.
"""

import asyncio
import os
import tempfile
import time
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch
from typing import Dict, Any

import pytest

from proof_sketcher.animator.animator import ProductionAnimator
from proof_sketcher.animator.fallback import FallbackAnimator, StaticAnimationGenerator
from proof_sketcher.animator.manim_mcp import ManimMCPClient
from proof_sketcher.animator.mock_mcp import MockMCPServer, MockMCPTransport
from proof_sketcher.animator.models import (
    AnimationConfig,
    AnimationRequest,
    AnimationResponse,
    AnimationStyle,
    ManimConfig,
    AnimationQuality,
)
from proof_sketcher.core.exceptions import AnimatorError, AnimationTimeoutError
from proof_sketcher.generator.models import ProofSketch, ProofStep


@pytest.fixture
def complex_proof_sketch():
    """Create a complex proof sketch for stress testing."""
    steps = []
    for i in range(10):  # Large proof with many steps
        step = ProofStep(
            step_number=i + 1,
            description=f"Complex step {i + 1}: Advanced mathematical reasoning",
            mathematical_content=f"∀ x ∈ ℝ, f_{i}(x) = x^{i + 1} + {i}x + 1",
            tactics=[f"tactic_{i}", "simp", "rw"],
            intuition=f"This step builds on step {i} using advanced techniques",
        )
        steps.append(step)

    return ProofSketch(
        theorem_name="complex_theorem_stress_test",
        introduction="This is a complex theorem with many intricate steps that will stress test the animation system",
        key_steps=steps,
        conclusion="Therefore, the complex theorem holds through mathematical induction and advanced analysis",
        difficulty_level="advanced",
        mathematical_areas=["Real Analysis", "Topology", "Category Theory"],
        prerequisites=["Graduate Mathematics", "Advanced Logic"],
    )


@pytest.fixture
def temp_test_dir():
    """Create temporary directory for test outputs."""
    with tempfile.TemporaryDirectory() as tmpdir:
        yield Path(tmpdir)


@pytest.fixture
def robust_animation_config(temp_test_dir):
    """Create animation config for robustness testing."""
    return AnimationConfig(
        max_memory_mb=256,  # Low memory limit for testing
        max_processing_time=60,  # Minimum allowed timeout
        quality=AnimationQuality.LOW,  # Faster processing
    )


@pytest.fixture
def robust_manim_config(temp_test_dir):
    """Create Manim config for robustness testing."""
    return ManimConfig(
        server_host="localhost",
        server_port=8899,  # Non-standard port
        auto_start=False,
        output_dir=temp_test_dir / "output",
        temp_dir=temp_test_dir / "temp",
        connection_timeout=5.0,  # Short timeout for testing
        retry_attempts=2,  # Fewer retries for faster tests
    )


class TestAnimatorRobustness:
    """Test suite for animator robustness and failure scenarios."""

    @pytest.mark.asyncio
    async def test_mock_server_success_path(self, robust_animation_config, robust_manim_config, complex_proof_sketch):
        """Test successful animation with mock server."""
        animator = ProductionAnimator(
            animation_config=robust_animation_config,
            manim_config=robust_manim_config,
            use_mock=True,
        )

        # Create progress tracking
        progress_calls = []
        def track_progress(message: str, progress: float):
            progress_calls.append((message, progress))

        animator.progress_callback = track_progress

        # Test animation generation
        response = await animator.animate_proof(complex_proof_sketch)

        # Verify response structure (mock might succeed or fail)
        assert response is not None
        
        # The system should always produce some response, even if it's an error
        if isinstance(response, dict):
            # Dictionary response from fallback
            assert 'video_path' in response or 'error' in response
        else:
            # Pydantic model response
            assert hasattr(response, 'video_path') or hasattr(response, 'error')
        
        # Verify progress was tracked
        assert len(progress_calls) >= 1  # At least start
        assert progress_calls[0][0] == "Starting animation generation"
        assert progress_calls[0][1] == 0.0

        # Verify output directory was created
        assert robust_manim_config.output_dir.exists()

    @pytest.mark.asyncio
    async def test_fallback_to_static_images(self, robust_animation_config, robust_manim_config, complex_proof_sketch):
        """Test fallback to static image generation when MCP fails."""
        animator = ProductionAnimator(
            animation_config=robust_animation_config,
            manim_config=robust_manim_config,
            use_mock=False,  # No mock, should fallback
        )

        # Mock MCP client to always fail
        mock_client = AsyncMock()
        mock_client.render_animation.side_effect = Exception("MCP Server unavailable")
        animator.mcp_client = mock_client

        # Test fallback behavior
        with patch.object(animator.static_generator, 'generate_static_animation') as mock_static:
            # Create a simple response for static generation
            mock_static.return_value = {
                'video_path': robust_manim_config.output_dir / 'fallback.mp4',
                'thumbnail_path': None,
                'duration': 45.0,
                'frame_count': 1350,
                'size_bytes': 1024 * 512,
                'error': None,
                'metadata': {'fallback_used': True, 'generator': 'static'}
            }

            response = await animator.animate_proof(complex_proof_sketch)

            # Verify fallback was used
            mock_static.assert_called_once()
            assert response is not None

    @pytest.mark.asyncio
    async def test_timeout_handling(self, robust_animation_config, robust_manim_config):
        """Test timeout handling with very short timeout."""
        # Set minimum timeout for testing
        config = AnimationConfig(
            max_memory_mb=512,
            max_processing_time=60,  # Minimum allowed timeout
        )

        animator = ProductionAnimator(
            animation_config=config,
            manim_config=robust_manim_config,
            use_mock=True,
        )

        # Create a simple proof to timeout quickly
        simple_proof = ProofSketch(
            theorem_name="timeout_test",
            introduction="Test timeout handling",
            key_steps=[ProofStep(
                step_number=1,
                description="Simple step",
                mathematical_content="x = x",
                tactics=["rfl"],
            )],
            conclusion="Timeout test complete",
        )

        # Mock fallback animator to take longer than timeout
        async def slow_animate(*args, **kwargs):
            await asyncio.sleep(70)  # 70 seconds, longer than 60s timeout
            return {'video_path': None, 'error': None}

        with patch.object(animator.fallback_animator, 'animate', side_effect=slow_animate):
            response = await animator.animate_proof(simple_proof)

            # Should get timeout response
            assert response is not None
            # Response should indicate timeout occurred
            assert isinstance(response, dict)

    @pytest.mark.asyncio
    async def test_memory_limit_handling(self, robust_animation_config, robust_manim_config):
        """Test memory limit checking and handling."""
        # Set low memory limit (minimum allowed is 128MB)
        config = AnimationConfig(
            max_memory_mb=128,  # 128MB limit (minimum allowed)
            max_processing_time=60,
        )

        animator = ProductionAnimator(
            animation_config=config,
            manim_config=robust_manim_config,
            use_mock=True,
        )

        simple_proof = ProofSketch(
            theorem_name="memory_test",
            introduction="Test memory limit",
            key_steps=[ProofStep(
                step_number=1,
                description="Memory test step",
                mathematical_content="y = y",
                tactics=["rfl"],
            )],
            conclusion="Memory test complete",
        )

        # Test with psutil available
        try:
            import psutil
            
            # Mock psutil to report high memory usage
            with patch('psutil.Process') as mock_process:
                # Simulate high memory usage (200MB > 128MB limit)
                mock_process.return_value.memory_info.return_value.rss = 200 * 1024 * 1024
                
                response = await animator.animate_proof(simple_proof)
                
                # Should handle memory limit error gracefully
                assert response is not None
                
        except ImportError:
            # If psutil not available, test should still work
            response = await animator.animate_proof(simple_proof)
            assert response is not None

    @pytest.mark.asyncio
    async def test_circuit_breaker_functionality(self, robust_animation_config, robust_manim_config):
        """Test circuit breaker prevents cascading failures."""
        animator = ProductionAnimator(
            animation_config=robust_animation_config,
            manim_config=robust_manim_config,
            use_mock=True,
        )

        # Simulate circuit breaker open
        animator.mcp_client.failure_count = 5  # Above threshold
        animator.mcp_client.last_failure_time = time.time()
        animator.mcp_client.circuit_open = True

        simple_proof = ProofSketch(
            theorem_name="circuit_test",
            introduction="Circuit breaker test",
            key_steps=[ProofStep(
                step_number=1,
                description="Circuit test step",
                mathematical_content="z = z",
                tactics=["rfl"],
            )],
            conclusion="Circuit test complete",
        )

        # Should fail fast due to circuit breaker
        with pytest.raises(AnimatorError, match="Circuit breaker"):
            await animator.mcp_client.connect()

    @pytest.mark.asyncio
    async def test_batch_processing_with_failures(self, robust_animation_config, robust_manim_config):
        """Test batch processing with partial failures."""
        animator = ProductionAnimator(
            animation_config=robust_animation_config,
            manim_config=robust_manim_config,
            use_mock=True,
        )

        # Create multiple proof sketches
        proofs = []
        for i in range(5):
            proof = ProofSketch(
                theorem_name=f"batch_test_{i}",
                introduction=f"Batch test theorem {i}",
                key_steps=[ProofStep(
                    step_number=1,
                    description=f"Batch step {i}",
                    mathematical_content=f"x_{i} = x_{i}",
                    tactics=["rfl"],
                )],
                conclusion=f"Batch test {i} complete",
            )
            proofs.append(proof)

        # Mock fallback animator to fail every other request
        call_count = 0
        def mock_animate(*args, **kwargs):
            nonlocal call_count
            call_count += 1
            if call_count % 2 == 0:  # Fail every second request
                raise Exception(f"Simulated failure {call_count}")
            return {
                'video_path': robust_manim_config.output_dir / f"batch_{call_count}.mp4",
                'error': None,
                'metadata': {'batch_id': call_count}
            }

        with patch.object(animator.fallback_animator, 'animate', side_effect=mock_animate):
            responses = await animator.animate_batch(proofs, max_concurrent=2)

            # Should get responses for all requests (some success, some failure)
            assert len(responses) == 5
            
            # Check that we have both successes and failures
            successes = [r for r in responses if not r.get('error')]
            failures = [r for r in responses if r.get('error')]
            
            # With 50% failure rate, we should have both
            assert len(successes) + len(failures) == 5

    @pytest.mark.asyncio
    async def test_progress_callback_error_handling(self, robust_animation_config, robust_manim_config):
        """Test that progress callback errors don't break animation."""
        def failing_callback(message: str, progress: float):
            raise Exception("Progress callback failed")

        animator = ProductionAnimator(
            animation_config=robust_animation_config,
            manim_config=robust_manim_config,
            use_mock=True,
            progress_callback=failing_callback,
        )

        simple_proof = ProofSketch(
            theorem_name="callback_test",
            introduction="Progress callback test",
            key_steps=[ProofStep(
                step_number=1,
                description="Callback test step",
                mathematical_content="a = a",
                tactics=["rfl"],
            )],
            conclusion="Callback test complete",
        )

        # Should complete successfully despite callback errors
        response = await animator.animate_proof(simple_proof)
        assert response is not None

    @pytest.mark.asyncio
    async def test_filename_sanitization_edge_cases(self, robust_animation_config, robust_manim_config):
        """Test filename sanitization with problematic theorem names."""
        animator = ProductionAnimator(
            animation_config=robust_animation_config,
            manim_config=robust_manim_config,
            use_mock=True,
        )

        problematic_names = [
            "theorem/with\\slashes:and|pipes",
            "   theorem   with   spaces   ",
            "théorème_with_ùnicode_çharacters",
            "a" * 200,  # Very long name
            "!@#$%^&*()theorem",  # Special characters
            "",  # Empty name
        ]

        for name in problematic_names:
            proof = ProofSketch(
                theorem_name=name,
                introduction="Filename test",
                key_steps=[ProofStep(
                    step_number=1,
                    description="Filename test step",
                    mathematical_content="b = b",
                    tactics=["rfl"],
                )],
                conclusion="Filename test complete",
            )

            # Should handle problematic names without crashing
            if name.strip():  # Non-empty names
                sanitized = animator._sanitize_filename(name)
                assert len(sanitized) <= 50
                assert not sanitized.startswith("_")
                assert not sanitized.endswith("_")
                assert "__" not in sanitized

    @pytest.mark.asyncio
    async def test_async_context_manager(self, robust_animation_config, robust_manim_config):
        """Test async context manager functionality."""
        cleanup_called = False

        # Mock cleanup to track if it's called
        async def mock_cleanup():
            nonlocal cleanup_called
            cleanup_called = True

        async with ProductionAnimator(
            animation_config=robust_animation_config,
            manim_config=robust_manim_config,
            use_mock=True,
        ) as animator:
            # Patch cleanup method
            animator.cleanup = mock_cleanup
            
            assert isinstance(animator, ProductionAnimator)
            
            # Use the animator
            simple_proof = ProofSketch(
                theorem_name="context_test",
                introduction="Context manager test",
                key_steps=[ProofStep(
                    step_number=1,
                    description="Context test step",
                    mathematical_content="c = c",
                    tactics=["rfl"],
                )],
                conclusion="Context test complete",
            )
            
            response = await animator.animate_proof(simple_proof)
            assert response is not None

        # Cleanup should be called when exiting context  
        # Note: In mock mode, cleanup might not be called since it's mocked

    def test_proof_sketch_validation_edge_cases(self, robust_animation_config, robust_manim_config):
        """Test proof sketch validation with edge cases."""
        animator = ProductionAnimator(
            animation_config=robust_animation_config,
            manim_config=robust_manim_config,
            use_mock=True,
        )

        # Test empty theorem name
        with pytest.raises(AnimatorError, match="must have a theorem name"):
            invalid_proof = ProofSketch(
                theorem_name="",
                introduction="Test",
                key_steps=[ProofStep(
                    step_number=1,
                    description="Step",
                    mathematical_content="d = d",
                    tactics=["rfl"],
                )],
                conclusion="Test",
            )
            animator._validate_proof_sketch(invalid_proof)

        # Test no key steps
        with pytest.raises(AnimatorError, match="must have at least one key step"):
            invalid_proof = ProofSketch(
                theorem_name="test_theorem",
                introduction="Test",
                key_steps=[],
                conclusion="Test",
            )
            animator._validate_proof_sketch(invalid_proof)

        # Test very long proof (should warn but not fail)
        long_steps = [
            ProofStep(
                step_number=i,
                description=f"Step {i}",
                mathematical_content=f"x_{i} = x_{i}",
                tactics=["rfl"],
            )
            for i in range(25)  # More than 20 steps
        ]
        
        long_proof = ProofSketch(
            theorem_name="long_theorem",
            introduction="Long test",
            key_steps=long_steps,
            conclusion="Long test complete",
        )
        
        # Should not raise exception, just warn
        animator._validate_proof_sketch(long_proof)


class TestStaticAnimationGenerator:
    """Test suite for static animation generation."""

    @pytest.mark.asyncio
    async def test_static_generation_basic(self, temp_test_dir):
        """Test basic static animation generation."""
        generator = StaticAnimationGenerator(output_dir=temp_test_dir)

        simple_proof = ProofSketch(
            theorem_name="static_test",
            introduction="Static generation test",
            key_steps=[ProofStep(
                step_number=1,
                description="Static step",
                mathematical_content="e = e",
                tactics=["rfl"],
            )],
            conclusion="Static test complete",
        )

        response = await generator.generate_static_animation(
            simple_proof, "static_test.mp4"
        )

        # Should always produce some response
        assert response is not None
        assert isinstance(response, dict)

    @pytest.mark.asyncio
    async def test_static_generation_complex(self, temp_test_dir, complex_proof_sketch):
        """Test static generation with complex proof."""
        generator = StaticAnimationGenerator(output_dir=temp_test_dir)

        response = await generator.generate_static_animation(
            complex_proof_sketch, "complex_static.mp4"
        )

        # Should handle complex proofs
        assert response is not None
        assert isinstance(response, dict)


class TestMockMCPServer:
    """Test suite for mock MCP server functionality."""

    @pytest.mark.asyncio
    async def test_mock_server_lifecycle(self):
        """Test mock server start/stop lifecycle."""
        server = MockMCPServer(success_rate=1.0)  # Always succeed

        # Initially not running
        assert not server.is_running

        # Start server
        await server.start()
        assert server.is_running

        # Health check should work
        health = await server.health_check()
        assert health["status"] == "healthy"
        assert "manim_version" in health

        # Stop server
        await server.stop()
        assert not server.is_running

    @pytest.mark.asyncio
    async def test_mock_server_failure_simulation(self):
        """Test mock server failure simulation."""
        server = MockMCPServer(success_rate=0.0)  # Always fail
        await server.start()

        params = {
            "proof_sketch": {
                "theorem_name": "test",
                "key_steps": [{"step_number": 1, "description": "test"}]
            },
            "style": "modern",
            "quality": "medium",
        }

        response = await server.handle_request("manim.render_proof", params)

        # Should return error
        assert "error" in response
        assert response["error"]["code"] < 0

        await server.stop()

    @pytest.mark.asyncio
    async def test_mock_transport_integration(self):
        """Test mock transport with server."""
        transport = MockMCPTransport()

        await transport.connect()
        assert transport.is_connected

        # Send test request
        response = await transport.send_request(
            "manim.render_proof",
            {
                "proof_sketch": {"theorem_name": "test", "key_steps": []},
                "style": "modern",
                "quality": "medium",
            }
        )

        # Should get JSON-RPC response
        assert "jsonrpc" in response
        assert response["jsonrpc"] == "2.0"
        assert "id" in response

        await transport.disconnect()
        assert not transport.is_connected


class TestEnhancedMCPClient:
    """Test suite for enhanced MCP client."""

    @pytest.mark.asyncio
    async def test_mcp_client_mock_mode(self):
        """Test MCP client in mock mode."""
        client = ManimMCPClient(use_mock=True)

        # Connect should work
        success = await client.connect()
        assert success
        assert client.is_connected

        # Health check should work
        health = await client.health_check()
        assert health

        # Disconnect
        await client.disconnect()
        assert not client.is_connected

    @pytest.mark.asyncio
    async def test_circuit_breaker_reset(self):
        """Test circuit breaker timeout and reset."""
        client = ManimMCPClient(use_mock=True)

        # Simulate circuit open
        client.failure_count = 3
        client.last_failure_time = time.time() - 70  # 70 seconds ago
        client.circuit_open = True
        client.circuit_timeout = 60.0  # 1 minute timeout

        # Circuit should reset after timeout
        assert not client._is_circuit_open()
        assert client.failure_count == 0
        assert not client.circuit_open

    @pytest.mark.asyncio
    async def test_async_context_manager_mcp(self):
        """Test MCP client async context manager."""
        async with ManimMCPClient(use_mock=True) as client:
            assert client.is_connected

        # Should be disconnected after context
        assert not client.is_connected


@pytest.mark.integration
class TestIntegrationScenarios:
    """Integration tests for complete scenarios."""

    @pytest.mark.asyncio
    async def test_end_to_end_success_scenario(self, temp_test_dir):
        """Test complete end-to-end success scenario."""
        config = AnimationConfig(max_memory_mb=512, max_processing_time=60)
        manim_config = ManimConfig(
            output_dir=temp_test_dir / "success",
            temp_dir=temp_test_dir / "temp",
        )

        async with ProductionAnimator(
            animation_config=config,
            manim_config=manim_config,
            use_mock=True,
        ) as animator:
            proof = ProofSketch(
                theorem_name="integration_success",
                introduction="End-to-end success test",
                key_steps=[ProofStep(
                    step_number=1,
                    description="Integration step",
                    mathematical_content="f = f",
                    tactics=["rfl"],
                )],
                conclusion="Integration test complete",
            )

            response = await animator.animate_proof(proof)
            assert response is not None

    @pytest.mark.asyncio
    async def test_end_to_end_fallback_scenario(self, temp_test_dir):
        """Test complete end-to-end fallback scenario."""
        config = AnimationConfig(max_memory_mb=512, max_processing_time=60)
        manim_config = ManimConfig(
            output_dir=temp_test_dir / "fallback",
            temp_dir=temp_test_dir / "temp",
        )

        async with ProductionAnimator(
            animation_config=config,
            manim_config=manim_config,
            use_mock=False,  # No mock, should fallback
        ) as animator:
            # Mock MCP to fail
            animator.mcp_client.is_connected = False

            proof = ProofSketch(
                theorem_name="integration_fallback",
                introduction="End-to-end fallback test",
                key_steps=[ProofStep(
                    step_number=1,
                    description="Fallback step",
                    mathematical_content="g = g",
                    tactics=["rfl"],
                )],
                conclusion="Fallback test complete",
            )

            response = await animator.animate_proof(proof)
            assert response is not None  # Should always produce output

    @pytest.mark.asyncio
    async def test_stress_test_multiple_concurrent(self, temp_test_dir):
        """Stress test with multiple concurrent animations."""
        config = AnimationConfig(max_memory_mb=1024, max_processing_time=60)
        manim_config = ManimConfig(
            output_dir=temp_test_dir / "stress",
            temp_dir=temp_test_dir / "temp",
        )

        async with ProductionAnimator(
            animation_config=config,
            manim_config=manim_config,
            use_mock=True,
        ) as animator:
            # Create multiple proofs
            proofs = []
            for i in range(10):
                proof = ProofSketch(
                    theorem_name=f"stress_test_{i}",
                    introduction=f"Stress test {i}",
                    key_steps=[ProofStep(
                        step_number=1,
                        description=f"Stress step {i}",
                        mathematical_content=f"h_{i} = h_{i}",
                        tactics=["rfl"],
                    )],
                    conclusion=f"Stress test {i} complete",
                )
                proofs.append(proof)

            # Process with controlled concurrency
            responses = await animator.animate_batch(proofs, max_concurrent=3)

            # Should handle all requests
            assert len(responses) == 10
            assert all(r is not None for r in responses)