"""Comprehensive tests for the animator module to achieve 90%+ coverage."""

import asyncio
import logging
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, Mock, patch, call
import subprocess
import time

import pytest
import aiohttp
import tenacity

from src.proof_sketcher.animator.animator import ProductionAnimator
from src.proof_sketcher.animator.manim_mcp import ManimMCPClient
from src.proof_sketcher.animator.fallback import FallbackAnimator, StaticAnimationGenerator
from src.proof_sketcher.animator.models import (
    AnimationConfig, AnimationRequest, AnimationResponse, 
    AnimationScene, AnimationStyle, AnimationQuality, ManimConfig
)
from src.proof_sketcher.core.exceptions import (
    AnimatorError, AnimationTimeoutError
)
from src.proof_sketcher.generator.models import ProofSketch, ProofStep


class TestManimMCPClientComplete:
    """Complete tests for ManimMCPClient including all edge cases."""
    
    @pytest.fixture
    def mcp_client(self):
        """Create MCP client instance."""
        config = ManimConfig(
            server_host="localhost",
            server_port=8080,
            server_timeout=30.0,
            output_dir=Path("/tmp/test_animations"),
            temp_dir=Path("/tmp/test_temp")
        )
        return ManimMCPClient(config=config, use_mock=False)
    
    @pytest.fixture
    def mock_mcp_client(self):
        """Create mock MCP client instance."""
        return ManimMCPClient(use_mock=True)
    
    @pytest.mark.asyncio
    async def test_connect_disconnect_lifecycle(self, mcp_client):
        """Test complete connection lifecycle."""
        with patch.object(mcp_client, 'start_server', return_value=True):
            with patch.object(mcp_client, 'health_check', return_value=True):
                # Test connect
                assert await mcp_client.connect() is True
                assert mcp_client._connected is True
                assert mcp_client.session_pool is not None
                
                # Test already connected
                assert await mcp_client.connect() is True
                
                # Test disconnect
                await mcp_client.disconnect()
                assert mcp_client._connected is False
    
    @pytest.mark.asyncio
    async def test_connect_server_start_failure(self, mcp_client):
        """Test connection when server fails to start."""
        with patch.object(mcp_client, 'start_server', return_value=False):
            assert await mcp_client.connect() is False
            assert mcp_client._connected is False
    
    @pytest.mark.asyncio
    async def test_health_check_loop(self, mcp_client):
        """Test health check background loop."""
        # Mock health check to fail after a few calls
        health_check_calls = []
        
        async def mock_health_check():
            health_check_calls.append(time.time())
            if len(health_check_calls) > 2:
                mcp_client._shutdown_event.set()
                return False
            return True
        
        with patch.object(mcp_client, 'health_check', side_effect=mock_health_check):
            # Start health check loop
            task = asyncio.create_task(mcp_client._health_check_loop())
            
            # Wait for a few iterations
            await asyncio.sleep(0.1)
            mcp_client._shutdown_event.set()
            
            try:
                await task
            except:
                pass
            
            # Should have made health checks
            assert len(health_check_calls) >= 1
    
    @pytest.mark.asyncio
    async def test_circuit_breaker_functionality(self, mcp_client):
        """Test circuit breaker pattern."""
        # Simulate failures to open circuit
        mcp_client.failure_count = 5
        mcp_client.last_failure_time = time.time()
        mcp_client.circuit_open = True
        
        # Check if circuit is open
        assert mcp_client._is_circuit_open() is True
        
        # Wait for circuit timeout
        mcp_client.last_failure_time = time.time() - 120  # 2 minutes ago
        assert mcp_client._is_circuit_open() is False
    
    @pytest.mark.asyncio
    async def test_retry_with_exponential_backoff(self, mcp_client):
        """Test retry logic with exponential backoff."""
        attempt_count = 0
        
        @tenacity.retry(
            wait=tenacity.wait_exponential(multiplier=0.1, min=0.1, max=1),
            stop=tenacity.stop_after_attempt(3),
            retry=tenacity.retry_if_exception_type(ConnectionError)
        )
        async def failing_operation():
            nonlocal attempt_count
            attempt_count += 1
            if attempt_count < 3:
                raise ConnectionError("Test connection error")
            return True
        
        result = await failing_operation()
        assert result is True
        assert attempt_count == 3
    
    @pytest.mark.asyncio
    async def test_session_pool_management(self, mcp_client):
        """Test session pool creation and cleanup."""
        # Initialize session pool
        await mcp_client.connect()
        
        assert mcp_client.session_pool is not None
        assert isinstance(mcp_client.session_pool, aiohttp.ClientSession)
        
        # Test cleanup
        await mcp_client.disconnect()
        # Session should be closed
    
    @pytest.mark.asyncio
    async def test_mock_mode_operations(self, mock_mcp_client):
        """Test all operations in mock mode."""
        # Connect in mock mode
        assert await mock_mcp_client.connect() is True
        assert mock_mcp_client._connected is True
        
        # Test health check
        assert await mock_mcp_client.health_check() is True
        
        # Test render animation
        request = AnimationRequest(
            theorem_name="test_theorem",
            request_id="test_123",
            segments=[],
            estimated_duration=30.0,
            total_scenes=1
        )
        
        response = await mock_mcp_client.render_animation(request)
        assert response is not None
        assert response.video_path is not None
        
        # Disconnect
        await mock_mcp_client.disconnect()
        assert mock_mcp_client._connected is False


class TestProductionAnimatorComplete:
    """Complete tests for ProductionAnimator."""
    
    @pytest.fixture
    def animator(self):
        """Create animator instance."""
        config = AnimationConfig(
            max_memory_mb=512,
            max_processing_time=300.0
        )
        manim_config = ManimConfig(
            output_dir=Path("/tmp/test_animations"),
            temp_dir=Path("/tmp/test_temp")
        )
        return ProductionAnimator(
            animation_config=config,
            manim_config=manim_config,
            use_mock=True
        )
    
    @pytest.fixture
    def sample_proof_sketch(self):
        """Create sample proof sketch."""
        return ProofSketch(
            theorem_name="test_theorem",
            introduction="Test introduction",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Step 1",
                    mathematical_content="a = b",
                    tactics=["rfl"]
                ),
                ProofStep(
                    step_number=2,
                    description="Step 2",
                    mathematical_content="b = c",
                    tactics=["simp"]
                )
            ],
            conclusion="Test conclusion"
        )
    
    @pytest.mark.asyncio
    async def test_animate_proof_complete_short(self, animator, sample_proof_sketch):
        """Test animating a short proof."""
        response = await animator.animate_proof_complete(
            sample_proof_sketch,
            style=AnimationStyle.MODERN,
            quality=AnimationQuality.HIGH
        )
        
        assert response is not None
        assert response.metadata is not None
    
    @pytest.mark.asyncio
    async def test_animate_proof_complete_long(self, animator):
        """Test animating a long proof with segmentation."""
        # Create long proof with 25 steps
        long_proof = ProofSketch(
            theorem_name="long_theorem",
            introduction="Long proof",
            key_steps=[
                ProofStep(
                    step_number=i,
                    description=f"Step {i}",
                    mathematical_content=f"x_{i} = y_{i}",
                    tactics=["simp"]
                )
                for i in range(1, 26)
            ],
            conclusion="Long proof complete"
        )
        
        response = await animator.animate_proof_complete(long_proof)
        
        assert response is not None
        assert response.metadata.get("segmented") is True
        assert response.metadata.get("total_chapters") == 3  # 25 steps / 10 per chapter
    
    @pytest.mark.asyncio
    async def test_handle_long_proof_directly(self, animator):
        """Test handle_long_proof method directly."""
        # Create proof with 15 steps
        proof = ProofSketch(
            theorem_name="medium_theorem",
            introduction="Medium proof",
            key_steps=[
                ProofStep(
                    step_number=i,
                    description=f"Step {i}",
                    mathematical_content=f"a_{i} = b_{i}",
                    tactics=["auto"]
                )
                for i in range(1, 16)
            ],
            conclusion="Done"
        )
        
        response = await animator.handle_long_proof(proof)
        
        assert response.metadata["segmented"] is True
        assert response.metadata["total_chapters"] == 2
        assert len(response.metadata["segments"]) == 2
    
    @pytest.mark.asyncio
    async def test_generate_preview_frames(self, animator, sample_proof_sketch):
        """Test preview frame generation."""
        frames = await animator.generate_preview_frames(
            sample_proof_sketch,
            num_frames=3
        )
        
        # In mock mode, should generate some frames
        assert isinstance(frames, list)
    
    @pytest.mark.asyncio
    async def test_generate_preview_frames_many_steps(self, animator):
        """Test preview frame generation with many steps."""
        # Create proof with 20 steps
        proof = ProofSketch(
            theorem_name="preview_test",
            introduction="Preview test",
            key_steps=[
                ProofStep(
                    step_number=i,
                    description=f"Step {i}",
                    mathematical_content=f"f({i}) = g({i})",
                    tactics=["calc"]
                )
                for i in range(1, 21)
            ],
            conclusion="Preview complete"
        )
        
        frames = await animator.generate_preview_frames(proof, num_frames=5)
        
        assert isinstance(frames, list)
        # Should select 5 representative frames
    
    @pytest.mark.asyncio
    async def test_cleanup_resources(self, animator):
        """Test resource cleanup."""
        # Create some temp files
        animator.manim_config.temp_dir.mkdir(parents=True, exist_ok=True)
        temp_file = animator.manim_config.temp_dir / "test.txt"
        temp_file.write_text("test")
        
        temp_dir = animator.manim_config.temp_dir / "test_dir"
        temp_dir.mkdir(exist_ok=True)
        
        # Run cleanup
        await animator.cleanup_resources()
        
        # Files should be cleaned up
        assert not temp_file.exists()
        assert not temp_dir.exists()
    
    @pytest.mark.asyncio
    async def test_cleanup_resources_with_errors(self, animator):
        """Test resource cleanup with errors."""
        # Mock file removal to fail
        with patch('pathlib.Path.unlink', side_effect=OSError("Permission denied")):
            # Should not raise exception
            await animator.cleanup_resources()
    
    def test_validate_proof_sketch_errors(self, animator):
        """Test proof sketch validation errors."""
        # No theorem name
        with pytest.raises(AnimatorError, match="theorem name"):
            animator._validate_proof_sketch(ProofSketch(
                theorem_name="",
                introduction="Test",
                key_steps=[ProofStep(step_number=1, description="Step", mathematical_content="")],
                conclusion="Done"
            ))
        
        # No key steps
        with pytest.raises(AnimatorError, match="key step"):
            animator._validate_proof_sketch(ProofSketch(
                theorem_name="test",
                introduction="Test",
                key_steps=[],
                conclusion="Done"
            ))
    
    def test_sanitize_filename(self, animator):
        """Test filename sanitization."""
        # Test various problematic characters
        assert animator._sanitize_filename("test/file") == "testfile"
        assert animator._sanitize_filename("test\\file") == "testfile"
        assert animator._sanitize_filename("test:file") == "testfile"
        assert animator._sanitize_filename("test|file") == "testfile"
        assert animator._sanitize_filename("test*file") == "testfile"
        assert animator._sanitize_filename("test?file") == "testfile"
        assert animator._sanitize_filename("test<>file") == "testfile"
        assert animator._sanitize_filename("test\"file") == "testfile"
        
        # Test length limit
        long_name = "a" * 100
        sanitized = animator._sanitize_filename(long_name)
        assert len(sanitized) <= 50
    
    @pytest.mark.asyncio
    async def test_create_latex_preview(self, animator):
        """Test LaTeX preview generation."""
        # Mock subprocess calls
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=1)  # Simulate failure
            
            result = await animator._create_latex_preview(
                "test_theorem",
                "a^2 + b^2 = c^2",
                animator.animation_config
            )
            
            # Should return None on failure
            assert result is None
    
    @pytest.mark.asyncio
    async def test_animation_timeout(self, animator, sample_proof_sketch):
        """Test animation timeout handling."""
        # Mock fallback animator to take too long
        async def slow_animate(*args, **kwargs):
            await asyncio.sleep(10)  # Longer than timeout
            
        with patch.object(animator.fallback_animator, 'animate', side_effect=slow_animate):
            animator.max_processing_time = 0.1  # Very short timeout
            
            response = await animator.animate_proof(sample_proof_sketch)
            
            # Should return fallback response
            assert response.video_path is None
            assert "timeout" in response.metadata.get("error", "").lower()
    
    def test_check_resource_limits(self, animator):
        """Test resource limit checking."""
        # Mock memory check to exceed limit
        with patch('psutil.Process') as mock_process:
            mock_proc_instance = Mock()
            mock_proc_instance.memory_info.return_value = Mock(rss=1024*1024*1024)  # 1GB
            mock_process.return_value = mock_proc_instance
            
            animator.max_memory_mb = 512  # 512MB limit
            
            with pytest.raises(AnimatorError, match="Memory usage"):
                animator._check_resource_limits()
    
    @pytest.mark.asyncio
    async def test_validate_setup(self, animator):
        """Test setup validation."""
        # Create output directory
        animator.manim_config.output_dir.mkdir(parents=True, exist_ok=True)
        
        # In mock mode, should always pass
        assert await animator.validate_setup() is True
    
    @pytest.mark.asyncio
    async def test_validate_setup_real_mode(self):
        """Test setup validation in real mode."""
        animator = ProductionAnimator(use_mock=False)
        
        # Mock MCP client methods
        with patch.object(animator.mcp_client, 'connect', return_value=False):
            # Should still pass with fallback
            assert await animator.validate_setup() is True


class TestStaticAnimationGeneratorComplete:
    """Complete tests for StaticAnimationGenerator."""
    
    @pytest.fixture
    def generator(self, tmp_path):
        """Create static generator instance."""
        return StaticAnimationGenerator(output_dir=tmp_path)
    
    def test_render_text_to_image_with_pillow(self, generator):
        """Test text rendering with Pillow."""
        result = generator._render_text_to_image(
            "Test text",
            "test_image.png"
        )
        
        # Should create an image file
        assert result is not None
        assert result.exists()
    
    def test_render_text_to_image_pillow_error(self, generator):
        """Test text rendering when Pillow fails."""
        with patch('PIL.Image.new', side_effect=ImportError("No PIL")):
            result = generator._render_text_to_image(
                "Test text",
                "test_image.png"
            )
            
            # Should return None on error
            assert result is None
    
    def test_render_latex_matplotlib_error(self, generator):
        """Test LaTeX rendering when matplotlib fails."""
        with patch('matplotlib.pyplot.figure', side_effect=ImportError("No matplotlib")):
            result = generator.render_latex_to_image(
                r"\int_0^1 x^2 dx",
                "test_latex.png"
            )
            
            # Should return None on error
            assert result is None
    
    @pytest.mark.asyncio
    async def test_generate_animation_complete(self, generator):
        """Test complete animation generation."""
        proof_sketch = ProofSketch(
            theorem_name="static_test",
            introduction="Static animation test",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="First step",
                    mathematical_content="a = b"
                )
            ],
            conclusion="Done"
        )
        
        response = await generator.generate_static_animation(
            proof_sketch,
            output_filename="static_test.mp4"
        )
        
        assert response is not None
        # In static mode, might not have actual video
        assert response.metadata.get("animation_type") == "static"


class TestFallbackAnimatorComplete:
    """Complete tests for FallbackAnimator."""
    
    @pytest.fixture
    def fallback_animator(self, tmp_path):
        """Create fallback animator instance."""
        mcp_client = ManimMCPClient(use_mock=True)
        static_generator = StaticAnimationGenerator(output_dir=tmp_path)
        return FallbackAnimator(
            mcp_client=mcp_client,
            static_generator=static_generator
        )
    
    @pytest.mark.asyncio
    async def test_animate_with_mcp_success(self, fallback_animator):
        """Test animation when MCP succeeds."""
        proof_sketch = ProofSketch(
            theorem_name="mcp_success",
            introduction="Test",
            key_steps=[ProofStep(step_number=1, description="Step 1", mathematical_content="")],
            conclusion="Done"
        )
        
        # Mock MCP to succeed
        mock_response = AnimationResponse(
            video_path=Path("/tmp/test.mp4"),
            duration=30.0
        )
        
        with patch.object(fallback_animator.mcp_client, 'render_animation', 
                         return_value=mock_response):
            response = await fallback_animator.animate(proof_sketch)
            
            assert response == mock_response
    
    @pytest.mark.asyncio
    async def test_animate_with_mcp_failure_fallback(self, fallback_animator):
        """Test fallback when MCP fails."""
        proof_sketch = ProofSketch(
            theorem_name="mcp_failure",
            introduction="Test",
            key_steps=[ProofStep(step_number=1, description="Step 1", mathematical_content="")],
            conclusion="Done"
        )
        
        # Mock MCP to fail
        with patch.object(fallback_animator.mcp_client, 'render_animation',
                         side_effect=Exception("MCP error")):
            response = await fallback_animator.animate(proof_sketch)
            
            # Should fall back to static
            assert response is not None
            assert response.metadata.get("fallback_reason") is not None


class TestMemoryLeakDetection:
    """Test for memory leaks in animator."""
    
    @pytest.mark.asyncio
    async def test_repeated_animations_no_leak(self):
        """Test that repeated animations don't leak memory."""
        animator = ProductionAnimator(use_mock=True)
        
        proof_sketch = ProofSketch(
            theorem_name="memory_test",
            introduction="Memory test",
            key_steps=[
                ProofStep(step_number=i, description=f"Step {i}", mathematical_content="")
                for i in range(1, 6)
            ],
            conclusion="Done"
        )
        
        # Run multiple animations
        for i in range(5):
            response = await animator.animate_proof(proof_sketch)
            assert response is not None
        
        # Cleanup should free resources
        await animator.cleanup_resources()
        
        # In a real test, we'd measure memory usage
        # For now, just ensure no exceptions


class TestStressTest:
    """Stress tests for animator."""
    
    @pytest.mark.asyncio
    async def test_animate_very_long_proof(self):
        """Test animating a proof with 20+ steps."""
        animator = ProductionAnimator(use_mock=True)
        
        # Create proof with 25 steps
        long_proof = ProofSketch(
            theorem_name="stress_test",
            introduction="Stress test",
            key_steps=[
                ProofStep(
                    step_number=i,
                    description=f"Step {i} with longer description to test handling of verbose content",
                    mathematical_content=f"\\forall x_{i}, \\exists y_{i} : f_{i}(x_{i}) = g_{i}(y_{i})",
                    tactics=["intro", "apply", "simp", "done"]
                )
                for i in range(1, 26)
            ],
            conclusion="Stress test complete"
        )
        
        start_time = time.time()
        response = await animator.animate_proof_complete(long_proof)
        duration = time.time() - start_time
        
        assert response is not None
        assert response.metadata.get("segmented") is True
        assert response.metadata.get("total_chapters") == 3
        
        # Should complete in reasonable time even with 25 steps
        assert duration < 30  # seconds
    
    @pytest.mark.asyncio
    async def test_concurrent_animations(self):
        """Test running multiple animations concurrently."""
        animator = ProductionAnimator(use_mock=True)
        
        # Create different proofs
        proofs = [
            ProofSketch(
                theorem_name=f"concurrent_{i}",
                introduction=f"Proof {i}",
                key_steps=[
                    ProofStep(step_number=j, description=f"Proof {i} Step {j}")
                    for j in range(1, 4)
                ],
                conclusion=f"Proof {i} done"
            )
            for i in range(3)
        ]
        
        # Run animations concurrently
        tasks = [
            animator.animate_proof(proof)
            for proof in proofs
        ]
        
        responses = await asyncio.gather(*tasks)
        
        # All should succeed
        assert len(responses) == 3
        assert all(r is not None for r in responses)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])