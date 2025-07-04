"""Focused tests to boost animator module coverage to 90%+."""

import asyncio
from pathlib import Path
from unittest.mock import Mock, patch, AsyncMock, MagicMock
import subprocess
import time

import pytest
import aiohttp

from src.proof_sketcher.animator.animator import ProductionAnimator
from src.proof_sketcher.animator.manim_mcp import ManimMCPClient
from src.proof_sketcher.animator.fallback import FallbackAnimator, StaticAnimationGenerator
from src.proof_sketcher.animator.models import (
    AnimationConfig, AnimationRequest, AnimationResponse,
    AnimationScene, AnimationStyle, AnimationQuality, ManimConfig,
    AnimationSegment, FormulaComponent, TransformationType
)
from src.proof_sketcher.core.exceptions import (
    AnimatorError, AnimationTimeoutError, MCPConnectionError
)
from src.proof_sketcher.generator.models import ProofSketch, ProofStep


class TestManimMCPClientCoverage:
    """Tests to improve ManimMCPClient coverage."""
    
    @pytest.mark.asyncio
    async def test_is_server_running_states(self):
        """Test is_server_running method in different states."""
        client = ManimMCPClient(use_mock=False)
        
        # No process
        assert client.is_server_running() is False
        
        # With process
        mock_process = Mock()
        mock_process.poll.return_value = None  # Still running
        client.server_process = mock_process
        assert client.is_server_running() is True
        
        # Process terminated
        mock_process.poll.return_value = 0
        assert client.is_server_running() is False
    
    @pytest.mark.asyncio
    async def test_wait_for_server_ready_timeout(self):
        """Test server ready timeout."""
        client = ManimMCPClient(use_mock=False)
        
        # The _wait_for_server_ready method is internal and uses a fixed timeout
        # We can test it indirectly through start_server
        client.config.server_timeout = 0.1
        with patch.object(client, 'health_check', return_value=False):
            with patch.object(client, '_check_manim_available', return_value=True):
                result = await client.start_server()
                assert result is False  # Should fail due to timeout
    
    @pytest.mark.asyncio 
    async def test_increment_circuit_breaker(self):
        """Test circuit breaker increment."""
        client = ManimMCPClient(use_mock=False)
        
        # Increment failures
        client._increment_circuit_breaker()
        assert client.failure_count == 1
        
        # Multiple increments
        for _ in range(4):
            client._increment_circuit_breaker()
        
        assert client.failure_count == 5
        assert client.circuit_open is True
    
    @pytest.mark.asyncio
    async def test_render_animation_circuit_open(self):
        """Test render when circuit is open."""
        client = ManimMCPClient(use_mock=False)
        client.circuit_open = True
        client.last_failure_time = time.time()
        
        request = AnimationRequest(
            theorem_name="test",
            request_id="test_123",
            segments=[],
            estimated_duration=30.0,
            total_scenes=1
        )
        
        with pytest.raises(MCPConnectionError, match="Circuit breaker is open"):
            await client.render_animation(request)
    
    @pytest.mark.asyncio
    async def test_render_animation_mock_mode(self):
        """Test animation rendering in mock mode."""
        client = ManimMCPClient(use_mock=True)
        
        request = AnimationRequest(
            theorem_name="mock_test",
            request_id="mock_123",
            segments=[
                AnimationSegment(
                    segment_id="seg1",
                    title="Segment 1",
                    scenes=[
                        AnimationScene(
                            scene_id="scene1",
                            title="Test Scene",
                            duration=5.0,
                            initial_formula="a = b",
                            final_formula="b = c",
                            transformation_type=TransformationType.SUBSTITUTION
                        )
                    ],
                    total_duration=5.0
                )
            ],
            estimated_duration=5.0,
            total_scenes=1
        )
        
        response = await client.render_animation(request)
        assert response is not None
        assert response.video_path is not None
    
    @pytest.mark.asyncio
    async def test_health_check_not_connected(self):
        """Test health check when not connected."""
        client = ManimMCPClient(use_mock=False) 
        client._connected = False
        
        result = await client.health_check()
        assert result is False
    
    @pytest.mark.asyncio
    async def test_get_session_pool_closed(self):
        """Test getting session from closed pool."""
        client = ManimMCPClient(use_mock=False)
        
        # Create and close session
        client.session_pool = aiohttp.ClientSession()
        await client.session_pool.close()
        
        # Should create new session
        async with client._get_session() as session:
            assert session is not None
            assert not session.closed


class TestFallbackAnimatorCoverage:
    """Tests to improve FallbackAnimator coverage."""
    
    @pytest.mark.asyncio
    async def test_animate_empty_proof(self):
        """Test animating empty proof."""
        mcp_client = ManimMCPClient(use_mock=True)
        static_gen = StaticAnimationGenerator(output_dir=Path("/tmp"))
        fallback = FallbackAnimator(mcp_client, static_gen)
        
        empty_proof = ProofSketch(
            theorem_name="empty",
            introduction="Empty proof",
            key_steps=[],
            conclusion="Nothing to prove"
        )
        
        response = await fallback.animate(empty_proof)
        assert response is not None
    
    @pytest.mark.asyncio
    async def test_animate_with_all_options(self):
        """Test animate with all style/quality options."""
        mcp_client = ManimMCPClient(use_mock=True)
        static_gen = StaticAnimationGenerator(output_dir=Path("/tmp"))
        fallback = FallbackAnimator(mcp_client, static_gen)
        
        proof = ProofSketch(
            theorem_name="styled",
            introduction="Styled proof",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Step",
                    mathematical_content="x = y"
                )
            ],
            conclusion="Done"
        )
        
        # Test different styles
        for style in AnimationStyle:
            response = await fallback.animate(proof, style=style)
            assert response is not None
        
        # Test different qualities
        for quality in AnimationQuality:
            response = await fallback.animate(proof, quality=quality)
            assert response is not None


class TestStaticAnimationGeneratorCoverage:
    """Tests to improve StaticAnimationGenerator coverage."""
    
    def test_create_slides_all_step_types(self, tmp_path):
        """Test slide creation with various step types."""
        generator = StaticAnimationGenerator(output_dir=tmp_path)
        
        # Test title slide
        title_path = tmp_path / "title.png"
        result = generator.create_title_slide("Test Theorem", "A test proof", title_path)
        assert result is True
        assert title_path.exists()
        
        # Test step slides
        steps = [
            ProofStep(
                step_number=1,
                description="Text only step",
                mathematical_content=""
            ),
            ProofStep(
                step_number=2,
                description="Math step",
                mathematical_content="\\int_0^1 x^2 dx = \\frac{1}{3}"
            ),
            ProofStep(
                step_number=3,
                description="Complex step with tactics",
                mathematical_content="\\forall x, P(x)",
                tactics=["intro", "apply", "exact"]
            )
        ]
        
        for i, step in enumerate(steps):
            step_path = tmp_path / f"step_{i}.png"
            result = generator.create_step_slide(step, i+1, len(steps), step_path)
            assert result is True
            assert step_path.exists()
        
        # Test conclusion slide
        conclusion_path = tmp_path / "conclusion.png"
        result = generator.create_conclusion_slide("QED", conclusion_path)
        assert result is True
        assert conclusion_path.exists()
    
    def test_images_to_video_success(self, tmp_path):
        """Test video creation from images."""
        generator = StaticAnimationGenerator(output_dir=tmp_path)
        
        # Create dummy image files
        images = []
        for i in range(3):
            img_path = tmp_path / f"frame_{i}.png"
            img_path.write_text("dummy")
            images.append(img_path)
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)
            
            result = generator.images_to_video(
                images, 
                tmp_path / "output.mp4",
                fps=1
            )
            
            assert result is True
            mock_run.assert_called_once()
    
    @pytest.mark.asyncio
    async def test_generate_static_animation_error_handling(self, tmp_path):
        """Test static animation with errors."""
        generator = StaticAnimationGenerator(output_dir=tmp_path)
        
        proof = ProofSketch(
            theorem_name="error_test",
            introduction="Error test",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Step",
                    mathematical_content="test"
                )
            ],
            conclusion="Done"
        )
        
        # Mock slide creation to fail
        with patch.object(generator, 'create_title_slide', side_effect=Exception("Test error")):
            response = await generator.generate_static_animation(proof)
            
            assert response is not None
            assert isinstance(response, dict)
            assert response.get('error') is not None


class TestProductionAnimatorCoverage:
    """Tests to improve ProductionAnimator coverage."""
    
    def test_post_process_animation_success(self, tmp_path):
        """Test post-processing animation."""
        animator = ProductionAnimator(use_mock=True)
        
        # Create dummy video file
        video_path = tmp_path / "test.mp4"
        video_path.write_text("dummy video")
        
        response = AnimationResponse(
            video_path=video_path,
            duration=30.0
        )
        
        # Run post-processing (should not fail even if tools missing)
        asyncio.run(animator._post_process_animation(response))
    
    def test_get_video_duration_no_ffprobe(self, tmp_path):
        """Test video duration when ffprobe missing."""
        animator = ProductionAnimator(use_mock=True)
        
        video_path = tmp_path / "test.mp4"
        video_path.write_text("dummy")
        
        with patch('subprocess.run', side_effect=FileNotFoundError):
            duration = animator._get_video_duration(video_path)
            assert duration is None
    
    def test_resource_limits_no_psutil(self):
        """Test resource checking without psutil."""
        animator = ProductionAnimator(use_mock=True)
        
        with patch('builtins.__import__', side_effect=ImportError):
            # Should not raise, just warn
            animator._check_resource_limits()
    
    @pytest.mark.asyncio
    async def test_validate_setup_no_output_dir(self, tmp_path):
        """Test setup validation with missing output dir."""
        config = AnimationConfig()
        # Use a path that doesn't exist but can be created
        nonexistent_dir = tmp_path / "nonexistent" / "deeply" / "nested"
        manim_config = ManimConfig(output_dir=nonexistent_dir)
        
        animator = ProductionAnimator(
            animation_config=config,
            manim_config=manim_config,
            use_mock=False
        )
        
        # In mock=False mode, it will try to connect to MCP
        # But with fallback support, it should still return True
        result = await animator.validate_setup()
        assert result is True  # Should pass with fallback support
    
    def test_validate_animation_request_edge_cases(self):
        """Test animation request validation edge cases."""
        animator = ProductionAnimator(use_mock=True)
        
        # No segments
        request1 = AnimationRequest(
            theorem_name="test",
            request_id="test1",
            segments=[],
            estimated_duration=30.0,
            total_scenes=0
        )
        assert animator._validate_animation_request(request1) is False
        
        # Invalid duration
        request2 = AnimationRequest(
            theorem_name="test",
            request_id="test2",
            segments=[AnimationSegment(
                segment_id="seg1",
                title="Segment",
                scenes=[],
                total_duration=5.0
            )],
            estimated_duration=-1.0,
            total_scenes=0
        )
        assert animator._validate_animation_request(request2) is False
    
    def test_check_output_directories_write_failure(self, tmp_path):
        """Test output directory check with write failure."""
        animator = ProductionAnimator(use_mock=True)
        animator.manim_config.output_dir = tmp_path
        
        with patch('pathlib.Path.write_text', side_effect=PermissionError):
            result = animator._check_output_directories()
            assert result is False


class TestModelsCoverage:
    """Tests to improve models coverage."""
    
    def test_animation_scene_with_all_fields(self):
        """Test AnimationScene with all optional fields."""
        scene = AnimationScene(
            scene_id="test",
            title="Test Scene",
            duration=5.0,
            initial_formula="a = b",
            final_formula="b = c",
            transformation_type=TransformationType.SUBSTITUTION,
            highlighted_parts=["a", "b"],
            intermediate_formulas=["a = x", "x = b"],
            narration_text="Test narration",
            fade_in_time=0.5,
            fade_out_time=0.5
        )
        
        assert scene.scene_id == "test"
        assert scene.title == "Test Scene"
        assert scene.narration_text == "Test narration"
        assert len(scene.highlighted_parts) == 2
        assert len(scene.intermediate_formulas) == 2
    
    def test_animation_request_needs_segmentation(self):
        """Test segmentation detection."""
        # Short request
        request1 = AnimationRequest(
            theorem_name="short",
            request_id="short1",
            segments=[],
            estimated_duration=30.0
        )
        assert request1.needs_segmentation is False
        
        # Long request  
        request2 = AnimationRequest(
            theorem_name="long",
            request_id="long1",
            segments=[],
            estimated_duration=800.0  # > 12 minutes
        )
        assert request2.needs_segmentation is True
    
    def test_manim_config_presets(self):
        """Test ManimConfig preset methods."""
        # Development preset
        dev_config = ManimConfig.development()
        assert dev_config.server_timeout == 60.0
        assert dev_config.keep_temp_files is True
        
        # Production preset
        prod_config = ManimConfig.production()
        assert prod_config.server_timeout == 600.0
        assert prod_config.memory_limit_mb == 4096
    
    def test_animation_config_from_dict(self):
        """Test AnimationConfig creation from dict."""
        config_dict = {
            "step_duration": 20.0,
            "max_memory_mb": 1024,
            "background_color": "#222222",
            "text_color": "#FFFFFF"
        }
        
        config = AnimationConfig(**config_dict)
        assert config.step_duration == 20.0
        assert config.max_memory_mb == 1024
        assert config.background_color == "#222222"
        assert config.text_color == "#FFFFFF"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])