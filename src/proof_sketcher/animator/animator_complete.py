"""Production-ready animator with fallback mechanisms."""

import asyncio
import logging
import psutil
import time
from pathlib import Path
from typing import Callable, Optional

from ..core.exceptions import AnimatorError, AnimationTimeoutError
from ..generator.models import ProofSketch
from .fallback import FallbackAnimator, StaticAnimationGenerator
from .manim_mcp_enhanced import EnhancedManimMCPClient
from .models import AnimationConfig, AnimationResponse, AnimationStyle, ManimConfig, AnimationQuality


class ProductionAnimator:
    """Production-ready animator with comprehensive error handling and fallbacks."""

    def __init__(
        self,
        animation_config: Optional[AnimationConfig] = None,
        manim_config: Optional[ManimConfig] = None,
        use_mock: bool = False,
        progress_callback: Optional[Callable[[str, float], None]] = None
    ):
        """Initialize the production animator.

        Args:
            animation_config: Animation configuration
            manim_config: Manim server configuration  
            use_mock: Use mock server for testing
            progress_callback: Optional progress callback function
        """
        self.animation_config = animation_config or AnimationConfig()
        self.manim_config = manim_config or ManimConfig()
        self.use_mock = use_mock
        self.progress_callback = progress_callback
        self.logger = logging.getLogger(__name__)

        # Initialize components
        self.mcp_client = EnhancedManimMCPClient(
            config=self.manim_config,
            use_mock=use_mock
        )
        self.static_generator = StaticAnimationGenerator(
            output_dir=self.animation_config.output_dir
        )
        self.fallback_animator = FallbackAnimator(
            mcp_client=self.mcp_client,
            static_generator=self.static_generator
        )

        # Resource monitoring
        self.max_memory_mb = getattr(self.animation_config, 'max_memory_mb', 1024)
        self.max_processing_time = getattr(self.animation_config, 'max_processing_time', 300)

        # Setup output directories
        self._setup_output_directories()

    async def animate_proof(
        self, proof_sketch: ProofSketch, 
        style: AnimationStyle = AnimationStyle.MODERN,
        quality: AnimationQuality = AnimationQuality.MEDIUM,
        output_filename: Optional[str] = None
    ) -> AnimationResponse:
        """Generate animation for a proof sketch with comprehensive error handling.

        Args:
            proof_sketch: The proof sketch to animate
            style: Animation style
            quality: Quality level
            output_filename: Optional output filename

        Returns:
            AnimationResponse with results or fallback content
        """
        start_time = time.time()
        
        # Generate output filename if not provided
        if not output_filename:
            safe_name = self._sanitize_filename(proof_sketch.theorem_name)
            output_filename = f"{safe_name}_animation.mp4"
        
        self._report_progress("Starting animation generation", 0.0)
        
        try:
            # Check resource limits before starting
            self._check_resource_limits()
            
            # Validate input
            self._validate_proof_sketch(proof_sketch)
            
            self._report_progress("Connecting to animation services", 0.1)
            
            # Use fallback animator which handles MCP -> static fallback
            response = await asyncio.wait_for(
                self.fallback_animator.animate(
                    proof_sketch=proof_sketch,
                    style=style,
                    quality=quality,
                    output_filename=output_filename
                ),
                timeout=self.max_processing_time
            )
            
            # Add timing metadata
            processing_time = time.time() - start_time
            if response.metadata is None:
                response.metadata = {}
            response.metadata.update({
                "processing_time_seconds": processing_time,
                "style": style.value,
                "quality": quality.value,
                "theorem_name": proof_sketch.theorem_name
            })
            
            self._report_progress("Animation generation completed", 1.0)
            self.logger.info(
                f"Animation completed for {proof_sketch.theorem_name} "
                f"in {processing_time:.2f}s"
            )
            
            return response
            
        except asyncio.TimeoutError:
            self.logger.error(f"Animation timed out after {self.max_processing_time}s")
            return self._create_timeout_response(proof_sketch, output_filename)
            
        except MemoryError:
            self.logger.error("Animation failed due to memory limit")
            return self._create_memory_error_response(proof_sketch, output_filename)
            
        except Exception as e:
            self.logger.error(f"Animation failed unexpectedly: {e}")
            return self._create_error_response(proof_sketch, output_filename, str(e))

    async def animate_batch(self, proof_sketches: list[ProofSketch],
                           style: AnimationStyle = AnimationStyle.MODERN,
                           quality: AnimationQuality = AnimationQuality.MEDIUM,
                           max_concurrent: int = 3) -> list[AnimationResponse]:
        """Animate multiple proof sketches with controlled concurrency.

        Args:
            proof_sketches: List of proof sketches to animate
            style: Animation style
            quality: Quality level  
            max_concurrent: Maximum concurrent animations

        Returns:
            List of animation responses
        """
        self.logger.info(f"Starting batch animation of {len(proof_sketches)} proofs")
        
        semaphore = asyncio.Semaphore(max_concurrent)
        
        async def animate_single(sketch: ProofSketch) -> AnimationResponse:
            async with semaphore:
                return await self.animate_proof(sketch, style, quality)
        
        # Process all animations concurrently with limit
        tasks = [animate_single(sketch) for sketch in proof_sketches]
        responses = await asyncio.gather(*tasks, return_exceptions=True)
        
        # Convert exceptions to error responses
        results = []
        for i, response in enumerate(responses):
            if isinstance(response, Exception):
                sketch = proof_sketches[i]
                error_response = self._create_error_response(
                    sketch, f"{sketch.theorem_name}_animation.mp4", str(response)
                )
                results.append(error_response)
            else:
                results.append(response)
        
        # Report batch results
        success_count = sum(1 for r in results if not r.error)
        self.logger.info(
            f"Batch animation completed: {success_count}/{len(results)} successful"
        )
        
        return results

    def _setup_output_directories(self) -> None:
        """Ensure output directories exist."""
        try:
            self.animation_config.output_dir.mkdir(parents=True, exist_ok=True)
            if hasattr(self.animation_config, 'temp_dir') and self.animation_config.temp_dir:
                self.animation_config.temp_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self.logger.error(f"Failed to create output directories: {e}")
            raise AnimatorError(f"Cannot create output directories: {e}")

    def _check_resource_limits(self) -> None:
        """Check if system resources are within limits."""
        # Check memory usage
        try:
            process = psutil.Process()
            memory_mb = process.memory_info().rss / (1024 * 1024)
            
            if memory_mb > self.max_memory_mb:
                raise MemoryError(
                    f"Memory usage {memory_mb:.1f}MB exceeds limit {self.max_memory_mb}MB"
                )
        except psutil.NoSuchProcess:
            pass  # Process monitoring not available
        except ImportError:
            self.logger.warning("psutil not available, skipping memory check")
        except Exception as e:
            self.logger.warning(f"Could not check memory limits: {e}")

    def _validate_proof_sketch(self, proof_sketch: ProofSketch) -> None:
        """Validate proof sketch for animation."""
        if not proof_sketch.theorem_name:
            raise AnimatorError("Proof sketch must have a theorem name")
        
        if not proof_sketch.key_steps:
            raise AnimatorError("Proof sketch must have at least one key step")
        
        # Check for excessively long proofs
        if len(proof_sketch.key_steps) > 20:
            self.logger.warning(
                f"Proof has {len(proof_sketch.key_steps)} steps, "
                "animation may be very long"
            )

    def _sanitize_filename(self, name: str) -> str:
        """Sanitize a filename for filesystem use."""
        # Replace problematic characters
        safe_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-"
        sanitized = "".join(c if c in safe_chars else "_" for c in name)
        
        # Remove multiple underscores and trim
        while "__" in sanitized:
            sanitized = sanitized.replace("__", "_")
        
        return sanitized.strip("_")[:50]  # Limit length

    def _report_progress(self, message: str, progress: float) -> None:
        """Report progress if callback is available."""
        if self.progress_callback:
            try:
                self.progress_callback(message, progress)
            except Exception as e:
                self.logger.warning(f"Progress callback failed: {e}")

    def _create_timeout_response(self, proof_sketch: ProofSketch, 
                                output_filename: str) -> AnimationResponse:
        """Create response for timeout scenarios."""
        return AnimationResponse(
            video_path=None,
            thumbnail_path=None,
            duration=0,
            frame_count=0,
            size_bytes=0,
            error=f"Animation timed out after {self.max_processing_time}s",
            metadata={
                "error_type": "timeout",
                "theorem_name": proof_sketch.theorem_name,
                "timeout_seconds": self.max_processing_time
            }
        )

    def _create_memory_error_response(self, proof_sketch: ProofSketch,
                                     output_filename: str) -> AnimationResponse:
        """Create response for memory errors."""
        return AnimationResponse(
            video_path=None,
            thumbnail_path=None,
            duration=0,
            frame_count=0,
            size_bytes=0,
            error=f"Animation exceeded memory limit of {self.max_memory_mb}MB",
            metadata={
                "error_type": "memory_limit",
                "theorem_name": proof_sketch.theorem_name,
                "memory_limit_mb": self.max_memory_mb
            }
        )

    def _create_error_response(self, proof_sketch: ProofSketch,
                              output_filename: str, error_message: str) -> AnimationResponse:
        """Create response for general errors."""
        return AnimationResponse(
            video_path=None,
            thumbnail_path=None,
            duration=0,
            frame_count=0,
            size_bytes=0,
            error=error_message,
            metadata={
                "error_type": "general",
                "theorem_name": proof_sketch.theorem_name
            }
        )

    async def validate_setup(self) -> bool:
        """Validate that the animation system is properly set up."""
        try:
            # Check output directories
            if not self.animation_config.output_dir.exists():
                self.logger.error("Output directory does not exist")
                return False

            # Test fallback animator
            if self.use_mock:
                self.logger.info("Using mock mode - validation passed")
                return True

            # Try to connect to MCP client
            try:
                async with self.mcp_client:
                    health_ok = await self.mcp_client.health_check()
                    if health_ok:
                        self.logger.info("MCP server connection validated")
                        return True
                    else:
                        self.logger.warning("MCP server health check failed, will use fallback")
                        return True  # Still valid with fallback
            except Exception as e:
                self.logger.warning(f"MCP server not available, will use fallback: {e}")
                return True  # Still valid with fallback

        except Exception as e:
            self.logger.error(f"Setup validation failed: {e}")
            return False

    async def cleanup(self) -> None:
        """Clean up resources."""
        try:
            await self.mcp_client.disconnect()
        except Exception as e:
            self.logger.warning(f"Error during cleanup: {e}")

    async def __aenter__(self):
        """Async context manager entry."""
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        await self.cleanup()


# Backward compatibility alias
ManimAnimator = ProductionAnimator