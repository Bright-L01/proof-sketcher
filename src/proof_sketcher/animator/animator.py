"""Production-ready animator with fallback mechanisms."""

import asyncio
import logging
import psutil
import time
from pathlib import Path
from typing import Callable, List, Optional

from ..core.exceptions import AnimatorError, AnimationTimeoutError
from ..generator.models import ProofSketch
from ..parser.models import TheoremInfo
from .fallback import FallbackAnimator, StaticAnimationGenerator
from .manim_mcp_enhanced import EnhancedManimMCPClient
from .models import AnimationConfig, AnimationRequest, AnimationResponse, AnimationStyle, ManimConfig, AnimationQuality


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
            output_dir=self.manim_config.output_dir or Path.cwd() / "animations"
        )
        self.fallback_animator = FallbackAnimator(
            mcp_client=self.mcp_client,
            static_generator=self.static_generator
        )

        # Resource monitoring
        self.max_memory_mb = self.animation_config.max_memory_mb
        self.max_processing_time = self.animation_config.max_processing_time

        # Setup output directories
        self._setup_output_directories()

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

    def _check_resource_limits(self) -> None:
        """Check if system resources are within limits."""
        # Check memory usage
        try:
            import psutil
            process = psutil.Process()
            memory_mb = process.memory_info().rss / (1024 * 1024)
            
            if memory_mb > self.max_memory_mb:
                raise MemoryError(
                    f"Memory usage {memory_mb:.1f}MB exceeds limit {self.max_memory_mb}MB"
                )
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

    def _setup_output_directories(self) -> None:
        """Ensure output directories exist."""
        output_dir = self.manim_config.output_dir or Path.cwd() / "animations"
        try:
            output_dir.mkdir(parents=True, exist_ok=True)
            if self.manim_config.temp_dir:
                self.manim_config.temp_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self.logger.error(f"Failed to create output directories: {e}")
            raise AnimatorError(f"Cannot create output directories: {e}")

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

        except AnimationTimeoutError as e:
            self.logger.error(f"Animation timeout for {proof_sketch.theorem_name}: {e}")
            return self._create_fallback_response(proof_sketch, str(e), start_time)

        except Exception as e:
            self.logger.exception(
                f"Animation generation failed for {proof_sketch.theorem_name}"
            )
            return self._create_fallback_response(proof_sketch, str(e), start_time)

    async def __aenter__(self):
        """Async context manager entry."""
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        try:
            await self.mcp_client.disconnect()
        except Exception as e:
            self.logger.warning(f"Error during cleanup: {e}")

    async def cleanup(self):
        """Clean up resources."""
        try:
            await self.mcp_client.disconnect()
        except Exception as e:
            self.logger.warning(f"Error during cleanup: {e}")

    async def validate_setup(self) -> bool:
        """Validate that the animation system is properly set up."""
        try:
            # Check output directories
            output_dir = self.manim_config.output_dir or Path.cwd() / "animations"
            if not output_dir.exists():
                self.logger.error("Output directory does not exist")
                return False

            # Test in mock mode
            if self.use_mock:
                self.logger.info("Using mock mode - validation passed")
                return True

            # Try to connect to MCP client
            try:
                success = await self.mcp_client.connect()
                if success:
                    health_ok = await self.mcp_client.health_check()
                    await self.mcp_client.disconnect()
                    if health_ok:
                        self.logger.info("MCP server connection validated")
                        return True
                    else:
                        self.logger.warning("MCP server health check failed, will use fallback")
                        return True  # Still valid with fallback
                else:
                    self.logger.warning("MCP server not available, will use fallback")
                    return True  # Still valid with fallback
            except Exception as e:
                self.logger.warning(f"MCP server not available, will use fallback: {e}")
                return True  # Still valid with fallback

        except Exception as e:
            self.logger.error(f"Setup validation failed: {e}")
            return False

    async def animate_batch(self, proof_sketches: List[ProofSketch],
                           style: AnimationStyle = AnimationStyle.MODERN,
                           quality: AnimationQuality = AnimationQuality.MEDIUM,
                           max_concurrent: int = 3) -> List[dict]:
        """Animate multiple proof sketches with controlled concurrency."""
        self.logger.info(f"Starting batch animation of {len(proof_sketches)} proofs")
        
        semaphore = asyncio.Semaphore(max_concurrent)
        
        async def animate_single(sketch: ProofSketch) -> dict:
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
                error_response = {
                    'video_path': None,
                    'thumbnail_path': None,
                    'duration': 0,
                    'frame_count': 0,
                    'size_bytes': 0,
                    'error': str(response),
                    'metadata': {
                        'error_type': 'batch_exception',
                        'theorem_name': sketch.theorem_name
                    }
                }
                results.append(error_response)
            else:
                results.append(response)
        
        # Report batch results
        success_count = sum(1 for r in results if not r.get('error'))
        self.logger.info(
            f"Batch animation completed: {success_count}/{len(results)} successful"
        )
        
        return results

    async def animate_single_step(
        self,
        step_description: str,
        source_formula: str,
        target_formula: str,
        config: Optional[AnimationConfig] = None,
    ) -> AnimationResponse:
        """Generate animation for a single proof step.

        Args:
            step_description: Description of the step
            source_formula: Starting formula
            target_formula: Ending formula
            config: Animation configuration

        Returns:
            Animation response
        """
        config = config or self.animation_config

        # Create a minimal proof sketch for this step
        from ..generator.models import ProofStep

        step = ProofStep(
            step_number=1,
            description=step_description,
            mathematical_content=f"{source_formula} = {target_formula}",
            tactics=[],
        )

        minimal_sketch = ProofSketch(
            theorem_name="single_step",
            introduction=step_description,
            key_steps=[step],
            conclusion="Step completed.",
        )

        return await self.animate_proof(minimal_sketch, config)

    async def create_preview_image(
        self, theorem: TheoremInfo, config: Optional[AnimationConfig] = None
    ) -> Optional[Path]:
        """Create a preview image for a theorem.

        Args:
            theorem: Theorem information
            config: Animation configuration

        Returns:
            Path to preview image if successful, None otherwise
        """
        config = config or self.animation_config

        try:
            # Convert theorem statement to LaTeX
            latex_formula = self.formula_extractor.convert_lean_to_latex(
                theorem.statement
            )

            # Create simple preview using LaTeX rendering
            preview_path = await self._create_latex_preview(
                theorem.name, latex_formula, config
            )

            return preview_path

        except Exception as e:
            self.logger.error(f"Failed to create preview for {theorem.name}: {e}")
            return None

    def validate_setup(self) -> bool:
        """Validate that the animation system is properly set up.

        Returns:
            True if setup is valid, False otherwise
        """
        try:
            # Check if required directories exist
            if not self._check_output_directories():
                return False

            # Test Manim MCP server
            async def test_server():
                async with ManimMCPManager(self.manim_config) as manager:
                    return await manager.validate_setup()

            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            try:
                server_valid = loop.run_until_complete(test_server())
            finally:
                loop.close()

            if not server_valid:
                self.logger.error("Manim MCP server validation failed")
                return False

            # Test formula extraction
            test_formula = "∀ n : Nat, n + 0 = n"
            try:
                latex_result = self.formula_extractor.convert_lean_to_latex(
                    test_formula
                )
                if not latex_result:
                    self.logger.error("Formula extraction test failed")
                    return False
            except Exception as e:
                self.logger.error(f"Formula extraction test error: {e}")
                return False

            self.logger.info("Animation system validation successful")
            return True

        except Exception as e:
            self.logger.error(f"Animation setup validation failed: {e}")
            return False

    def get_animation_info(self, proof_sketch: ProofSketch) -> dict:
        """Get information about what would be animated.

        Args:
            proof_sketch: Proof sketch to analyze

        Returns:
            Dictionary with animation information
        """
        request = self.scene_builder.build_animation_request(
            proof_sketch, self.animation_config
        )

        return {
            "theorem_name": proof_sketch.theorem_name,
            "estimated_duration": request.estimated_duration,
            "total_scenes": request.total_scenes,
            "segments": len(request.segments),
            "needs_segmentation": request.needs_segmentation,
            "segment_info": [
                {
                    "title": segment.title,
                    "scenes": len(segment.scenes),
                    "duration": segment.total_duration,
                }
                for segment in request.segments
            ],
        }

    def _setup_output_directories(self) -> None:
        """Set up output directories."""
        if not self.manim_config.output_dir:
            self.manim_config.output_dir = Path.cwd() / "animations"

        if not self.manim_config.temp_dir:
            self.manim_config.temp_dir = Path.cwd() / "temp"

        self.manim_config.output_dir.mkdir(parents=True, exist_ok=True)
        self.manim_config.temp_dir.mkdir(parents=True, exist_ok=True)

    def _check_output_directories(self) -> bool:
        """Check if output directories are accessible."""
        try:
            if not self.manim_config.output_dir.exists():
                self.manim_config.output_dir.mkdir(parents=True, exist_ok=True)

            if not self.manim_config.temp_dir.exists():
                self.manim_config.temp_dir.mkdir(parents=True, exist_ok=True)

            # Test write access
            test_file = self.manim_config.output_dir / ".test_write"
            test_file.write_text("test")
            test_file.unlink()

            return True

        except Exception as e:
            self.logger.error(f"Output directory check failed: {e}")
            return False

    def _validate_animation_request(self, request: AnimationRequest) -> bool:
        """Validate that an animation request is valid."""
        if not request.segments:
            self.logger.error("Animation request has no segments")
            return False

        if request.estimated_duration <= 0:
            self.logger.error("Animation request has invalid duration")
            return False

        for segment in request.segments:
            if not segment.scenes:
                self.logger.error(f"Segment {segment.title} has no scenes")
                return False

            for scene in segment.scenes:
                if not scene.initial_formula and not scene.final_formula:
                    self.logger.error(f"Scene {scene.scene_id} has no formulas")
                    return False

        return True

    async def _post_process_animation(
        self, response: AnimationResponse
    ) -> AnimationResponse:
        """Post-process animation response."""
        if not response.has_video:
            return response

        # Add additional metadata
        if response.video_path and response.video_path.exists():
            # Update file size
            response.file_size_mb = response.video_path.stat().st_size / (1024 * 1024)

            # Verify video duration
            actual_duration = await self._get_video_duration(response.video_path)
            if actual_duration:
                response.actual_duration = actual_duration

        return response

    async def _get_video_duration(self, video_path: Path) -> Optional[float]:
        """Get duration of video file."""
        try:
            # Use ffprobe to get video duration
            result = subprocess.run(
                [
                    "ffprobe",
                    "-v",
                    "quiet",
                    "-show_entries",
                    "format=duration",
                    "-of",
                    "csv=p=0",
                    str(video_path),
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )

            if result.returncode == 0:
                return float(result.stdout.strip())
        except Exception as e:
            self.logger.warning(f"Could not get video duration: {e}")

        return None

    async def _create_latex_preview(
        self, theorem_name: str, latex_formula: str, config: AnimationConfig
    ) -> Optional[Path]:
        """Create a preview image using LaTeX rendering."""
        try:
            preview_path = self.manim_config.output_dir / f"{theorem_name}_preview.png"

            # Create LaTeX document
            latex_content = f"""
\\documentclass{{article}}
\\usepackage{{amsmath}}
\\usepackage{{amsfonts}}
\\usepackage{{amssymb}}
\\usepackage[active,tightpage]{{preview}}
\\begin{{document}}
\\begin{{preview}}
\\begin{{equation*}}
{latex_formula}
\\end{{equation*}}
\\end{{preview}}
\\end{{document}}
"""

            # Write LaTeX file
            latex_file = self.manim_config.temp_dir / f"{theorem_name}_preview.tex"
            latex_file.write_text(latex_content)

            # Compile with pdflatex
            result = subprocess.run(
                [
                    "pdflatex",
                    "-output-directory",
                    str(self.manim_config.temp_dir),
                    str(latex_file),
                ],
                capture_output=True,
                timeout=30,
            )

            if result.returncode == 0:
                # Convert PDF to PNG
                pdf_file = self.manim_config.temp_dir / f"{theorem_name}_preview.pdf"
                if pdf_file.exists():
                    convert_result = subprocess.run(
                        [
                            "convert",
                            "-density",
                            "300",
                            str(pdf_file),
                            str(preview_path),
                        ],
                        capture_output=True,
                        timeout=30,
                    )

                    if convert_result.returncode == 0 and preview_path.exists():
                        return preview_path

        except Exception as e:
            self.logger.warning(f"LaTeX preview generation failed: {e}")

        return None

    def _create_fallback_response(
        self, proof_sketch: ProofSketch, error_message: str, start_time: float
    ) -> dict:
        """Create fallback response when animation fails."""
        generation_time = (time.time() - start_time) * 1000

        return {
            'video_path': None,
            'thumbnail_path': None,
            'duration': 0,
            'frame_count': 0,
            'size_bytes': 0,
            'error': error_message,
            'metadata': {
                'error_type': 'fallback',
                'theorem_name': proof_sketch.theorem_name,
                'generation_time_ms': generation_time,
                'warnings': ['Animation generation failed, fallback response created']
            }
        }


class CachedManimAnimator:
    """Wrapper around ManimAnimator that adds caching."""

    def __init__(
        self,
        animator: "ProductionAnimator",
        cache_manager=None,  # Could integrate with existing cache system
    ):
        """Initialize cached animator.

        Args:
            animator: ProductionAnimator instance
            cache_manager: Cache manager for responses
        """
        self.animator = animator
        self.cache = cache_manager
        self.logger = logging.getLogger(__name__)

    async def animate_proof(
        self, proof_sketch: ProofSketch, config: Optional[AnimationConfig] = None
    ) -> AnimationResponse:
        """Animate proof with caching."""
        if not config or not config.cache_responses:
            return await self.animator.animate_proof(proof_sketch, config)

        # Generate cache key
        cache_key = self._get_cache_key(proof_sketch, config)

        # Try cache first
        if self.cache:
            cached_response = self.cache.get(cache_key)
            if cached_response and cached_response.has_video:
                self.logger.debug(
                    f"Using cached animation for {proof_sketch.theorem_name}"
                )
                return cached_response

        # Generate new animation
        response = await self.animator.animate_proof(proof_sketch, config)

        # Cache successful results
        if response.success and self.cache:
            self.cache.put(cache_key, response)

        return response

    def _get_cache_key(self, proof_sketch: ProofSketch, config: AnimationConfig) -> str:
        """Generate cache key for animation."""
        import hashlib

        content = f"{proof_sketch.theorem_name}:{len(proof_sketch.key_steps)}"
        content += f":{config.quality.value}:{config.style.value}"
        content += f":{config.width}x{config.height}"

        # Include proof content hash
        proof_content = proof_sketch.introduction + proof_sketch.conclusion
        for step in proof_sketch.key_steps:
            proof_content += step.description + step.mathematical_content

        content_hash = hashlib.md5(proof_content.encode()).hexdigest()[:8]
        content += f":{content_hash}"

        return hashlib.sha256(content.encode()).hexdigest()

    def __getattr__(self, name):
        """Delegate other methods to the underlying animator."""
        return getattr(self.animator, name)


# Backward compatibility alias
ManimAnimator = ProductionAnimator
