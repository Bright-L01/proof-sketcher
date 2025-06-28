"""Main animator class that orchestrates proof animation generation."""

import asyncio
import logging
import subprocess
import time
from pathlib import Path
from typing import Optional

from ..generator.models import ProofSketch
from ..parser.models import TheoremInfo
from .formula_extractor import FormulaExtractor
from .manim_mcp import ManimMCPManager
from .models import (AnimationConfig, AnimationRequest, AnimationResponse,
                     AnimationTimeoutError, ManimConfig)
from .scene_builder import ProofAnimationBuilder


class ManimAnimator:
    """Main class for generating mathematical proof animations."""

    def __init__(
        self,
        animation_config: Optional[AnimationConfig] = None,
        manim_config: Optional[ManimConfig] = None,
    ):
        """Initialize the animator.

        Args:
            animation_config: Configuration for animation generation
            manim_config: Configuration for Manim MCP server
        """
        self.animation_config = animation_config or AnimationConfig()
        self.manim_config = manim_config or ManimConfig()
        self.scene_builder = ProofAnimationBuilder(self.animation_config)
        self.formula_extractor = FormulaExtractor()
        self.logger = logging.getLogger(__name__)

        # Initialize output directories
        self._setup_output_directories()

    async def animate_proof(
        self, proof_sketch: ProofSketch, config: Optional[AnimationConfig] = None
    ) -> AnimationResponse:
        """Generate animation for a proof sketch.

        Args:
            proof_sketch: Proof sketch to animate
            config: Animation configuration override

        Returns:
            Animation response with video path and metadata
        """
        config = config or self.animation_config
        start_time = time.time()

        try:
            self.logger.info(
                f"Starting animation generation for {proof_sketch.theorem_name}"
            )

            # Build animation request
            request = self.scene_builder.build_animation_request(proof_sketch, config)

            # Validate request
            if not self._validate_animation_request(request):
                return AnimationResponse(
                    request=request,
                    success=False,
                    error_message="Invalid animation request",
                )

            # Generate animation using MCP server
            async with ManimMCPManager(self.manim_config) as manager:
                response = await manager.render_animation(request)

            # Post-process response
            if response.success:
                response = await self._post_process_animation(response)

            generation_time = (time.time() - start_time) * 1000
            response.generation_time_ms = generation_time

            duration_str = f"{response.actual_duration:.1f}s" if response.actual_duration is not None else "N/A"
            self.logger.info(
                f"Animation generation completed for {proof_sketch.theorem_name}: "
                f"success={response.success}, duration={duration_str}"
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
    ) -> AnimationResponse:
        """Create fallback response when animation fails."""
        # Create minimal request for fallback
        import uuid

        from .models import (AnimationScene, AnimationSegment,
                             TransformationType)

        fallback_scene = AnimationScene(
            scene_id=f"{proof_sketch.theorem_name}_fallback",
            title="Theorem Statement",
            duration=30.0,
            initial_formula="",
            final_formula=self.formula_extractor.convert_lean_to_latex(
                proof_sketch.theorem_name
            ),
            transformation_type=TransformationType.EXPANSION,
            narration_text=proof_sketch.introduction,
        )

        fallback_segment = AnimationSegment(
            segment_id=f"{proof_sketch.theorem_name}_fallback_segment",
            title="Fallback",
            scenes=[fallback_scene],
        )

        fallback_request = AnimationRequest(
            theorem_name=proof_sketch.theorem_name,
            request_id=str(uuid.uuid4()),
            segments=[fallback_segment],
            config=self.animation_config,
        )

        generation_time = (time.time() - start_time) * 1000

        return AnimationResponse(
            request=fallback_request,
            generation_time_ms=generation_time,
            success=False,
            error_message=error_message,
            warnings=["Animation generation failed, fallback response created"],
        )


class CachedManimAnimator:
    """Wrapper around ManimAnimator that adds caching."""

    def __init__(
        self,
        animator: ManimAnimator,
        cache_manager=None,  # Could integrate with existing cache system
    ):
        """Initialize cached animator.

        Args:
            animator: ManimAnimator instance
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
