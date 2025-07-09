"""Example: Animating the add_zero theorem proof.

This example demonstrates how to create and animate a proof of the theorem:
    theorem add_zero (n : Nat) : n + 0 = n := by
      induction n with
      | zero => rfl
      | succ n ih => simp [Nat.add_succ, ih]

The animation should show:
1. Initial statement: n + 0 = n
2. Base case: 0 + 0 = 0 (highlight reflexivity)
3. Inductive step: (n + 1) + 0 = n + 1
4. Transform using add_succ: (n + 0) + 1 = n + 1
5. Apply IH: n + 1 = n + 1
6. QED visualization
"""

import asyncio
import logging

from proof_sketcher.animator.animator import ManimAnimator
from proof_sketcher.animator.models import AnimationConfig, ManimConfig
from proof_sketcher.generator.models import ProofSketch, ProofStep

# Set up logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


def create_add_zero_proof_sketch() -> ProofSketch:
    """Create the proof sketch for the add_zero theorem."""

    # Define proof steps
    steps = [
        ProofStep(
            step_number=1,
            description="Base case: We need to show that 0 + 0 = 0",
            mathematical_content="0 + 0 = 0",
            tactics=["rfl"],
            intuition="This follows immediately from reflexivity of equality, since 0 + 0 is definitionally equal to 0.",
        ),
        ProofStep(
            step_number=2,
            description="Inductive step: Assume n + 0 = n (inductive hypothesis)",
            mathematical_content="n + 0 = n → (n + 1) + 0 = n + 1",
            tactics=["simp", "Nat.add_succ"],
            intuition="We assume the theorem holds for n and need to prove it for n + 1.",
        ),
        ProofStep(
            step_number=3,
            description="Transform the left side using the definition of addition",
            mathematical_content="(n + 1) + 0 = (n + 0) + 1",
            tactics=["Nat.add_succ"],
            intuition="By the definition of addition for successor, (n + 1) + m = (n + m) + 1.",
        ),
        ProofStep(
            step_number=4,
            description="Apply the inductive hypothesis",
            mathematical_content="(n + 0) + 1 = n + 1",
            tactics=["simp", "ih"],
            intuition="Since we know n + 0 = n by the inductive hypothesis, we can substitute.",
        ),
        ProofStep(
            step_number=5,
            description="Conclude the proof",
            mathematical_content="n + 1 = n + 1",
            tactics=["rfl"],
            intuition="We have shown (n + 1) + 0 = n + 1, completing the inductive step.",
        ),
    ]

    # Create the proof sketch
    proof_sketch = ProofSketch(
        theorem_name="add_zero",
        introduction=(
            "We prove that adding zero to any natural number gives the same number. "
            "This fundamental property of addition is proven using mathematical induction. "
            "The key insight is that addition is defined recursively on the first argument, "
            "so adding zero to any number should intuitively leave it unchanged."
        ),
        key_steps=steps,
        conclusion=(
            "By mathematical induction, we have proven that n + 0 = n for all natural numbers n. "
            "This establishes that 0 is the right identity element for addition on natural numbers, "
            "which is a cornerstone property in arithmetic."
        ),
        difficulty_level="beginner",
        mathematical_areas=["arithmetic", "induction", "natural_numbers"],
        prerequisites=[
            "natural_numbers",
            "mathematical_induction",
            "definitional_equality",
        ],
    )

    return proof_sketch


async def animate_add_zero_example():
    """Generate animation for the add_zero theorem."""

    logger.info("Creating add_zero proof sketch...")
    proof_sketch = create_add_zero_proof_sketch()

    logger.info(f"Proof sketch created with {proof_sketch.total_steps} steps")
    logger.info(f"Difficulty level: {proof_sketch.difficulty_level}")
    logger.info(f"Mathematical areas: {', '.join(proof_sketch.mathematical_areas)}")

    # Configure animation settings
    animation_config = AnimationConfig(
        quality=AnimationConfig.medium.quality,  # 720p for good quality
        style=AnimationConfig.modern.style,  # Clean, modern look
        base_duration=45.0,  # Longer base duration for educational content
        step_duration=20.0,  # Generous time per step
        max_duration=300.0,  # 5 minutes max
        show_step_numbers=True,
        highlight_changes=True,
        chapter_markers=True,
        font_size=42,  # Large, readable text
        pause_time=3.0,  # Longer pauses for comprehension
    )

    # Configure Manim server
    manim_config = ManimConfig(
        server_timeout=300.0,  # 5 minutes for complex animations
        render_timeout=120.0,  # 2 minutes per scene
        auto_start=True,
        auto_restart=True,
        keep_temp_files=True,  # Keep for debugging
    )

    # Create animator
    animator = ManimAnimator(animation_config, manim_config)

    # Get animation info first
    logger.info("Analyzing animation requirements...")
    anim_info = animator.get_animation_info(proof_sketch)

    logger.info("Animation will have:")
    logger.info(
        f"  - Estimated duration: {anim_info['estimated_duration']:.1f} seconds"
    )
    logger.info(f"  - Total scenes: {anim_info['total_scenes']}")
    logger.info(f"  - Segments: {anim_info['segments']}")
    logger.info(f"  - Needs segmentation: {anim_info['needs_segmentation']}")

    for i, segment_info in enumerate(anim_info["segment_info"]):
        logger.info(
            f"  - Segment {i+1}: {segment_info['title']} "
            f"({segment_info['scenes']} scenes, {segment_info['duration']:.1f}s)"
        )

    # Validate setup
    logger.info("Validating animation setup...")
    try:
        if animator.validate_setup():
            logger.info("✓ Animation setup validated successfully")
        else:
            logger.warning("⚠ Animation setup validation failed - will use fallback")
    except Exception as e:
        logger.warning(f"⚠ Setup validation error: {e} - will use fallback")

    # Generate animation
    logger.info("Starting animation generation...")
    try:
        response = await animator.animate_proof(proof_sketch, animation_config)

        if response.success:
            logger.info("✓ Animation generated successfully!")
            logger.info(f"  - Video path: {response.video_path}")
            logger.info(f"  - Actual duration: {response.actual_duration:.1f}s")
            logger.info(f"  - File size: {response.file_size_mb:.1f} MB")
            logger.info(f"  - Generation time: {response.generation_time_ms:.0f}ms")

            if response.has_preview:
                logger.info(f"  - Preview image: {response.preview_image_path}")

            if response.chapter_markers:
                logger.info("  - Chapter markers:")
                for time_stamp, title in response.chapter_markers:
                    logger.info(f"    {time_stamp:.1f}s: {title}")

            if response.has_segments:
                logger.info(f"  - Segments: {len(response.segments_paths)}")
                for i, segment_path in enumerate(response.segments_paths):
                    logger.info(f"    Segment {i+1}: {segment_path}")

        else:
            logger.error("✗ Animation generation failed")
            logger.error(f"  Error: {response.error_message}")
            if response.warnings:
                for warning in response.warnings:
                    logger.warning(f"  Warning: {warning}")

    except Exception as e:
        logger.exception("Animation generation failed with exception")
        logger.error(f"Error: {e}")

    return response


async def create_preview_only():
    """Create just a preview image for the add_zero theorem."""
    from proof_sketcher.parser.models import TheoremInfo

    logger.info("Creating preview image for add_zero theorem...")

    theorem = TheoremInfo(name="add_zero", statement="∀ n : Nat, n + 0 = n")

    animator = ManimAnimator()

    try:
        preview_path = await animator.create_preview_image(theorem)

        if preview_path:
            logger.info(f"✓ Preview created: {preview_path}")
        else:
            logger.warning("⚠ Preview creation failed (LaTeX tools may be missing)")

    except Exception as e:
        logger.error(f"✗ Preview creation error: {e}")


def main():
    """Main function to run the example."""
    logger.info("=== Add Zero Theorem Animation Example ===")
    logger.info("")
    logger.info("This example demonstrates animating the proof of:")
    logger.info("  theorem add_zero (n : Nat) : n + 0 = n")
    logger.info("")

    # Run the animation
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)

    try:
        # Try full animation first
        logger.info("Attempting full animation...")
        response = loop.run_until_complete(animate_add_zero_example())

        # If full animation failed, try preview only
        if not response.success:
            logger.info("")
            logger.info("Full animation failed, trying preview image...")
            loop.run_until_complete(create_preview_only())

    except KeyboardInterrupt:
        logger.info("Animation cancelled by user")
    except Exception as e:
        logger.exception("Example failed")
    finally:
        loop.close()

    logger.info("")
    logger.info("=== Example Complete ===")


if __name__ == "__main__":
    main()
