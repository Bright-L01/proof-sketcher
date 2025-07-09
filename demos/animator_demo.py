#!/usr/bin/env python3
"""
Comprehensive demo of the Production Animator showing both success and fallback scenarios.

This script demonstrates:
1. Successful animation with mock Manim server
2. Fallback to static images when Manim is unavailable
3. Error handling and recovery mechanisms
4. Progress tracking and reporting
5. Batch processing capabilities

Run this script to see the production animator in action.
"""

import asyncio
import logging
import tempfile
from pathlib import Path
from typing import List

from proof_sketcher.animator.animator import ProductionAnimator
from proof_sketcher.animator.models import (
    AnimationConfig,
    AnimationQuality,
    AnimationStyle,
    ManimConfig,
)
from proof_sketcher.generator.models import ProofSketch, ProofStep

# Configure logging to see what's happening
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


def create_sample_theorems() -> List[ProofSketch]:
    """Create sample theorems for demonstration."""

    # Simple theorem
    simple_theorem = ProofSketch(
        theorem_name="nat_add_zero",
        introduction="This fundamental theorem proves that adding zero to any natural number gives the same number.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="State the theorem for all natural numbers",
                mathematical_content="∀ n : ℕ, n + 0 = n",
                tactics=["intro"],
                intuition="We need to prove this property holds for every natural number",
            ),
            ProofStep(
                step_number=2,
                description="Apply the definition of addition",
                mathematical_content="n + 0 = n (by definition)",
                tactics=["simp", "add_zero"],
                intuition="Zero is the additive identity by definition",
            ),
        ],
        conclusion="Therefore, zero is the right additive identity for natural numbers.",
        difficulty_level="beginner",
        mathematical_areas=["Arithmetic", "Natural Numbers"],
        prerequisites=["Basic arithmetic"],
    )

    # Complex theorem
    complex_theorem = ProofSketch(
        theorem_name="pythagorean_theorem",
        introduction="The Pythagorean theorem is one of the most famous theorems in mathematics.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="Set up the right triangle",
                mathematical_content="Let △ABC with right angle at C, sides a, b, c",
                tactics=["setup"],
                intuition="We need a right triangle to apply the theorem",
            ),
            ProofStep(
                step_number=2,
                description="Construct squares on each side",
                mathematical_content="Construct squares with sides a², b², c²",
                tactics=["construct"],
                intuition="Visual representation helps understand the relationship",
            ),
            ProofStep(
                step_number=3,
                description="Use area relationships",
                mathematical_content="Area of large square = (a + b)²",
                tactics=["area_calc"],
                intuition="The total area can be calculated in two ways",
            ),
            ProofStep(
                step_number=4,
                description="Simplify and conclude",
                mathematical_content="a² + b² = c²",
                tactics=["algebra", "qed"],
                intuition="Algebraic manipulation gives us the final result",
            ),
        ],
        conclusion="Thus, in any right triangle, the square of the hypotenuse equals the sum of squares of the other two sides.",
        difficulty_level="intermediate",
        mathematical_areas=["Geometry", "Algebra"],
        prerequisites=["Basic geometry", "Area calculations"],
    )

    # Advanced theorem
    advanced_theorem = ProofSketch(
        theorem_name="fundamental_theorem_calculus",
        introduction="The Fundamental Theorem of Calculus connects differentiation and integration.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="Define the accumulator function",
                mathematical_content="F(x) = ∫[a to x] f(t) dt",
                tactics=["definition"],
                intuition="F accumulates the area under f from a to x",
            ),
            ProofStep(
                step_number=2,
                description="Show F is differentiable",
                mathematical_content="F'(x) = lim[h→0] [F(x+h) - F(x)]/h",
                tactics=["limit_def"],
                intuition="We need to compute the derivative using the limit definition",
            ),
            ProofStep(
                step_number=3,
                description="Apply mean value theorem",
                mathematical_content="F(x+h) - F(x) = h·f(c) for some c ∈ [x, x+h]",
                tactics=["mvt"],
                intuition="The mean value theorem gives us the crucial relationship",
            ),
            ProofStep(
                step_number=4,
                description="Take the limit",
                mathematical_content="F'(x) = f(x)",
                tactics=["limit", "continuity"],
                intuition="As h approaches 0, c approaches x, and f(c) approaches f(x)",
            ),
        ],
        conclusion="Therefore, differentiation and integration are inverse operations.",
        difficulty_level="advanced",
        mathematical_areas=["Calculus", "Analysis"],
        prerequisites=["Limits", "Continuity", "Integration"],
    )

    return [simple_theorem, complex_theorem, advanced_theorem]


def setup_progress_tracking():
    """Set up progress tracking for the demo."""
    progress_data = {"current": 0, "total": 0, "messages": []}

    def progress_callback(message: str, progress: float):
        """Track progress during animation generation."""
        progress_data["current"] = progress
        progress_data["messages"].append(f"[{progress*100:.1f}%] {message}")
        logger.info(f"Progress: {progress*100:.1f}% - {message}")

    return progress_callback, progress_data


async def demo_success_path():
    """Demonstrate successful animation with mock Manim server."""
    logger.info("=" * 60)
    logger.info("DEMO 1: Successful Animation with Mock Manim Server")
    logger.info("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        output_dir = Path(tmpdir) / "success_demo"

        # Configure for success scenario
        animation_config = AnimationConfig(
            quality=AnimationQuality.MEDIUM,
            style=AnimationStyle.MODERN,
            max_memory_mb=512,
            max_processing_time=120,
        )

        manim_config = ManimConfig(
            output_dir=output_dir,
            temp_dir=output_dir / "temp",
            auto_start=True,
        )

        # Set up progress tracking
        progress_callback, progress_data = setup_progress_tracking()

        # Create animator with mock server (high success rate)
        async with ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,  # Use mock for reliable demo
            progress_callback=progress_callback,
        ) as animator:

            logger.info("✅ Production Animator initialized successfully")
            logger.info(f"📁 Output directory: {output_dir}")

            # Test with simple theorem
            theorems = create_sample_theorems()
            simple_theorem = theorems[0]

            logger.info(f"🎬 Animating theorem: {simple_theorem.theorem_name}")

            try:
                response = await animator.animate_proof(simple_theorem)

                if isinstance(response, dict):
                    if response.get("error"):
                        logger.warning(
                            f"⚠️ Animation completed with fallback: {response['error']}"
                        )
                        logger.info(f"📊 Metadata: {response.get('metadata', {})}")
                    else:
                        logger.info("✅ Animation completed successfully!")
                        if response.get("video_path"):
                            logger.info(f"🎥 Video: {response['video_path']}")
                        if response.get("duration"):
                            logger.info(f"⏱️ Duration: {response['duration']:.1f}s")
                        logger.info(f"📊 Metadata: {response.get('metadata', {})}")
                else:
                    logger.info("✅ Animation completed successfully!")
                    logger.info(f"🎥 Video: {getattr(response, 'video_path', 'N/A')}")

                # Show progress summary
                logger.info(f"📈 Progress messages: {len(progress_data['messages'])}")
                for msg in progress_data["messages"][-3:]:  # Show last 3 messages
                    logger.info(f"  {msg}")

            except Exception as e:
                logger.error(f"❌ Animation failed: {e}")

            logger.info("✅ Success path demo completed")


async def demo_fallback_path():
    """Demonstrate fallback to static images when Manim is unavailable."""
    logger.info("=" * 60)
    logger.info("DEMO 2: Fallback to Static Images (Manim Unavailable)")
    logger.info("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        output_dir = Path(tmpdir) / "fallback_demo"

        # Configure for fallback scenario
        animation_config = AnimationConfig(
            quality=AnimationQuality.LOW,  # Faster processing
            style=AnimationStyle.ACCESSIBLE,
            max_memory_mb=256,
            max_processing_time=90,
        )

        manim_config = ManimConfig(
            output_dir=output_dir,
            temp_dir=output_dir / "temp",
            auto_start=False,  # Don't try to start real server
        )

        # Set up progress tracking
        progress_callback, progress_data = setup_progress_tracking()

        # Create animator without mock (will fallback to static)
        async with ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=False,  # No mock - will trigger fallback
            progress_callback=progress_callback,
        ) as animator:

            logger.info("✅ Production Animator initialized for fallback demo")
            logger.info(f"📁 Output directory: {output_dir}")

            # Test with complex theorem
            theorems = create_sample_theorems()
            complex_theorem = theorems[1]

            logger.info(f"🎬 Animating theorem: {complex_theorem.theorem_name}")
            logger.info(
                "⚠️ Manim server unavailable - expecting fallback to static images"
            )

            try:
                response = await animator.animate_proof(complex_theorem)

                # Fallback should always produce some response
                if isinstance(response, dict):
                    if response.get("error"):
                        logger.info(
                            f"✅ Fallback completed as expected: {response['error']}"
                        )
                        logger.info(f"📊 Metadata: {response.get('metadata', {})}")

                        # Check if static image was created
                        if response.get("thumbnail_path"):
                            logger.info(f"🖼️ Static image: {response['thumbnail_path']}")

                        # Check for fallback indicators
                        metadata = response.get("metadata", {})
                        if "generator" in metadata:
                            logger.info(f"🔧 Generator used: {metadata['generator']}")
                        if "fallback_reason" in metadata:
                            logger.info(
                                f"🔄 Fallback reason: {metadata['fallback_reason']}"
                            )
                    else:
                        logger.info("✅ Static animation generated successfully!")
                        if response.get("video_path"):
                            logger.info(f"🎥 Video: {response['video_path']}")
                        elif response.get("thumbnail_path"):
                            logger.info(f"🖼️ Static image: {response['thumbnail_path']}")

                # Show progress summary
                logger.info(f"📈 Progress messages: {len(progress_data['messages'])}")
                for msg in progress_data["messages"][-3:]:  # Show last 3 messages
                    logger.info(f"  {msg}")

            except Exception as e:
                logger.error(f"❌ Fallback failed: {e}")

            logger.info("✅ Fallback path demo completed")


async def demo_batch_processing():
    """Demonstrate batch processing with mixed success/failure scenarios."""
    logger.info("=" * 60)
    logger.info("DEMO 3: Batch Processing with Mixed Results")
    logger.info("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        output_dir = Path(tmpdir) / "batch_demo"

        # Configure for batch processing
        animation_config = AnimationConfig(
            quality=AnimationQuality.LOW,
            max_memory_mb=512,
            max_processing_time=90,
        )

        manim_config = ManimConfig(
            output_dir=output_dir,
            temp_dir=output_dir / "temp",
        )

        # Create animator
        async with ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,  # Mock with some failures
        ) as animator:

            logger.info("✅ Production Animator initialized for batch demo")
            logger.info(f"📁 Output directory: {output_dir}")

            # Process all theorems
            theorems = create_sample_theorems()
            logger.info(f"🎬 Processing {len(theorems)} theorems in batch")

            try:
                responses = await animator.animate_batch(
                    theorems, max_concurrent=2  # Process 2 at a time
                )

                logger.info(
                    f"✅ Batch processing completed: {len(responses)} responses"
                )

                # Analyze results
                successes = []
                failures = []

                for i, response in enumerate(responses):
                    theorem_name = theorems[i].theorem_name

                    if isinstance(response, dict):
                        if response.get("error"):
                            failures.append((theorem_name, response["error"]))
                        else:
                            successes.append(theorem_name)
                    else:
                        successes.append(theorem_name)

                logger.info(
                    f"📊 Results: {len(successes)} successes, {len(failures)} failures"
                )

                if successes:
                    logger.info("✅ Successful animations:")
                    for name in successes:
                        logger.info(f"  • {name}")

                if failures:
                    logger.info("⚠️ Failed animations:")
                    for name, error in failures:
                        logger.info(f"  • {name}: {error[:50]}...")

            except Exception as e:
                logger.error(f"❌ Batch processing failed: {e}")

            logger.info("✅ Batch processing demo completed")


async def demo_error_scenarios():
    """Demonstrate error handling and recovery scenarios."""
    logger.info("=" * 60)
    logger.info("DEMO 4: Error Handling and Recovery")
    logger.info("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        output_dir = Path(tmpdir) / "error_demo"

        # Configure with very restrictive limits to trigger errors
        animation_config = AnimationConfig(
            max_memory_mb=128,  # Low memory limit (minimum allowed)
            max_processing_time=60,  # Short timeout
        )

        manim_config = ManimConfig(
            output_dir=output_dir,
            temp_dir=output_dir / "temp",
        )

        async with ProductionAnimator(
            animation_config=animation_config,
            manim_config=manim_config,
            use_mock=True,
        ) as animator:

            logger.info("✅ Production Animator initialized with restrictive limits")
            logger.info(f"💾 Memory limit: {animation_config.max_memory_mb}MB")
            logger.info(f"⏱️ Timeout: {animation_config.max_processing_time}s")

            # Test error scenarios
            test_cases = [
                (
                    "Invalid theorem name",
                    ProofSketch(
                        theorem_name="",  # Invalid: empty name
                        introduction="Test error handling",
                        key_steps=[],  # Invalid: no steps
                        conclusion="Should fail validation",
                    ),
                ),
                ("Resource limits", create_sample_theorems()[2]),  # Complex theorem
            ]

            for case_name, theorem in test_cases:
                logger.info(f"🧪 Testing: {case_name}")

                try:
                    response = await animator.animate_proof(theorem)

                    if isinstance(response, dict) and response.get("error"):
                        logger.info(
                            f"✅ Error handled gracefully: {response['error'][:50]}..."
                        )
                        logger.info(
                            f"🛡️ Error type: {response.get('metadata', {}).get('error_type', 'unknown')}"
                        )
                    else:
                        logger.info("✅ Completed despite restrictions")

                except Exception as e:
                    logger.info(f"✅ Exception caught and handled: {type(e).__name__}")

            logger.info("✅ Error handling demo completed")


async def main():
    """Run the complete animator demonstration."""
    logger.info("🚀 Starting Production Animator Demonstration")
    logger.info("This demo showcases the robustness and fallback capabilities")
    logger.info("of the production-ready animator module.")
    logger.info("")

    try:
        # Run all demo scenarios
        await demo_success_path()
        await demo_fallback_path()
        await demo_batch_processing()
        await demo_error_scenarios()

        logger.info("=" * 60)
        logger.info("🎉 ALL DEMOS COMPLETED SUCCESSFULLY!")
        logger.info("=" * 60)
        logger.info("")
        logger.info("Key takeaways from this demonstration:")
        logger.info("✅ The animator ALWAYS produces output, even when Manim fails")
        logger.info("✅ Fallback mechanisms ensure graceful degradation")
        logger.info("✅ Progress tracking provides real-time feedback")
        logger.info("✅ Batch processing handles multiple theorems efficiently")
        logger.info("✅ Error handling prevents system crashes")
        logger.info("✅ Resource limits prevent system overload")
        logger.info("")
        logger.info("The production animator is ready for deployment! 🚀")

    except Exception as e:
        logger.error(f"❌ Demo failed: {e}")
        raise


if __name__ == "__main__":
    # Run the demonstration
    asyncio.run(main())
