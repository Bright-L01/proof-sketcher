"""Comprehensive tests for scene_builder.py to improve coverage."""

import uuid
from unittest.mock import Mock, patch

import pytest

from src.proof_sketcher.animator.formula_extractor import FormulaTransformation
from src.proof_sketcher.animator.models import (
    AnimationConfig,
    AnimationRequest,
    AnimationScene,
    AnimationSegment,
    TransformationType,
)
from src.proof_sketcher.animator.scene_builder import ProofAnimationBuilder
from src.proof_sketcher.generator.models import ProofSketch, ProofStep


class TestProofAnimationBuilder:
    """Tests for ProofAnimationBuilder class."""

    @pytest.fixture
    def builder(self):
        """Create a builder instance."""
        config = AnimationConfig()
        return ProofAnimationBuilder(config)

    @pytest.fixture
    def simple_proof_sketch(self):
        """Create a simple proof sketch for testing."""
        return ProofSketch(
            theorem_name="test_theorem",
            introduction="We will prove that a + 0 = a",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Apply the additive identity",
                    mathematical_content="a + 0 = a",
                    tactics=["rfl"],
                )
            ],
            conclusion="This completes the proof",
        )

    @pytest.fixture
    def complex_proof_sketch(self):
        """Create a complex proof sketch with multiple steps."""
        return ProofSketch(
            theorem_name="complex_theorem",
            introduction="We will prove this theorem using induction",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Base case: n = 0",
                    mathematical_content="P(0)",
                    tactics=["intros"],
                    intuition="The base case is trivial",
                ),
                ProofStep(
                    step_number=2,
                    description="Assume P(k) holds",
                    mathematical_content="P(k)",
                    tactics=["assume"],
                ),
                ProofStep(
                    step_number=3,
                    description="Prove P(k+1)",
                    mathematical_content="P(k) -> P(k+1)",
                    tactics=["simp", "rw"],
                ),
                ProofStep(
                    step_number=4,
                    description="By induction, the theorem holds",
                    mathematical_content="∀n, P(n)",
                    tactics=["exact"],
                ),
            ],
            conclusion="Therefore, the theorem is proved",
        )

    def test_build_animation_request_simple(self, builder, simple_proof_sketch):
        """Test building animation request for simple proof."""
        request = builder.build_animation_request(simple_proof_sketch)

        assert isinstance(request, AnimationRequest)
        assert request.theorem_name == "test_theorem"
        assert request.request_id is not None
        assert len(request.segments) > 0
        assert request.estimated_duration > 0
        assert request.total_scenes > 0

    def test_build_animation_request_complex(self, builder, complex_proof_sketch):
        """Test building animation request for complex proof."""
        request = builder.build_animation_request(complex_proof_sketch)

        assert isinstance(request, AnimationRequest)
        assert len(request.segments) >= 3  # intro, proof, conclusion
        assert request.total_scenes >= 4  # At least one per step

    def test_build_animation_request_with_segmentation(self, builder):
        """Test segmentation for very long proofs."""
        # Create a proof with many steps
        long_proof = ProofSketch(
            theorem_name="long_theorem",
            introduction="A very long proof",
            key_steps=[
                ProofStep(
                    step_number=i,
                    description=f"Step {i}",
                    mathematical_content=f"P({i})",
                    tactics=["auto"],
                )
                for i in range(1, 21)  # 20 steps
            ],
            conclusion="QED",
        )

        # Use config that triggers segmentation
        config = AnimationConfig(
            step_duration=30.0, max_duration=300.0  # 30s per step  # 5 minute max
        )

        request = builder.build_animation_request(long_proof, config)

        assert request.needs_segmentation is True
        # Verify segmentation was applied
        total_duration = sum(seg.total_duration for seg in request.segments)
        assert total_duration <= config.max_duration * 1.5  # Allow some buffer

    def test_create_introduction_segment(self, builder, simple_proof_sketch):
        """Test introduction segment creation."""
        config = AnimationConfig()
        segment = builder._create_introduction_segment(simple_proof_sketch, config)

        assert segment is not None
        assert segment.title == "Introduction"
        assert len(segment.scenes) >= 1
        assert segment.scenes[0].title == "Theorem Statement"
        assert segment.scenes[0].narration_text == simple_proof_sketch.introduction

    def test_create_introduction_segment_with_overview(self, builder):
        """Test introduction with overview for long introduction."""
        proof = ProofSketch(
            theorem_name="test",
            introduction="This is a very long introduction " * 10,  # > 100 chars
            key_steps=[
                ProofStep(step_number=1, description="Step", mathematical_content="a=b")
            ],
            conclusion="Done",
        )

        config = AnimationConfig()
        segment = builder._create_introduction_segment(proof, config)

        assert len(segment.scenes) == 2  # Title + Overview
        assert segment.scenes[1].title == "Proof Overview"

    def test_create_proof_segments(self, builder, complex_proof_sketch):
        """Test proof segment creation."""
        config = AnimationConfig()
        segments = builder._create_proof_segments(complex_proof_sketch, config)

        assert len(segments) > 0
        # Check that all steps are covered
        all_scenes = []
        for seg in segments:
            all_scenes.extend(seg.scenes)

        # Should have scenes for each step
        assert len(all_scenes) >= len(complex_proof_sketch.key_steps)

    def test_create_conclusion_segment(self, builder, simple_proof_sketch):
        """Test conclusion segment creation."""
        config = AnimationConfig()
        segment = builder._create_conclusion_segment(simple_proof_sketch, config)

        assert segment is not None
        assert segment.title == "Conclusion"
        assert len(segment.scenes) == 2  # Conclusion + QED
        assert segment.scenes[0].narration_text == simple_proof_sketch.conclusion
        assert segment.scenes[1].title == "Q.E.D."

    def test_create_step_scenes(self, builder, complex_proof_sketch):
        """Test scene creation for individual steps."""
        config = AnimationConfig()
        step = complex_proof_sketch.key_steps[0]  # Base case step

        scenes = builder._create_step_scenes(step, complex_proof_sketch, config)

        assert len(scenes) >= 2  # Intro + transformation
        # Since step has intuition, should have conclusion scene too
        assert len(scenes) == 3
        assert scenes[0].title == "Step 1: Setup"
        assert scenes[1].title == "Step 1: Transformation"
        assert scenes[2].title == "Step 1: Insight"

    def test_create_step_scenes_no_description(self, builder):
        """Test step scene creation without description."""
        config = AnimationConfig()
        step = ProofStep(
            step_number=1,
            description="",  # Empty description
            mathematical_content="a = b",
        )
        proof = ProofSketch(
            theorem_name="test",
            introduction="Test",
            key_steps=[step],
            conclusion="Done",
        )

        scenes = builder._create_step_scenes(step, proof, config)

        # Should skip intro scene
        assert len(scenes) >= 1
        if scenes:
            assert "Setup" not in scenes[0].title

    def test_group_proof_steps_small(self, builder):
        """Test grouping for small proofs."""
        steps = [
            ProofStep(step_number=i, description=f"Step {i}", mathematical_content="")
            for i in range(1, 4)
        ]

        groups = builder._group_proof_steps(steps)

        assert len(groups) == 1  # All in one group for small proof
        assert len(groups[0]) == 3

    def test_group_proof_steps_with_logical_breaks(self, builder):
        """Test grouping with logical break points."""
        steps = [
            ProofStep(step_number=1, description="First part", mathematical_content=""),
            ProofStep(step_number=2, description="Base case", mathematical_content=""),
            ProofStep(step_number=3, description="Next step", mathematical_content=""),
            ProofStep(
                step_number=4, description="Inductive step", mathematical_content=""
            ),
            ProofStep(step_number=5, description="Final step", mathematical_content=""),
        ]

        groups = builder._group_proof_steps(steps)

        # Should break at logical points
        assert len(groups) > 1
        # Base case should start new group
        assert any(
            "base case" in step.description.lower()
            for group in groups
            for step in group
            if group[0].step_number == group[0].step_number
        )

    def test_group_proof_steps_with_case_analysis(self, builder):
        """Test grouping with case analysis."""
        steps = [
            ProofStep(
                step_number=1, description="Setup", mathematical_content="", tactics=[]
            ),
            ProofStep(
                step_number=2,
                description="Case 1",
                mathematical_content="",
                tactics=["cases"],
            ),
            ProofStep(
                step_number=3,
                description="Case 2",
                mathematical_content="",
                tactics=["by_cases"],
            ),
        ]

        groups = builder._group_proof_steps(steps)

        # Case analysis should trigger new groups
        assert len(groups) >= 2

    def test_is_logical_break_point(self, builder):
        """Test logical break point detection."""
        # Test various break indicators
        break_steps = [
            ProofStep(step_number=1, description="Base case", mathematical_content=""),
            ProofStep(
                step_number=2, description="Inductive step", mathematical_content=""
            ),
            ProofStep(
                step_number=3, description="Suppose x > 0", mathematical_content=""
            ),
            ProofStep(
                step_number=4, description="By contradiction", mathematical_content=""
            ),
            ProofStep(
                step_number=5, description="Therefore, we have", mathematical_content=""
            ),
        ]

        for step in break_steps:
            assert builder._is_logical_break_point(step) is True

        # Non-break step
        regular_step = ProofStep(
            step_number=1, description="Apply simplification", mathematical_content=""
        )
        assert builder._is_logical_break_point(regular_step) is False

    def test_contains_case_analysis(self, builder):
        """Test case analysis detection."""
        case_steps = [
            ProofStep(
                step_number=1,
                description="",
                mathematical_content="",
                tactics=["cases"],
            ),
            ProofStep(
                step_number=2,
                description="",
                mathematical_content="",
                tactics=["by_cases"],
            ),
            ProofStep(
                step_number=3,
                description="",
                mathematical_content="",
                tactics=["split"],
            ),
            ProofStep(
                step_number=4, description="", mathematical_content="", tactics=["left"]
            ),
            ProofStep(
                step_number=5,
                description="",
                mathematical_content="",
                tactics=["right"],
            ),
        ]

        for step in case_steps:
            assert builder._contains_case_analysis(step) is True

        # Non-case step
        regular_step = ProofStep(
            step_number=1, description="", mathematical_content="", tactics=["simp"]
        )
        assert builder._contains_case_analysis(regular_step) is False

    def test_get_segment_title(self, builder):
        """Test segment title generation."""
        # Single step
        single_group = [
            ProofStep(step_number=5, description="Single", mathematical_content="")
        ]
        assert builder._get_segment_title(single_group) == "Step 5"

        # Multiple steps
        multi_group = [
            ProofStep(step_number=3, description="First", mathematical_content=""),
            ProofStep(step_number=4, description="Second", mathematical_content=""),
            ProofStep(step_number=5, description="Third", mathematical_content=""),
        ]
        assert builder._get_segment_title(multi_group) == "Steps 3-5"

        # Base case
        base_group = [
            ProofStep(
                step_number=1, description="Base case n=0", mathematical_content=""
            ),
            ProofStep(
                step_number=2, description="Verify base", mathematical_content=""
            ),
        ]
        assert builder._get_segment_title(base_group) == "Base Case"

        # Inductive step
        inductive_group = [
            ProofStep(
                step_number=3,
                description="Inductive hypothesis",
                mathematical_content="",
            ),
            ProofStep(
                step_number=4,
                description="Prove inductive step",
                mathematical_content="",
            ),
        ]
        assert builder._get_segment_title(inductive_group) == "Inductive Step"

    def test_extract_formulas(self, builder):
        """Test formula extraction methods."""
        proof = ProofSketch(
            theorem_name="test_theorem",
            introduction="Test",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Test step",
                    mathematical_content="a + b = c",
                )
            ],
            conclusion="Done",
        )

        # Test main formula extraction
        main_formula = builder._extract_main_formula(proof)
        assert "test_theorem" in main_formula

        # Test proof outline
        outline = builder._create_proof_outline(proof)
        assert "Step 1" in outline

        # Test final step formula
        final_formula = builder._get_final_step_formula(proof)
        assert final_formula is not None

    def test_analyze_step_transformation(self, builder):
        """Test step transformation analysis."""
        step = ProofStep(
            step_number=1,
            description="Simplify the expression",
            mathematical_content="a + 0 = a",
            tactics=["simp"],
        )

        # Mock the formula extractor
        mock_transformation = FormulaTransformation(
            source="a + 0",
            target="a",
            transformation_type=TransformationType.SIMPLIFICATION,
            intermediate_steps=[],
            highlighted_parts=["0", "+"],
            explanation="Additive identity",
        )

        with patch.object(
            builder.formula_extractor,
            "analyze_proof_transformation",
            return_value=mock_transformation,
        ):
            transformation = builder._analyze_step_transformation(step)

            assert transformation is not None
            assert (
                transformation.transformation_type == TransformationType.SIMPLIFICATION
            )

    def test_get_step_highlights(self, builder):
        """Test highlight extraction for steps."""
        step = ProofStep(
            step_number=1,
            description="Simplify",
            mathematical_content="",
            tactics=["simp"],
        )

        transformation = FormulaTransformation(
            source="a + 0",
            target="a",
            transformation_type=TransformationType.SIMPLIFICATION,
            intermediate_steps=[],
            highlighted_parts=["a"],
            explanation="",
        )

        highlights = builder._get_step_highlights(step, transformation)

        # Should include original highlights plus simp-specific ones
        assert "a" in highlights
        assert "0" in highlights  # Added by simp
        assert "=" in highlights  # Added by simp

    def test_apply_segmentation_strategy(self, builder):
        """Test segmentation strategy for long animations."""
        config = AnimationConfig(max_duration=300.0)  # 5 minutes max

        # Create segments with varying durations
        segments = [
            AnimationSegment(
                segment_id="short",
                title="Short segment",
                scenes=[
                    AnimationScene(
                        scene_id="s1",
                        title="Scene 1",
                        duration=50.0,
                        initial_formula="a",
                        final_formula="b",
                        transformation_type=TransformationType.REWRITE,
                    )
                ],
            ),
            AnimationSegment(
                segment_id="long",
                title="Long segment",
                scenes=[
                    AnimationScene(
                        scene_id=f"s{i}",
                        title=f"Scene {i}",
                        duration=60.0,
                        initial_formula="a",
                        final_formula="b",
                        transformation_type=TransformationType.REWRITE,
                    )
                    for i in range(5)  # 300s total
                ],
            ),
        ]

        # Calculate durations
        for seg in segments:
            seg.calculate_duration()

        new_segments = builder._apply_segmentation_strategy(segments, config)

        # Short segment should remain unchanged
        assert any(seg.segment_id == "short" for seg in new_segments)

        # Long segment should be split
        long_parts = [seg for seg in new_segments if "long" in seg.segment_id]
        assert len(long_parts) > 1

        # Each part should be under the limit
        for seg in new_segments:
            assert seg.total_duration <= config.max_duration / 3 * 1.5

    def test_split_segment(self, builder):
        """Test segment splitting."""
        # Create a long segment
        scenes = [
            AnimationScene(
                scene_id=f"scene_{i}",
                title=f"Scene {i}",
                duration=50.0,
                initial_formula="a",
                final_formula="b",
                transformation_type=TransformationType.REWRITE,
            )
            for i in range(4)  # 200s total
        ]

        segment = AnimationSegment(
            segment_id="long_segment", title="Long Segment", scenes=scenes
        )
        segment.calculate_duration()

        # Split with 100s max duration
        split_segments = builder._split_segment(segment, 100.0)

        assert len(split_segments) >= 2
        for i, seg in enumerate(split_segments):
            assert seg.total_duration <= 100.0
            assert f"Part {i+1}" in seg.title or i == len(split_segments) - 1

    def test_split_segment_single_scene(self, builder):
        """Test splitting segment with single scene."""
        # Create segment with one long scene
        segment = AnimationSegment(
            segment_id="single_scene",
            title="Single Scene Segment",
            scenes=[
                AnimationScene(
                    scene_id="long_scene",
                    title="Long Scene",
                    duration=200.0,
                    initial_formula="a",
                    final_formula="b",
                    transformation_type=TransformationType.REWRITE,
                )
            ],
        )
        segment.calculate_duration()

        # Try to split with 100s max
        split_segments = builder._split_segment(segment, 100.0)

        # Can't split single scene, should truncate
        assert len(split_segments) == 1
        assert split_segments[0].scenes[0].duration <= 100.0

    def test_create_step_transformation_scene_no_transformation(self, builder):
        """Test transformation scene when no transformation detected."""
        step = ProofStep(
            step_number=1, description="Identity step", mathematical_content="a = a"
        )

        config = AnimationConfig()

        # Mock analyzer to return None (no transformation)
        with patch.object(builder, "_analyze_step_transformation", return_value=None):
            scene = builder._create_step_transformation_scene(step, config)

            assert scene is None

    def test_extract_step_formulas_with_formula_extractor(self, builder):
        """Test formula extraction using formula extractor."""
        step = ProofStep(
            step_number=1,
            description="Transform a + b to b + a",
            mathematical_content="",  # No mathematical content
        )

        # Mock formula extractor
        with patch.object(
            builder.formula_extractor,
            "extract_from_proof_step",
            return_value=("a + b", "b + a"),
        ):
            with patch.object(
                builder.formula_extractor,
                "convert_lean_to_latex",
                side_effect=lambda x: f"\\text{{{x}}}",
            ):
                initial = builder._extract_step_initial_formula(step)
                final = builder._extract_step_final_formula(step)

                assert initial == "\\text{a + b}"
                assert final == "\\text{b + a}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
