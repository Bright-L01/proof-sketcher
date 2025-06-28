"""Scene builder for converting proof sketches to animation scenes."""

import logging
import uuid
from typing import List, Optional

from ..generator.models import ProofSketch, ProofStep
from .formula_extractor import FormulaExtractor, FormulaTransformation
from .models import (AnimationConfig, AnimationRequest, AnimationScene,
                     AnimationSegment, TransformationType)


class ProofAnimationBuilder:
    """Builds animation scenes from proof sketches."""

    def __init__(self, config: Optional[AnimationConfig] = None):
        """Initialize the builder.

        Args:
            config: Animation configuration. Uses default if None.
        """
        self.config = config or AnimationConfig()
        self.formula_extractor = FormulaExtractor()
        self.logger = logging.getLogger(__name__)

    def build_animation_request(
        self, proof_sketch: ProofSketch, config: Optional[AnimationConfig] = None
    ) -> AnimationRequest:
        """Build complete animation request from proof sketch.

        Args:
            proof_sketch: Proof sketch to animate
            config: Animation configuration override

        Returns:
            Complete animation request
        """
        config = config or self.config

        # Create segments based on proof structure
        segments = self._create_segments(proof_sketch, config)

        # Create animation request
        request = AnimationRequest(
            theorem_name=proof_sketch.theorem_name,
            request_id=str(uuid.uuid4()),
            segments=segments,
            config=config,
        )

        # Calculate estimated duration
        request.calculate_estimated_duration()

        # If duration exceeds limit, apply segmentation strategy
        if request.needs_segmentation:
            segments = self._apply_segmentation_strategy(segments, config)
            request.segments = segments
            request.calculate_estimated_duration()

        self.logger.info(
            f"Built animation request for {proof_sketch.theorem_name}: "
            f"{request.total_scenes} scenes, {request.estimated_duration:.1f}s"
        )

        return request

    def _create_segments(
        self, proof_sketch: ProofSketch, config: AnimationConfig
    ) -> List[AnimationSegment]:
        """Create animation segments from proof sketch.

        Args:
            proof_sketch: Proof sketch
            config: Animation configuration

        Returns:
            List of animation segments
        """
        segments = []

        # Introduction segment
        intro_segment = self._create_introduction_segment(proof_sketch, config)
        if intro_segment:
            segments.append(intro_segment)

        # Main proof segments
        proof_segments = self._create_proof_segments(proof_sketch, config)
        segments.extend(proof_segments)

        # Conclusion segment
        conclusion_segment = self._create_conclusion_segment(proof_sketch, config)
        if conclusion_segment:
            segments.append(conclusion_segment)

        return segments

    def _create_introduction_segment(
        self, proof_sketch: ProofSketch, config: AnimationConfig
    ) -> Optional[AnimationSegment]:
        """Create introduction segment.

        Args:
            proof_sketch: Proof sketch
            config: Animation configuration

        Returns:
            Introduction segment or None
        """
        scenes = []

        # Title scene
        title_scene = AnimationScene(
            scene_id=f"{proof_sketch.theorem_name}_title",
            title="Theorem Statement",
            duration=config.base_duration * 0.3,  # 30% of base duration
            initial_formula="",
            final_formula=self._extract_main_formula(proof_sketch),
            transformation_type=TransformationType.EXPANSION,
            narration_text=proof_sketch.introduction,
            fade_in_time=2.0,
            fade_out_time=1.0,
            pause_after=2.0,
        )
        scenes.append(title_scene)

        # Overview scene (if introduction is substantial)
        if len(proof_sketch.introduction) > 100:
            overview_scene = AnimationScene(
                scene_id=f"{proof_sketch.theorem_name}_overview",
                title="Proof Overview",
                duration=config.base_duration * 0.2,
                initial_formula=self._extract_main_formula(proof_sketch),
                final_formula=self._create_proof_outline(proof_sketch),
                transformation_type=TransformationType.EXPANSION,
                narration_text=f"We will prove this in {len(proof_sketch.key_steps)} main steps.",
                fade_in_time=1.0,
                fade_out_time=1.0,
                pause_after=1.5,
            )
            scenes.append(overview_scene)

        if scenes:
            segment = AnimationSegment(
                segment_id=f"{proof_sketch.theorem_name}_introduction",
                title="Introduction",
                scenes=scenes,
            )
            segment.calculate_duration()
            return segment

        return None

    def _create_proof_segments(
        self, proof_sketch: ProofSketch, config: AnimationConfig
    ) -> List[AnimationSegment]:
        """Create main proof segments from proof steps.

        Args:
            proof_sketch: Proof sketch
            config: Animation configuration

        Returns:
            List of proof segments
        """
        segments = []

        # Group steps into logical segments
        step_groups = self._group_proof_steps(proof_sketch.key_steps)

        for group_idx, step_group in enumerate(step_groups):
            segment_scenes = []

            for step in step_group:
                # Create scenes for this step
                step_scenes = self._create_step_scenes(step, proof_sketch, config)
                segment_scenes.extend(step_scenes)

            if segment_scenes:
                segment = AnimationSegment(
                    segment_id=f"{proof_sketch.theorem_name}_proof_{group_idx}",
                    title=self._get_segment_title(step_group),
                    scenes=segment_scenes,
                )
                segment.calculate_duration()
                segments.append(segment)

        return segments

    def _create_conclusion_segment(
        self, proof_sketch: ProofSketch, config: AnimationConfig
    ) -> Optional[AnimationSegment]:
        """Create conclusion segment.

        Args:
            proof_sketch: Proof sketch
            config: Animation configuration

        Returns:
            Conclusion segment or None
        """
        scenes = []

        # Final result scene
        final_scene = AnimationScene(
            scene_id=f"{proof_sketch.theorem_name}_conclusion",
            title="Conclusion",
            duration=config.base_duration * 0.3,
            initial_formula=self._get_final_step_formula(proof_sketch),
            final_formula=self._extract_main_formula(proof_sketch),
            transformation_type=TransformationType.EQUALITY_CHAIN,
            narration_text=proof_sketch.conclusion,
            fade_in_time=1.0,
            fade_out_time=2.0,
            pause_after=3.0,
        )
        scenes.append(final_scene)

        # QED scene
        qed_scene = AnimationScene(
            scene_id=f"{proof_sketch.theorem_name}_qed",
            title="Q.E.D.",
            duration=config.base_duration * 0.2,
            initial_formula=self._extract_main_formula(proof_sketch),
            final_formula=self._extract_main_formula(proof_sketch) + r" \quad \square",
            transformation_type=TransformationType.EXPANSION,
            narration_text="This completes the proof.",
            fade_in_time=1.0,
            fade_out_time=2.0,
            pause_after=2.0,
        )
        scenes.append(qed_scene)

        segment = AnimationSegment(
            segment_id=f"{proof_sketch.theorem_name}_conclusion",
            title="Conclusion",
            scenes=scenes,
        )
        segment.calculate_duration()
        return segment

    def _create_step_scenes(
        self, step: ProofStep, proof_sketch: ProofSketch, config: AnimationConfig
    ) -> List[AnimationScene]:
        """Create animation scenes for a single proof step.

        Args:
            step: Proof step
            proof_sketch: Overall proof sketch
            config: Animation configuration

        Returns:
            List of scenes for this step
        """
        scenes = []

        # Step introduction scene
        intro_scene = self._create_step_intro_scene(step, config)
        if intro_scene:
            scenes.append(intro_scene)

        # Main transformation scene
        transform_scene = self._create_step_transformation_scene(step, config)
        if transform_scene:
            scenes.append(transform_scene)

        # Step conclusion scene (if needed)
        if step.intuition and len(step.intuition) > 50:
            conclusion_scene = self._create_step_conclusion_scene(step, config)
            if conclusion_scene:
                scenes.append(conclusion_scene)

        return scenes

    def _create_step_intro_scene(
        self, step: ProofStep, config: AnimationConfig
    ) -> Optional[AnimationScene]:
        """Create introduction scene for a proof step."""
        if not step.description:
            return None

        # Extract formulas from the step
        initial_formula = self._extract_step_initial_formula(step)

        scene = AnimationScene(
            scene_id=f"step_{step.step_number}_intro",
            title=f"Step {step.step_number}: Setup",
            duration=config.step_duration * 0.3,
            initial_formula=initial_formula,
            final_formula=initial_formula,
            transformation_type=TransformationType.EXPANSION,
            narration_text=step.description,
            fade_in_time=1.0,
            fade_out_time=0.5,
            pause_after=1.0,
        )

        return scene

    def _create_step_transformation_scene(
        self, step: ProofStep, config: AnimationConfig
    ) -> Optional[AnimationScene]:
        """Create main transformation scene for a proof step."""
        # Extract transformation from step
        transformation = self._analyze_step_transformation(step)

        if not transformation:
            return None

        # Determine highlighted parts
        highlighted_parts = self._get_step_highlights(step, transformation)

        scene = AnimationScene(
            scene_id=f"step_{step.step_number}_transform",
            title=f"Step {step.step_number}: Transformation",
            duration=config.step_duration,
            initial_formula=transformation.source,
            final_formula=transformation.target,
            intermediate_formulas=transformation.intermediate_steps,
            transformation_type=transformation.transformation_type,
            highlighted_parts=highlighted_parts,
            narration_text=transformation.explanation,
            fade_in_time=1.0,
            fade_out_time=1.0,
            pause_after=config.pause_time,
        )

        return scene

    def _create_step_conclusion_scene(
        self, step: ProofStep, config: AnimationConfig
    ) -> Optional[AnimationScene]:
        """Create conclusion scene for a proof step."""
        if not step.intuition:
            return None

        final_formula = self._extract_step_final_formula(step)

        scene = AnimationScene(
            scene_id=f"step_{step.step_number}_conclusion",
            title=f"Step {step.step_number}: Insight",
            duration=config.step_duration * 0.4,
            initial_formula=final_formula,
            final_formula=final_formula,
            transformation_type=TransformationType.EXPANSION,
            narration_text=step.intuition,
            fade_in_time=0.5,
            fade_out_time=1.0,
            pause_after=1.5,
        )

        return scene

    def _group_proof_steps(self, steps: List[ProofStep]) -> List[List[ProofStep]]:
        """Group proof steps into logical segments.

        Args:
            steps: List of proof steps

        Returns:
            List of step groups
        """
        if len(steps) <= 3:
            # Small proof, keep all steps in one group
            return [steps]

        groups = []
        current_group = []

        for step in steps:
            current_group.append(step)

            # Start new group if current one is getting large or at logical break
            if (
                len(current_group) >= 3
                or self._is_logical_break_point(step)
                or self._contains_case_analysis(step)
            ):
                groups.append(current_group)
                current_group = []

        # Add remaining steps
        if current_group:
            if groups and len(current_group) == 1:
                # Merge single remaining step with last group
                groups[-1].extend(current_group)
            else:
                groups.append(current_group)

        return groups

    def _is_logical_break_point(self, step: ProofStep) -> bool:
        """Check if step represents a logical break point."""
        indicators = [
            "base case",
            "inductive step",
            "case",
            "suppose",
            "assume",
            "contradiction",
            "therefore",
            "hence",
            "thus",
        ]

        description_lower = step.description.lower()
        return any(indicator in description_lower for indicator in indicators)

    def _contains_case_analysis(self, step: ProofStep) -> bool:
        """Check if step contains case analysis."""
        case_tactics = ["cases", "by_cases", "split", "left", "right"]
        return any(tactic in step.tactics for tactic in case_tactics)

    def _get_segment_title(self, step_group: List[ProofStep]) -> str:
        """Get appropriate title for a segment based on its steps."""
        if len(step_group) == 1:
            return f"Step {step_group[0].step_number}"

        first_step = step_group[0].step_number
        last_step = step_group[-1].step_number

        # Check for specific patterns
        descriptions = [step.description.lower() for step in step_group]

        if any("base case" in desc for desc in descriptions):
            return "Base Case"
        elif any("inductive" in desc for desc in descriptions):
            return "Inductive Step"
        elif any("case" in desc for desc in descriptions):
            return "Case Analysis"
        else:
            return f"Steps {first_step}-{last_step}"

    def _extract_main_formula(self, proof_sketch: ProofSketch) -> str:
        """Extract the main theorem formula."""
        # This would ideally come from the theorem statement
        # For now, use a placeholder approach
        return f"\\text{{{proof_sketch.theorem_name}}}"

    def _create_proof_outline(self, proof_sketch: ProofSketch) -> str:
        """Create a visual outline of the proof structure."""
        steps = [f"\\text{{Step {i+1}}}" for i in range(len(proof_sketch.key_steps))]
        return " \\to ".join(steps)

    def _get_final_step_formula(self, proof_sketch: ProofSketch) -> str:
        """Get the formula from the final proof step."""
        if proof_sketch.key_steps:
            return self._extract_step_final_formula(proof_sketch.key_steps[-1])
        return self._extract_main_formula(proof_sketch)

    def _extract_step_initial_formula(self, step: ProofStep) -> str:
        """Extract initial formula for a step."""
        # Try to extract from mathematical content
        if step.mathematical_content:
            return self.formula_extractor.convert_lean_to_latex(
                step.mathematical_content
            )

        # Fallback to step description
        before_formula, _ = self.formula_extractor.extract_from_proof_step(
            step.description
        )
        return self.formula_extractor.convert_lean_to_latex(before_formula)

    def _extract_step_final_formula(self, step: ProofStep) -> str:
        """Extract final formula for a step."""
        # Try to extract from mathematical content
        if step.mathematical_content:
            return self.formula_extractor.convert_lean_to_latex(
                step.mathematical_content
            )

        # Try to extract from description
        _, after_formula = self.formula_extractor.extract_from_proof_step(
            step.description
        )
        if after_formula:
            return self.formula_extractor.convert_lean_to_latex(after_formula)

        # Fallback
        return self._extract_step_initial_formula(step)

    def _analyze_step_transformation(
        self, step: ProofStep
    ) -> Optional[FormulaTransformation]:
        """Analyze the transformation performed by a proof step."""
        initial_formula = self._extract_step_initial_formula(step)
        final_formula = self._extract_step_final_formula(step)

        if initial_formula == final_formula:
            return None

        # Create proof step text from tactics
        proof_step_text = " ".join(step.tactics) if step.tactics else step.description

        return self.formula_extractor.analyze_proof_transformation(
            initial_formula, final_formula, proof_step_text
        )

    def _get_step_highlights(
        self, step: ProofStep, transformation: FormulaTransformation
    ) -> List[str]:
        """Get parts to highlight for a step."""
        highlights = transformation.highlighted_parts.copy()

        # Add step-specific highlights based on tactics
        if "simp" in step.tactics:
            highlights.extend(["0", "1", "+", "="])
        elif "rw" in " ".join(step.tactics):
            # Highlight rewritten parts
            pass

        return highlights

    def _apply_segmentation_strategy(
        self, segments: List[AnimationSegment], config: AnimationConfig
    ) -> List[AnimationSegment]:
        """Apply segmentation strategy for long animations."""
        max_segment_duration = config.max_duration / 3  # Aim for 3 major segments max

        new_segments = []

        for segment in segments:
            if segment.total_duration <= max_segment_duration:
                new_segments.append(segment)
            else:
                # Split long segment
                split_segments = self._split_segment(segment, max_segment_duration)
                new_segments.extend(split_segments)

        return new_segments

    def _split_segment(
        self, segment: AnimationSegment, max_duration: float
    ) -> List[AnimationSegment]:
        """Split a segment that's too long."""
        if len(segment.scenes) <= 1:
            # Can't split further, just truncate
            for scene in segment.scenes:
                scene.duration = min(scene.duration, max_duration)
            segment.calculate_duration()
            return [segment]

        # Split scenes into smaller segments
        new_segments = []
        current_scenes = []
        current_duration = 0.0

        for scene in segment.scenes:
            if current_duration + scene.duration > max_duration and current_scenes:
                # Create new segment with current scenes
                new_segment = AnimationSegment(
                    segment_id=f"{segment.segment_id}_part_{len(new_segments) + 1}",
                    title=f"{segment.title} (Part {len(new_segments) + 1})",
                    scenes=current_scenes,
                )
                new_segment.calculate_duration()
                new_segments.append(new_segment)

                current_scenes = [scene]
                current_duration = scene.duration
            else:
                current_scenes.append(scene)
                current_duration += scene.duration

        # Add remaining scenes
        if current_scenes:
            new_segment = AnimationSegment(
                segment_id=f"{segment.segment_id}_part_{len(new_segments) + 1}",
                title=(
                    f"{segment.title} (Part {len(new_segments) + 1})"
                    if new_segments
                    else segment.title
                ),
                scenes=current_scenes,
            )
            new_segment.calculate_duration()
            new_segments.append(new_segment)

        return new_segments
