"""Template-based educational generator for Lean theorem explanations.

⚠️ IMPORTANT: This is a template-based system, not AI-powered. It uses pattern matching
and predefined templates to generate explanations at different educational levels.
"""

from __future__ import annotations

from ..parser.models import TheoremInfo
from .models import EducationalLevel, GenerationConfig, ProofSketch
from .offline import EducationalGenerator


class SimpleGenerator:
    """Educational generator implementing the Proof Explanation Ladder.

    This generator serves undergraduate discrete mathematics students transitioning
    to formal proofs by providing progressive explanations at 4 complexity levels:

    Level 1 (Intuitive): Why this theorem matters and what it means
    Level 2 (Conceptual): What proof strategy we're using and why
    Level 3 (Bridging): How informal reasoning maps to formal steps
    Level 4 (Formal): Complete Lean 4 syntax with annotations
    """

    def __init__(self) -> None:
        """Initialize educational generator with the Proof Explanation Ladder."""
        self.educational_generator = EducationalGenerator()

    @property
    def offline_generator(self):
        """Backward compatibility property."""
        return self.educational_generator

    def generate_offline(self, theorem: TheoremInfo) -> ProofSketch:
        """Generate educational proof sketch with progressive complexity levels.

        Args:
            theorem: Theorem to explain

        Returns:
            Educational proof sketch with 4-level explanations
        """
        return self.educational_generator.generate_proof_sketch(theorem)

    def generate_proof_sketch(
        self, theorem: TheoremInfo, config: GenerationConfig | None = None
    ) -> ProofSketch:
        """Generate educational proof sketch with the Proof Explanation Ladder.

        Args:
            theorem: Theorem to explain
            config: Generation config (ignored in educational mode)

        Returns:
            Educational proof sketch with progressive complexity levels
        """
        return self.generate_offline(theorem)

    def generate_explanation_for_level(
        self, theorem: TheoremInfo, level: EducationalLevel
    ) -> dict[str, str]:
        """Generate explanation for a specific educational level.

        Args:
            theorem: Theorem to explain
            level: Educational complexity level (1-4)

        Returns:
            Dictionary with overview, steps, and conclusion for the specified level
        """
        sketch = self.generate_proof_sketch(theorem)

        # Extract explanations for the specified level
        overview = sketch.get_overview(level)
        conclusion = sketch.get_conclusion(level)

        # Get step explanations for this level
        step_explanations = []
        for step in sketch.key_steps:
            step_explanations.append(step.get_explanation(level))

        return {
            "overview": overview,
            "steps": step_explanations,
            "conclusion": conclusion,
            "level": level.value,
            "theorem_name": theorem.name,
        }

    def generate_educational_sketch(
        self,
        theorem: TheoremInfo,
        target_level: str = "intermediate",
        config: GenerationConfig | None = None,
    ) -> ProofSketch:
        """Generate educational proof sketch with Lean Learning Bridge approach.

        Args:
            theorem: Theorem to explain (any type)
            target_level: Target educational level (beginner/intermediate/advanced)
            config: Generation config (ignored in educational mode)

        Returns:
            Educational proof sketch with progressive complexity levels
        """
        # Import here to avoid circular imports
        from ..parser.lsp_client import SemanticTheoremInfo

        # Convert SemanticTheoremInfo to TheoremInfo if needed
        if isinstance(theorem, SemanticTheoremInfo):
            base_theorem = TheoremInfo(
                name=theorem.name,
                statement=theorem.statement,
                proof=theorem.proof,
                dependencies=theorem.dependencies,
                line_number=theorem.line_number,
                docstring=theorem.docstring,
                namespace=theorem.namespace,
                visibility=theorem.visibility,
                tactics=theorem.tactics,
                is_axiom=theorem.is_axiom,
                file_path=theorem.file_path,
                start_line=theorem.start_line,
                end_line=theorem.end_line,
            )
            return self.generate_offline(base_theorem)
        else:
            return self.generate_offline(theorem)

    def get_learning_progression(self, theorem: TheoremInfo) -> dict[str, dict]:
        """Get the complete learning progression for a theorem across all 4 levels.

        This method implements the core Lean Learning Bridge functionality,
        providing a structured path from intuitive understanding to formal proofs.

        Args:
            theorem: Theorem to explain

        Returns:
            Dictionary with explanations for all 4 educational levels
        """
        sketch = self.generate_proof_sketch(theorem)

        progression = {}
        for level in EducationalLevel:
            progression[level.value] = self.generate_explanation_for_level(
                theorem, level
            )

        # Add metadata about the learning progression
        progression["metadata"] = {
            "theorem_name": theorem.name,
            "proof_strategy": sketch.proof_strategy.value,
            "discrete_math_topic": sketch.discrete_math_topic,
            "difficulty_level": sketch.difficulty_level,
            "mathematical_areas": sketch.mathematical_areas,
            "prerequisites": sketch.prerequisites,
        }

        return progression
