"""Semantic-aware generator for educational proof explanations.

This generator leverages the semantic analysis from LSP to create progressive,
educational explanations that adapt to different skill levels and learning contexts.

Key Features:
- Progressive difficulty explanations (beginner → intermediate → advanced)
- Semantic context awareness (proof methods, mathematical entities)
- Educational bridging between informal and formal mathematics
- Tactic-by-tactic proof walkthroughs
- Mathematical intuition development
- Prerequisite identification and explanation

Educational Philosophy:
- Start with intuition, then formalize
- Connect to familiar concepts
- Explain the "why" behind each step
- Build understanding progressively
- Encourage mathematical thinking

Usage:
    >>> generator = SemanticGenerator()
    >>> semantic_theorem = SemanticTheoremInfo(...)
    >>> sketch = generator.generate_educational_sketch(
    ...     semantic_theorem,
    ...     target_level="intermediate"
    ... )
"""

from __future__ import annotations

import logging

from ..parser.lsp_client import SemanticTheoremInfo, TacticInfo
from ..parser.models import TheoremInfo
from .models import GenerationConfig, ProofSketch, ProofStep


class EducationalLevel:
    """Constants for educational levels."""

    BEGINNER = "beginner"
    INTERMEDIATE = "intermediate"
    ADVANCED = "advanced"


class SemanticGenerator:
    """Advanced generator using semantic analysis for educational content."""

    def __init__(self, cache_dir: str | None = None):
        """Initialize the semantic generator.

        Args:
            cache_dir: Optional caching directory
        """
        self.logger = logging.getLogger(__name__)
        self.cache_dir = cache_dir

        # Educational templates and strategies
        self.proof_method_explanations = self._init_proof_method_explanations()
        self.tactic_explanations = self._init_tactic_explanations()
        self.mathematical_contexts = self._init_mathematical_contexts()

    def generate_educational_sketch(
        self,
        theorem: SemanticTheoremInfo | TheoremInfo,
        target_level: str = EducationalLevel.INTERMEDIATE,
        config: GenerationConfig | None = None,
    ) -> ProofSketch:
        """Generate an educational proof sketch adapted to the target level.

        Args:
            theorem: Theorem with semantic analysis
            target_level: Target educational level
            config: Generation configuration

        Returns:
            Educational proof sketch
        """
        self.logger.info(
            f"Generating educational sketch for {theorem.name} at {target_level} level"
        )

        # Handle both semantic and regular theorem info
        if isinstance(theorem, SemanticTheoremInfo):
            return self._generate_semantic_sketch(theorem, target_level, config)
        else:
            return self._generate_basic_sketch(theorem, target_level, config)

    def generate_proof_sketch(
        self,
        theorem: SemanticTheoremInfo | TheoremInfo,
        config: GenerationConfig | None = None,
    ) -> ProofSketch:
        """Generate proof sketch (backward compatibility method).

        Args:
            theorem: Theorem to explain
            config: Generation config

        Returns:
            Generated proof sketch
        """
        return self.generate_educational_sketch(
            theorem, EducationalLevel.INTERMEDIATE, config
        )

    def generate_offline(
        self, theorem: SemanticTheoremInfo | TheoremInfo
    ) -> ProofSketch:
        """Generate proof sketch using offline mode (backward compatibility).

        Args:
            theorem: Theorem to explain

        Returns:
            Generated proof sketch
        """
        return self.generate_educational_sketch(
            theorem, EducationalLevel.INTERMEDIATE, None
        )

    def _generate_semantic_sketch(
        self,
        theorem: SemanticTheoremInfo,
        target_level: str,
        config: GenerationConfig | None = None,
    ) -> ProofSketch:
        """Generate sketch using full semantic analysis."""

        # Analyze the theorem's educational characteristics
        edu_profile = self._analyze_educational_profile(theorem)

        # Generate level-appropriate introduction
        introduction = self._generate_level_introduction(
            theorem, target_level, edu_profile
        )

        # Generate progressive proof steps
        steps = self._generate_progressive_steps(theorem, target_level, edu_profile)

        # Generate educational conclusion
        conclusion = self._generate_educational_conclusion(
            theorem, target_level, edu_profile
        )

        # Determine educational metadata
        difficulty = self._determine_educational_difficulty(theorem, target_level)
        areas = self._identify_educational_areas(theorem)
        prerequisites = self._generate_educational_prerequisites(theorem, target_level)

        return ProofSketch(
            theorem_name=theorem.name,
            theorem_statement=theorem.statement or "",
            introduction=introduction,
            key_steps=steps,
            conclusion=conclusion,
            difficulty_level=difficulty,
            mathematical_areas=areas,
            prerequisites=prerequisites,
        )

    def _generate_basic_sketch(
        self,
        theorem: TheoremInfo,
        target_level: str,
        config: GenerationConfig | None = None,
    ) -> ProofSketch:
        """Generate basic educational sketch for non-semantic theorems."""

        # Generate basic introduction
        introduction = self._generate_basic_introduction(theorem, target_level)

        # Generate basic steps
        steps = self._generate_basic_steps(theorem, target_level)

        # Generate basic conclusion
        conclusion = self._generate_basic_conclusion(theorem, target_level)

        return ProofSketch(
            theorem_name=theorem.name,
            theorem_statement=theorem.statement or "",
            introduction=introduction,
            key_steps=steps,
            conclusion=conclusion,
            difficulty_level=target_level,
            mathematical_areas=["mathematics"],
            prerequisites=["Basic mathematical reasoning"],
        )

    def _generate_basic_introduction(
        self, theorem: TheoremInfo, target_level: str
    ) -> str:
        """Generate basic introduction for non-semantic theorems."""

        intro = f"This theorem, {theorem.name}, "

        # Basic classification
        statement = theorem.statement or ""
        if "=" in statement:
            intro += "establishes an equality between mathematical expressions. "
        elif "→" in statement or "->" in statement:
            intro += "shows an implication relationship. "
        else:
            intro += "proves an important mathematical relationship. "

        # Add level-appropriate context
        if target_level == EducationalLevel.BEGINNER:
            intro += "Let's work through this step by step to understand what it means and why it's true."
        elif target_level == EducationalLevel.INTERMEDIATE:
            intro += "We'll examine the mathematical reasoning behind this result."
        else:  # Advanced
            intro += "This formal statement can be established through rigorous mathematical proof."

        return intro

    def _generate_basic_steps(
        self, theorem: TheoremInfo, target_level: str
    ) -> list[ProofStep]:
        """Generate basic steps for non-semantic theorems."""

        steps = []

        # Setup step
        steps.append(
            ProofStep(
                step_number=1,
                description="Set up the proof context",
                tactics=["setup"],
                mathematical_content="Initial assumptions and goal",
                intuition=self._get_basic_setup_intuition(target_level),
            )
        )

        # Main reasoning step
        proof = theorem.proof or ""
        if "simp" in proof.lower():
            description = "Apply simplification rules"
            intuition = self._get_basic_simp_intuition(target_level)
        elif "rw" in proof.lower():
            description = "Apply rewriting steps"
            intuition = self._get_basic_rw_intuition(target_level)
        elif "induction" in proof.lower():
            description = "Use mathematical induction"
            intuition = self._get_basic_induction_intuition(target_level)
        else:
            description = "Apply mathematical reasoning"
            intuition = self._get_basic_reasoning_intuition(target_level)

        steps.append(
            ProofStep(
                step_number=2,
                description=description,
                tactics=["main"],
                mathematical_content="Core proof steps",
                intuition=intuition,
            )
        )

        return steps

    def _generate_basic_conclusion(
        self, theorem: TheoremInfo, target_level: str
    ) -> str:
        """Generate basic conclusion for non-semantic theorems."""

        conclusion = f"This completes the proof of {theorem.name}. "

        if target_level == EducationalLevel.BEGINNER:
            conclusion += "Understanding proofs like this helps build mathematical reasoning skills."
        elif target_level == EducationalLevel.INTERMEDIATE:
            conclusion += "This result demonstrates important mathematical principles."
        else:  # Advanced
            conclusion += (
                "This formally establishes the stated mathematical relationship."
            )

        return conclusion

    def _get_basic_setup_intuition(self, target_level: str) -> str:
        """Basic setup intuition by level."""
        if target_level == EducationalLevel.BEGINNER:
            return (
                "We start by understanding what we're trying to prove and what we know."
            )
        elif target_level == EducationalLevel.INTERMEDIATE:
            return "We establish our assumptions and clearly state our goal."
        else:
            return "We formalize the hypothesis context and goal statement."

    def _get_basic_simp_intuition(self, target_level: str) -> str:
        """Basic simplification intuition by level."""
        if target_level == EducationalLevel.BEGINNER:
            return "We use known mathematical rules to simplify until the answer is obvious."
        elif target_level == EducationalLevel.INTERMEDIATE:
            return "We apply simplification rules to reduce the expression to a normal form."
        else:
            return "We invoke the simplifier to apply simp lemmas and normalization."

    def _get_basic_rw_intuition(self, target_level: str) -> str:
        """Basic rewriting intuition by level."""
        if target_level == EducationalLevel.BEGINNER:
            return "We replace equals with equals, just like substitution in algebra."
        elif target_level == EducationalLevel.INTERMEDIATE:
            return "We apply equational reasoning to transform the expression."
        else:
            return "We perform term rewriting using established equalities."

    def _get_basic_induction_intuition(self, target_level: str) -> str:
        """Basic induction intuition by level."""
        if target_level == EducationalLevel.BEGINNER:
            return "We prove it works for the first case, then show each case leads to the next."
        elif target_level == EducationalLevel.INTERMEDIATE:
            return "We apply mathematical induction with base case and inductive step."
        else:
            return (
                "We utilize the induction principle of the underlying inductive type."
            )

    def _get_basic_reasoning_intuition(self, target_level: str) -> str:
        """Basic reasoning intuition by level."""
        if target_level == EducationalLevel.BEGINNER:
            return "We use logical reasoning to show why the statement must be true."
        elif target_level == EducationalLevel.INTERMEDIATE:
            return (
                "We apply appropriate mathematical techniques to establish the result."
            )
        else:
            return "We employ the relevant proof-theoretic methods for this type of statement."

    def _analyze_educational_profile(
        self, theorem: SemanticTheoremInfo
    ) -> dict[str, any]:
        """Analyze theorem for educational characteristics."""
        return {
            "complexity": theorem.complexity_score,
            "proof_method": theorem.proof_method,
            "mathematical_entities": theorem.mathematical_entities,
            "tactic_count": len(theorem.tactic_sequence),
            "proof_length": len(theorem.proof or ""),
            "has_induction": any(
                t.name == "induction" for t in theorem.tactic_sequence
            ),
            "has_cases": any(t.name == "cases" for t in theorem.tactic_sequence),
            "is_computational": theorem.proof_method
            in ["simplification", "rewriting", "calculation"],
            "is_structural": theorem.proof_method in ["induction", "case_analysis"],
        }

    def _generate_level_introduction(
        self,
        theorem: SemanticTheoremInfo,
        target_level: str,
        edu_profile: dict[str, any],
    ) -> str:
        """Generate introduction appropriate to the educational level."""

        base_intro = f"This theorem, {theorem.name}, "

        if target_level == EducationalLevel.BEGINNER:
            return self._generate_beginner_introduction(
                theorem, edu_profile, base_intro
            )
        elif target_level == EducationalLevel.INTERMEDIATE:
            return self._generate_intermediate_introduction(
                theorem, edu_profile, base_intro
            )
        else:  # Advanced
            return self._generate_advanced_introduction(
                theorem, edu_profile, base_intro
            )

    def _generate_beginner_introduction(
        self, theorem: SemanticTheoremInfo, edu_profile: dict[str, any], base: str
    ) -> str:
        """Generate beginner-level introduction with intuitive explanations."""

        intro = base + "shows us something fundamental about mathematics. "

        # Add intuitive explanation based on statement
        statement = theorem.statement or ""
        if "=" in statement:
            intro += "It proves that two mathematical expressions are equal - they represent the same value, just written differently. "
        elif "→" in statement or "->" in statement:
            intro += "It shows that if one thing is true, then another thing must also be true. "
        elif "∀" in statement or "forall" in statement:
            intro += (
                "It proves something is true for all possible cases we might consider. "
            )

        # Add context about proof method
        method = edu_profile.get("proof_method", "unknown")
        if method == "induction":
            intro += "The proof uses mathematical induction - like climbing a ladder, we prove it works for the first step, then show that if it works for any step, it works for the next step too. "
        elif method == "simplification":
            intro += "The proof works by simplifying the mathematical expressions until we can see they're obviously equal. "
        elif method == "case_analysis":
            intro += "The proof considers different possible cases separately, showing that the statement is true in each case. "

        # Add encouragement for beginners
        if edu_profile.get("complexity", 0) < 3:
            intro += "This is a good theorem to study because the proof is straightforward and uses fundamental mathematical ideas."
        else:
            intro += "While this theorem might seem challenging at first, we'll break it down step by step to understand how it works."

        return intro

    def _generate_intermediate_introduction(
        self, theorem: SemanticTheoremInfo, edu_profile: dict[str, any], base: str
    ) -> str:
        """Generate intermediate-level introduction with mathematical context."""

        intro = base + "establishes an important relationship in "

        # Add mathematical context
        entities = edu_profile.get("mathematical_entities", [])
        if entities:
            if any(entity in ["Nat", "Int", "Real"] for entity in entities):
                intro += "number theory and arithmetic. "
            elif any(entity in ["Set", "List", "Vector"] for entity in entities):
                intro += "algebraic structures and data types. "
            else:
                intro += "mathematical structures and their properties. "
        else:
            intro += "fundamental mathematics. "

        # Explain the proof approach
        method = edu_profile.get("proof_method", "unknown")
        method_explanation = self.proof_method_explanations.get(method, {}).get(
            "intermediate", ""
        )
        if method_explanation:
            intro += method_explanation + " "

        # Add complexity context
        complexity = edu_profile.get("complexity", 0)
        if complexity < 2:
            intro += (
                "The proof is relatively direct, using basic mathematical principles. "
            )
        elif complexity < 4:
            intro += "The proof requires several steps and careful reasoning. "
        else:
            intro += "This is a sophisticated proof that demonstrates advanced mathematical techniques. "

        return intro

    def _generate_advanced_introduction(
        self, theorem: SemanticTheoremInfo, edu_profile: dict[str, any], base: str
    ) -> str:
        """Generate advanced-level introduction with formal context."""

        intro = base + "is a formal statement that "

        # Technical classification
        statement = theorem.statement or ""
        if "∀" in statement and "∃" in statement:
            intro += "combines universal and existential quantification. "
        elif "∀" in statement:
            intro += "makes a universal claim across all elements of the domain. "
        elif "∃" in statement:
            intro += "establishes the existence of objects with specific properties. "
        elif "=" in statement:
            intro += "establishes an equality relation with potential computational content. "

        # Proof-theoretic analysis
        method = edu_profile.get("proof_method", "unknown")
        if method == "induction":
            intro += "The proof employs structural induction, leveraging the inductive principle of the underlying type. "
        elif method == "case_analysis":
            intro += "The proof proceeds by case analysis, exhaustively covering all possible scenarios. "
        elif method == "rewriting":
            intro += (
                "The proof primarily uses equational reasoning and term rewriting. "
            )

        # Complexity analysis
        complexity = edu_profile.get("complexity", 0)
        if complexity > 5:
            intro += "The proof complexity suggests non-trivial interactions between multiple mathematical concepts. "

        # Semantic context
        if theorem.semantic_dependencies:
            intro += f"This theorem depends on {len(theorem.semantic_dependencies)} other results, indicating its position in the broader mathematical development. "

        return intro

    def _generate_progressive_steps(
        self,
        theorem: SemanticTheoremInfo,
        target_level: str,
        edu_profile: dict[str, any],
    ) -> list[ProofStep]:
        """Generate proof steps appropriate to the educational level."""

        if theorem.tactic_sequence:
            return self._generate_tactic_based_steps(theorem, target_level, edu_profile)
        else:
            return self._generate_generic_educational_steps(
                theorem, target_level, edu_profile
            )

    def _generate_tactic_based_steps(
        self,
        theorem: SemanticTheoremInfo,
        target_level: str,
        edu_profile: dict[str, any],
    ) -> list[ProofStep]:
        """Generate steps based on actual tactic sequence."""

        steps = []

        # Group tactics into logical steps
        tactic_groups = self._group_tactics_educationally(theorem.tactic_sequence)

        for i, group in enumerate(tactic_groups, 1):
            step = self._create_educational_step(
                step_number=i,
                tactics=group,
                theorem=theorem,
                target_level=target_level,
                edu_profile=edu_profile,
            )
            steps.append(step)

        return steps

    def _group_tactics_educationally(
        self, tactics: list[TacticInfo]
    ) -> list[list[TacticInfo]]:
        """Group tactics into educational units."""
        if not tactics:
            return []

        groups = []
        current_group = []

        for tactic in tactics:
            current_group.append(tactic)

            # End group on major proof steps
            if tactic.name in ["induction", "cases", "simp", "exact"]:
                groups.append(current_group)
                current_group = []

        # Add remaining tactics if any
        if current_group:
            groups.append(current_group)

        return groups or [[tactic] for tactic in tactics[:3]]  # Fallback

    def _create_educational_step(
        self,
        step_number: int,
        tactics: list[TacticInfo],
        theorem: SemanticTheoremInfo,
        target_level: str,
        edu_profile: dict[str, any],
    ) -> ProofStep:
        """Create an educational proof step from tactics."""

        main_tactic = tactics[0] if tactics else None
        if not main_tactic:
            return self._create_generic_step(step_number, target_level)

        # Get educational explanation for this tactic
        tactic_info = self.tactic_explanations.get(main_tactic.name, {})
        level_info = tactic_info.get(target_level, tactic_info.get("default", {}))

        description = level_info.get("description", f"Apply {main_tactic.name}")
        intuition = level_info.get(
            "intuition", f"This step uses {main_tactic.name} to make progress."
        )

        # Enhance with context
        if target_level == EducationalLevel.BEGINNER:
            intuition = self._enhance_intuition_for_beginners(
                intuition, main_tactic, edu_profile
            )
        elif target_level == EducationalLevel.ADVANCED:
            description = self._enhance_description_for_advanced(
                description, main_tactic, edu_profile
            )

        return ProofStep(
            step_number=step_number,
            description=description,
            tactics=[t.name for t in tactics],
            mathematical_content=f"Tactics: {', '.join(t.name for t in tactics)}",
            intuition=intuition,
        )

    def _enhance_intuition_for_beginners(
        self, base_intuition: str, tactic: TacticInfo, edu_profile: dict[str, any]
    ) -> str:
        """Enhance intuition with beginner-friendly explanations."""

        enhanced = base_intuition

        if tactic.name == "induction":
            enhanced += " Think of it like proving something works for all natural numbers by showing: (1) it works for 0, and (2) if it works for any number n, it also works for n+1."
        elif tactic.name == "simp":
            enhanced += " This is like simplifying an algebraic expression by applying known rules automatically."
        elif tactic.name == "rw":
            enhanced += " We're replacing equals with equals, just like substituting in algebra."
        elif tactic.name == "cases":
            enhanced += " We consider each possibility separately, like checking different cases in a word problem."

        return enhanced

    def _enhance_description_for_advanced(
        self, base_description: str, tactic: TacticInfo, edu_profile: dict[str, any]
    ) -> str:
        """Enhance description with advanced technical details."""

        enhanced = base_description

        if tactic.name == "induction":
            enhanced += " (utilizing the induction principle of the inductive type)"
        elif tactic.name == "simp":
            enhanced += " (applying the simp normal form and congruence closure)"
        elif tactic.name == "rw":
            enhanced += " (performing definitional equality and rewriting modulo definitional equality)"

        return enhanced

    def _generate_generic_educational_steps(
        self,
        theorem: SemanticTheoremInfo,
        target_level: str,
        edu_profile: dict[str, any],
    ) -> list[ProofStep]:
        """Generate generic educational steps when specific tactics aren't available."""

        steps = []

        # Step 1: Setup and context
        steps.append(
            ProofStep(
                step_number=1,
                description="Establish the proof context and understand what we need to show",
                tactics=["setup"],
                mathematical_content="Initial proof state and goal",
                intuition=self._get_setup_intuition(target_level, edu_profile),
            )
        )

        # Step 2: Main reasoning
        main_intuition = self._get_main_reasoning_intuition(target_level, edu_profile)
        steps.append(
            ProofStep(
                step_number=2,
                description="Apply the main mathematical reasoning",
                tactics=["main_step"],
                mathematical_content="Core logical progression",
                intuition=main_intuition,
            )
        )

        # Step 3: Conclusion (if complex enough)
        if edu_profile.get("complexity", 0) > 2:
            steps.append(
                ProofStep(
                    step_number=3,
                    description="Complete the proof and verify our result",
                    tactics=["conclude"],
                    mathematical_content="Final verification",
                    intuition=self._get_conclusion_intuition(target_level, edu_profile),
                )
            )

        return steps

    def _get_setup_intuition(
        self, target_level: str, edu_profile: dict[str, any]
    ) -> str:
        """Generate setup intuition based on level and complexity."""

        if target_level == EducationalLevel.BEGINNER:
            return "Before we start proving anything, we need to understand exactly what we're trying to show and what tools we have available."
        elif target_level == EducationalLevel.INTERMEDIATE:
            return "We begin by establishing our assumptions and clearly stating our goal, ensuring we understand the mathematical structures involved."
        else:
            return "We initialize the proof state, establish the hypothesis context, and formalize the goal statement within the appropriate logical framework."

    def _get_main_reasoning_intuition(
        self, target_level: str, edu_profile: dict[str, any]
    ) -> str:
        """Generate main reasoning intuition."""

        method = edu_profile.get("proof_method", "unknown")

        if target_level == EducationalLevel.BEGINNER:
            if method == "induction":
                return "We use mathematical induction - like dominoes falling, we show the first case works, then that each case leads to the next."
            elif method == "simplification":
                return "We simplify both sides of the equation using mathematical rules until we can see they're the same."
            else:
                return "We apply mathematical reasoning step by step to show why our statement must be true."
        elif target_level == EducationalLevel.INTERMEDIATE:
            if method == "induction":
                return "We apply the principle of mathematical induction, proving the base case and the inductive step."
            elif method == "case_analysis":
                return "We perform case analysis, systematically considering all possible scenarios."
            else:
                return "We apply the appropriate mathematical techniques based on the structure of our goal."
        else:
            return "We employ the relevant proof-theoretic techniques, leveraging the logical structure of the statement and available hypotheses."

    def _get_conclusion_intuition(
        self, target_level: str, edu_profile: dict[str, any]
    ) -> str:
        """Generate conclusion intuition."""

        if target_level == EducationalLevel.BEGINNER:
            return "We verify that our reasoning is complete and that we've proven exactly what we set out to prove."
        elif target_level == EducationalLevel.INTERMEDIATE:
            return "We confirm that our proof is sound and that we've satisfied all the requirements of the theorem statement."
        else:
            return "We verify the logical validity of our derivation and confirm that the proof term type-checks against the goal type."

    def _create_generic_step(self, step_number: int, target_level: str) -> ProofStep:
        """Create a generic proof step when no specific information is available."""

        return ProofStep(
            step_number=step_number,
            description=f"Step {step_number}: Apply mathematical reasoning",
            tactics=["unknown"],
            mathematical_content="Mathematical progress",
            intuition="This step advances the proof using logical principles.",
        )

    def _generate_educational_conclusion(
        self,
        theorem: SemanticTheoremInfo,
        target_level: str,
        edu_profile: dict[str, any],
    ) -> str:
        """Generate educational conclusion with learning insights."""

        base_conclusion = f"This completes our proof of {theorem.name}. "

        if target_level == EducationalLevel.BEGINNER:
            return self._generate_beginner_conclusion(base_conclusion, edu_profile)
        elif target_level == EducationalLevel.INTERMEDIATE:
            return self._generate_intermediate_conclusion(base_conclusion, edu_profile)
        else:
            return self._generate_advanced_conclusion(
                base_conclusion, edu_profile, theorem
            )

    def _generate_beginner_conclusion(
        self, base: str, edu_profile: dict[str, any]
    ) -> str:
        """Generate beginner-friendly conclusion with learning takeaways."""

        conclusion = base

        # Add learning insights
        method = edu_profile.get("proof_method", "unknown")
        if method == "induction":
            conclusion += "This proof demonstrates the power of mathematical induction - a fundamental technique for proving statements about all natural numbers. "
        elif method == "simplification":
            conclusion += "This proof shows how mathematical rules can automatically simplify complex expressions. "
        elif method == "case_analysis":
            conclusion += "This proof illustrates how breaking a problem into cases can make complex proofs manageable. "

        # Add encouragement
        complexity = edu_profile.get("complexity", 0)
        if complexity < 3:
            conclusion += "Understanding proofs like this builds the foundation for more advanced mathematics."
        else:
            conclusion += "While this proof was challenging, working through it step-by-step helps develop mathematical reasoning skills."

        return conclusion

    def _generate_intermediate_conclusion(
        self, base: str, edu_profile: dict[str, any]
    ) -> str:
        """Generate intermediate-level conclusion with mathematical connections."""

        conclusion = base

        # Add mathematical significance
        method = edu_profile.get("proof_method", "unknown")
        method_context = self.proof_method_explanations.get(method, {}).get(
            "significance", ""
        )
        if method_context:
            conclusion += method_context + " "

        # Add complexity insights
        complexity = edu_profile.get("complexity", 0)
        if complexity > 4:
            conclusion += "The sophisticated proof techniques used here appear frequently in advanced mathematics. "

        conclusion += "Results like this often serve as building blocks for more complex theorems."
        return conclusion

    def _generate_advanced_conclusion(
        self, base: str, edu_profile: dict[str, any], theorem: SemanticTheoremInfo
    ) -> str:
        """Generate advanced conclusion with formal insights."""

        conclusion = base

        # Add formal analysis
        if theorem.semantic_dependencies:
            conclusion += f"This result relies on {len(theorem.semantic_dependencies)} auxiliary lemmas, indicating its integration within the formal development. "

        # Add proof-theoretic insights
        if edu_profile.get("complexity", 0) > 5:
            conclusion += "The proof complexity suggests non-trivial interactions between the underlying mathematical structures. "

        # Add computational content if applicable
        if edu_profile.get("is_computational", False):
            conclusion += "This theorem has computational content and may be useful for verified computation. "

        return conclusion

    def _determine_educational_difficulty(
        self, theorem: SemanticTheoremInfo, target_level: str
    ) -> str:
        """Determine educational difficulty based on semantic analysis and target level."""

        # Base difficulty from complexity score
        complexity = theorem.complexity_score

        if target_level == EducationalLevel.BEGINNER:
            # For beginners, lower the apparent difficulty
            if complexity < 2:
                return "beginner"
            elif complexity < 4:
                return "intermediate"
            else:
                return "advanced"
        elif target_level == EducationalLevel.INTERMEDIATE:
            # Standard difficulty mapping
            if complexity < 3:
                return "beginner"
            elif complexity < 6:
                return "intermediate"
            else:
                return "advanced"
        else:  # Advanced
            # For advanced users, be more nuanced
            if complexity < 4:
                return "beginner"
            elif complexity < 7:
                return "intermediate"
            else:
                return "advanced"

    def _identify_educational_areas(self, theorem: SemanticTheoremInfo) -> list[str]:
        """Identify mathematical areas for educational context."""

        areas = set(theorem.mathematical_entities)

        # Add areas based on proof methods
        method = theorem.proof_method
        if method == "induction":
            areas.add("Mathematical Induction")
        elif method == "case_analysis":
            areas.add("Logical Reasoning")
        elif method == "rewriting":
            areas.add("Algebraic Manipulation")
        elif method == "simplification":
            areas.add("Computational Mathematics")

        # Add areas based on entities
        entities = theorem.mathematical_entities
        if any(entity in ["Nat", "Int"] for entity in entities):
            areas.add("Number Theory")
        if any(entity in ["Real", "Complex"] for entity in entities):
            areas.add("Analysis")
        if any(entity in ["Set", "List"] for entity in entities):
            areas.add("Discrete Mathematics")

        return list(areas) if areas else ["Mathematics"]

    def _generate_educational_prerequisites(
        self, theorem: SemanticTheoremInfo, target_level: str
    ) -> list[str]:
        """Generate educational prerequisites based on analysis and level."""

        prereqs = set()

        # Add based on proof method
        method = theorem.proof_method
        if method == "induction":
            if target_level == EducationalLevel.BEGINNER:
                prereqs.add("Understanding of natural numbers")
                prereqs.add("Basic logical reasoning")
            else:
                prereqs.add("Mathematical induction principle")
                prereqs.add("Recursive definitions")

        # Add based on mathematical entities
        entities = theorem.mathematical_entities
        if any(entity in ["Real", "Complex"] for entity in entities):
            prereqs.add("Real number properties")
        if any(entity in ["Set"] for entity in entities):
            prereqs.add("Basic set theory")
        if "Group" in entities or "Ring" in entities:
            prereqs.add("Abstract algebra basics")

        # Add based on complexity
        if theorem.complexity_score > 5:
            prereqs.add("Mathematical maturity")
            if target_level != EducationalLevel.ADVANCED:
                prereqs.add("Comfort with formal proofs")

        return list(prereqs) if prereqs else ["Basic mathematical reasoning"]

    def _init_proof_method_explanations(self) -> dict[str, dict[str, str]]:
        """Initialize explanations for different proof methods."""

        return {
            "induction": {
                "beginner": "This proof uses mathematical induction, building up from simple cases.",
                "intermediate": "The proof employs mathematical induction over the natural number structure.",
                "advanced": "This proof utilizes structural induction over the inductive type.",
                "significance": "Induction is fundamental to reasoning about recursive structures.",
            },
            "case_analysis": {
                "beginner": "This proof considers different cases separately.",
                "intermediate": "The proof proceeds by exhaustive case analysis.",
                "advanced": "The proof employs pattern matching and case distinction.",
                "significance": "Case analysis is essential for handling complex logical structures.",
            },
            "simplification": {
                "beginner": "This proof simplifies expressions using mathematical rules.",
                "intermediate": "The proof relies on automated simplification and normalization.",
                "advanced": "The proof utilizes the simp normal form and congruence closure.",
                "significance": "Simplification demonstrates the power of computational proof techniques.",
            },
            "rewriting": {
                "beginner": "This proof replaces equals with equals step by step.",
                "intermediate": "The proof uses equational reasoning and substitution.",
                "advanced": "The proof employs term rewriting modulo definitional equality.",
                "significance": "Rewriting is fundamental to equality-based reasoning.",
            },
        }

    def _init_tactic_explanations(self) -> dict[str, dict[str, dict[str, str]]]:
        """Initialize detailed tactic explanations by level."""

        return {
            "simp": {
                "beginner": {
                    "description": "Simplify using mathematical rules",
                    "intuition": "This automatically applies known mathematical facts to simplify the expression.",
                },
                "intermediate": {
                    "description": "Apply simplification rules and normalization",
                    "intuition": "The simp tactic applies a database of simplification lemmas to normalize the goal.",
                },
                "advanced": {
                    "description": "Invoke the simplifier with congruence closure",
                    "intuition": "This employs the simp normal form, applying simp lemmas with congruence closure and automatic unfolding.",
                },
            },
            "rw": {
                "beginner": {
                    "description": "Rewrite using an equality",
                    "intuition": "We replace the left side of an equation with the right side (or vice versa).",
                },
                "intermediate": {
                    "description": "Apply rewriting with the given lemma",
                    "intuition": "This performs directed rewriting using the specified equality or equivalence.",
                },
                "advanced": {
                    "description": "Execute term rewriting modulo definitional equality",
                    "intuition": "This performs higher-order pattern matching and rewriting, handling β-reduction and definitional equality.",
                },
            },
            "induction": {
                "beginner": {
                    "description": "Use mathematical induction",
                    "intuition": "We prove the statement for all cases by showing it works for the base case and that each case implies the next.",
                },
                "intermediate": {
                    "description": "Apply the induction principle",
                    "intuition": "This generates subgoals for the base case and inductive step, following the structure of the inductive type.",
                },
                "advanced": {
                    "description": "Invoke structural induction with the elimination principle",
                    "intuition": "This applies the eliminator for the inductive type, generating goals corresponding to each constructor.",
                },
            },
        }

    def _init_mathematical_contexts(self) -> dict[str, str]:
        """Initialize mathematical context explanations."""

        return {
            "arithmetic": "This involves basic arithmetic operations and their fundamental properties.",
            "algebra": "This concerns algebraic structures and their morphisms.",
            "analysis": "This relates to analytical properties such as limits and continuity.",
            "topology": "This involves topological spaces and continuous mappings.",
            "logic": "This concerns logical relationships and propositional reasoning.",
            "set_theory": "This involves operations and relationships within set theory.",
            "type_theory": "This relates to type-theoretic constructions and dependent types.",
        }
