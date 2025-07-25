"""Educational content generator for doc-gen4 integration."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from typing import Any

from ..generator.progressive_generator import ProgressiveGenerator, ProgressiveSketch
from ..generator.semantic_generator import EducationalLevel, SemanticGenerator
from ..parser.models import TheoremInfo


@dataclass
class EducationalMetadata:
    """Metadata about educational content generation."""

    difficulty_level: str
    concepts: list[str]
    prerequisites: list[str]
    learning_objectives: list[str]
    estimated_time_minutes: int
    visualization_suggestions: list[str]


@dataclass
class InteractiveElement:
    """Interactive element for educational content."""

    type: str  # "expandable", "visualization", "example", "exercise"
    title: str
    content: str
    level: str = "all"  # "beginner", "intermediate", "advanced", "all"


class EducationalContentGenerator:
    """Generates educational content for doc-gen4 integration."""

    def __init__(self):
        """Initialize the educational content generator."""
        self.progressive_generator = ProgressiveGenerator()
        self.semantic_generator = SemanticGenerator()

    def generate_content_from_docgen(
        self,
        name: str,
        statement: str,
        proof: str = "",
        docstring: str | None = None,
        context: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        """Generate educational content from doc-gen4 data.

        Args:
            name: Name of the theorem/lemma
            statement: Type/statement from doc-gen4
            proof: Proof term or tactic proof
            docstring: Optional documentation string
            context: Additional context from doc-gen4

        Returns:
            Educational content dictionary
        """
        # Create theorem info from doc-gen4 data
        theorem_info = self._create_theorem_info(
            name=name,
            statement=statement,
            proof=proof,
            docstring=docstring,
            context=context,
        )

        # Generate progressive explanations
        progressive_content = (
            self.progressive_generator.generate_progressive_explanation(theorem_info)
        )

        # Generate metadata
        metadata = self._generate_metadata(theorem_info, progressive_content)

        # Create interactive elements
        interactive_elements = self._create_interactive_elements(
            theorem_info, progressive_content
        )

        return {
            "progressive_explanations": {
                "beginner": progressive_content.levels.get("beginner", {}),
                "intermediate": progressive_content.levels.get("intermediate", {}),
                "advanced": progressive_content.levels.get("advanced", {}),
            },
            "learning_pathway": [
                step.to_dict() for step in progressive_content.learning_pathway
            ],
            "key_concepts": [
                concept.to_dict() for concept in progressive_content.key_concepts
            ],
            "metadata": metadata.__dict__,
            "interactive_elements": [
                element.__dict__ for element in interactive_elements
            ],
            "generated_at": datetime.now().isoformat(),
        }

    def _create_theorem_info(
        self,
        name: str,
        statement: str,
        proof: str = "",
        docstring: str | None = None,
        context: dict[str, Any] | None = None,
    ) -> TheoremInfo:
        """Create TheoremInfo from doc-gen4 data.

        Args:
            name: Name of the theorem
            statement: Statement/type
            proof: Proof term
            docstring: Documentation
            context: Additional context

        Returns:
            TheoremInfo object
        """
        return TheoremInfo(
            name=name,
            statement=statement,
            proof=proof,
            docstring=docstring,
            dependencies=self._extract_dependencies(statement, proof),
            line_number=None,
            namespace=self._extract_namespace(name),
            visibility="public",
            tactics=self._extract_tactics(proof),
            is_axiom=False,
            file_path=None,
            start_line=None,
            end_line=None,
        )

    def _generate_metadata(
        self, theorem_info: TheoremInfo, progressive_content: ProgressiveSketch
    ) -> EducationalMetadata:
        """Generate educational metadata.

        Args:
            theorem_info: Theorem information
            progressive_content: Progressive explanations

        Returns:
            Educational metadata
        """
        # Extract key concepts
        concepts = [concept.concept for concept in progressive_content.key_concepts]

        # Estimate difficulty based on statement complexity
        difficulty_level = self._estimate_difficulty(theorem_info.statement)

        # Extract prerequisites
        prerequisites = [
            step.title for step in progressive_content.learning_pathway[:3]
        ]

        # Generate learning objectives
        learning_objectives = [
            f"Understand the statement of {theorem_info.name}",
            f"Grasp the key concepts: {', '.join(concepts[:3])}",
            "Follow the proof strategy and main steps",
        ]

        # Estimate time based on complexity
        estimated_time = self._estimate_learning_time(theorem_info, progressive_content)

        # Generate visualization suggestions
        visualization_suggestions = self._generate_visualization_suggestions(
            theorem_info, progressive_content
        )

        return EducationalMetadata(
            difficulty_level=difficulty_level,
            concepts=concepts,
            prerequisites=prerequisites,
            learning_objectives=learning_objectives,
            estimated_time_minutes=estimated_time,
            visualization_suggestions=visualization_suggestions,
        )

    def _create_interactive_elements(
        self, theorem_info: TheoremInfo, progressive_content: ProgressiveSketch
    ) -> list[InteractiveElement]:
        """Create interactive elements for the theorem.

        Args:
            theorem_info: Theorem information
            progressive_content: Progressive explanations

        Returns:
            List of interactive elements
        """
        elements = []

        # Expandable proof overview
        elements.append(
            InteractiveElement(
                type="expandable",
                title="Proof Overview",
                content=(
                    getattr(
                        progressive_content.levels.get("intermediate"),
                        "introduction",
                        "Intermediate level overview",
                    )
                    if progressive_content.levels.get("intermediate")
                    else "Intermediate level overview"
                ),
                level="intermediate",
            )
        )

        # Key concepts exploration
        for concept in progressive_content.key_concepts[:3]:
            elements.append(
                InteractiveElement(
                    type="expandable",
                    title=f"Concept: {concept.concept}",
                    content=concept.informal_description,
                    level="beginner",
                )
            )

        # Learning pathway steps
        for i, step in enumerate(progressive_content.learning_pathway[:3]):
            elements.append(
                InteractiveElement(
                    type="example",
                    title=f"Step {i + 1}: {step.title}",
                    content=step.explanation,
                    level="intermediate",
                )
            )

        # Visualization suggestions
        if "geometric" in theorem_info.statement.lower():
            elements.append(
                InteractiveElement(
                    type="visualization",
                    title="Geometric Visualization",
                    content="This theorem has geometric interpretations that can be visualized.",
                    level="beginner",
                )
            )

        return elements

    def _extract_dependencies(self, statement: str, proof: str) -> list[str]:
        """Extract dependencies from statement and proof.

        Args:
            statement: Theorem statement
            proof: Proof term

        Returns:
            List of dependencies
        """
        # Simple dependency extraction (could be enhanced with LSP)
        dependencies = []

        # Common theorem dependencies
        common_deps = ["Nat", "Int", "Real", "List", "Set", "Function"]
        for dep in common_deps:
            if dep in statement or dep in proof:
                dependencies.append(dep)

        return dependencies

    def _extract_namespace(self, name: str) -> str | None:
        """Extract namespace from theorem name.

        Args:
            name: Theorem name

        Returns:
            Namespace or None
        """
        if "." in name:
            return name.rsplit(".", 1)[0]
        return None

    def _extract_tactics(self, proof: str) -> list[str]:
        """Extract tactics from proof.

        Args:
            proof: Proof term or tactic proof

        Returns:
            List of tactics used
        """
        # Simple tactic extraction
        tactics = []
        common_tactics = [
            "rw",
            "simp",
            "apply",
            "intro",
            "cases",
            "induction",
            "exact",
            "by",
        ]

        for tactic in common_tactics:
            if tactic in proof:
                tactics.append(tactic)

        return tactics

    def _estimate_difficulty(self, statement: str) -> str:
        """Estimate difficulty level based on statement complexity.

        Args:
            statement: Theorem statement

        Returns:
            Difficulty level
        """
        # Simple heuristic based on statement complexity
        if len(statement) < 50:
            return EducationalLevel.BEGINNER
        elif len(statement) < 100:
            return EducationalLevel.INTERMEDIATE
        else:
            return EducationalLevel.ADVANCED

    def _estimate_learning_time(
        self, theorem_info: TheoremInfo, progressive_content: ProgressiveSketch
    ) -> int:
        """Estimate learning time in minutes.

        Args:
            theorem_info: Theorem information
            progressive_content: Progressive content

        Returns:
            Estimated time in minutes
        """
        # Base time
        base_time = 5

        # Add time for concept complexity
        concept_time = len(progressive_content.key_concepts) * 2

        # Add time for proof complexity
        proof_time = len(progressive_content.learning_pathway) * 3

        # Add time for statement complexity
        statement_time = len(theorem_info.statement) // 20

        return base_time + concept_time + proof_time + statement_time

    def _generate_visualization_suggestions(
        self, theorem_info: TheoremInfo, progressive_content: ProgressiveSketch
    ) -> list[str]:
        """Generate visualization suggestions.

        Args:
            theorem_info: Theorem information
            progressive_content: Progressive content

        Returns:
            List of visualization suggestions
        """
        suggestions = []

        # Geometric visualizations
        if any(
            word in theorem_info.statement.lower()
            for word in ["triangle", "circle", "point", "line"]
        ):
            suggestions.append("Geometric diagram showing the mathematical objects")

        # Algebraic visualizations
        if any(
            word in theorem_info.statement.lower()
            for word in ["function", "equation", "graph"]
        ):
            suggestions.append("Graph or plot showing the mathematical relationship")

        # Set theory visualizations
        if any(
            word in theorem_info.statement.lower()
            for word in ["set", "subset", "union", "intersection"]
        ):
            suggestions.append("Venn diagram or set visualization")

        # Number theory visualizations
        if any(
            word in theorem_info.statement.lower()
            for word in ["prime", "divisor", "factor"]
        ):
            suggestions.append("Number line or factorization diagram")

        # Default visualization
        if not suggestions:
            suggestions.append("Conceptual diagram showing the theorem structure")

        return suggestions
