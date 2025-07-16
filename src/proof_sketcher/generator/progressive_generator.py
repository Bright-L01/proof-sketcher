"""Progressive explanation generator for multi-level educational content.

This generator creates comprehensive educational materials that guide learners
from intuitive understanding to formal mathematical reasoning. It produces
multiple explanation levels simultaneously and provides learning pathways
that bridge the gap between informal and formal mathematics.

Key Features:
- Multi-level explanations (novice → intermediate → advanced)
- Learning pathway generation
- Concept prerequisite mapping
- Interactive exploration suggestions
- Mathematical intuition development
- Formal reasoning bridge-building

Educational Approach:
- Start with concrete examples and intuition
- Gradually introduce mathematical formalism
- Connect to broader mathematical contexts
- Encourage active learning and exploration
- Provide multiple perspectives on the same concept

Usage:
    >>> generator = ProgressiveGenerator()
    >>> theorem = SemanticTheoremInfo(...)
    >>> progressive_sketch = generator.generate_progressive_explanation(theorem)
    >>> 
    >>> # Access different levels
    >>> novice_explanation = progressive_sketch.levels["novice"]
    >>> advanced_explanation = progressive_sketch.levels["advanced"]
    >>> 
    >>> # Get learning pathway
    >>> pathway = progressive_sketch.learning_pathway
"""

import logging
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Union

from ..parser.lsp_client import SemanticTheoremInfo
from ..parser.models import TheoremInfo
from .models import ProofSketch, ProofStep
from .semantic_generator import SemanticGenerator, EducationalLevel


@dataclass
class LearningStep:
    """A single step in a learning pathway."""
    
    title: str
    description: str
    level: str
    concepts: List[str] = field(default_factory=list)
    examples: List[str] = field(default_factory=list)
    exercises: List[str] = field(default_factory=list)
    resources: List[str] = field(default_factory=list)


@dataclass
class ConceptExplanation:
    """Explanation of a mathematical concept at different levels."""
    
    concept: str
    informal_description: str
    formal_definition: str
    examples: List[str] = field(default_factory=list)
    common_misconceptions: List[str] = field(default_factory=list)
    related_concepts: List[str] = field(default_factory=list)


@dataclass
class ProgressiveSketch:
    """A multi-level educational explanation of a theorem."""
    
    theorem_name: str
    theorem_statement: str
    
    # Multi-level explanations
    levels: Dict[str, ProofSketch] = field(default_factory=dict)
    
    # Educational enhancements
    learning_pathway: List[LearningStep] = field(default_factory=list)
    key_concepts: List[ConceptExplanation] = field(default_factory=list)
    intuitive_examples: List[str] = field(default_factory=list)
    formal_connections: List[str] = field(default_factory=list)
    
    # Interactive elements
    exploration_suggestions: List[str] = field(default_factory=list)
    visualization_ideas: List[str] = field(default_factory=list)
    extension_problems: List[str] = field(default_factory=list)
    
    # Metadata
    estimated_study_time: Dict[str, int] = field(default_factory=dict)  # minutes per level
    difficulty_progression: List[float] = field(default_factory=list)
    mathematical_maturity_required: Dict[str, str] = field(default_factory=dict)


class ProgressiveGenerator:
    """Generator for progressive multi-level educational content."""
    
    def __init__(self):
        """Initialize the progressive generator."""
        self.logger = logging.getLogger(__name__)
        self.semantic_generator = SemanticGenerator()
        
        # Educational content databases
        self.concept_database = self._init_concept_database()
        self.example_database = self._init_example_database()
        self.pathway_templates = self._init_pathway_templates()
        
    def generate_progressive_explanation(
        self, theorem: Union[SemanticTheoremInfo, TheoremInfo]
    ) -> ProgressiveSketch:
        """Generate a comprehensive progressive explanation.
        
        Args:
            theorem: Theorem to explain progressively
            
        Returns:
            Complete progressive explanation with multiple levels
        """
        self.logger.info(f"Generating progressive explanation for {theorem.name}")
        
        # Generate explanations for all levels
        levels = {}
        difficulty_scores = []
        
        for level in [EducationalLevel.BEGINNER, EducationalLevel.INTERMEDIATE, EducationalLevel.ADVANCED]:
            sketch = self.semantic_generator.generate_educational_sketch(theorem, level)
            levels[level] = sketch
            
            # Track difficulty progression
            if isinstance(theorem, SemanticTheoremInfo):
                difficulty_scores.append(theorem.complexity_score)
            else:
                # Estimate difficulty for basic theorems
                difficulty_scores.append(self._estimate_basic_difficulty(theorem, level))
        
        # Extract key concepts
        key_concepts = self._extract_key_concepts(theorem, levels)
        
        # Generate learning pathway
        learning_pathway = self._generate_learning_pathway(theorem, levels, key_concepts)
        
        # Generate intuitive examples
        examples = self._generate_intuitive_examples(theorem, key_concepts)
        
        # Generate exploration suggestions
        explorations = self._generate_exploration_suggestions(theorem, levels)
        
        # Generate formal connections
        connections = self._generate_formal_connections(theorem, levels)
        
        # Estimate study times
        study_times = self._estimate_study_times(theorem, levels)
        
        # Generate extension problems
        extensions = self._generate_extension_problems(theorem, levels)
        
        return ProgressiveSketch(
            theorem_name=theorem.name,
            theorem_statement=theorem.statement or "",
            levels=levels,
            learning_pathway=learning_pathway,
            key_concepts=key_concepts,
            intuitive_examples=examples,
            formal_connections=connections,
            exploration_suggestions=explorations,
            visualization_ideas=self._generate_visualization_ideas(theorem),
            extension_problems=extensions,
            estimated_study_time=study_times,
            difficulty_progression=difficulty_scores,
            mathematical_maturity_required=self._assess_maturity_requirements(theorem, levels),
        )
        
    def _extract_key_concepts(
        self,
        theorem: Union[SemanticTheoremInfo, TheoremInfo],
        levels: Dict[str, ProofSketch]
    ) -> List[ConceptExplanation]:
        """Extract and explain key mathematical concepts."""
        
        concepts = []
        
        # Extract concepts from theorem content
        statement = theorem.statement or ""
        proof = theorem.proof or ""
        content = f"{statement} {proof}".lower()
        
        # Check for key mathematical concepts
        if any(word in content for word in ["induction", "inductive"]):
            concepts.append(self._explain_induction_concept())
            
        if any(word in content for word in ["=", "equal"]):
            concepts.append(self._explain_equality_concept())
            
        if any(word in content for word in ["∀", "forall", "all"]):
            concepts.append(self._explain_universal_quantification())
            
        if any(word in content for word in ["∃", "exists", "some"]):
            concepts.append(self._explain_existential_quantification())
            
        if any(word in content for word in ["→", "->", "implies"]):
            concepts.append(self._explain_implication_concept())
            
        # Add type-specific concepts
        if isinstance(theorem, SemanticTheoremInfo):
            for entity in theorem.mathematical_entities:
                if entity.lower() in ["nat", "natural"]:
                    concepts.append(self._explain_natural_numbers())
                elif entity.lower() in ["real"]:
                    concepts.append(self._explain_real_numbers())
                elif entity.lower() in ["set"]:
                    concepts.append(self._explain_sets())
                    
        return concepts
        
    def _generate_learning_pathway(
        self,
        theorem: Union[SemanticTheoremInfo, TheoremInfo],
        levels: Dict[str, ProofSketch],
        concepts: List[ConceptExplanation]
    ) -> List[LearningStep]:
        """Generate a structured learning pathway."""
        
        pathway = []
        
        # Step 1: Build intuition
        pathway.append(LearningStep(
            title="Build Intuition",
            description="Develop an intuitive understanding of what the theorem means",
            level="beginner",
            concepts=[c.concept for c in concepts],
            examples=self._get_intuitive_examples(theorem),
            exercises=self._get_intuition_exercises(theorem),
            resources=["Visual aids", "Concrete examples", "Analogies"]
        ))
        
        # Step 2: Understand the formal statement
        pathway.append(LearningStep(
            title="Understand the Formal Statement", 
            description="Learn to read and interpret the mathematical notation",
            level="intermediate",
            concepts=["Mathematical notation", "Logical structure"],
            examples=self._get_notation_examples(theorem),
            exercises=self._get_notation_exercises(theorem),
            resources=["Symbol glossary", "Statement breakdown", "Logical analysis"]
        ))
        
        # Step 3: Follow the proof strategy
        proof_method = getattr(theorem, 'proof_method', 'unknown')
        pathway.append(LearningStep(
            title="Follow the Proof Strategy",
            description=f"Understand the {proof_method} approach used in the proof",
            level="intermediate",
            concepts=[f"{proof_method.title()} method", "Proof structure"],
            examples=self._get_proof_strategy_examples(theorem, proof_method),
            exercises=self._get_proof_exercises(theorem),
            resources=["Step-by-step walkthrough", "Proof patterns", "Common techniques"]
        ))
        
        # Step 4: Master the formal details
        pathway.append(LearningStep(
            title="Master the Formal Details",
            description="Work through the rigorous mathematical proof",
            level="advanced",
            concepts=["Formal logic", "Rigorous reasoning"],
            examples=self._get_formal_examples(theorem),
            exercises=self._get_formal_exercises(theorem),
            resources=["Formal proof systems", "Logic references", "Advanced texts"]
        ))
        
        # Step 5: Explore connections and extensions
        pathway.append(LearningStep(
            title="Explore Connections",
            description="See how this theorem connects to broader mathematics",
            level="advanced",
            concepts=["Mathematical connections", "Applications"],
            examples=self._get_connection_examples(theorem),
            exercises=self._get_extension_exercises(theorem),
            resources=["Related theorems", "Applications", "Research directions"]
        ))
        
        return pathway
        
    def _generate_intuitive_examples(
        self,
        theorem: Union[SemanticTheoremInfo, TheoremInfo],
        concepts: List[ConceptExplanation]
    ) -> List[str]:
        """Generate concrete, intuitive examples."""
        
        examples = []
        statement = theorem.statement or ""
        
        # Generate examples based on theorem type
        if "+" in statement and any(word in statement.lower() for word in ["nat", "number"]):
            examples.extend([
                "Try with small numbers: 3 + 0 = 3, 7 + 0 = 7",
                "Think about adding nothing to a pile of objects",
                "Consider counting: if you have 5 items and add 0 more, you still have 5"
            ])
            
        if "=" in statement:
            examples.extend([
                "Like saying 'this pile has the same number as that pile'",
                "Two different ways of writing the same thing",
                "Mathematical equations are like balanced scales"
            ])
            
        if "induction" in (theorem.proof or "").lower():
            examples.extend([
                "Like dominoes falling: prove the first falls, and each falling domino knocks over the next",
                "Like climbing a ladder: show you can reach the first rung, and from any rung you can reach the next",
                "Like a mathematical domino effect"
            ])
            
        return examples
        
    def _generate_exploration_suggestions(
        self,
        theorem: Union[SemanticTheoremInfo, TheoremInfo],
        levels: Dict[str, ProofSketch]
    ) -> List[str]:
        """Generate suggestions for interactive exploration."""
        
        suggestions = []
        
        # Basic explorations
        suggestions.extend([
            f"Try proving {theorem.name} yourself before reading the solution",
            "Look up the definitions of all terms used in the statement",
            "Find other theorems that use similar proof techniques"
        ])
        
        # Specific to theorem content
        statement = theorem.statement or ""
        proof = theorem.proof or ""
        
        if "+" in statement:
            suggestions.append("Experiment with different numbers to see the pattern")
            suggestions.append("Try drawing pictures or using physical objects")
            
        if "induction" in proof.lower():
            suggestions.append("Practice the induction pattern with simpler statements")
            suggestions.append("Identify the base case and inductive step clearly")
            
        if "=" in statement:
            suggestions.append("Try to come up with counterexamples (they won't work, but it's instructive)")
            suggestions.append("Think about what makes equality relationships special")
            
        # Interactive elements
        suggestions.extend([
            "Create your own examples using the same pattern",
            "Explain the theorem to someone else in your own words",
            "Write down any questions that come up while studying",
            "Connect this to other mathematics you know"
        ])
        
        return suggestions
        
    def _generate_formal_connections(
        self,
        theorem: Union[SemanticTheoremInfo, TheoremInfo],
        levels: Dict[str, ProofSketch]
    ) -> List[str]:
        """Generate connections to formal mathematical contexts."""
        
        connections = []
        
        # Analyze mathematical context
        if isinstance(theorem, SemanticTheoremInfo):
            entities = theorem.mathematical_entities
            
            if any(entity in ["Nat", "Int"] for entity in entities):
                connections.extend([
                    "This theorem is part of the foundation of number theory",
                    "It contributes to our understanding of arithmetic operations",
                    "Similar patterns appear in other algebraic structures"
                ])
                
            if theorem.proof_method == "induction":
                connections.extend([
                    "Induction is fundamental to reasoning about recursive structures",
                    "This pattern appears throughout mathematics and computer science",
                    "The induction principle is derived from the structure of natural numbers"
                ])
                
        # General connections
        connections.extend([
            "This type of theorem appears in foundational mathematics",
            "Understanding proofs like this builds mathematical maturity",
            "The techniques used here apply to many other problems"
        ])
        
        return connections
        
    def _estimate_study_times(
        self,
        theorem: Union[SemanticTheoremInfo, TheoremInfo],
        levels: Dict[str, ProofSketch]
    ) -> Dict[str, int]:
        """Estimate study time needed for each level (in minutes)."""
        
        base_time = 15  # Base time in minutes
        
        # Adjust based on complexity
        complexity_factor = 1.0
        if isinstance(theorem, SemanticTheoremInfo):
            complexity_factor = min(theorem.complexity_score / 3.0, 3.0)  # Cap at 3x
        else:
            proof_length = len(theorem.proof or "")
            complexity_factor = min(proof_length / 50.0, 3.0)
            
        return {
            EducationalLevel.BEGINNER: int(base_time * complexity_factor),
            EducationalLevel.INTERMEDIATE: int(base_time * complexity_factor * 1.5),
            EducationalLevel.ADVANCED: int(base_time * complexity_factor * 2.0),
        }
        
    def _generate_extension_problems(
        self,
        theorem: Union[SemanticTheoremInfo, TheoremInfo],
        levels: Dict[str, ProofSketch]
    ) -> List[str]:
        """Generate extension problems for further learning."""
        
        problems = []
        statement = theorem.statement or ""
        
        # Generate based on theorem content
        if "+" in statement and "0" in statement:
            problems.extend([
                "What about n + 1? Can you prove n + 1 = 1 + n?",
                "Does this work for other operations like multiplication?",
                "What happens with negative numbers?"
            ])
            
        if "=" in statement:
            problems.extend([
                "Find three different ways to prove the same equality",
                "What properties make equality 'work' mathematically?",
                "How does this relate to the concept of mathematical functions?"
            ])
            
        # General extensions
        problems.extend([
            f"Try to generalize {theorem.name} to other mathematical structures",
            "Look for the dual or opposite version of this theorem",
            "Research the history and applications of this result"
        ])
        
        return problems
        
    def _assess_maturity_requirements(
        self,
        theorem: Union[SemanticTheoremInfo, TheoremInfo],
        levels: Dict[str, ProofSketch]
    ) -> Dict[str, str]:
        """Assess mathematical maturity required for each level."""
        
        requirements = {}
        
        # Analyze complexity
        complexity = 2.0  # Default
        if isinstance(theorem, SemanticTheoremInfo):
            complexity = theorem.complexity_score
        
        if complexity < 2:
            requirements[EducationalLevel.BEGINNER] = "Basic algebra and logical thinking"
            requirements[EducationalLevel.INTERMEDIATE] = "Comfort with mathematical notation"
            requirements[EducationalLevel.ADVANCED] = "Introduction to proofs"
        elif complexity < 4:
            requirements[EducationalLevel.BEGINNER] = "Pre-calculus mathematics"
            requirements[EducationalLevel.INTERMEDIATE] = "Introduction to proofs and logic"
            requirements[EducationalLevel.ADVANCED] = "Mathematical maturity and proof experience"
        else:
            requirements[EducationalLevel.BEGINNER] = "Calculus and mathematical maturity"
            requirements[EducationalLevel.INTERMEDIATE] = "Advanced undergraduate mathematics"
            requirements[EducationalLevel.ADVANCED] = "Graduate-level mathematical sophistication"
            
        return requirements
        
    def _generate_visualization_ideas(
        self, theorem: Union[SemanticTheoremInfo, TheoremInfo]
    ) -> List[str]:
        """Generate ideas for visualizing the theorem."""
        
        ideas = []
        statement = theorem.statement or ""
        
        if "+" in statement:
            ideas.extend([
                "Draw number lines showing addition",
                "Use physical objects or manipulatives",
                "Create bar charts or pictographs"
            ])
            
        if "=" in statement:
            ideas.extend([
                "Show both sides of the equation visually",
                "Use balance scales to represent equality",
                "Create side-by-side comparisons"
            ])
            
        if "induction" in (theorem.proof or "").lower():
            ideas.extend([
                "Animate the domino effect",
                "Show the ladder-climbing metaphor",
                "Visualize the base case and inductive step"
            ])
            
        # General visualization ideas
        ideas.extend([
            "Create step-by-step proof animations",
            "Use interactive tools to explore the concept",
            "Draw concept maps connecting related ideas"
        ])
        
        return ideas
        
    # Helper methods for generating specific educational content
    
    def _get_intuitive_examples(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get intuitive examples for building understanding."""
        return [
            "Work with small, concrete numbers first",
            "Use physical objects or drawings when possible",
            "Connect to everyday experiences with counting or measuring"
        ]
        
    def _get_notation_examples(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get examples for understanding notation."""
        return [
            "Break down each symbol and what it means",
            "Practice reading the statement aloud in English",
            "Compare to similar statements you already know"
        ]
        
    def _get_proof_strategy_examples(self, theorem: Union[SemanticTheoremInfo, TheoremInfo], method: str) -> List[str]:
        """Get examples for understanding proof strategies."""
        if method == "induction":
            return [
                "Practice identifying what needs to be proven in the base case",
                "Work through the inductive step with specific examples",
                "See how the pattern builds from simple to complex cases"
            ]
        elif method == "simplification":
            return [
                "Apply one simplification rule at a time",
                "Keep track of which rules you're using",
                "Practice recognizing when expressions are fully simplified"
            ]
        else:
            return [
                "Break the proof into smaller, manageable steps",
                "Identify the key insight or technique being used",
                "Practice the same technique on similar problems"
            ]
            
    def _get_formal_examples(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get examples for formal understanding."""
        return [
            "Work through every detail of the formal proof",
            "Verify each logical step independently",
            "Connect to the formal definition of each concept used"
        ]
        
    def _get_intuition_exercises(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get exercises for building intuition."""
        return [
            f"Explain {theorem.name} to a friend using only everyday language",
            "Find real-world situations where this pattern appears",
            "Create your own examples that illustrate the same principle"
        ]
        
    def _get_notation_exercises(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get exercises for mastering notation."""
        return [
            "Translate the statement into plain English",
            "Identify all the mathematical symbols and their meanings",
            "Write similar statements using the same notation patterns"
        ]
        
    def _get_proof_exercises(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get exercises for understanding proofs."""
        return [
            f"Try to prove {theorem.name} yourself before looking at the solution",
            "Identify the main steps and substeps in the given proof",
            "Practice the same proof technique on a simpler problem"
        ]
        
    def _get_formal_exercises(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get exercises for formal mastery."""
        return [
            "Write out every step of the proof in complete detail",
            "Verify that each step follows logically from the previous ones",
            "Research the formal foundations of the concepts used"
        ]
        
    def _get_connection_examples(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get examples of mathematical connections."""
        return [
            "Find other theorems that use similar techniques",
            "Look for applications in other areas of mathematics",
            "Research the historical development of these ideas"
        ]
        
    def _get_extension_exercises(self, theorem: Union[SemanticTheoremInfo, TheoremInfo]) -> List[str]:
        """Get exercises for extending understanding."""
        return [
            f"Try to generalize {theorem.name} to other mathematical contexts",
            "Look for counterexamples to similar-looking but false statements",
            "Research open problems related to this area of mathematics"
        ]
        
    def _estimate_basic_difficulty(self, theorem: TheoremInfo, level: str) -> float:
        """Estimate difficulty for basic theorems."""
        base_difficulty = 2.0
        proof_length = len(theorem.proof or "")
        
        # Adjust based on proof length and content
        if proof_length < 20:
            complexity = 1.0
        elif proof_length < 100:
            complexity = 2.0
        else:
            complexity = 3.0
            
        # Adjust for educational level
        level_multipliers = {
            EducationalLevel.BEGINNER: 0.8,
            EducationalLevel.INTERMEDIATE: 1.0,
            EducationalLevel.ADVANCED: 1.2,
        }
        
        return complexity * level_multipliers.get(level, 1.0)
        
    # Concept explanation methods
    
    def _explain_induction_concept(self) -> ConceptExplanation:
        """Explain mathematical induction."""
        return ConceptExplanation(
            concept="Mathematical Induction",
            informal_description="A proof technique like dominoes falling - prove it works for the first case, then show each case leads to the next.",
            formal_definition="A method of mathematical proof used to establish that a property P(n) holds for all natural numbers n, by proving P(0) and that P(k) implies P(k+1).",
            examples=["Proving formulas for sums", "Establishing properties of recursive definitions"],
            common_misconceptions=["Thinking you assume what you want to prove", "Forgetting the base case"],
            related_concepts=["Recursion", "Well-ordering principle", "Strong induction"]
        )
        
    def _explain_equality_concept(self) -> ConceptExplanation:
        """Explain mathematical equality."""
        return ConceptExplanation(
            concept="Mathematical Equality",
            informal_description="Two expressions that represent the same mathematical object or value.",
            formal_definition="A relation = such that a = b means a and b denote the same mathematical object, satisfying reflexivity, symmetry, and transitivity.",
            examples=["2 + 3 = 5", "x² - 1 = (x-1)(x+1)"],
            common_misconceptions=["Confusing equality with assignment", "Thinking = means 'calculate'"],
            related_concepts=["Equivalence relations", "Substitution", "Identity"]
        )
        
    def _explain_universal_quantification(self) -> ConceptExplanation:
        """Explain universal quantification."""
        return ConceptExplanation(
            concept="Universal Quantification (∀)",
            informal_description="A statement that something is true for ALL possible cases in a given domain.",
            formal_definition="∀x P(x) means that property P holds for every element x in the domain of discourse.",
            examples=["∀n ∈ ℕ: n ≥ 0", "All triangles have three sides"],
            common_misconceptions=["Proving with just one example", "Confusing ∀ with ∃"],
            related_concepts=["Existential quantification", "Domain of discourse", "Logical validity"]
        )
        
    def _explain_existential_quantification(self) -> ConceptExplanation:
        """Explain existential quantification."""
        return ConceptExplanation(
            concept="Existential Quantification (∃)",
            informal_description="A statement that something is true for AT LEAST ONE case in a given domain.",
            formal_definition="∃x P(x) means that there exists at least one element x in the domain such that property P(x) holds.",
            examples=["∃n ∈ ℕ: n > 100", "There exists a prime number greater than 1000"],
            common_misconceptions=["Thinking ∃ means 'exactly one'", "Confusing ∃ with ∀"],
            related_concepts=["Universal quantification", "Witness", "Constructive vs. non-constructive proofs"]
        )
        
    def _explain_implication_concept(self) -> ConceptExplanation:
        """Explain logical implication."""
        return ConceptExplanation(
            concept="Logical Implication (→)",
            informal_description="If the first statement is true, then the second statement must also be true.",
            formal_definition="P → Q (P implies Q) is false only when P is true and Q is false; otherwise it's true.",
            examples=["If x > 5, then x > 3", "Being a square implies being a rectangle"],
            common_misconceptions=["Confusing implication with causation", "Thinking the converse is always true"],
            related_concepts=["Contrapositive", "Converse", "Biconditional", "Modus ponens"]
        )
        
    def _explain_natural_numbers(self) -> ConceptExplanation:
        """Explain natural numbers."""
        return ConceptExplanation(
            concept="Natural Numbers (ℕ)",
            informal_description="The counting numbers: 0, 1, 2, 3, 4, ...",
            formal_definition="The smallest set containing 0 and closed under the successor operation, often defined via Peano axioms.",
            examples=["Counting objects", "Indexing sequences", "Mathematical induction"],
            common_misconceptions=["Whether 0 is included varies by convention", "Thinking they're the same as integers"],
            related_concepts=["Integers", "Peano axioms", "Induction", "Recursion"]
        )
        
    def _explain_real_numbers(self) -> ConceptExplanation:
        """Explain real numbers."""
        return ConceptExplanation(
            concept="Real Numbers (ℝ)",
            informal_description="All numbers on the number line, including fractions and irrational numbers.",
            formal_definition="The unique complete ordered field, often constructed as Dedekind cuts or Cauchy sequences of rationals.",
            examples=["π", "√2", "1/3", "All decimals"],
            common_misconceptions=["Thinking all reals are rational", "Confusing with complex numbers"],
            related_concepts=["Rational numbers", "Irrational numbers", "Completeness", "Continuity"]
        )
        
    def _explain_sets(self) -> ConceptExplanation:
        """Explain sets."""
        return ConceptExplanation(
            concept="Sets",
            informal_description="Collections of distinct objects, where order doesn't matter.",
            formal_definition="A collection of distinct objects, often defined by listing elements or by a property that characterizes membership.",
            examples=["{1, 2, 3}", "Set of all even numbers", "Empty set ∅"],
            common_misconceptions=["Order matters in sets", "Sets can contain duplicates"],
            related_concepts=["Functions", "Relations", "Cardinality", "Set operations"]
        )
        
    # Database initialization methods
    
    def _init_concept_database(self) -> Dict[str, ConceptExplanation]:
        """Initialize the concept explanation database."""
        return {
            "induction": self._explain_induction_concept(),
            "equality": self._explain_equality_concept(),
            "universal": self._explain_universal_quantification(),
            "existential": self._explain_existential_quantification(),
            "implication": self._explain_implication_concept(),
            "natural_numbers": self._explain_natural_numbers(),
            "real_numbers": self._explain_real_numbers(),
            "sets": self._explain_sets(),
        }
        
    def _init_example_database(self) -> Dict[str, List[str]]:
        """Initialize the example database."""
        return {
            "arithmetic": [
                "2 + 3 = 5",
                "7 × 1 = 7", 
                "10 - 0 = 10"
            ],
            "algebra": [
                "x + 0 = x for any number x",
                "(a + b) + c = a + (b + c)",
                "ab = ba for any numbers a, b"
            ],
            "induction": [
                "1 + 2 + ... + n = n(n+1)/2",
                "2ⁿ > n for n ≥ 1",
                "Properties of Fibonacci numbers"
            ]
        }
        
    def _init_pathway_templates(self) -> Dict[str, List[str]]:
        """Initialize learning pathway templates."""
        return {
            "equality_proofs": [
                "Understand what equality means",
                "Learn basic algebraic manipulation",
                "Practice substitution and simplification",
                "Master formal equality reasoning"
            ],
            "induction_proofs": [
                "Understand the domino analogy",
                "Practice base cases",
                "Learn the inductive step pattern",
                "Master formal induction proofs"
            ],
            "logical_reasoning": [
                "Understand basic logical connectives",
                "Practice reading formal statements",
                "Learn proof strategies",
                "Master formal logical reasoning"
            ]
        }