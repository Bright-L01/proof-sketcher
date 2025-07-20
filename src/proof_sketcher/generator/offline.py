"""Offline mode for Proof Sketcher - AI-free explanations.

Features:
- AST-only proof sketch generation
- Template-based explanations
- No external dependencies
- Cached response fallback
- Basic mathematical context
"""

from __future__ import annotations

import logging
import re
from datetime import datetime
from pathlib import Path
from typing import Any, ClassVar

from ..parser.models import TheoremInfo
from .models import (
    GenerationConfig,
    GenerationRequest,
    GenerationResponse,
    ProofSketch,
    ProofStep,
)


# Simple exceptions for MVP
class GeneratorError(Exception):
    """Exception for generation errors."""

    def __init__(self, message: str, details: dict[str, Any] | None = None):
        super().__init__(message)
        self.details = details or {}


def handle_error(error: Exception) -> None:
    """Simple error handler."""
    logging.error(f"Generation error: {error}")


class EducationalTemplates:
    """Educational template repository for discrete mathematics."""

    # Progressive explanation templates for theorem introductions
    THEOREM_INTRO_TEMPLATES: ClassVar = {
        "equality": {
            "intuitive": "This theorem shows that two mathematical expressions are actually the same thing, just written differently.",
            "conceptual": "This theorem establishes an equality relationship by demonstrating that both sides represent identical mathematical values.",
            "bridging": "We prove this equality by showing that the left and right sides evaluate to the same result through logical reasoning.",
            "formal": "This theorem establishes an equality relationship using formal mathematical logic and Lean 4's type system.",
        },
        "induction": {
            "intuitive": "This theorem is like climbing a ladder - if we can step on the first rung and always move to the next rung, we can climb as high as we want.",
            "conceptual": "This theorem uses mathematical induction, a powerful proof technique that establishes a property for all natural numbers by proving a base case and an inductive step.",
            "bridging": "Mathematical induction works by: (1) proving the property holds for a starting value, then (2) proving that if it holds for any number k, it must also hold for k+1.",
            "formal": "This theorem employs the principle of mathematical induction over the natural numbers, utilizing Lean 4's induction tactics and recursive structure definitions.",
        },
        "existence": {
            "intuitive": "This theorem proves that something exists - like proving there's at least one solution to a puzzle.",
            "conceptual": "This theorem demonstrates the existence of mathematical objects with specific properties using constructive or non-constructive methods.",
            "bridging": "We prove existence either by constructing a specific example that works, or by showing that assuming no such object exists leads to a contradiction.",
            "formal": "This theorem establishes existence using existential quantification (∃) with either explicit construction or proof by contradiction.",
        },
        "default": {
            "intuitive": "This theorem establishes an important mathematical fact that helps us understand how certain mathematical objects behave.",
            "conceptual": "This theorem demonstrates a fundamental relationship in discrete mathematics using rigorous logical reasoning.",
            "bridging": "We prove this theorem by carefully applying logical steps that transform the given assumptions into the desired conclusion.",
            "formal": "This theorem utilizes formal mathematical logic and Lean 4's type system to establish the stated mathematical relationship.",
        },
    }

    # Progressive proof strategy explanations
    PROOF_STRATEGY_TEMPLATES: ClassVar = {
        "by_simp": {
            "intuitive": "We use automatic simplification to clean up the expression.",
            "conceptual": "The simp tactic applies known simplification rules to automatically resolve the goal.",
            "bridging": "Lean's simp tactic searches through its database of simplification lemmas to transform the goal into a trivially true statement.",
            "formal": "The simp tactic in Lean 4 performs automated rewriting using the simp set of lemmas, utilizing conditional rewriting and congruence closure.",
        },
        "by_induction": {
            "intuitive": "We use the domino effect - prove it works for the first case, then show how each case makes the next one work.",
            "conceptual": "Mathematical induction proves the statement by establishing a base case and proving that each case implies the next.",
            "bridging": "We structure the proof with: (1) base case verification, (2) inductive hypothesis assumption, and (3) inductive step demonstration.",
            "formal": "The induction tactic in Lean 4 applies the induction principle for the relevant type, generating goals for the base case and inductive step with appropriate hypotheses.",
        },
        "by_contradiction": {
            "intuitive": "We assume the opposite of what we want to prove and show this leads to an impossible situation.",
            "conceptual": "Proof by contradiction (reductio ad absurdum) assumes the negation of the goal and derives a logical contradiction.",
            "bridging": "We formally assume ¬P (not P) and use logical reasoning to derive both Q and ¬Q for some statement Q, which is impossible.",
            "formal": "Classical proof by contradiction uses the principle of excluded middle (P ∨ ¬P) and explosion (⊥ → P) to establish the goal.",
        },
        "by_cases": {
            "intuitive": "We break the problem into smaller pieces and solve each piece separately.",
            "conceptual": "Case analysis systematically examines all possible scenarios to prove the statement holds in every case.",
            "bridging": "We identify the key cases that exhaustively cover all possibilities, then prove the goal separately for each case.",
            "formal": "The cases tactic in Lean 4 uses pattern matching and decidability to split the proof into exhaustive subcases based on the structure of inductive types.",
        },
        "default": {
            "intuitive": "We use logical reasoning to make progress toward our goal.",
            "conceptual": "This step applies appropriate mathematical reasoning to advance the proof.",
            "bridging": "We apply formal logical rules to transform our current state closer to the desired conclusion.",
            "formal": "This step utilizes Lean 4's type theory and logical framework to establish the required mathematical relationship.",
        },
    }

    # Discrete mathematics topic patterns and explanations
    DISCRETE_MATH_TOPICS: ClassVar = {
        "arithmetic": {
            "patterns": [r"add", r"mul", r"succ", r"zero", r"one", r"\+", r"\*"],
            "explanation": "This deals with basic arithmetic operations on natural numbers, fundamental to all of mathematics.",
        },
        "induction": {
            "patterns": [
                r"induction",
                r"nat\.rec",
                r"nat_rec",
                r"∀.*nat",
                r"forall.*nat",
            ],
            "explanation": "This uses mathematical induction, a cornerstone proof technique for establishing properties of natural numbers.",
        },
        "logic": {
            "patterns": [r"and", r"or", r"not", r"→", r"↔", r"∀", r"∃", r"iff"],
            "explanation": "This involves propositional and predicate logic, the foundation of mathematical reasoning.",
        },
        "set_theory": {
            "patterns": [r"set", r"∈", r"⊆", r"∪", r"∩", r"subset", r"union", r"inter"],
            "explanation": "This deals with set theory concepts, fundamental to organizing mathematical objects into collections.",
        },
        "combinatorics": {
            "patterns": [
                r"factorial",
                r"choose",
                r"binomial",
                r"permutation",
                r"combination",
            ],
            "explanation": "This involves counting principles and combinatorial analysis, essential for discrete probability and algorithm analysis.",
        },
        "graph_theory": {
            "patterns": [
                r"graph",
                r"vertex",
                r"edge",
                r"path",
                r"cycle",
                r"tree",
                r"connected",
            ],
            "explanation": "This concerns graph structures and their properties, crucial for computer science and network analysis.",
        },
        "number_theory": {
            "patterns": [r"prime", r"divisible", r"gcd", r"lcm", r"mod", r"congruent"],
            "explanation": "This explores properties of integers, including divisibility, prime numbers, and modular arithmetic.",
        },
    }

    # Difficulty assessment patterns
    DIFFICULTY_PATTERNS: ClassVar = {
        "beginner": [
            r"simp",
            r"refl",
            r"rfl",
            r"trivial",
            r"assumption",
            r"exact",
            r"apply\s+\w+",
            r"^\s*by\s+\w+\s*$",
        ],
        "intermediate": [
            r"cases",
            r"split",
            r"constructor",
            r"left",
            r"right",
            r"have",
            r"let",
            r"show",
            r"suffices",
        ],
        "advanced": [
            r"induction",
            r"match",
            r"unfold",
            r"conv",
            r"calc",
            r"ext",
            r"funext",
            r"congr",
            r"abel",
            r"ring",
        ],
    }


class EducationalGenerator:
    """Generator for educational proof explanations focused on discrete mathematics."""

    def __init__(self, cache_dir: Path | None = None):
        """Initialize educational generator.

        Args:
            cache_dir: Directory for cached responses
        """
        self.logger = logging.getLogger(__name__)
        self.cache_dir = cache_dir
        self.templates = EducationalTemplates()

        # Statistics
        self.generated_count = 0
        self.cache_hits = 0

    def generate_proof_sketch(
        self, theorem: TheoremInfo, config: GenerationConfig | None = None
    ) -> ProofSketch:
        """Generate proof sketch from theorem AST without AI.

        Args:
            theorem: Parsed theorem to explain
            config: Generation configuration (mostly ignored in offline mode)

        Returns:
            Generated proof sketch
        """
        self.logger.info(f"Generating offline proof sketch for: {theorem.name}")

        try:
            # Check cache first
            if self.cache_dir:
                cached = self._try_cache_lookup(theorem)
                if cached:
                    self.cache_hits += 1
                    return cached

            # Generate from AST
            sketch = self._generate_from_ast(theorem)
            self.generated_count += 1

            # Cache result if cache directory is available
            if self.cache_dir:
                self._cache_result(theorem, sketch)

            return sketch

        except Exception as e:
            error = GeneratorError(
                f"Failed to generate offline proof sketch: {e}",
                details={"theorem_name": theorem.name, "cause": str(e)},
            )
            handle_error(error)
            raise error from e

    def _generate_from_ast(self, theorem: TheoremInfo) -> ProofSketch:
        """Generate educational proof sketch by analyzing theorem AST."""
        from .models import ProofStrategy

        # Analyze theorem characteristics
        theorem_type = self._classify_theorem_type(theorem.statement or "")
        proof_strategy = self._identify_proof_strategy(theorem)
        discrete_topic = self._identify_discrete_math_topic(theorem)

        # Generate progressive overviews
        intro_templates = self.templates.THEOREM_INTRO_TEMPLATES.get(
            theorem_type, self.templates.THEOREM_INTRO_TEMPLATES["default"]
        )

        intuitive_overview = intro_templates["intuitive"]
        conceptual_overview = intro_templates["conceptual"]
        bridging_overview = intro_templates["bridging"]
        formal_overview = intro_templates["formal"]

        # Generate educational proof steps
        steps = self._generate_educational_steps(theorem, proof_strategy)

        # Generate progressive conclusions
        (
            intuitive_conclusion,
            conceptual_conclusion,
            bridging_conclusion,
            formal_conclusion,
        ) = self._generate_progressive_conclusions(theorem, steps, proof_strategy)

        # Determine difficulty and mathematical areas
        difficulty = self._assess_difficulty(theorem)
        math_areas = self._identify_mathematical_areas(theorem)
        prerequisites = self._identify_prerequisites(theorem)

        return ProofSketch(
            theorem_name=theorem.name,
            theorem_statement=theorem.statement or "",
            intuitive_overview=intuitive_overview,
            conceptual_overview=conceptual_overview,
            bridging_overview=bridging_overview,
            formal_overview=formal_overview,
            key_steps=steps,
            intuitive_conclusion=intuitive_conclusion,
            conceptual_conclusion=conceptual_conclusion,
            bridging_conclusion=bridging_conclusion,
            formal_conclusion=formal_conclusion,
            proof_strategy=proof_strategy,
            discrete_math_topic=discrete_topic,
            difficulty_level=difficulty,
            mathematical_areas=math_areas,
            prerequisites=prerequisites,
        )

    def _generate_introduction(self, theorem: TheoremInfo) -> str:
        """Generate introduction by analyzing theorem statement."""
        statement = theorem.statement or ""
        theorem_type = self._classify_theorem_type(statement)

        # Get base template
        intro = self.templates.THEOREM_INTRO_TEMPLATES.get(
            theorem_type, self.templates.THEOREM_INTRO_TEMPLATES["default"]
        )

        # Add context if available
        if theorem.docstring:
            intro += f" {theorem.docstring}"

        # Add statement information
        if "=" in statement:
            intro += " It involves establishing an equality between mathematical expressions."
        elif "→" in statement or "->" in statement:
            intro += " It demonstrates an implication relationship."
        elif "∀" in statement or "forall" in statement:
            intro += " It makes a universal claim about all elements of a certain type."
        elif "∃" in statement or "exists" in statement:
            intro += " It proves the existence of elements with specific properties."

        return intro

    def _identify_proof_strategy(self, theorem: TheoremInfo) -> "ProofStrategy":
        """Identify the primary proof strategy used in the theorem."""
        from .models import ProofStrategy

        proof_text = (theorem.proof or "").lower()
        statement = (theorem.statement or "").lower()

        # Pattern matching for proof strategies
        if any(
            pattern in proof_text for pattern in ["induction", "nat.rec", "nat_rec"]
        ):
            return ProofStrategy.INDUCTION
        elif any(
            pattern in proof_text
            for pattern in ["contradiction", "false.elim", "absurd"]
        ):
            return ProofStrategy.CONTRADICTION
        elif any(pattern in proof_text for pattern in ["cases", "match", "split"]):
            return ProofStrategy.CASES
        elif (
            any(pattern in statement for pattern in ["∃", "exists"])
            and "constructor" in proof_text
        ):
            return ProofStrategy.CONSTRUCTION
        else:
            return ProofStrategy.DIRECT

    def _identify_discrete_math_topic(self, theorem: TheoremInfo) -> str | None:
        """Identify the specific discrete mathematics topic."""
        content = f"{theorem.statement} {theorem.proof or ''} {theorem.docstring or ''}".lower()

        for topic, info in self.templates.DISCRETE_MATH_TOPICS.items():
            if any(re.search(pattern, content) for pattern in info["patterns"]):
                return topic

        return None

    def _generate_educational_steps(
        self, theorem: TheoremInfo, strategy: "ProofStrategy"
    ) -> list["ProofStep"]:
        """Generate educational proof steps with progressive explanations."""
        from .models import ProofStep

        proof_text = theorem.proof or ""

        # Determine main tactics used
        if "induction" in proof_text.lower():
            return self._generate_induction_steps(theorem)
        elif "simp" in proof_text.lower() or "rfl" in proof_text.lower():
            return self._generate_simplification_steps(theorem)
        elif "cases" in proof_text.lower():
            return self._generate_case_analysis_steps(theorem)
        else:
            return self._generate_direct_proof_steps(theorem)

    def _generate_progressive_conclusions(
        self, theorem: TheoremInfo, steps: list["ProofStep"], strategy: "ProofStrategy"
    ) -> tuple[str, str, str, str]:
        """Generate conclusions for all four educational levels."""
        theorem_name = theorem.name

        # Level 1: Intuitive
        intuitive = f"We've shown that {theorem_name} is true by using clear logical reasoning. This result helps us understand important mathematical relationships."

        # Level 2: Conceptual
        if strategy.value == "induction":
            conceptual = f"This completes our inductive proof of {theorem_name}. By establishing the base case and inductive step, we've proven the property holds for all natural numbers."
        elif strategy.value == "contradiction":
            conceptual = f"By deriving a contradiction from the negation of {theorem_name}, we've established that the theorem must be true."
        else:
            conceptual = f"Through systematic logical reasoning, we've established {theorem_name} using the {strategy.value} proof strategy."

        # Level 3: Bridging
        bridging = f"The formal proof of {theorem_name} demonstrates how our intuitive understanding translates into rigorous mathematical logic with {len(steps)} key steps."

        # Level 4: Formal
        formal = f"This completes the formal verification of {theorem_name} in Lean 4, establishing the theorem within the type-theoretic foundation of mathematics."

        return intuitive, conceptual, bridging, formal

    def _generate_induction_steps(self, theorem: TheoremInfo) -> list["ProofStep"]:
        """Generate educational steps for induction proofs."""
        from .models import ProofStep

        steps = []

        # Step 1: Base case
        steps.append(
            ProofStep(
                step_number=1,
                intuitive_explanation="First, we check that our statement works for the simplest case (usually n = 0).",
                conceptual_explanation="We establish the base case of the induction by verifying the property holds for the initial value.",
                bridging_explanation="The base case provides the foundation: we prove P(0) holds by direct verification or simple reasoning.",
                formal_explanation="We prove the base case P(0) using Lean's definitional equality and basic tactics like rfl or simp.",
                tactics=["simp", "rfl"],
                mathematical_content="Base case verification",
                lean_code="base case proof here",
            )
        )

        # Step 2: Inductive step
        steps.append(
            ProofStep(
                step_number=2,
                intuitive_explanation="Next, we show that if our statement works for any number k, then it must also work for k+1.",
                conceptual_explanation="We prove the inductive step: assuming P(k) holds, we demonstrate that P(k+1) must also hold.",
                bridging_explanation="The inductive step uses the inductive hypothesis P(k) to construct a proof of P(k+1), typically through algebraic manipulation or logical reasoning.",
                formal_explanation="Using Lean's induction tactic, we assume the inductive hypothesis and apply it along with other lemmas to prove the successor case.",
                tactics=["induction", "simp"],
                mathematical_content="Inductive step with hypothesis",
                lean_code="inductive step proof here",
            )
        )

        return steps

    def _generate_simplification_steps(self, theorem: TheoremInfo) -> list["ProofStep"]:
        """Generate educational steps for simplification proofs."""
        from .models import ProofStep

        steps = []

        steps.append(
            ProofStep(
                step_number=1,
                intuitive_explanation="We use the fact that mathematical expressions can be simplified to their most basic form.",
                conceptual_explanation="This proof relies on automatic simplification, where known mathematical facts reduce the goal to a trivially true statement.",
                bridging_explanation="The simp tactic applies a database of simplification lemmas to transform the goal through valid mathematical equivalences.",
                formal_explanation="Lean's simp tactic performs conditional rewriting using the simp attribute database, with reflexivity (rfl) handling definitional equality.",
                tactics=["simp", "rfl"],
                mathematical_content="Automatic simplification to trivial goal",
                lean_code=theorem.proof or "by simp",
            )
        )

        return steps

    def _generate_case_analysis_steps(self, theorem: TheoremInfo) -> list["ProofStep"]:
        """Generate educational steps for case analysis proofs."""
        from .models import ProofStep

        steps = []

        steps.append(
            ProofStep(
                step_number=1,
                intuitive_explanation="We break the problem into all possible cases and solve each one separately.",
                conceptual_explanation="Case analysis systematically examines all possible scenarios, proving the goal holds in every case.",
                bridging_explanation="We use pattern matching or decidability to split the proof into exhaustive subcases, then prove each subgoal individually.",
                formal_explanation="The cases tactic in Lean 4 uses the structure of inductive types to generate subgoals for each constructor.",
                tactics=["cases"],
                mathematical_content="Exhaustive case analysis",
                lean_code="cases analysis here",
            )
        )

        return steps

    def _generate_direct_proof_steps(self, theorem: TheoremInfo) -> list["ProofStep"]:
        """Generate educational steps for direct proofs."""
        from .models import ProofStep

        steps = []

        steps.append(
            ProofStep(
                step_number=1,
                intuitive_explanation="We use straightforward logical reasoning to connect our assumptions with the conclusion.",
                conceptual_explanation="This direct proof establishes the goal through a clear chain of logical steps from the premises.",
                bridging_explanation="We apply logical rules and previously proven results to systematically transform our assumptions into the desired conclusion.",
                formal_explanation="Using Lean's type theory, we construct a term of the target type through function application and logical combinators.",
                tactics=["apply", "exact"],
                mathematical_content="Direct logical reasoning",
                lean_code=theorem.proof or "direct proof here",
            )
        )

        return steps

    def _generate_generic_steps(self, theorem: TheoremInfo) -> list[ProofStep]:
        """Generate generic proof steps when detailed parsing isn't available."""
        steps = []

        # Step 1: Setup
        steps.append(
            ProofStep(
                step_number=1,
                description="Set up the proof context and introduce necessary assumptions",
                tactics=["intro"],
                mathematical_content="Setting up proof variables and assumptions",
                intuition="We begin by introducing the mathematical objects we need to work with.",
            )
        )

        # Step 2: Apply main reasoning
        if "induction" in (theorem.proof or "").lower():
            steps.append(
                ProofStep(
                    step_number=2,
                    description="Apply mathematical induction",
                    tactics=["induction"],
                    mathematical_content="Proof by induction on the structure",
                    intuition="We use induction to prove the property holds for all cases.",
                )
            )
        elif "simp" in (theorem.proof or "").lower():
            steps.append(
                ProofStep(
                    step_number=2,
                    description="Simplify the expression using known rules",
                    tactics=["simp"],
                    mathematical_content="Automated simplification",
                    intuition="The result follows directly from simplification rules.",
                )
            )
        else:
            steps.append(
                ProofStep(
                    step_number=2,
                    description="Apply the main reasoning step",
                    tactics=["apply"],
                    mathematical_content="Main logical step",
                    intuition="This step makes the key logical connection needed for the proof.",
                )
            )

        return steps

    def _describe_tactics(self, tactics: list[str], step_number: int) -> str:
        """Generate description based on tactics used."""
        if not tactics:
            return f"Step {step_number}: Make progress using logical reasoning"

        main_tactic = tactics[0]
        tactic_key = f"by_{main_tactic}"

        template = self.templates.PROOF_STRATEGY_TEMPLATES.get(
            tactic_key, self.templates.PROOF_STRATEGY_TEMPLATES["default"]
        )

        return f"Step {step_number}: {template}"

    def _generate_step_intuition(self, tactics: list[str], goal: str | None) -> str:
        """Generate intuitive explanation for a proof step."""
        if not tactics:
            return "This step uses mathematical reasoning to advance the proof."

        main_tactic = tactics[0]

        intuitions = {
            "simp": "This simplifies the mathematical expression automatically.",
            "rw": "This rewrites the expression using known equalities.",
            "exact": "This provides a precise mathematical object that solves the goal.",
            "apply": "This uses a previously proven result to make progress.",
            "intro": "This introduces new variables or assumptions we can work with.",
            "cases": "This breaks down the problem into manageable cases.",
            "induction": "This proves the statement by building up from simpler cases.",
            "refl": "This uses the fact that everything equals itself.",
            "assumption": "This uses one of our current assumptions to solve the goal.",
        }

        return intuitions.get(
            main_tactic, "This step advances the proof using logical reasoning."
        )

    def _generate_conclusion(self, theorem: TheoremInfo, steps: list[ProofStep]) -> str:
        """Generate conclusion based on theorem and proof steps."""
        conclusion = f"This completes the proof of {theorem.name}."

        if len(steps) == 1:
            conclusion += " The result follows directly from a single application of mathematical principles."
        elif len(steps) <= 3:
            conclusion += (
                " The proof is straightforward, requiring only a few logical steps."
            )
        else:
            conclusion += " The proof involves multiple steps that build upon each other to establish the result."

        # Add context about the theorem's significance
        if "fundamental" in (theorem.docstring or "").lower():
            conclusion += " This is a fundamental result with broad applications."
        elif "lemma" in theorem.name.lower():
            conclusion += " This lemma supports the proof of more complex theorems."

        return conclusion

    def _classify_theorem_type(self, statement: str) -> str:
        """Classify theorem based on statement patterns."""
        statement_lower = statement.lower()

        if "=" in statement and "≠" not in statement:
            return "equality"
        elif any(op in statement for op in ["<", ">", "≤", "≥", "≠"]):
            return "inequality"
        elif "∃" in statement or "exists" in statement_lower:
            return "existence"
        elif "!" in statement and ("∃" in statement or "exists" in statement_lower):
            return "uniqueness"
        elif "→" in statement or "->" in statement or "implies" in statement_lower:
            return "implication"
        elif "↔" in statement or "<->" in statement or "if" in statement_lower:
            return "equivalence"
        elif "∈" in statement or "in" in statement_lower:
            return "membership"
        elif "function" in statement_lower or "map" in statement_lower:
            return "function"
        elif any(word in statement_lower for word in ["induction", "inductive"]):
            return "induction"
        else:
            return "default"

    def _assess_difficulty(self, theorem: TheoremInfo) -> str:
        """Assess theorem difficulty based on proof complexity."""
        proof_text = theorem.proof or ""

        # Count matches for each difficulty level
        scores = {"beginner": 0, "intermediate": 0, "advanced": 0}

        for level, patterns in self.templates.DIFFICULTY_PATTERNS.items():
            for pattern in patterns:
                scores[level] += len(re.findall(pattern, proof_text, re.IGNORECASE))

        # Determine difficulty based on highest score
        max_score = max(scores.values())
        if max_score == 0:
            return "intermediate"  # Default

        return max(scores.keys(), key=lambda k: scores[k])

    def _identify_mathematical_areas(self, theorem: TheoremInfo) -> list[str]:
        """Identify mathematical areas based on theorem content."""
        areas = set()
        content = f"{theorem.statement} {theorem.proof or ''} {theorem.docstring or ''}".lower()

        # Pattern matching for mathematical areas
        area_patterns = {
            "algebra": [r"ring", r"field", r"group", r"algebraic", r"polynomial"],
            "arithmetic": [r"add", r"mul", r"div", r"succ", r"nat", r"int"],
            "logic": [r"and", r"or", r"not", r"implies", r"if", r"forall", r"exists"],
            "set_theory": [r"set", r"union", r"intersection", r"subset", r"member"],
            "analysis": [r"limit", r"continuous", r"derivative", r"integral", r"real"],
            "topology": [r"open", r"closed", r"compact", r"connected", r"metric"],
            "number_theory": [r"prime", r"divisible", r"gcd", r"lcm", r"modular"],
            "type_theory": [r"type", r"inductive", r"structure", r"class", r"instance"],
        }

        for area, patterns in area_patterns.items():
            if any(re.search(pattern, content) for pattern in patterns):
                areas.add(area)

        return list(areas) if areas else ["mathematics"]

    def _identify_prerequisites(self, theorem: TheoremInfo) -> list[str]:
        """Identify prerequisites based on theorem dependencies."""
        prereqs = set()
        content = f"{theorem.statement} {theorem.proof or ''}".lower()

        # Common prerequisite patterns
        if any(word in content for word in ["induction", "nat"]):
            prereqs.add("Natural numbers and mathematical induction")

        if any(word in content for word in ["real", "continuous"]):
            prereqs.add("Real analysis fundamentals")

        if any(word in content for word in ["group", "ring", "field"]):
            prereqs.add("Abstract algebra basics")

        if any(word in content for word in ["set", "function"]):
            prereqs.add("Set theory and functions")

        if "type" in content:
            prereqs.add("Type theory basics")

        return list(prereqs) if prereqs else ["Basic mathematical reasoning"]

    def _try_cache_lookup(self, theorem: TheoremInfo) -> ProofSketch | None:
        """Try to find cached result for theorem."""
        if not self.cache_dir or not self.cache_dir.exists():
            return None

        cache_file = self.cache_dir / f"{theorem.name}.json"
        if not cache_file.exists():
            return None

        try:
            import json

            with open(cache_file) as f:
                data = json.load(f)

            # Convert back to ProofSketch
            steps = [ProofStep(**step_data) for step_data in data["key_steps"]]
            data["key_steps"] = steps

            self.logger.debug(f"Cache hit for theorem: {theorem.name}")
            return ProofSketch(**data)

        except Exception as e:
            self.logger.warning(f"Failed to load cached result for {theorem.name}: {e}")
            return None

    def _cache_result(self, theorem: TheoremInfo, sketch: ProofSketch) -> None:
        """Cache the generated result."""
        if not self.cache_dir:
            return

        try:
            self.cache_dir.mkdir(parents=True, exist_ok=True)
            cache_file = self.cache_dir / f"{theorem.name}.json"

            # Convert to JSON-serializable format
            data = sketch.dict()

            import json

            with open(cache_file, "w") as f:
                json.dump(data, f, indent=2)

            self.logger.debug(f"Cached result for theorem: {theorem.name}")

        except Exception as e:
            self.logger.warning(f"Failed to cache result for {theorem.name}: {e}")

    def get_stats(self) -> dict[str, Any]:
        """Get generator statistics."""
        return {
            "generated_count": self.generated_count,
            "cache_hits": self.cache_hits,
            "cache_hit_rate": self.cache_hits
            / max(self.generated_count + self.cache_hits, 1),
            "educational_mode": True,
        }


# Backward compatibility alias
OfflineGenerator = EducationalGenerator


def create_offline_response(
    request: GenerationRequest, sketch: ProofSketch, generation_time_ms: float
) -> GenerationResponse:
    """Create a GenerationResponse for offline-generated content."""
    return GenerationResponse(
        request=request,
        content=sketch,
        generated_at=datetime.now(),
        generation_time_ms=generation_time_ms,
        success=True,
        error_message=None,
        token_count=None,  # Not applicable for offline generation
    )
