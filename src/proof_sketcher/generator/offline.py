"""Offline mode for Proof Sketcher - AI-free explanations.

Features:
- AST-only proof sketch generation
- Template-based explanations
- No external dependencies
- Cached response fallback
- Basic mathematical context
"""

import logging
import re
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any

from ..core.exceptions import handle_error, GeneratorError
from ..parser.models import TheoremInfo
from .models import ProofSketch, ProofStep, GenerationConfig, GenerationRequest, GenerationResponse


class OfflineTemplates:
    """Template repository for offline explanations."""
    
    # Basic explanation templates
    THEOREM_INTRO_TEMPLATES = {
        "equality": "This theorem establishes an equality relationship between mathematical expressions.",
        "inequality": "This theorem proves an inequality or ordering relationship.",
        "existence": "This theorem demonstrates the existence of mathematical objects with specific properties.",
        "uniqueness": "This theorem proves that certain mathematical objects are unique.",
        "implication": "This theorem shows that one mathematical condition implies another.",
        "equivalence": "This theorem establishes that two conditions are mathematically equivalent.",
        "induction": "This theorem uses mathematical induction to prove a property for all natural numbers.",
        "membership": "This theorem concerns membership relationships in mathematical sets or structures.",
        "function": "This theorem establishes properties of mathematical functions.",
        "default": "This theorem establishes a fundamental mathematical relationship."
    }
    
    # Proof strategy templates
    PROOF_STRATEGY_TEMPLATES = {
        "by_simp": "This step uses simplification tactics to automatically resolve the goal.",
        "by_rw": "This step applies rewriting rules to transform the expression.",
        "by_exact": "This step provides a direct proof term that exactly matches the goal.",
        "by_apply": "This step applies a known theorem or lemma to make progress.",
        "by_intro": "This step introduces assumptions or variables into the proof context.",
        "by_cases": "This step analyzes different cases to handle all possibilities.",
        "by_induction": "This step uses mathematical induction to prove the statement.",
        "by_contradiction": "This step proves the statement by assuming the opposite leads to a contradiction.",
        "by_reflexivity": "This step uses the reflexive property of the relation.",
        "by_symmetry": "This step uses the symmetric property of the relation.",
        "by_transitivity": "This step uses the transitive property of the relation.",
        "default": "This step makes progress toward proving the goal using logical reasoning."
    }
    
    # Mathematical context templates
    MATH_AREA_CONTEXTS = {
        "algebra": "This involves algebraic manipulation and properties of mathematical operations.",
        "arithmetic": "This deals with basic arithmetic operations and their properties.",
        "logic": "This involves logical reasoning and propositional relationships.",
        "set_theory": "This concerns operations and relationships within set theory.",
        "number_theory": "This involves properties and relationships of numbers.",
        "analysis": "This deals with limits, continuity, and analytical properties.",
        "topology": "This involves topological properties and continuous mappings.",
        "category_theory": "This concerns categorical structures and morphisms.",
        "type_theory": "This involves type-theoretic constructions and relationships.",
        "default": "This involves fundamental mathematical reasoning."
    }
    
    # Difficulty assessment patterns
    DIFFICULTY_PATTERNS = {
        "beginner": [
            r"simp", r"refl", r"rfl", r"trivial", r"assumption",
            r"exact", r"apply\s+\w+", r"^\s*by\s+\w+\s*$"
        ],
        "intermediate": [
            r"cases", r"split", r"constructor", r"left", r"right",
            r"have", r"let", r"show", r"suffices"
        ],
        "advanced": [
            r"induction", r"match", r"unfold", r"conv", r"calc",
            r"ext", r"funext", r"congr", r"abel", r"ring"
        ]
    }


class OfflineGenerator:
    """Generator for offline proof sketches using AST analysis only."""
    
    def __init__(self, cache_dir: Optional[Path] = None):
        """Initialize offline generator.
        
        Args:
            cache_dir: Directory for cached responses
        """
        self.logger = logging.getLogger(__name__)
        self.cache_dir = cache_dir
        self.templates = OfflineTemplates()
        
        # Statistics
        self.generated_count = 0
        self.cache_hits = 0
        
    def generate_proof_sketch(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None
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
                details={"theorem_name": theorem.name, "cause": str(e)}
            )
            handle_error(error)
            raise error
    
    def _generate_from_ast(self, theorem: TheoremInfo) -> ProofSketch:
        """Generate proof sketch by analyzing theorem AST."""
        
        # Analyze theorem statement
        intro = self._generate_introduction(theorem)
        
        # Generate proof steps
        steps = self._generate_proof_steps(theorem)
        
        # Generate conclusion
        conclusion = self._generate_conclusion(theorem, steps)
        
        # Determine difficulty and mathematical areas
        difficulty = self._assess_difficulty(theorem)
        math_areas = self._identify_mathematical_areas(theorem)
        prerequisites = self._identify_prerequisites(theorem)
        
        return ProofSketch(
            theorem_name=theorem.name,
            introduction=intro,
            key_steps=steps,
            conclusion=conclusion,
            difficulty_level=difficulty,
            mathematical_areas=math_areas,
            prerequisites=prerequisites
        )
    
    def _generate_introduction(self, theorem: TheoremInfo) -> str:
        """Generate introduction by analyzing theorem statement."""
        statement = theorem.statement or ""
        theorem_type = self._classify_theorem_type(statement)
        
        # Get base template
        intro = self.templates.THEOREM_INTRO_TEMPLATES.get(
            theorem_type, 
            self.templates.THEOREM_INTRO_TEMPLATES["default"]
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
    
    def _generate_proof_steps(self, theorem: TheoremInfo) -> List[ProofStep]:
        """Generate proof steps from parsed proof."""
        # TheoremInfo doesn't have proof_steps, so generate generic steps
        return self._generate_generic_steps(theorem)
    
    
    def _generate_generic_steps(self, theorem: TheoremInfo) -> List[ProofStep]:
        """Generate generic proof steps when detailed parsing isn't available."""
        steps = []
        
        # Step 1: Setup
        steps.append(ProofStep(
            step_number=1,
            description="Set up the proof context and introduce necessary assumptions",
            tactics=["intro"],
            mathematical_content="Setting up proof variables and assumptions",
            intuition="We begin by introducing the mathematical objects we need to work with."
        ))
        
        # Step 2: Apply main reasoning
        if "induction" in (theorem.proof or "").lower():
            steps.append(ProofStep(
                step_number=2,
                description="Apply mathematical induction",
                tactics=["induction"],
                mathematical_content="Proof by induction on the structure",
                intuition="We use induction to prove the property holds for all cases."
            ))
        elif "simp" in (theorem.proof or "").lower():
            steps.append(ProofStep(
                step_number=2,
                description="Simplify the expression using known rules",
                tactics=["simp"],
                mathematical_content="Automated simplification",
                intuition="The result follows directly from simplification rules."
            ))
        else:
            steps.append(ProofStep(
                step_number=2,
                description="Apply the main reasoning step",
                tactics=["apply"],
                mathematical_content="Main logical step",
                intuition="This step makes the key logical connection needed for the proof."
            ))
        
        return steps
    
    def _describe_tactics(self, tactics: List[str], step_number: int) -> str:
        """Generate description based on tactics used."""
        if not tactics:
            return f"Step {step_number}: Make progress using logical reasoning"
        
        main_tactic = tactics[0]
        tactic_key = f"by_{main_tactic}"
        
        template = self.templates.PROOF_STRATEGY_TEMPLATES.get(
            tactic_key,
            self.templates.PROOF_STRATEGY_TEMPLATES["default"]
        )
        
        return f"Step {step_number}: {template}"
    
    def _generate_step_intuition(self, tactics: List[str], goal: Optional[str]) -> str:
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
            "assumption": "This uses one of our current assumptions to solve the goal."
        }
        
        return intuitions.get(main_tactic, "This step advances the proof using logical reasoning.")
    
    def _generate_conclusion(self, theorem: TheoremInfo, steps: List[ProofStep]) -> str:
        """Generate conclusion based on theorem and proof steps."""
        conclusion = f"This completes the proof of {theorem.name}."
        
        if len(steps) == 1:
            conclusion += " The result follows directly from a single application of mathematical principles."
        elif len(steps) <= 3:
            conclusion += " The proof is straightforward, requiring only a few logical steps."
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
        elif "↔" in statement or "<->" in statement or "iff" in statement_lower:
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
    
    def _identify_mathematical_areas(self, theorem: TheoremInfo) -> List[str]:
        """Identify mathematical areas based on theorem content."""
        areas = set()
        content = f"{theorem.statement} {theorem.proof or ''} {theorem.docstring or ''}".lower()
        
        # Pattern matching for mathematical areas
        area_patterns = {
            "algebra": [r"ring", r"field", r"group", r"algebraic", r"polynomial"],
            "arithmetic": [r"add", r"mul", r"div", r"succ", r"nat", r"int"],
            "logic": [r"and", r"or", r"not", r"implies", r"iff", r"forall", r"exists"],
            "set_theory": [r"set", r"union", r"intersection", r"subset", r"member"],
            "analysis": [r"limit", r"continuous", r"derivative", r"integral", r"real"],
            "topology": [r"open", r"closed", r"compact", r"connected", r"metric"],
            "number_theory": [r"prime", r"divisible", r"gcd", r"lcm", r"modular"],
            "type_theory": [r"type", r"inductive", r"structure", r"class", r"instance"]
        }
        
        for area, patterns in area_patterns.items():
            if any(re.search(pattern, content) for pattern in patterns):
                areas.add(area)
        
        return list(areas) if areas else ["mathematics"]
    
    def _identify_prerequisites(self, theorem: TheoremInfo) -> List[str]:
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
    
    def _try_cache_lookup(self, theorem: TheoremInfo) -> Optional[ProofSketch]:
        """Try to find cached result for theorem."""
        if not self.cache_dir or not self.cache_dir.exists():
            return None
        
        cache_file = self.cache_dir / f"{theorem.name}.json"
        if not cache_file.exists():
            return None
        
        try:
            import json
            with open(cache_file, 'r') as f:
                data = json.load(f)
            
            # Convert back to ProofSketch
            steps = [ProofStep(**step_data) for step_data in data['key_steps']]
            data['key_steps'] = steps
            
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
            with open(cache_file, 'w') as f:
                json.dump(data, f, indent=2)
            
            self.logger.debug(f"Cached result for theorem: {theorem.name}")
            
        except Exception as e:
            self.logger.warning(f"Failed to cache result for {theorem.name}: {e}")
    
    def get_stats(self) -> Dict[str, Any]:
        """Get generator statistics."""
        return {
            "generated_count": self.generated_count,
            "cache_hits": self.cache_hits,
            "cache_hit_rate": self.cache_hits / max(self.generated_count + self.cache_hits, 1),
            "offline_mode": True
        }


def create_offline_response(
    request: GenerationRequest,
    sketch: ProofSketch,
    generation_time_ms: float
) -> GenerationResponse:
    """Create a GenerationResponse for offline-generated content."""
    return GenerationResponse(
        request=request,
        content=sketch,
        generated_at=datetime.now(),
        generation_time_ms=generation_time_ms,
        success=True,
        error_message=None,
        token_count=None  # Not applicable for offline generation
    )