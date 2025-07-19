"""Generator module for creating natural language explanations of Lean theorems.

⚠️ IMPORTANT: Despite the naming, this module currently uses TEMPLATE-BASED generation,
not AI language models. The "AI" and "Claude" class names are legacy from planned
features that were not implemented.

Key Components:
    SimpleGenerator: Template-based explanation generator
    ProofSketch: Data model for generated explanations
    GenerationConfig: Configuration for generation parameters

Current Implementation:
    - Template-based generation with pattern matching
    - 4-level educational progression (intuitive → formal)
    - Basic proof strategy detection
    - No actual AI or LLM integration

Limitations:
    - Generic, non-theorem-specific explanations
    - Limited mathematical accuracy
    - No semantic understanding of proofs

Example:
    >>> from proof_sketcher.generator import AIGenerator
    >>> from proof_sketcher.parser import TheoremInfo
    >>>
    >>> # Create generator
    >>> generator = AIGenerator()
    >>>
    >>> # Generate explanation
    >>> theorem = TheoremInfo(name="add_comm", statement="a + b = b + a")
    >>> sketch = generator.generate_proof_sketch(theorem)
    >>>
    >>> print(sketch.introduction)
    >>> for step in sketch.key_steps:
    ...     print(f"- {step.description}")

Generation Types:
    - concise: Brief explanation focusing on key ideas
    - detailed: Comprehensive explanation with all steps
    - tutorial: Educational explanation with background

For configuration options, see GenerationConfig documentation.
"""

from .models import GenerationConfig, ProofSketch, ProofStep
from .progressive_generator import (
    ConceptExplanation,
    LearningStep,
    ProgressiveGenerator,
    ProgressiveSketch,
)
from .semantic_generator import EducationalLevel, SemanticGenerator
from .simple_generator import SimpleGenerator

# Default to simple generator (template-based)
# Note: Despite the names, these are all template-based, not AI
AIGenerator = SimpleGenerator

# Backward compatibility aliases (all template-based)
ClaudeGenerator = SimpleGenerator

__all__ = [
    "AIGenerator",
    "ClaudeGenerator",  # Backward compatibility
    "ConceptExplanation",
    "EducationalLevel",
    "GenerationConfig",
    "LearningStep",
    "ProgressiveGenerator",
    "ProgressiveSketch",
    "ProofSketch",
    "ProofStep",
    "SemanticGenerator",
    "SimpleGenerator",
]
