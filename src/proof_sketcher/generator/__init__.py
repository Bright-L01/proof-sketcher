"""Generator module for creating natural language explanations of Lean theorems.

This module uses AI language models to generate human-readable explanations of formal
mathematical theorems and their proofs. It produces structured explanations
with step-by-step breakdowns and key insights.

Key Components:
    AIGenerator: Main generator class using AI CLI tools
    ProofSketch: Data model for generated explanations
    GenerationConfig: Configuration for generation parameters
    GenerationCache: Caching adapter for generation responses

Features:
    - Natural language generation from formal proofs
    - Step-by-step proof explanations
    - Mathematical context integration
    - Multiple explanation types (concise, detailed, tutorial)
    - Response caching to reduce API calls
    - Streaming output support

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
from .simple_generator import SimpleGenerator

# Use simple generator for MVP
AIGenerator = SimpleGenerator

# Backward compatibility aliases
ClaudeGenerator = AIGenerator

__all__ = [
    "AIGenerator",
    "SimpleGenerator",
    "ClaudeGenerator",  # Backward compatibility
    "ProofSketch",
    "ProofStep", 
    "GenerationConfig",
]
