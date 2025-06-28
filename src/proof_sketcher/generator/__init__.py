"""Generator module for creating natural language explanations of Lean theorems.

This module uses Claude AI to generate human-readable explanations of formal
mathematical theorems and their proofs. It produces structured explanations
with step-by-step breakdowns and key insights.

Key Components:
    ClaudeGenerator: Main generator class using Claude API
    ProofSketch: Data model for generated explanations
    GenerationConfig: Configuration for generation parameters
    ResponseCache: Caching system for API responses

Features:
    - Natural language generation from formal proofs
    - Step-by-step proof explanations
    - Mathematical context integration
    - Multiple explanation types (concise, detailed, tutorial)
    - Response caching to reduce API calls
    - Streaming output support

Example:
    >>> from proof_sketcher.generator import ClaudeGenerator
    >>> from proof_sketcher.parser import TheoremInfo
    >>>
    >>> # Create generator
    >>> generator = ClaudeGenerator()
    >>>
    >>> # Generate explanation
    >>> theorem = TheoremInfo(name="add_comm", statement="a + b = b + a")
    >>> sketch = generator.generate_proof_sketch(theorem)
    >>>
    >>> print(sketch.explanation)
    >>> for step in sketch.steps:
    ...     print(f"- {step.description}")

Generation Types:
    - concise: Brief explanation focusing on key ideas
    - detailed: Comprehensive explanation with all steps
    - tutorial: Educational explanation with background

For configuration options, see GenerationConfig documentation.
"""

from .cache import CacheManager
from .claude import ClaudeGenerator
from .models import GenerationConfig, ProofSketch, ProofStep

__all__ = [
    "ClaudeGenerator",
    "ProofSketch",
    "ProofStep",
    "GenerationConfig",
    "CacheManager",
]
