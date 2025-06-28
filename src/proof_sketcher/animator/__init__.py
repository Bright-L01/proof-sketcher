"""Animation module for creating mathematical proof animations using Manim.

This module provides functionality to generate animated visualizations of
mathematical proofs. It uses Manim (Mathematical Animation Engine) to create
high-quality animations that synchronize with natural language explanations.

Key Components:
    ManimAnimator: Main animation generator
    ManimMCPClient: MCP server client for Manim rendering
    AnimationConfig: Configuration for animation parameters
    ProofAnimationBuilder: Scene builder for proof animations
    FormulaExtractor: Extract mathematical formulas from text

Features:
    - Animated theorem statements and proof steps
    - LaTeX formula rendering and transformations
    - Synchronized narration with visual elements
    - Multiple animation styles and quality settings
    - Caching system for rendered animations
    - MCP protocol integration for remote rendering

Example:
    >>> from proof_sketcher.animator import ManimAnimator, AnimationConfig
    >>> from proof_sketcher.generator import ProofSketch
    >>>
    >>> # Configure animation
    >>> config = AnimationConfig(quality="1080p", fps=60)
    >>> animator = ManimAnimator(config)
    >>>
    >>> # Generate animation from proof sketch
    >>> sketch = ProofSketch(...)  # From generator
    >>> animation = animator.create_animation(sketch)
    >>>
    >>> # Save animation
    >>> animation.save("proof_animation.mp4")

Animation Styles:
    - classic: Traditional mathematical presentation
    - modern: Contemporary design with gradients
    - minimal: Clean, distraction-free style
    - educational: Enhanced with annotations

Quality Settings:
    - 480p: Quick preview (854x480)
    - 720p: Standard quality (1280x720)
    - 1080p: High definition (1920x1080)
    - 4K: Ultra high definition (3840x2160)

For advanced usage and customization, see the individual class documentation.
"""

from .animator import CachedManimAnimator, ManimAnimator
from .formula_extractor import FormulaExtractor, LeanToLatexConverter
from .manim_mcp import ManimMCPClient, ManimMCPManager
from .models import (AnimationConfig, AnimationQuality, AnimationRequest,
                     AnimationResponse, AnimationStyle, ManimConfig,
                     TransformationType)
from .scene_builder import ProofAnimationBuilder

# Convenience alias for backward compatibility
AnimationGenerator = ManimAnimator

__all__ = [
    "ManimAnimator",
    "CachedManimAnimator",
    "AnimationGenerator",
    "AnimationConfig",
    "ManimConfig",
    "AnimationQuality",
    "AnimationStyle",
    "AnimationRequest",
    "AnimationResponse",
    "TransformationType",
    "ProofAnimationBuilder",
    "FormulaExtractor",
    "LeanToLatexConverter",
    "ManimMCPManager",
    "ManimMCPClient",
]
