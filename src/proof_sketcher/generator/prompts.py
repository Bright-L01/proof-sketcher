"""Backward compatibility module for prompt templates.

This module provides backward compatibility for the prompt system.
The actual implementation has been moved to prompts/ package.
"""

# Import everything from the new location for backward compatibility
from .prompts import (
    PromptTemplates,
    prompt_templates,
    render_proof_sketch_prompt,
    render_eli5_prompt,
    render_tactic_explanation_prompt,
    render_step_by_step_prompt,
    render_mathematical_context_prompt,
)

__all__ = [
    "PromptTemplates",
    "prompt_templates",
    "render_proof_sketch_prompt",
    "render_eli5_prompt",
    "render_tactic_explanation_prompt",
    "render_step_by_step_prompt",
    "render_mathematical_context_prompt",
]