"""Prompt templates and rendering for natural language generation.

This package provides a modular prompt system with Jinja2 templates
for different generation types.
"""

from .convenience import (
    render_eli5_prompt,
    render_mathematical_context_prompt,
    render_proof_sketch_prompt,
    render_step_by_step_prompt,
    render_tactic_explanation_prompt,
)

# Import for backward compatibility
from .renderers import PromptTemplates, prompt_templates

__all__ = [
    "PromptTemplates",
    "prompt_templates",
    "render_proof_sketch_prompt",
    "render_eli5_prompt",
    "render_tactic_explanation_prompt",
    "render_step_by_step_prompt",
    "render_mathematical_context_prompt",
]
