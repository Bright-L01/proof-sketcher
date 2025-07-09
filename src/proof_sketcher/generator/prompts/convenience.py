"""Convenience functions for common prompt rendering tasks."""

from typing import Optional

from ...parser.models import TheoremInfo
from ..models import GenerationConfig, GenerationType
from .renderers import prompt_templates


def render_proof_sketch_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render proof sketch prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.PROOF_SKETCH,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )


def render_eli5_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render ELI5 prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.ELI5_EXPLANATION,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )


def render_tactic_explanation_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render tactic explanation prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.TACTIC_EXPLANATION,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )


def render_step_by_step_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render step-by-step prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.STEP_BY_STEP,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )


def render_mathematical_context_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render mathematical context prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.MATHEMATICAL_CONTEXT,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )
