"""Template rendering functionality for prompt generation."""

from typing import List, Optional

from jinja2 import Template

from ..models import GenerationConfig, GenerationType
from .eli5 import ELI5Template
from .mathematical_context import MathematicalContextTemplate
from .proof_sketch import ProofSketchTemplate
from .step_by_step import StepByStepTemplate
from .tactic_explanation import TacticExplanationTemplate


class PromptTemplates:
    """Collection of prompt templates for different generation types."""

    def __init__(self) -> None:
        """Initialize with template instances."""
        self._templates = {
            GenerationType.PROOF_SKETCH: ProofSketchTemplate(),
            GenerationType.ELI5_EXPLANATION: ELI5Template(),
            GenerationType.TACTIC_EXPLANATION: TacticExplanationTemplate(),
            GenerationType.STEP_BY_STEP: StepByStepTemplate(),
            GenerationType.MATHEMATICAL_CONTEXT: MathematicalContextTemplate(),
        }

    @property
    def proof_sketch_template(self) -> Template:
        """Get compiled proof sketch template."""
        return self._templates[GenerationType.PROOF_SKETCH].get_template()

    @property
    def eli5_template(self) -> Template:
        """Get compiled ELI5 template."""
        return self._templates[GenerationType.ELI5_EXPLANATION].get_template()

    @property
    def tactic_explanation_template(self) -> Template:
        """Get compiled tactic explanation template."""
        return self._templates[GenerationType.TACTIC_EXPLANATION].get_template()

    @property
    def step_by_step_template(self) -> Template:
        """Get compiled step-by-step template."""
        return self._templates[GenerationType.STEP_BY_STEP].get_template()

    @property
    def mathematical_context_template(self) -> Template:
        """Get compiled mathematical context template."""
        return self._templates[GenerationType.MATHEMATICAL_CONTEXT].get_template()

    def get_template(self, generation_type: GenerationType) -> Template:
        """Get the appropriate template for a generation type."""
        if generation_type not in self._templates:
            raise ValueError(
                f"No template found for generation type: {generation_type}"
            )

        return self._templates[generation_type].get_template()

    def render_prompt(
        self,
        generation_type: GenerationType,
        theorem_name: str,
        theorem_statement: str,
        config: GenerationConfig,
        dependencies: Optional[List[str]] = None,
        proof_text: Optional[str] = None,
        docstring: Optional[str] = None,
        mathematical_context: Optional[str] = None,
    ) -> str:
        """Render a prompt template with the given parameters."""
        template = self.get_template(generation_type)

        return template.render(
            theorem_name=theorem_name,
            theorem_statement=theorem_statement,
            config=config,
            dependencies=dependencies or [],
            proof_text=proof_text,
            docstring=docstring,
            mathematical_context=mathematical_context,
        )


# Global instance for easy access
prompt_templates = PromptTemplates()
