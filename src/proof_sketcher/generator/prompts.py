"""Prompt templates for natural language generation using Jinja2."""

from typing import List, Optional

from jinja2 import BaseLoader, Environment, Template

from ..parser.models import TheoremInfo
from .models import GenerationConfig, GenerationType


class PromptTemplates:
    """Collection of Jinja2 templates for different generation types."""

    def __init__(self):
        """Initialize with Jinja2 environment."""
        self.env = Environment(
            loader=BaseLoader(), trim_blocks=True, lstrip_blocks=True
        )

        # Add custom filters
        self.env.filters["format_dependencies"] = self._format_dependencies
        self.env.filters["format_statement"] = self._format_statement

    def _format_dependencies(self, dependencies: List[str]) -> str:
        """Format dependencies list for display."""
        if not dependencies:
            return "None"
        if len(dependencies) <= 3:
            return ", ".join(dependencies)
        return f"{', '.join(dependencies[:3])}, and {len(dependencies) - 3} others"

    def _format_statement(self, statement: str) -> str:
        """Format theorem statement for better readability."""
        # Clean up common Lean syntax for natural language
        statement = statement.replace("∀", "for all")
        statement = statement.replace("∃", "there exists")
        statement = statement.replace("→", "implies")
        statement = statement.replace("↔", "if and only if")
        statement = statement.replace("¬", "not")
        statement = statement.replace("∧", "and")
        statement = statement.replace("∨", "or")
        return statement

    @property
    def proof_sketch_template(self) -> Template:
        """Template for generating structured proof sketches."""
        template_str = """
You are a mathematics professor creating a clear, structured proof sketch. Your goal is to explain the proof strategy and key insights in natural language.

## Theorem Information
**Theorem:** {{ theorem_name }}
**Statement:** {{ theorem_statement | format_statement }}
{% if dependencies %}**Dependencies:** {{ dependencies | format_dependencies }}{% endif %}
{% if docstring %}**Context:** {{ docstring }}{% endif %}
{% if mathematical_context %}**Mathematical Context:** {{ mathematical_context }}{% endif %}
{% if proof_text %}**Lean Proof:** {{ proof_text }}{% endif %}

## Task
Create a structured proof sketch that includes:
1. **Introduction**: Explain what the theorem means and why it's important
2. **Key Steps**: Break down the proof into 3-5 main logical steps
3. **Conclusion**: Tie everything together and highlight the main insight

## Requirements
- Write for {{ config.verbosity }} level ({{ config.verbosity }})
- Focus on mathematical intuition and strategy
- Explain the "why" behind each step, not just the "what"
- Use clear, accessible language while maintaining mathematical precision
- For each step, include:
  - A clear description of what's being done
  - The mathematical reasoning
  - Key tactics or techniques used
  {% if config.include_reasoning %}- Intuitive explanation of why this step works{% endif %}

## Response Format
Please respond with a JSON object containing:
```json
{
  "theorem_name": "{{ theorem_name }}",
  "introduction": "Clear explanation of the theorem and its significance",
  "key_steps": [
    {
      "step_number": 1,
      "description": "What this step accomplishes",
      "mathematical_content": "The mathematical details",
      "tactics": ["list", "of", "tactics"],
      "intuition": "Why this step works/is needed"
    }
  ],
  "conclusion": "Summary and main insights",
  "difficulty_level": "beginner|intermediate|advanced",
  "mathematical_areas": ["area1", "area2"],
  "prerequisites": ["prereq1", "prereq2"]
}
```
"""
        return self.env.from_string(template_str)

    @property
    def eli5_template(self) -> Template:
        """Template for ELI5 (Explain Like I'm 5) explanations."""
        template_str = """
You are explaining mathematics to someone who is curious but doesn't have advanced mathematical training. Your goal is to make the theorem accessible and interesting.

## Theorem Information
**Theorem:** {{ theorem_name }}
**Statement:** {{ theorem_statement | format_statement }}
{% if dependencies %}**Builds on:** {{ dependencies | format_dependencies }}{% endif %}
{% if docstring %}**Context:** {{ docstring }}{% endif %}
{% if mathematical_context %}**Mathematical Context:** {{ mathematical_context }}{% endif %}

## Task
Create an ELI5 explanation that:
1. Uses analogies and everyday examples
2. Avoids heavy mathematical notation
3. Focuses on the intuition and "big picture"
4. Explains why someone should care about this result
5. Makes the mathematics feel approachable and interesting

## Audience
- Curious learners without advanced math background
- People who want to understand the intuition
- Those who might be intimidated by formal mathematics

## Style Guidelines
- Use conversational, friendly tone
- Include relatable analogies
- Break down complex ideas into simple parts
- Ask rhetorical questions to engage the reader
- Use "you" to make it personal
- Explain technical terms when you use them
- Show enthusiasm for the mathematics

## Length
Aim for {{ config.verbosity }} explanation:
{% if config.verbosity == "concise" %}- Keep it under 200 words
- Focus on the single most important insight{% elif config.verbosity == "detailed" %}- 300-500 words
- Include 1-2 good analogies
- Cover the main ideas clearly{% else %}- 500-800 words
- Multiple analogies and examples
- Cover prerequisites and applications{% endif %}

Please write a clear, engaging ELI5 explanation of this theorem.
"""
        return self.env.from_string(template_str)

    @property
    def tactic_explanation_template(self) -> Template:
        """Template for explaining specific Lean tactics used in proofs."""
        template_str = """
You are a Lean 4 expert explaining proof tactics to someone learning formal mathematics. Focus on practical understanding.

## Theorem Information
**Theorem:** {{ theorem_name }}
**Statement:** {{ theorem_statement | format_statement }}
{% if proof_text %}**Proof:** {{ proof_text }}{% endif %}
{% if dependencies %}**Dependencies:** {{ dependencies | format_dependencies }}{% endif %}
{% if mathematical_context %}**Mathematical Context:** {{ mathematical_context }}{% endif %}

## Task
Explain the proof tactics used in this theorem:
1. Identify the main tactics used
2. Explain what each tactic does
3. Explain why each tactic was chosen
4. Suggest alternatives where applicable
5. Highlight any particularly clever or interesting tactic usage

## Focus Areas
- **Tactic purpose**: What does each tactic accomplish?
- **Tactic strategy**: Why was this tactic chosen over alternatives?
- **Common patterns**: How do these tactics fit into broader proof patterns?
- **Learning tips**: What should a student remember about these tactics?

## Style
- Write for {{ config.verbosity }} level
- Include code snippets where helpful
- Explain both the technical details and the intuition
- Connect tactics to the overall proof strategy
{% if config.include_reasoning %}- Include reasoning about tactic selection{% endif %}

Please provide a clear explanation of the tactics used in this proof.
"""
        return self.env.from_string(template_str)

    @property
    def step_by_step_template(self) -> Template:
        """Template for detailed step-by-step proof walkthroughs."""
        template_str = """
You are a mathematics tutor providing a detailed step-by-step walkthrough of a proof. Your goal is to make every step crystal clear.

## Theorem Information
**Theorem:** {{ theorem_name }}
**Statement:** {{ theorem_statement | format_statement }}
{% if dependencies %}**Prerequisites:** {{ dependencies | format_dependencies }}{% endif %}
{% if docstring %}**Context:** {{ docstring }}{% endif %}
{% if mathematical_context %}**Mathematical Context:** {{ mathematical_context }}{% endif %}
{% if proof_text %}**Formal Proof:** {{ proof_text }}{% endif %}

## Task
Create a detailed step-by-step walkthrough that:
1. **Sets up the problem**: What are we trying to prove?
2. **Outlines the strategy**: What's our overall approach?
3. **Works through each step**: Detailed explanations of every move
4. **Justifies each step**: Why is this step valid/necessary?
5. **Connects to the big picture**: How does each step fit the strategy?

## Step-by-Step Requirements
For each step, include:
- **What we're doing**: Clear statement of the action
- **Why we're doing it**: Motivation and reasoning
- **How it works**: Mathematical justification
- **What we achieve**: What this step accomplishes
- **Next steps**: How this connects to what follows

## Audience
- Students learning to write proofs
- People who want to understand the logical flow
- Anyone who gets lost in mathematical arguments

## Style
- Number each step clearly
- Use "we" language to include the reader
- Explain assumptions and definitions as needed
- Point out common stumbling blocks
- Include "sanity checks" along the way
- {{ config.verbosity }} level of detail

Please provide a comprehensive step-by-step walkthrough of this proof.
"""
        return self.env.from_string(template_str)

    def get_template(self, generation_type: GenerationType) -> Template:
        """Get the appropriate template for a generation type."""
        template_map = {
            GenerationType.PROOF_SKETCH: self.proof_sketch_template,
            GenerationType.ELI5_EXPLANATION: self.eli5_template,
            GenerationType.TACTIC_EXPLANATION: self.tactic_explanation_template,
            GenerationType.STEP_BY_STEP: self.step_by_step_template,
        }

        template = template_map.get(generation_type)
        if template is None:
            raise ValueError(
                f"No template found for generation type: {generation_type}"
            )

        return template

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
