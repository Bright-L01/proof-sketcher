"""
Fixed AI generator that uses the new client-based architecture.
This replaces the broken subprocess-based implementation.
"""

import json
import logging
from typing import Iterator, Optional

from ..ai import AIClient, AnthropicClient, OfflineClient
from ..core.exceptions import GeneratorError
from ..core.interfaces import IGenerator
from ..parser.models import TheoremInfo
from .models import (
    GenerationConfig,
    GenerationRequest,
    GenerationResponse,
    GenerationType,
    ProofSketch,
    ProofStep,
)


class FixedAIGenerator(IGenerator):
    """Fixed AI generator using proper SDK integration instead of broken CLI."""

    def __init__(
        self,
        ai_client: Optional[AIClient] = None,
        default_config: Optional[GenerationConfig] = None,
        use_offline_fallback: bool = True,
    ):
        """Initialize the fixed AI generator.

        Args:
            ai_client: AI client to use (defaults to AnthropicClient)
            default_config: Default generation configuration
            use_offline_fallback: Whether to fallback to offline mode
        """
        self.logger = logging.getLogger(__name__)
        self.default_config = default_config or GenerationConfig()
        self.use_offline_fallback = use_offline_fallback

        # Initialize AI client
        if ai_client:
            self.ai_client = ai_client
        else:
            # Try Anthropic first
            anthropic_client = AnthropicClient(
                max_tokens=self.default_config.max_tokens,
                temperature=self.default_config.temperature,
            )

            if anthropic_client.is_available():
                self.ai_client = anthropic_client
                self.logger.info("Using Anthropic Claude for AI generation")
            elif use_offline_fallback:
                self.ai_client = OfflineClient()
                self.logger.warning("Using offline fallback - AI service unavailable")
            else:
                raise GeneratorError(
                    "No AI service available and offline fallback disabled"
                )

    def generate_proof_sketch(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> ProofSketch:
        """Generate a proof sketch for the theorem.

        Args:
            theorem: Theorem information
            config: Generation configuration
            mathematical_context: Additional context

        Returns:
            ProofSketch object

        Raises:
            GeneratorError: If generation fails
        """
        config = config or self.default_config

        # Build prompt for proof sketch
        prompt = self._build_proof_sketch_prompt(theorem, mathematical_context)

        try:
            # Generate response
            response = self.ai_client.generate(
                prompt, max_tokens=config.max_tokens, temperature=config.temperature
            )

            # Parse response into ProofSketch
            return self._parse_proof_sketch(response, theorem)

        except Exception as e:
            self.logger.error(f"Failed to generate proof sketch: {e}")
            raise GeneratorError(f"Proof sketch generation failed: {e}")

    def generate_eli5_explanation(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> str:
        """Generate an ELI5 explanation.

        Args:
            theorem: Theorem information
            config: Generation configuration
            mathematical_context: Additional context

        Returns:
            Simple explanation text
        """
        config = config or self.default_config

        prompt = """Explain this theorem like I'm five years old:

Theorem: {theorem.name}
Statement: {theorem.statement}

Make it simple and use analogies a child would understand."""

        try:
            return self.ai_client.generate(
                prompt, max_tokens=config.max_tokens, temperature=config.temperature
            )
        except Exception as e:
            self.logger.error(f"Failed to generate ELI5 explanation: {e}")
            return "This theorem is like a math rule that always works!"

    def generate_tactic_explanation(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> str:
        """Generate explanation of tactics used.

        Args:
            theorem: Theorem information
            config: Generation configuration
            mathematical_context: Additional context

        Returns:
            Tactic explanation text
        """
        config = config or self.default_config

        prompt = """Explain the Lean tactics used in this proof:

Theorem: {theorem.name}
Proof: {theorem.proof}

Focus on why each tactic is used and what it accomplishes."""

        try:
            return self.ai_client.generate(
                prompt, max_tokens=config.max_tokens, temperature=config.temperature
            )
        except Exception as e:
            self.logger.error(f"Failed to generate tactic explanation: {e}")
            return "This proof uses standard Lean tactics to establish the result."

    def generate_step_by_step(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> str:
        """Generate step-by-step walkthrough.

        Args:
            theorem: Theorem information
            config: Generation configuration
            mathematical_context: Additional context

        Returns:
            Step-by-step explanation text
        """
        config = config or self.default_config

        prompt = """Provide a detailed step-by-step walkthrough of this proof:

Theorem: {theorem.name}
Statement: {theorem.statement}
Proof: {theorem.proof}

Break down each step and explain the reasoning."""

        try:
            return self.ai_client.generate(
                prompt, max_tokens=config.max_tokens, temperature=config.temperature
            )
        except Exception as e:
            self.logger.error(f"Failed to generate step-by-step explanation: {e}")
            return "Step 1: Set up the proof\nStep 2: Apply the main argument\nStep 3: Conclude"

    def generate_streaming(
        self,
        theorem: TheoremInfo,
        generation_type: GenerationType,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> Iterator[str]:
        """Generate with streaming (not implemented in this version).

        Just returns the full response as a single chunk.
        """
        if generation_type == GenerationType.PROOF_SKETCH:
            result = str(
                self.generate_proof_sketch(theorem, config, mathematical_context)
            )
        elif generation_type == GenerationType.ELI5:
            result = self.generate_eli5_explanation(
                theorem, config, mathematical_context
            )
        elif generation_type == GenerationType.TACTIC_EXPLANATION:
            result = self.generate_tactic_explanation(
                theorem, config, mathematical_context
            )
        elif generation_type == GenerationType.STEP_BY_STEP:
            result = self.generate_step_by_step(theorem, config, mathematical_context)
        else:
            result = "Unsupported generation type"

        yield result

    def _build_proof_sketch_prompt(
        self, theorem: TheoremInfo, mathematical_context: Optional[str]
    ) -> str:
        """Build prompt for proof sketch generation."""
        prompt = """Generate a natural language proof sketch for this Lean theorem.

Theorem: {theorem.name}
Statement: {theorem.statement}
Dependencies: {', '.join(theorem.dependencies) if theorem.dependencies else 'None'}"""

        if theorem.docstring:
            prompt += f"\nDocstring: {theorem.docstring}"

        if theorem.proof:
            prompt += f"\nFormal Proof: {theorem.proof}"

        if mathematical_context:
            prompt += f"\nAdditional Context: {mathematical_context}"

        prompt += """

Please provide a JSON response with this structure:
{
  "theorem_name": "name",
  "introduction": "Brief introduction",
  "key_steps": [
    {
      "step_number": 1,
      "description": "What this step does",
      "mathematical_content": "The math involved",
      "tactics": ["tactic1", "tactic2"]
    }
  ],
  "conclusion": "Summary of what was proved",
  "difficulty_level": "beginner|intermediate|advanced",
  "mathematical_areas": ["area1", "area2"],
  "prerequisites": ["prerequisite1", "prerequisite2"]
}"""

        return prompt

    def _parse_proof_sketch(self, response: str, theorem: TheoremInfo) -> ProofSketch:
        """Parse AI response into ProofSketch object."""
        try:
            # Try to extract JSON from response
            content = response.strip()

            # Remove markdown code blocks if present
            if content.startswith("```json"):
                content = content.split("```json")[1].split("```")[0].strip()
            elif content.startswith("```"):
                content = content.split("```")[1].split("```")[0].strip()

            # Parse JSON
            data = json.loads(content)

            # Create ProofSketch
            return ProofSketch(
                theorem_name=data.get("theorem_name", theorem.name),
                theorem_statement=theorem.statement or "",
                introduction=data.get("introduction", ""),
                key_steps=[ProofStep(**step) for step in data.get("key_steps", [])],
                conclusion=data.get("conclusion", ""),
                difficulty_level=data.get("difficulty_level", "intermediate"),
                mathematical_areas=data.get("mathematical_areas", []),
                prerequisites=data.get("prerequisites", []),
            )

        except (json.JSONDecodeError, KeyError, TypeError) as e:
            self.logger.warning(f"Failed to parse structured response: {e}")

            # Fallback: Create simple proof sketch from text
            return ProofSketch(
                theorem_name=theorem.name,
                theorem_statement=theorem.statement or "",
                introduction=(
                    response[:200] + "..." if len(response) > 200 else response
                ),
                key_steps=[
                    ProofStep(
                        step_number=1,
                        description="See the detailed explanation above",
                        mathematical_content=theorem.statement,
                        tactics=[],
                    )
                ],
                conclusion="The theorem has been established.",
                difficulty_level="intermediate",
                mathematical_areas=["general"],
                prerequisites=[],
            )
