"""
Anthropic Claude integration using the official SDK.
Replaces the broken subprocess-based Claude CLI integration.
"""

import logging
import os
from typing import Any, Dict, Optional

from .base_client import AIClient

# Try to import anthropic, but don't fail if not available
try:
    from anthropic import Anthropic

    ANTHROPIC_AVAILABLE = True
except ImportError:
    ANTHROPIC_AVAILABLE = False
    Anthropic = None


class AnthropicClient(AIClient):
    """Anthropic Claude integration using the official SDK.

    This replaces the broken subprocess-based implementation that
    was trying to call a non-existent 'claude' CLI executable.
    """

    def __init__(
        self,
        api_key: Optional[str] = None,
        model: str = "claude-3-5-sonnet-20241022",
        max_tokens: int = 2000,
        temperature: float = 0.7,
    ):
        """Initialize the Anthropic client.

        Args:
            api_key: Anthropic API key (defaults to ANTHROPIC_API_KEY env var)
            model: Model to use
            max_tokens: Maximum tokens to generate
            temperature: Temperature for generation
        """
        self.logger = logging.getLogger(__name__)
        self.model = model
        self.max_tokens = max_tokens
        self.temperature = temperature
        self.client = None

        if not ANTHROPIC_AVAILABLE:
            self.logger.warning(
                "Anthropic SDK not installed. Install with: pip install anthropic"
            )
            return

        # Get API key
        api_key = api_key or os.getenv("ANTHROPIC_API_KEY")
        if not api_key:
            self.logger.warning(
                "ANTHROPIC_API_KEY not set. AI features will be unavailable."
            )
            return

        try:
            self.client = Anthropic(api_key=api_key)
            self.logger.info("Anthropic client initialized successfully")
        except Exception as e:
            self.logger.error(f"Failed to initialize Anthropic client: {e}")
            self.client = None

    def generate(self, prompt: str, **kwargs) -> str:
        """Generate response using Claude.

        Args:
            prompt: Input prompt
            **kwargs: Additional parameters (model, max_tokens, temperature)

        Returns:
            Generated text response

        Raises:
            Exception: If generation fails
        """
        if not self.is_available():
            return self._fallback_response(prompt)

        # Override defaults with kwargs
        model = kwargs.get("model", self.model)
        max_tokens = kwargs.get("max_tokens", self.max_tokens)
        temperature = kwargs.get("temperature", self.temperature)

        try:
            self.logger.debug(f"Generating with Claude: {model}")
            response = self.client.messages.create(
                model=model,
                max_tokens=max_tokens,
                temperature=temperature,
                messages=[{"role": "user", "content": prompt}],
            )

            # Extract text from response
            if response.content and len(response.content) > 0:
                return response.content[0].text
            else:
                self.logger.warning("Empty response from Claude")
                return self._fallback_response(prompt)

        except Exception as e:
            self.logger.error(f"Claude API error: {e}")
            return self._fallback_response(prompt)

    def is_available(self) -> bool:
        """Check if Anthropic service is available.

        Returns:
            True if client is initialized and ready
        """
        return ANTHROPIC_AVAILABLE and self.client is not None

    def get_info(self) -> Dict[str, Any]:
        """Get information about the Anthropic client.

        Returns:
            Dictionary with client information
        """
        info = super().get_info()
        info.update(
            {
                "provider": "Anthropic",
                "model": self.model,
                "sdk_available": ANTHROPIC_AVAILABLE,
                "api_key_set": bool(os.getenv("ANTHROPIC_API_KEY")),
                "temperature": self.temperature,
                "max_tokens": self.max_tokens,
            }
        )
        return info

    def _fallback_response(self, prompt: str) -> str:
        """Generate a fallback response when API is unavailable.

        Args:
            prompt: Original prompt

        Returns:
            Fallback response text
        """
        self.logger.info("Using fallback response due to API unavailability")

        # Check if this is a theorem explanation request
        if "theorem" in prompt.lower() or "proo" in prompt.lower():
            return """This theorem demonstrates an important mathematical property.

The proof follows a structured approach:
1. We establish the initial conditions
2. We apply the relevant mathematical principles
3. We verify that our conclusion follows logically

This result has applications in various areas of mathematics and provides a foundation for further theoretical developments.

Note: This is a template response as the AI service is currently unavailable. For detailed explanations, please ensure the AI service is properly configured."""

        return "AI service temporarily unavailable. Please check your configuration and try again."
