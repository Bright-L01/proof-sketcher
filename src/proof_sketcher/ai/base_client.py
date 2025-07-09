"""
Base AI client interface.
Defines the contract for AI integrations.
"""

from abc import ABC, abstractmethod
from typing import Any, Dict, Optional


class AIClient(ABC):
    """Base class for AI integrations.

    This provides a consistent interface for different AI providers
    and allows for easy swapping between providers or fallback to
    offline mode.
    """

    @abstractmethod
    def generate(self, prompt: str, **kwargs) -> str:
        """Generate response from prompt.

        Args:
            prompt: Input prompt for the AI
            **kwargs: Additional provider-specific parameters

        Returns:
            Generated text response

        Raises:
            Exception: If generation fails
        """
        pass

    @abstractmethod
    def is_available(self) -> bool:
        """Check if the AI service is available.

        Returns:
            True if service is available, False otherwise
        """
        pass

    def get_info(self) -> Dict[str, Any]:
        """Get information about the AI client.

        Returns:
            Dictionary with client information
        """
        return {
            "client_type": self.__class__.__name__,
            "is_available": self.is_available(),
        }
