"""
AI integration module for Proof Sketcher.
Provides AI-powered natural language generation for theorem explanations.
"""

from .anthropic_client import AnthropicClient
from .base_client import AIClient
from .offline_client import OfflineClient

__all__ = ["AIClient", "AnthropicClient", "OfflineClient"]
