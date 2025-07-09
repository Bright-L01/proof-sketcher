"""
AI integration module for Proof Sketcher.
Provides AI-powered natural language generation for theorem explanations.
"""

from .base_client import AIClient
from .anthropic_client import AnthropicClient
from .offline_client import OfflineClient

__all__ = ['AIClient', 'AnthropicClient', 'OfflineClient']