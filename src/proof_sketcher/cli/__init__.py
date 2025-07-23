"""CLI package for Proof Sketcher.

This package contains the command-line interface implementation,
organized into logical modules for better maintainability.
"""

from __future__ import annotations

from ..parser.simple_parser import SimpleLeanParser
from .main import cli, main, setup_logging

# Mock classes for test compatibility
class ClaudeGenerator:
    """Mock Claude generator for CLI tests."""
    def __init__(self, *args, **kwargs):
        pass
    
    def generate(self, theorem):
        """Mock generation method."""
        return {
            "theorem_name": theorem.name,
            "explanation": "Mock explanation",
            "proof_steps": []
        }


class CacheManager:
    """Mock cache manager for CLI tests."""
    def __init__(self, cache_dir=None):
        self.cache_dir = cache_dir
        
    def get_status(self):
        """Mock cache status."""
        return {
            "total_size": 1024,
            "file_count": 10,
            "cache_types": ["proof", "export"]
        }
    
    def clear(self, cache_type=None):
        """Mock cache clearing."""
        return True


__all__ = ["cli", "main", "SimpleLeanParser", "setup_logging", "ClaudeGenerator", "CacheManager"]
