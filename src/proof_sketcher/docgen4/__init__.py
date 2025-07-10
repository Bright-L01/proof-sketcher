"""doc-gen4 integration module.

This module provides functionality to integrate with and enhance doc-gen4 output.
"""

from .enhancer import DocGen4Enhancer
from .integration import DocGen4Integration
from .models import DocGen4Declaration, DocGen4Module, EnhancedDeclaration
from .parser import DocGen4Parser

__all__ = [
    "DocGen4Parser",
    "DocGen4Enhancer",
    "DocGen4Integration",
    "DocGen4Declaration",
    "DocGen4Module",
    "EnhancedDeclaration",
]
