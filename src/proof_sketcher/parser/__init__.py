"""Parser module for extracting theorem information from Lean 4 files.

This module provides functionality to parse Lean 4 source files and extract
theorem definitions, statements, proofs, and metadata. It supports both
standalone Lean files and Lake projects.

Key Components:
    LeanParser: Main parser class (SimpleLeanParser)
    SimpleLeanParser: Regex-based parser for theorem extraction
    TheoremInfo: Data model for theorem information
    ParseResult: Container for parse results and errors
    
    DEPRECATED:
    LeanLSPClient: (DEPRECATED) LSP client - non-functional, do not use
    HybridLeanParser: (DEPRECATED) Hybrid parser - uses broken LSP
    SemanticTheoremInfo: (DEPRECATED) Enhanced theorem info from LSP

Features:
    - Fast regex-based theorem extraction
    - Support for nested namespaces
    - Tactic extraction
    - Dependency tracking
    - Error handling and recovery

Example:
    >>> from proof_sketcher.parser import LeanParser
    >>>
    >>> # Create parser
    >>> parser = LeanParser()
    >>>
    >>> # Parse file
    >>> result = parser.parse_file("example.lean")
    >>> theorem = result.theorems[0]
    >>> print(f"Theorem: {theorem.name}")
    >>> print(f"Statement: {theorem.statement}")

For more details, see the individual module documentation.

IMPORTANT: The LSP integration has been deprecated due to performance issues
(1000x slower, 0 theorems extracted). Use SimpleLeanParser for all parsing needs.
"""

from .hybrid_parser import HybridLeanParser
from .lsp_client import LeanLSPClient, ProofState, SemanticTheoremInfo, TacticInfo
from .models import ParseResult, TheoremInfo
from .simple_parser import SimpleLeanParser

# Use simple parser as default (LSP is deprecated and non-functional)
LeanParser = SimpleLeanParser

__all__ = [
    "HybridLeanParser",
    "LeanLSPClient",
    "LeanParser",
    "ParseResult",
    "ProofState",
    "SemanticTheoremInfo",
    "SimpleLeanParser",
    "TacticInfo",
    "TheoremInfo",
]
