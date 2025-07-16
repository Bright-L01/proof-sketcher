"""Parser module for extracting theorem information from Lean 4 files.

This module provides functionality to parse Lean 4 source files and extract
theorem definitions, statements, proofs, and metadata. It supports both
standalone Lean files and Lake projects with advanced semantic analysis.

Key Components:
    LeanParser: Hybrid parser class (LSP + fallback)
    LeanLSPClient: Full semantic analysis via Lean 4 LSP
    SimpleLeanParser: Regex-based parser for basic extraction
    TheoremInfo: Data model for theorem information
    SemanticTheoremInfo: Enhanced theorem info with semantic data
    ParseResult: Container for parse results and errors

Features:
    - LSP-powered semantic analysis (Phase 9)
    - Proof state evolution tracking
    - Tactic sequence extraction
    - Mathematical entity recognition
    - Complexity scoring and difficulty assessment
    - Robust fallback to regex parsing
    - Educational content generation support

Example:
    >>> from proof_sketcher.parser import LeanParser
    >>>
    >>> # Create hybrid parser (prefers LSP, falls back to simple)
    >>> parser = LeanParser()
    >>>
    >>> # Parse with semantic analysis
    >>> result = await parser.parse_file("example.lean")
    >>> theorem = result.theorems[0]
    >>> print(f"Complexity: {theorem.complexity_score}")
    >>> print(f"Tactics: {[t.name for t in theorem.tactic_sequence]}")

For more details, see the individual module documentation.
"""

from .hybrid_parser import HybridLeanParser
from .lsp_client import LeanLSPClient, ProofState, SemanticTheoremInfo, TacticInfo
from .models import ParseResult, TheoremInfo
from .simple_parser import SimpleLeanParser

# Use hybrid parser as default (LSP + fallback)
LeanParser = HybridLeanParser

__all__ = [
    "LeanParser",
    "HybridLeanParser",
    "LeanLSPClient",
    "SimpleLeanParser",
    "ParseResult",
    "TheoremInfo",
    "SemanticTheoremInfo",
    "ProofState",
    "TacticInfo",
]
