"""Parser module for extracting theorem information from Lean 4 files.

This module provides functionality to parse Lean 4 source files and extract
theorem definitions, statements, proofs, and metadata. It supports both
standalone Lean files and Lake projects.

Key Components:
    LeanParser: Main parser class for processing Lean files
    TheoremInfo: Data model for theorem information
    ParseResult: Container for parse results and errors
    ParserConfig: Configuration options for parsing

Features:
    - Extract theorem names, statements, and proof bodies
    - Handle Lake project dependencies
    - Support for mathlib4 imports
    - Robust error handling with fallback strategies
    - Caching of parse results

Example:
    >>> from proof_sketcher.parser import LeanParser, ParserConfig
    >>>
    >>> # Create parser with custom config
    >>> config = ParserConfig(lean_timeout=60)
    >>> parser = LeanParser(config)
    >>>
    >>> # Parse a Lean file
    >>> result = parser.parse_file("example.lean")
    >>> for theorem in result.theorems:
    ...     print(f"{theorem.name}: {theorem.statement}")

For more details, see the individual module documentation.
"""

from .config import ParserConfig
from .lean_parser import LeanParser
from .models import ParseResult, TheoremInfo

__all__ = [
    "LeanParser",
    "ParseResult",
    "TheoremInfo",
    "ParserConfig",
]
