"""CLI package for Proof Sketcher.

This package contains the command-line interface implementation,
organized into logical modules for better maintainability.
"""

from __future__ import annotations

from ..parser.simple_parser import SimpleLeanParser
from .main import cli, main

__all__ = ["cli", "main", "SimpleLeanParser"]
