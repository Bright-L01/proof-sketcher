"""CLI commands for Proof Sketcher."""

# Re-export all commands for easy access
from __future__ import annotations

from .batch import batch
from .cache import cache
from .config import config
from .enhance import enhance
from .info import formats, version
from .list_theorems import list_theorems
from .optimize import optimize
from .performance import performance
from .prove import prove

__all__ = [
    "batch",
    "cache",
    "config",
    "enhance",
    "formats",
    "list_theorems",
    "optimize",
    "performance",
    "prove",
    "version",
]
