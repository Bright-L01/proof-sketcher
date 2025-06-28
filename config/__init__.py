"""Configuration module for Proof Sketcher.

This module provides centralized configuration management with support for:
- Default configurations
- Configuration files (.proof-sketcher.yaml, pyproject.toml)
- Environment variable overrides
- Runtime configuration updates
"""

from .config import (
    ExportConfig,
    ProofSketcherConfig,
    get_config,
    reset_config,
    set_config,
)

__all__ = [
    "ExportConfig",
    "ProofSketcherConfig",
    "get_config",
    "set_config",
    "reset_config",
]