"""Backward compatibility module.

This module provides backward compatibility for the CLI.
The actual implementation has been moved to cli.main.
"""

# Import everything from the new location for backward compatibility
from .cli.main import cli, main

__all__ = ["cli", "main"]
