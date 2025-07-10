"""Proof Sketcher: Transform Lean 4 theorems into natural language explanations.

Proof Sketcher bridges the gap between formal mathematical proofs in Lean 4 
and human-readable explanations. It generates natural language descriptions 
of theorems and their proofs with simple static diagrams.

Key Features:
    - Parse Lean 4 theorem files and extract theorem information
    - Generate natural language explanations using Claude AI
    - Create simple static diagrams for visualization
    - Export to multiple formats (HTML, Markdown, PDF)
    - Future: Integration with doc-gen4

Basic Usage:
    >>> from proof_sketcher.parser import LeanParser
    >>> from proof_sketcher.generator import ClaudeGenerator
    >>>
    >>> # Parse a Lean file
    >>> parser = LeanParser()
    >>> result = parser.parse_file("example.lean")
    >>>
    >>> # Generate natural language explanation
    >>> generator = ClaudeGenerator()
    >>> for theorem in result.theorems:
    ...     sketch = generator.generate_proof_sketch(theorem)
    ...     print(sketch.explanation)

Command Line Usage:
    $ proof-sketcher prove example.lean --format html
    $ proof-sketcher config show
    $ proof-sketcher cache status

Environment Variables:
    PROOF_SKETCHER_DEBUG: Enable debug mode
    PROOF_SKETCHER_CONFIG: Path to configuration file
    PROOF_SKETCHER_CACHE_DIR: Override cache directory

For more information, see:
    - Documentation: https://github.com/your-org/proof-sketcher
    - Examples: https://github.com/your-org/proof-sketcher/examples
"""

__version__ = "0.0.1a1"  # Alpha 1, NOT production!
__author__ = "Proof Sketcher Contributors"

# Re-export main components for convenience
from .generator import ClaudeGenerator
from .parser import LeanParser

__all__ = [
    "LeanParser",
    "ClaudeGenerator",
    "__version__",
]
