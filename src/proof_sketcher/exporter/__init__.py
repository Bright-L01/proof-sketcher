"""Export module for generating output in various formats.

This module provides functionality to export proof sketches and animations
to various output formats including HTML, Markdown, PDF, and Jupyter notebooks.

Key Components:
    BaseExporter: Abstract base class for all exporters
    HTMLExporter: Generate HTML documentation
    MarkdownExporter: Generate Markdown files
    PDFExporter: Generate PDF documents via LaTeX
    JupyterExporter: Generate interactive notebooks
    TemplateManager: Manage export templates

Features:
    - Multiple output formats with consistent structure
    - Template-based rendering with Jinja2
    - Cross-reference generation
    - Media embedding (animations, images)
    - Batch export with parallelization
    - Customizable themes and styles

Example:
    >>> from proof_sketcher.exporter import HTMLExporter, ExportOptions
    >>> from proof_sketcher.generator import ProofSketch
    >>>
    >>> # Configure export
    >>> options = ExportOptions(
    ...     output_dir=Path("docs"),
    ...     html_theme="modern",
    ...     include_animations=True
    ... )
    >>>
    >>> # Create exporter
    >>> exporter = HTMLExporter(options)
    >>>
    >>> # Export single sketch
    >>> sketch = ProofSketch(...)  # From generator
    >>> result = exporter.export_single(sketch)
    >>>
    >>> # Export multiple with index
    >>> results = exporter.export_multiple(sketches)

Export Formats:
    - HTML: Web-ready documentation with interactive features
    - Markdown: GitHub-compatible documentation
    - PDF: Publication-ready documents via LaTeX
    - Jupyter: Interactive educational notebooks

For template customization, see the templates/ directory.
"""

from .batch_processor import BatchExporter
from .simple_html import SimpleHTMLExporter
from .simple_markdown import SimpleMarkdownExporter

# Use simple exporters for MVP
MarkdownExporter = SimpleMarkdownExporter
HTMLExporter = SimpleHTMLExporter

__all__ = [
    "MarkdownExporter",
    "SimpleMarkdownExporter",
    "HTMLExporter",
    "SimpleHTMLExporter",
    "BatchExporter",
]
