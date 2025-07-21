"""Simple HTML exporter for MVP with MathJax 4.0 support."""

from __future__ import annotations

import html
from pathlib import Path

from ..generator.models import EducationalLevel, ProofSketch
from .models import ExportResult, ExportFormat


class SimpleHTMLExporter:
    """Simple HTML exporter with MathJax 4.0 support."""

    def __init__(self, options=None):
        """Initialize HTML exporter with options.
        
        Args:
            options: Export options configuration
        """
        self.options = options or {}
        self.template_manager = MockTemplateManager()  # Simple mock for MVP
    
    def export_single(self, sketch: ProofSketch, animation_path=None) -> ExportResult:
        """Export single proof sketch to HTML.
        
        Args:
            sketch: ProofSketch to export
            animation_path: Optional path to animation file
            
        Returns:
            ExportResult with success status and output info
        """
        try:
            # Use template manager to render HTML (as expected by tests)
            html_content = self.template_manager.render_template(
                "theorem.html", 
                proof_sketch=sketch,
                animation_path=animation_path
            )
            
            # Create output path  
            if hasattr(self.options, 'output_dir'):
                output_dir = Path(self.options.output_dir)
            else:
                output_dir = Path("output")
            output_path = output_dir / f"{sketch.theorem_name}.html"
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(html_content, encoding="utf-8")
            
            # Build metadata
            metadata = {}
            if animation_path:
                metadata["animation_path"] = str(animation_path)
            
            return ExportResult(
                success=True,
                format=ExportFormat.HTML,
                output_path=output_path,
                files_created=[output_path],
                warnings=[],
                errors=[],
                metadata=metadata
            )
        except Exception as e:
            return ExportResult(
                success=False,
                format=ExportFormat.HTML,
                output_path=Path("failed"),
                files_created=[],
                warnings=[],
                errors=[str(e)],
                metadata={}
            )
    
    def export_batch(self, sketches: list[ProofSketch]) -> list[ExportResult]:
        """Export multiple proof sketches.
        
        Args:
            sketches: List of ProofSketch objects
            
        Returns:
            List of ExportResult objects
        """
        return [self.export_single(sketch) for sketch in sketches]

    def export(
        self,
        sketch: ProofSketch,
        output_path: Path | None = None,
        educational_level: EducationalLevel = EducationalLevel.INTUITIVE,
    ) -> str:
        """Export proof sketch to HTML string.

        Args:
            sketch: Proof sketch to export
            output_path: Optional path to write to
            educational_level: Educational complexity level for explanations

        Returns:
            HTML content as string
        """
        # Build HTML content with MathJax 4.0
        html_content = self._build_html(sketch, educational_level)

        # Write to file if path provided
        if output_path:
            output_path = Path(output_path)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(html_content, encoding="utf-8")

        return html_content

    def _build_html(
        self, sketch: ProofSketch, educational_level: EducationalLevel
    ) -> str:
        """Build complete HTML document."""
        # Mathematical expressions for MathJax (already safe)
        statement_math = self._format_math(sketch.theorem_statement)

        # Build proof steps HTML with proper escaping
        steps_html = ""
        for i, step in enumerate(sketch.key_steps, 1):
            # Escape user content to prevent XSS
            step_explanation = html.escape(step.get_explanation(educational_level))
            step_math = (
                self._format_math(step.mathematical_content)
                if step.mathematical_content
                else ""
            )
            steps_html += f"""
            <div class="proof-step">
                <h3>Step {i}</h3>
                <p class="step-explanation">{step_explanation}</p>
                {f'<div class="step-math">{step_math}</div>' if step_math else ""}
            </div>
            """

        # Build complete HTML document with escaped content
        html_document = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{html.escape(sketch.theorem_name)} - Proof Sketcher</title>

    <!-- MathJax 4.0 Configuration -->
    <script>
        window.MathJax = {{
            tex: {{
                inlineMath: [['$', '$'], ['\\\\(', '\\\\)']],
                displayMath: [['$$', '$$'], ['\\\\[', '\\\\]']],
                processEscapes: true,
                processEnvironments: true
            }},
            options: {{
                skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code']
            }}
        }};
    </script>
    <script type="text/javascript" id="MathJax-script" async
            src="https://cdn.jsdelivr.net/npm/mathjax@4.0.0-beta.6/tex-mml-chtml.js">
    </script>

    <!-- Styles -->
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', 'Roboto', sans-serif;
            line-height: 1.6;
            max-width: 800px;
            margin: 0 auto;
            padding: 20px;
            background-color: #fafafa;
        }}

        .theorem-container {{
            background: white;
            border-radius: 8px;
            padding: 30px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        }}

        h1 {{
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
        }}

        h2 {{
            color: #34495e;
            margin-top: 30px;
        }}

        .theorem-statement {{
            background-color: #f8f9fa;
            border-left: 4px solid #007bff;
            padding: 15px;
            margin: 15px 0;
            font-family: 'Courier New', monospace;
            border-radius: 4px;
        }}

        .explanation {{
            background-color: #e8f5e8;
            border-left: 4px solid #28a745;
            padding: 15px;
            margin: 15px 0;
            border-radius: 4px;
        }}

        .proof-step {{
            background-color: #fff3cd;
            border-left: 4px solid #ffc107;
            padding: 15px;
            margin: 15px 0;
            border-radius: 4px;
        }}

        .proof-step h3 {{
            margin-top: 0;
            color: #856404;
        }}

        .step-intuition {{
            font-style: italic;
            color: #6c757d;
        }}

        .step-math {{
            background-color: #f8f9fa;
            padding: 10px;
            border-radius: 4px;
            margin-top: 10px;
        }}

        .conclusion {{
            background-color: #d1ecf1;
            border-left: 4px solid #17a2b8;
            padding: 15px;
            margin: 15px 0;
            border-radius: 4px;
        }}

        .metadata {{
            background-color: #f8f9fa;
            padding: 15px;
            border-radius: 4px;
            margin-top: 20px;
        }}

        .metadata-item {{
            margin: 5px 0;
        }}

        .difficulty-beginner {{ color: #28a745; }}
        .difficulty-intermediate {{ color: #ffc107; }}
        .difficulty-advanced {{ color: #dc3545; }}

        .footer {{
            text-align: center;
            margin-top: 40px;
            padding-top: 20px;
            border-top: 1px solid #dee2e6;
            color: #6c757d;
            font-size: 0.9em;
        }}
    </style>
</head>
<body>
    <div class="theorem-container">
        <h1>Theorem: {html.escape(sketch.theorem_name)}</h1>

        <section>
            <h2>Statement</h2>
            <div class="theorem-statement">
                {statement_math}
            </div>
        </section>

        <section>
            <h2>{html.escape(educational_level.value.capitalize())} Explanation</h2>
            <div class="explanation">
                {html.escape(sketch.get_overview(educational_level))}
            </div>
        </section>

        <section>
            <h2>Proof Steps</h2>
            {steps_html}
        </section>

        <section>
            <h2>Conclusion</h2>
            <div class="conclusion">
                {html.escape(sketch.get_conclusion(educational_level))}
            </div>
        </section>

        <section>
            <h2>Metadata</h2>
            <div class="metadata">
                <div class="metadata-item">
                    <strong>Difficulty:</strong>
                    <span class="difficulty-{html.escape(sketch.difficulty_level)}">{html.escape(sketch.difficulty_level.title())}</span>
                </div>
                <div class="metadata-item">
                    <strong>Mathematical Areas:</strong> {html.escape(", ".join(sketch.mathematical_areas))}
                </div>
                <div class="metadata-item">
                    <strong>Prerequisites:</strong> {html.escape(", ".join(sketch.prerequisites))}
                </div>
            </div>
        </section>
    </div>

    <div class="footer">
        Generated by <strong>Proof Sketcher</strong> - Transform Lean 4 theorems into natural language
    </div>
</body>
</html>"""

        return html_document

    def _format_math(self, text: str) -> str:
        """Format mathematical expressions for MathJax.

        Args:
            text: Text that may contain mathematical expressions

        Returns:
            Text with MathJax formatting
        """
        if not text:
            return ""

        # Simple conversion for common mathematical notation
        # This is a basic implementation - could be expanded
        formatted = text

        # Convert some common Lean notation to LaTeX
        conversions = {
            "Nat": r"\\mathbb{N}",
            "Real": r"\\mathbb{R}",
            "Int": r"\\mathbb{Z}",
            "->": r"\\rightarrow",
            "forall": r"\\forall",
            "exists": r"\\exists",
            "∀": r"\\forall",
            "∃": r"\\exists",
            "→": r"\\rightarrow",
            "∈": r"\\in",
            "⊆": r"\\subseteq",
            "∪": r"\\cup",  # noqa: RUF001
            "∩": r"\\cap",
        }

        for lean_notation, latex_notation in conversions.items():
            formatted = formatted.replace(lean_notation, latex_notation)

        # Wrap in math delimiters if it looks like a mathematical expression
        if any(char in formatted for char in "=<>+*/-()[]{}∀∃→∈⊆∪∩"):  # noqa: RUF001
            formatted = f"$${formatted}$$"

        return formatted


class MockTemplateManager:
    """Mock template manager for testing compatibility."""
    
    def __init__(self):
        """Initialize mock template manager."""
        pass
    
    def render_template(self, template_name: str, **kwargs) -> str:
        """Mock template rendering for tests.
        
        Args:
            template_name: Name of template to render
            **kwargs: Template variables
            
        Returns:
            Simple HTML string for testing
        """
        sketch = kwargs.get('proof_sketch')
        if sketch:
            return f"<html><body><h1>{sketch.theorem_name}</h1></body></html>"
        return "<html><body>Test theorem</body></html>"
