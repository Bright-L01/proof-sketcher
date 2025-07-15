"""Simple HTML exporter for MVP with MathJax 4.0 support."""

from pathlib import Path
from typing import Optional

from ..generator.models import ProofSketch


class SimpleHTMLExporter:
    """Simple HTML exporter with MathJax 4.0 support."""

    def export(self, sketch: ProofSketch, output_path: Optional[Path] = None) -> str:
        """Export proof sketch to HTML string.

        Args:
            sketch: Proof sketch to export
            output_path: Optional path to write to

        Returns:
            HTML content as string
        """
        # Build HTML content with MathJax 4.0
        html_content = self._build_html(sketch)

        # Write to file if path provided
        if output_path:
            output_path = Path(output_path)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(html_content, encoding="utf-8")

        return html_content

    def _build_html(self, sketch: ProofSketch) -> str:
        """Build complete HTML document."""
        # Mathematical expressions for MathJax
        statement_math = self._format_math(sketch.theorem_statement)
        
        # Build proof steps HTML
        steps_html = ""
        for i, step in enumerate(sketch.key_steps, 1):
            step_math = self._format_math(step.mathematical_content) if step.mathematical_content else ""
            steps_html += f"""
            <div class="proof-step">
                <h3>Step {i}: {step.description}</h3>
                <p class="step-intuition">{step.intuition}</p>
                {f'<div class="step-math">{step_math}</div>' if step_math else ''}
            </div>
            """

        # Build complete HTML document
        html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{sketch.theorem_name} - Proof Sketcher</title>
    
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
        <h1>Theorem: {sketch.theorem_name}</h1>
        
        <section>
            <h2>Statement</h2>
            <div class="theorem-statement">
                {statement_math}
            </div>
        </section>
        
        <section>
            <h2>Explanation</h2>
            <div class="explanation">
                {sketch.introduction}
            </div>
        </section>
        
        <section>
            <h2>Proof Steps</h2>
            {steps_html}
        </section>
        
        <section>
            <h2>Conclusion</h2>
            <div class="conclusion">
                {sketch.conclusion}
            </div>
        </section>
        
        <section>
            <h2>Metadata</h2>
            <div class="metadata">
                <div class="metadata-item">
                    <strong>Difficulty:</strong> 
                    <span class="difficulty-{sketch.difficulty_level}">{sketch.difficulty_level.title()}</span>
                </div>
                <div class="metadata-item">
                    <strong>Mathematical Areas:</strong> {', '.join(sketch.mathematical_areas)}
                </div>
                <div class="metadata-item">
                    <strong>Prerequisites:</strong> {', '.join(sketch.prerequisites)}
                </div>
            </div>
        </section>
    </div>
    
    <div class="footer">
        Generated by <strong>Proof Sketcher</strong> - Transform Lean 4 theorems into natural language
    </div>
</body>
</html>"""
        
        return html

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
            "∪": r"\\cup",
            "∩": r"\\cap",
        }
        
        for lean_notation, latex_notation in conversions.items():
            formatted = formatted.replace(lean_notation, latex_notation)
        
        # Wrap in math delimiters if it looks like a mathematical expression
        if any(char in formatted for char in "=<>+*/-()[]{}∀∃→∈⊆∪∩"):
            formatted = f"$${formatted}$$"
        
        return formatted