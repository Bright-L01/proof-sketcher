"""Simple markdown exporter for MVP."""

from pathlib import Path
from typing import Optional

from ..generator.models import ProofSketch


class SimpleMarkdownExporter:
    """Minimal markdown exporter that just outputs basic markdown."""

    def export(self, sketch: ProofSketch, output_path: Optional[Path] = None) -> str:
        """Export proof sketch to markdown string.

        Args:
            sketch: Proof sketch to export
            output_path: Optional path to write to

        Returns:
            Markdown content as string
        """
        # Build markdown content
        lines = []

        # Title
        lines.append(f"# Theorem: {sketch.theorem_name}")
        lines.append("")

        # Statement
        if sketch.theorem_statement:
            lines.append("## Statement")
            lines.append(f"```lean")
            lines.append(sketch.theorem_statement)
            lines.append("```")
            lines.append("")

        # Introduction
        if sketch.introduction:
            lines.append("## Explanation")
            lines.append(sketch.introduction)
            lines.append("")

        # Key Steps
        if sketch.key_steps:
            lines.append("## Proof Steps")
            for i, step in enumerate(sketch.key_steps, 1):
                lines.append(f"### Step {i}: {step.description}")
                if step.intuition:
                    lines.append(step.intuition)
                lines.append("")

        # Conclusion
        if sketch.conclusion:
            lines.append("## Conclusion")
            lines.append(sketch.conclusion)
            lines.append("")

        # Difficulty and Areas
        if sketch.difficulty_level:
            lines.append("## Metadata")
            lines.append(f"- **Difficulty**: {sketch.difficulty_level}")
            if sketch.mathematical_areas:
                lines.append(f"- **Areas**: {', '.join(sketch.mathematical_areas)}")
            if sketch.prerequisites:
                lines.append(f"- **Prerequisites**: {', '.join(sketch.prerequisites)}")
            lines.append("")

        # Join lines
        content = "\n".join(lines)

        # Write to file if path provided
        if output_path:
            output_path = Path(output_path)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(content, encoding="utf-8")

        return content
