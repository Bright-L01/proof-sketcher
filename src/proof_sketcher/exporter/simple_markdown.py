"""Simple markdown exporter for MVP."""

from pathlib import Path

from ..generator.models import ProofSketch, EducationalLevel


class SimpleMarkdownExporter:
    """Minimal markdown exporter that just outputs basic markdown."""

    def export(self, sketch: ProofSketch, output_path: Path | None = None, educational_level: EducationalLevel = EducationalLevel.INTUITIVE) -> str:
        """Export proof sketch to markdown string.

        Args:
            sketch: Proof sketch to export
            output_path: Optional path to write to
            educational_level: Educational complexity level for explanations

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
            lines.append("```lean")
            lines.append(sketch.theorem_statement)
            lines.append("```")
            lines.append("")

        # Educational Overview
        overview = sketch.get_overview(educational_level)
        if overview:
            level_name = educational_level.value.capitalize()
            lines.append(f"## {level_name} Explanation")
            lines.append(overview)
            lines.append("")

        # Proof Steps
        if sketch.key_steps:
            lines.append("## Proof Steps")
            for i, step in enumerate(sketch.key_steps, 1):
                step_explanation = step.get_explanation(educational_level)
                lines.append(f"### Step {i}")
                lines.append(step_explanation)
                lines.append("")

        # Conclusion
        conclusion = sketch.get_conclusion(educational_level)
        if conclusion:
            lines.append("## Conclusion")
            lines.append(conclusion)
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
