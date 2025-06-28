#!/usr/bin/env python3
"""Basic usage example for Proof Sketcher."""

from pathlib import Path

from proof_sketcher.exporter import ExportOptions, HTMLExporter
from proof_sketcher.generator import ClaudeGenerator
from proof_sketcher.parser import LeanParser


def main():
    """Demonstrate basic Proof Sketcher usage."""
    # Parse a Lean file
    parser = LeanParser()
    result = parser.parse_file(Path("examples/simple_proof.lean"))

    if result.errors:
        print("Parse errors:")
        for error in result.errors:
            print(f"  - {error}")

    if not result.theorems:
        print("No theorems found!")
        return

    print(f"Found {len(result.theorems)} theorems")

    # Generate natural language explanations
    generator = ClaudeGenerator()
    sketches = []

    for theorem in result.theorems:
        print(f"\nProcessing: {theorem.name}")
        try:
            sketch = generator.generate_proof_sketch(theorem)
            sketches.append(sketch)

            print(f"  Statement: {theorem.statement}")
            print(f"  Explanation: {sketch.explanation[:100]}...")
            print(f"  Steps: {len(sketch.steps)}")
        except Exception as e:
            print(f"  Error: {e}")

    # Export to HTML
    if sketches:
        print("\nExporting to HTML...")
        options = ExportOptions(
            output_dir=Path("output"),
            create_index=True
        )

        exporter = HTMLExporter(options)
        result = exporter.export_multiple(sketches)

        if result.success:
            print(f"✓ Exported {len(result.files_created)} files")
            print(f"✓ Output saved to: {result.output_path}")
        else:
            print(f"✗ Export failed: {result.errors}")


if __name__ == "__main__":
    main()
