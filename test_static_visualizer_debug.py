#!/usr/bin/env python3
"""
Debug static visualizer issues.
"""

from src.proof_sketcher.animator.static_fallback import StaticVisualizer


def debug_static_visualizer():
    """Debug the static visualizer."""

    print("🔍 Debugging Static Visualizer")
    print("=" * 40)

    # Initialize visualizer
    visualizer = StaticVisualizer()

    print(f"Available: {visualizer.is_available()}")
    print(f"Supported formats: {visualizer.get_supported_formats()}")
    print()

    # Create test data
    theorem = {"name": "Test Theorem", "statement": "2 + 2 = 4"}

    sketch = {
        "key_steps": [
            {
                "description": "Start with 2 + 2",
                "mathematical_content": "2 + 2",
                "tactics": ["simp"],
            },
            {
                "description": "Evaluate to get 4",
                "mathematical_content": "4",
                "tactics": ["rfl"],
            },
        ]
    }

    # Try creating diagram with debug info
    print("🎨 Creating proof diagram...")
    try:
        success = visualizer.create_proof_diagram(
            theorem, sketch, "debug_proof_diagram.png"
        )

        print(f"Success: {success}")

        from pathlib import Path

        if Path("debug_proof_diagram.png").exists():
            size = Path("debug_proof_diagram.png").stat().st_size
            print(f"File size: {size} bytes")
        else:
            print("File not created")

    except Exception as e:
        print(f"Error: {e}")
        import traceback

        traceback.print_exc()


if __name__ == "__main__":
    debug_static_visualizer()
