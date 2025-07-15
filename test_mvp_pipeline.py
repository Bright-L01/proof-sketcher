#!/usr/bin/env python3
"""MVP Integration Test - Proves the basic pipeline works."""

import sys
from pathlib import Path

# Add src to Python path
sys.path.insert(0, str(Path(__file__).parent / "src"))


def test_minimal_pipeline():
    """Test the minimal pipeline: Lean → Parse → Generate → Export."""

    print("=" * 60)
    print("MVP PIPELINE TEST")
    print("=" * 60)

    # Step 1: Create a simple Lean file
    print("\n1. Creating test Lean file...")
    lean_content = """
-- Simple theorem about natural numbers
theorem add_zero (n : Nat) : n + 0 = n := by
  simp

-- Commutativity of addition
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp [Nat.zero_add]
  | succ a ih => rw [Nat.succ_add, ih, Nat.add_succ]

-- A simple lemma
lemma mul_one (n : Nat) : n * 1 = n := by
  simp
"""

    test_file = Path("test_theorem.lean")
    test_file.write_text(lean_content)
    print(f"   ✓ Created {test_file}")

    # Step 2: Parse the file
    print("\n2. Parsing Lean file...")
    try:
        from proof_sketcher.parser import LeanParser

        parser = LeanParser()
        result = parser.parse_file(test_file)

        if not result.success:
            print(f"   ✗ Parsing failed: {result.errors}")
            return False

        print(f"   ✓ Parsing successful! Found {len(result.theorems)} theorems:")
        for theorem in result.theorems:
            print(f"      - {theorem.name}: {theorem.statement}")

    except Exception as e:
        print(f"   ✗ Parser error: {e}")
        return False

    # Step 3: Generate offline explanation
    print("\n3. Generating explanations...")
    try:
        from proof_sketcher.generator import AIGenerator

        generator = AIGenerator()
        sketches = []

        for theorem in result.theorems:
            print(f"   - Generating for {theorem.name}...")
            sketch = generator.generate_offline(theorem)
            sketches.append(sketch)
            print(f"     ✓ Generated: {sketch.introduction[:60]}...")

    except Exception as e:
        print(f"   ✗ Generator error: {e}")
        return False

    # Step 4: Export to markdown
    print("\n4. Exporting to markdown...")
    try:
        from proof_sketcher.exporter import MarkdownExporter

        exporter = MarkdownExporter()
        output_dir = Path("output")
        output_dir.mkdir(exist_ok=True)

        for sketch in sketches:
            output_file = output_dir / f"{sketch.theorem_name}.md"
            content = exporter.export(sketch, output_file)
            print(f"   ✓ Exported {sketch.theorem_name} to {output_file}")

    except Exception as e:
        print(f"   ✗ Exporter error: {e}")
        return False

    # Step 5: Verify output
    print("\n5. Verifying output...")
    expected_files = ["add_zero.md", "add_comm.md", "mul_one.md"]
    all_exist = True

    for filename in expected_files:
        file_path = output_dir / filename
        if file_path.exists():
            size = file_path.stat().st_size
            print(f"   ✓ {filename} exists ({size} bytes)")

            # Check content
            content = file_path.read_text()
            if "# Theorem:" in content and "## Statement" in content:
                print(f"     ✓ Content looks valid")
            else:
                print(f"     ✗ Content missing expected sections")
                all_exist = False
        else:
            print(f"   ✗ {filename} missing")
            all_exist = False

    # Clean up
    print("\n6. Cleaning up...")
    test_file.unlink()
    print(f"   ✓ Removed {test_file}")

    # Summary
    print("\n" + "=" * 60)
    if all_exist:
        print("✅ MVP PIPELINE TEST PASSED!")
        print("\nThe basic pipeline works:")
        print("  Lean file → Parser → Generator → Markdown")
        return True
    else:
        print("❌ MVP PIPELINE TEST FAILED!")
        print("\nSome components are not working correctly.")
        return False


def show_sample_output():
    """Display a sample of the generated output."""
    print("\n" + "=" * 60)
    print("SAMPLE OUTPUT")
    print("=" * 60)

    sample_file = Path("output/add_zero.md")
    if sample_file.exists():
        content = sample_file.read_text()
        lines = content.split("\n")

        # Show first 20 lines
        print("\nFirst 20 lines of add_zero.md:")
        print("-" * 40)
        for line in lines[:20]:
            print(line)
        print("...")
    else:
        print("No sample output found.")


if __name__ == "__main__":
    # Run the test
    success = test_minimal_pipeline()

    if success:
        show_sample_output()

    # Exit with appropriate code
    sys.exit(0 if success else 1)
