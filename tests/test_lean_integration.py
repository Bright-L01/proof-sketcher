"""Test script for verifying Lean integration works."""

import json
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from proof_sketcher.parser.lean_parser import LeanParser


def test_basic_parsing():
    """Test basic parsing functionality."""
    parser = LeanParser()

    # Test with our example files
    example_file = Path("examples/lean_project/ProofSketcherExamples/Nat.lean")

    if not example_file.exists():
        print(f"Example file not found: {example_file}")
        return

    print(f"Testing parser with: {example_file}")
    result = parser.parse_file(example_file)

    print("\nParse Result:")
    print(f"  Success: {result.success}")
    print(f"  Theorems found: {len(result.theorems)}")
    print(f"  Errors: {len(result.errors)}")

    if result.theorems:
        print("\nTheorems:")
        for theorem in result.theorems:
            print(f"  - {theorem.name}")
            print(f"    Statement: {theorem.statement[:80]}...")
            if theorem.dependencies:
                print(f"    Dependencies: {', '.join(theorem.dependencies)}")
            if theorem.tactics:
                print(f"    Tactics: {', '.join(theorem.tactics)}")

    if result.errors:
        print("\nErrors:")
        for error in result.errors:
            print(f"  - {error.message}")


def test_extractor_output():
    """Test what the extractor should output."""
    # Mock extractor output
    extractor_output = {
        "name": "nat_add_comm",
        "type": "∀ (m n : Nat), m + n = n + m",
        "value": "proof by induction",
        "docString": "Addition is commutative for natural numbers",
        "tactics": ["induction", "simp", "add_succ"],
        "dependencies": ["Nat.add", "Nat.add_succ", "Nat.zero_add"],
        "isAxiom": False,
    }

    print("\nExpected Extractor Output Format:")
    print(json.dumps(extractor_output, indent=2))


if __name__ == "__main__":
    print("Testing Lean Integration")
    print("=" * 50)

    test_basic_parsing()
    test_extractor_output()
