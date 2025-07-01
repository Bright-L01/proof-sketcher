"""Direct test of Lean parser without full package import."""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

# Import only what we need
from proof_sketcher.parser.config import ParserConfig
from proof_sketcher.parser.lean_parser import LeanParser


def test_basic_parsing():
    """Test basic parsing functionality."""
    # Create parser with config that doesn't require Lean
    config = ParserConfig(
        fallback_to_regex=True,
        lean_executable="lean",  # Even if not installed
        lake_executable="lake",  # Even if not installed
    )

    parser = LeanParser(config)

    # Test with our example file
    example_file = Path("examples/lean_project/ProofSketcherExamples/Nat.lean")

    if not example_file.exists():
        print(f"Example file not found: {example_file}")
        return

    print(f"Testing parser with: {example_file}")
    print(f"Lean available: {parser.check_lean_available()}")
    print(f"Lake available: {parser.check_lake_available()}")

    result = parser.parse_file(example_file)

    print("\nParse Result:")
    print(f"  Success: {result.success}")
    print(f"  Theorems found: {len(result.theorems)}")
    print(f"  Errors: {len(result.errors)}")

    if result.theorems:
        print("\nTheorems (using regex fallback):")
        for theorem in result.theorems:
            print(f"\n  {theorem.name}")
            print(f"    Statement: {theorem.statement}")
            if theorem.proof:
                print(f"    Proof: {theorem.proof[:100]}...")
            print(f"    Line: {theorem.line_number}")

    if result.errors:
        print("\nErrors/Warnings:")
        for error in result.errors:
            print(f"  [{error.severity}] {error.message}")


def test_lean_extractor_format():
    """Show what the Lean extractor should return."""
    import json

    print("\n" + "=" * 50)
    print("Expected Lean Extractor Output Format:")
    print("=" * 50)

    example_output = {
        "name": "nat_add_comm",
        "type": "∀ (m n : Nat), m + n = n + m",
        "value": "fun m n => by induction m with | zero => simp | succ m ih => simp [add_succ, ih]",
        "docString": "Addition is commutative for natural numbers",
        "tactics": ["induction", "simp"],
        "dependencies": ["Nat.add_succ", "Nat.zero_add"],
        "isAxiom": False,
    }

    print(json.dumps(example_output, indent=2))

    print("\nThis JSON should be printed to stdout by the Lean extractor")


if __name__ == "__main__":
    print("Direct Lean Parser Test")
    print("=" * 50)

    test_basic_parsing()
    test_lean_extractor_format()
