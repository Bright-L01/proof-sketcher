#!/usr/bin/env python3
"""Quick test script for doc-gen4 integration."""

import json
import tempfile
from pathlib import Path

from proof_sketcher.docgen4 import (
    DocGen4Declaration,
    DocGen4Enhancer,
    DocGen4Integration,
    DocGen4Parser,
    EnhancedDeclaration,
)


def test_parser():
    """Test the doc-gen4 parser."""
    print("Testing DocGen4Parser...")

    # Create test data
    test_declarations = [
        {
            "name": "Nat.add_comm",
            "kind": "theorem",
            "type": "∀ (a b : ℕ), a + b = b + a",
            "doc": "Addition of natural numbers is commutative",
            "line": 42,
        },
        {
            "name": "Nat.zero_add",
            "kind": "theorem",
            "type": "∀ (n : ℕ), 0 + n = n",
            "doc": "Zero is left identity for addition",
            "line": 50,
        },
    ]

    # Write test file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
        json.dump(test_declarations, f)
        test_file = Path(f.name)

    try:
        parser = DocGen4Parser()
        declarations = parser.parse_declarations_json(test_file)

        print(f"✓ Parsed {len(declarations)} declarations")
        for decl in declarations:
            print(f"  - {decl.name}: {decl.kind}")

        # Test filtering
        theorems = [d for d in declarations if d.is_theorem]
        print(f"✓ Found {len(theorems)} theorems")

    finally:
        test_file.unlink()


def test_enhancer():
    """Test the HTML enhancer."""
    print("\nTesting DocGen4Enhancer...")

    # Create test HTML
    test_html = """
    <!DOCTYPE html>
    <html>
    <head><title>Test</title></head>
    <body>
        <div class="decl" id="Nat.add_comm">
            <div class="decl_header">
                <span class="decl_kind">theorem</span>
                <span class="decl_name">Nat.add_comm</span>
                <span class="decl_type">∀ (a b : ℕ), a + b = b + a</span>
            </div>
        </div>
    </body>
    </html>
    """

    with tempfile.TemporaryDirectory() as tmpdir:
        html_path = Path(tmpdir) / "test.html"
        html_path.write_text(test_html)

        # Create enhanced declaration
        decl = DocGen4Declaration(
            name="Nat.add_comm", kind="theorem", type="∀ (a b : ℕ), a + b = b + a"
        )
        enhanced = EnhancedDeclaration(
            declaration=decl,
            explanation="This theorem states that addition is commutative for natural numbers.",
        )

        # Enhance HTML
        enhancer = DocGen4Enhancer()
        enhancer.enhance_html_file(html_path, {"Nat.add_comm": enhanced}, backup=False)

        # Check result
        result = html_path.read_text()
        assert "proof-sketcher-explanation" in result
        assert "Natural Language Explanation" in result
        assert "commutative" in result

        print("✓ HTML enhanced successfully")
        print(f"✓ Added {enhancer.enhanced_count} explanations")


def test_integration():
    """Test the full integration pipeline."""
    print("\nTesting DocGen4Integration...")

    integration = DocGen4Integration()
    print("✓ Integration module initialized")

    # Test offline explanation generation
    decl = DocGen4Declaration(
        name="test_theorem", kind="theorem", type="P → Q", doc="A test theorem"
    )

    explanation = integration._generate_offline_explanation(decl)
    print(f"Generated explanation: {explanation[:100]}...")
    assert "theorem" in explanation.lower()
    assert (
        "natural language" in explanation.lower()
        or "explanation" in explanation.lower()
    )

    print("✓ Offline explanation generation works")


if __name__ == "__main__":
    print("Running doc-gen4 integration tests...\n")

    try:
        test_parser()
        test_enhancer()
        test_integration()

        print("\n✅ All tests passed!")

    except Exception as e:
        print(f"\n❌ Test failed: {e}")
        import traceback

        traceback.print_exc()
