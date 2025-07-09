#!/usr/bin/env python3
"""
Test script for the Lean extractor integration.
"""

import tempfile
from pathlib import Path

from src.proof_sketcher.parser.lean_extractor import LeanExtractor


def test_lean_extractor():
    """Test the Lean extractor with a simple example."""

    # Create a simple test file
    test_content = """-- Simple test theorems
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem simple_example : 1 + 1 = 2 := rfl

theorem identity_function (α : Type) (x : α) : x = x := rfl
"""

    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write(test_content)
        test_file = Path(f.name)

    try:
        # Initialize extractor
        extractor = LeanExtractor()

        print("🔍 Extractor Status:")
        version_info = extractor.get_version_info()
        for key, value in version_info.items():
            print(f"  {key}: {value}")

        print(f"\n📁 Test file: {test_file}")

        if not extractor.is_available():
            print(
                "⚠️  Extractor not available - this is expected as we don't have a built Lean extractor yet"
            )
            print("   The parser will fall back to the regex-based method")
            return

        # Try to extract all theorems
        print("\n🔎 Extracting all theorems...")
        try:
            theorems = extractor.extract_file(test_file)
            print(f"Found {len(theorems)} theorems:")
            for thm in theorems:
                print(
                    f"  - {thm.get('name', 'unknown')}: {thm.get('type', 'unknown type')}"
                )
        except Exception as e:
            print(f"❌ Failed to extract all theorems: {e}")

        # Try to extract specific theorem
        print("\n🎯 Extracting specific theorem 'add_zero'...")
        try:
            theorem = extractor.extract_theorem(test_file, "add_zero")
            if theorem:
                print(f"✅ Successfully extracted: {theorem['name']}")
                print(f"   Type: {theorem['type']}")
                print(f"   Value: {theorem.get('value', 'N/A')}")
            else:
                print("❌ Theorem not found")
        except Exception as e:
            print(f"❌ Failed to extract specific theorem: {e}")

        # Test conversion to TheoremInfo
        print("\n🔄 Testing conversion to TheoremInfo...")
        try:
            theorem_info = extractor.extract_to_theorem_info(test_file, "add_zero")
            if theorem_info:
                print(f"✅ Converted to TheoremInfo: {theorem_info.name}")
                print(f"   Statement: {theorem_info.statement}")
            else:
                print("❌ Conversion failed")
        except Exception as e:
            print(f"❌ Conversion error: {e}")

    finally:
        # Clean up
        test_file.unlink()
        print(f"\n🧹 Cleaned up test file")


if __name__ == "__main__":
    test_lean_extractor()
