#!/usr/bin/env python3
"""
Simple Performance Test - Quick validation of basic functionality
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root / "src"))

from proof_sketcher.generator.offline import OfflineGenerator
from proof_sketcher.parser.simple_parser import SimpleLeanParser


def test_basic_file_parsing():
    """Test basic file parsing performance"""
    print("Testing basic file parsing...")

    # Create a simple test file
    test_file = project_root / "test_simple.lean"
    test_file.write_text(
        """
theorem simple_test : 1 + 1 = 2 := by
  rfl

theorem add_zero (n : ℕ) : n + 0 = n := by
  rfl
"""
    )

    try:
        parser = SimpleLeanParser()
        start_time = time.time()

        result = parser.parse_file(test_file)
        parse_time = time.time() - start_time

        print(f"Parse time: {parse_time:.3f}s")
        print(f"Success: {result.success}")
        print(f"Theorems found: {len(result.theorems) if result.success else 0}")

        if result.success:
            for theorem in result.theorems:
                print(f"  - {theorem.name}")

        return result.success

    finally:
        # Cleanup
        if test_file.exists():
            test_file.unlink()


def test_university_files():
    """Test the university-scale files we created"""
    print("\nTesting university-scale files...")

    test_files = [
        "tests/data/university_scale_basic.lean",
        "tests/data/university_scale_intermediate.lean",
        "tests/data/university_scale_advanced.lean",
    ]

    parser = SimpleLeanParser()
    generator = OfflineGenerator()

    for test_file in test_files:
        file_path = project_root / test_file
        if not file_path.exists():
            print(f"Skipping {test_file} - file not found")
            continue

        print(f"\nTesting: {file_path.name}")

        start_time = time.time()
        result = parser.parse_file(file_path)
        parse_time = time.time() - start_time

        file_size_mb = file_path.stat().st_size / 1024 / 1024
        print(f"  File size: {file_size_mb:.2f} MB")
        print(f"  Parse time: {parse_time:.3f}s")
        print(f"  Success: {result.success}")

        if result.success:
            theorem_count = len(result.theorems)
            print(f"  Theorems found: {theorem_count}")

            # Test sketch generation on first few theorems
            generation_count = 0
            generation_start = time.time()

            for i, theorem in enumerate(result.theorems[:3]):  # Test first 3
                try:
                    sketch = generator.generate_proof_sketch(theorem)
                    if sketch:
                        generation_count += 1
                    print(f"    Generated sketch for: {theorem.name}")
                except Exception as e:
                    print(f"    Failed to generate sketch for {theorem.name}: {e}")

            generation_time = time.time() - generation_start
            print(f"  Generation time (3 theorems): {generation_time:.3f}s")
            print(f"  Success rate: {generation_count}/3")

            # Calculate throughput
            if parse_time > 0:
                throughput = theorem_count / parse_time
                print(f"  Parse throughput: {throughput:.1f} theorems/sec")


def main():
    print("🚀 Simple Performance Test for Proof-Sketcher")
    print("=" * 50)

    # Test 1: Basic functionality
    basic_success = test_basic_file_parsing()
    if not basic_success:
        print("❌ Basic parsing test failed")
        return False

    # Test 2: University files
    test_university_files()

    print("\n✅ Simple performance test completed")
    return True


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
