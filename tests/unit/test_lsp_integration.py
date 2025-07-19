"""Test script for LSP integration and Phase 9 semantic analysis features.

DEPRECATED: These tests are for the non-functional LSP integration.
The LSP client extracts 0 theorems and is 1000x slower than SimpleLeanParser.
These tests are kept for historical reference only.

This test was intended to verify:
1. LSP client functionality and semantic analysis
2. Hybrid parser operation with fallback
3. Enhanced theorem information extraction
4. Educational content generation improvements
5. Backward compatibility with existing code

However, the LSP integration never worked properly.
Use SimpleLeanParser for all parsing needs.
"""

import asyncio
import logging
import tempfile
from pathlib import Path

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")

# Test Lean code with various complexity levels
LEAN_TEST_CONTENT = """
-- Basic theorem (beginner level)
theorem add_zero (n : Nat) : n + 0 = n := by simp

-- Intermediate theorem with cases
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_succ, ih, Nat.succ_add]

-- Advanced theorem with complex proof
theorem dvd_antisymm {a b : Nat} (h1 : a ∣ b) (h2 : b ∣ a) (ha : 0 < a) : a = b := by
  cases' h1 with k hk
  cases' h2 with l hl
  rw [hk] at hl
  rw [← mul_assoc] at hl
  have : k * l = 1 := Nat.eq_one_of_mul_one_left hl ha
  cases' Nat.eq_one_of_mul_eq_one this with hk' hl'
  rw [hk', one_mul] at hk
  exact hk.symm

-- Simple lemma
lemma zero_add (n : Nat) : 0 + n = n := by
  simp [Nat.zero_add]
"""


async def test_lsp_client():
    """Test the LSP client directly."""
    print("🔍 Testing LSP Client...")

    from proof_sketcher.parser.lsp_client import LeanLSPClient

    # Create temporary Lean file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write(LEAN_TEST_CONTENT)
        temp_path = Path(f.name)

    try:
        client = LeanLSPClient()

        # Test LSP parsing
        result = await client.parse_file(temp_path)

        print(f"✅ LSP parsing success: {result.success}")
        print(f"📊 Found {len(result.theorems)} theorems")
        print(f"⏱️  Parse time: {result.parse_time_ms:.1f}ms")
        print(f"🔧 Metadata: {result.metadata}")

        # Analyze first theorem if available
        if result.theorems:
            theorem = result.theorems[0]
            print(f"\n📖 First theorem: {theorem.name}")
            print(f"📝 Statement: {theorem.statement}")
            print(f"🧮 Complexity score: {theorem.complexity_score}")
            print(f"🔨 Proof method: {theorem.proof_method}")
            print(f"🧠 Mathematical entities: {theorem.mathematical_entities}")
            print(f"🎯 Tactic sequence: {[t.name for t in theorem.tactic_sequence]}")

        return result.success

    except Exception as e:
        print(f"❌ LSP test failed: {e}")
        return False
    finally:
        temp_path.unlink()


async def test_hybrid_parser():
    """Test the hybrid parser with both LSP and fallback modes."""
    print("\n🔄 Testing Hybrid Parser...")

    from proof_sketcher.parser import SimpleLeanParser

    # Create temporary Lean file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write(LEAN_TEST_CONTENT)
        temp_path = Path(f.name)

    try:
        parser = SimpleLeanParser()

        # Check parser status
        status = await parser.get_parser_status()
        print(f"📋 Parser status: {status}")

        # Test parsing
        result = await parser.parse_file(temp_path)

        print(f"✅ Hybrid parsing success: {result.success}")
        if result.metadata:
            print(f"📁 File path: {result.metadata.file_path}")
            print(f"📊 File size: {result.metadata.file_size} bytes")
            print(f"🔢 Total lines: {result.metadata.total_lines}")
            print(f"🔧 Lean version: {result.metadata.lean_version}")
        else:
            print("🔧 No metadata available")

        if result.theorems:
            print(f"📊 Found {len(result.theorems)} theorems")

            # Analyze theorem complexity distribution
            complexities = [t.complexity_score for t in result.theorems]
            avg_complexity = sum(complexities) / len(complexities)
            print(f"📈 Average complexity: {avg_complexity:.2f}")

            # Show proof methods
            methods = [t.proof_method for t in result.theorems]
            print(f"🔨 Proof methods: {set(methods)}")

        return result.success

    except Exception as e:
        print(f"❌ Hybrid parser test failed: {e}")
        return False
    finally:
        temp_path.unlink()


def test_backward_compatibility():
    """Test that existing code still works with new parser."""
    print("\n🔄 Testing Backward Compatibility...")

    try:
        # This should work exactly as before
        from proof_sketcher.exporter import MarkdownBaseExporter
        from proof_sketcher.generator import SimpleGenerator
        from proof_sketcher.parser import SimpleLeanParser

        # Create temporary Lean file
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write("theorem test_theorem (n : Nat) : n + 0 = n := by simp")
            temp_path = Path(f.name)

        try:
            # Test the old synchronous interface
            parser = SimpleLeanParser()
            result = parser.parse_file_sync(temp_path)

            print(f"✅ Sync parsing works: {result.success}")

            if result.success and result.theorems:
                # Test generation
                generator = SimpleGenerator()
                sketch = generator.generate_offline(result.theorems[0])

                print(f"✅ Generation works: {sketch.theorem_name}")

                # Test export
                exporter = MarkdownBaseExporter()
                markdown = exporter.export(sketch)

                print(f"✅ Export works: {len(markdown)} chars")
                print("✅ Full pipeline compatibility confirmed")

                return True
            else:
                print("❌ No theorems found in compatibility test")
                return False

        finally:
            temp_path.unlink()

    except Exception as e:
        print(f"❌ Backward compatibility test failed: {e}")
        return False


def test_educational_enhancement():
    """Test the educational content enhancement features."""
    print("\n📚 Testing Educational Enhancement...")

    try:
        from proof_sketcher.generator import SimpleGenerator
        from proof_sketcher.parser import SimpleLeanParser

        # Create test theorem with various complexity levels
        content = """
        -- Beginner: Simple simp proof
        theorem easy_theorem (n : Nat) : n + 0 = n := by simp

        -- Intermediate: Induction proof
        theorem medium_theorem (n : Nat) : 0 + n = n := by
          induction n with
          | zero => rfl
          | succ n ih => rw [Nat.add_succ, ih]

        -- Advanced: Complex proof with multiple tactics
        theorem hard_theorem (a b c : Nat) : a + b + c = c + b + a := by
          rw [Nat.add_assoc, Nat.add_comm a, Nat.add_assoc, Nat.add_comm b]
        """

        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            temp_path = Path(f.name)

        try:
            parser = SimpleLeanParser()
            result = parser.parse_file_sync(temp_path)

            if result.success:
                print(
                    f"📊 Analyzed {len(result.theorems)} theorems for educational content"
                )

                # Test complexity scoring
                for i, theorem in enumerate(result.theorems):
                    print(f"  {i + 1}. {theorem.name}")
                    print(f"     Complexity: {theorem.complexity_score:.2f}")
                    print(f"     Method: {theorem.proof_method}")
                    print(f"     Entities: {theorem.mathematical_entities}")

                    # Generate educational content
                    generator = SimpleGenerator()
                    sketch = generator.generate_offline(theorem)

                    print(f"     Difficulty: {sketch.difficulty_level}")
                    print(f"     Areas: {sketch.mathematical_areas}")
                    print(f"     Prerequisites: {sketch.prerequisites}")
                    print()

                print("✅ Educational enhancement working correctly")
                return True
            else:
                print("❌ Failed to parse theorems for educational test")
                return False

        finally:
            temp_path.unlink()

    except Exception as e:
        print(f"❌ Educational enhancement test failed: {e}")
        return False


async def run_all_tests():
    """Run all tests and report results."""
    print("🚀 Starting Phase 9 LSP Integration Tests")
    print("=" * 50)

    tests = [
        ("LSP Client", test_lsp_client()),
        ("Hybrid Parser", test_hybrid_parser()),
        ("Backward Compatibility", test_backward_compatibility()),
        ("Educational Enhancement", test_educational_enhancement()),
    ]

    results = []
    for name, test in tests:
        print(f"\n{'=' * 20} {name} {'=' * 20}")
        try:
            if asyncio.iscoroutine(test):
                result = await test
            else:
                result = test
            results.append((name, result))
        except Exception as e:
            print(f"❌ Test {name} crashed: {e}")
            results.append((name, False))

    # Summary
    print("\n" + "=" * 50)
    print("📋 TEST SUMMARY")
    print("=" * 50)

    passed = 0
    for name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status}: {name}")
        if result:
            passed += 1

    print(f"\n📊 Results: {passed}/{len(results)} tests passed")

    if passed == len(results):
        print("🎉 Phase 9 LSP Integration: ALL TESTS PASSED!")
        print("🚀 Ready for Phase 9 completion and cleanup")
    else:
        print("⚠️  Some tests failed - review implementation")

    return passed == len(results)


if __name__ == "__main__":
    success = asyncio.run(run_all_tests())
    exit(0 if success else 1)
