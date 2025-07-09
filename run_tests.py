#!/usr/bin/env python3
"""
Simple test runner for proof sketcher tests.
Bypasses pytest issues and focuses on real functionality testing.
"""

import sys
import tempfile
import time
import traceback
from pathlib import Path

# Add source to path
sys.path.insert(0, ".")


def run_test(test_name, test_func):
    """Run a single test function."""
    print(f"\n{'='*60}")
    print(f"Running: {test_name}")
    print("=" * 60)

    try:
        start_time = time.time()
        test_func()
        end_time = time.time()
        print(f"✅ PASSED ({end_time - start_time:.2f}s)")
        return True
    except Exception as e:
        print(f"❌ FAILED: {e}")
        traceback.print_exc()
        return False


def test_parser_functionality():
    """Test parser core functionality."""
    from src.proof_sketcher.parser.lean_parser import LeanParser

    # Test 1: Parse valid Lean file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write("theorem test (n : Nat) : n + 0 = n := by simp")
        temp_file = Path(f.name)

    try:
        parser = LeanParser()
        result = parser.parse_file(temp_file)

        assert result.success, "Parser should succeed"
        assert len(result.theorems) == 1, "Should find one theorem"
        theorem = result.theorems[0]
        assert theorem.name == "test", f"Expected 'test', got '{theorem.name}'"
        assert theorem.statement != "", "Statement should not be empty"
        assert theorem.statement != "Unknown", "Statement should not be 'Unknown'"
        assert "n + 0 = n" in theorem.statement, "Statement should contain math"

        print(f"  ✓ Parsed theorem: {theorem.name}")
        print(f"  ✓ Statement: {theorem.statement}")

        # Test 2: Parse non-existent file
        result = parser.parse_file(Path("/nonexistent/file.lean"))
        assert not result.success, "Should fail for non-existent file"
        assert len(result.errors) > 0, "Should have errors"

        print("  ✓ Error handling works")

    finally:
        temp_file.unlink()


def test_generator_functionality():
    """Test generator core functionality."""
    from src.proof_sketcher.generator.ai_generator_fixed import FixedAIGenerator
    from src.proof_sketcher.generator.offline import OfflineGenerator
    from src.proof_sketcher.parser.models import TheoremInfo

    theorem = TheoremInfo(
        name="test_theorem",
        statement="∀ (n : Nat), n + 0 = n",
        proof="by simp",
        dependencies=[],
        docstring="Test theorem",
    )

    # Test offline generator
    offline_gen = OfflineGenerator()
    sketch = offline_gen.generate_proof_sketch(theorem)

    assert sketch.theorem_name == "test_theorem", "Name should match"
    assert (
        sketch.theorem_statement == "∀ (n : Nat), n + 0 = n"
    ), "Statement should match"
    assert len(sketch.key_steps) > 0, "Should have steps"
    assert sketch.introduction != "", "Should have introduction"
    assert sketch.conclusion != "", "Should have conclusion"

    print(f"  ✓ Offline generator works")
    print(f"  ✓ Generated {len(sketch.key_steps)} steps")

    # Test AI generator with offline fallback
    ai_gen = FixedAIGenerator(use_offline_fallback=True)
    ai_sketch = ai_gen.generate_proof_sketch(theorem)

    assert ai_sketch.theorem_name == "test_theorem", "AI name should match"
    assert (
        ai_sketch.theorem_statement == "∀ (n : Nat), n + 0 = n"
    ), "AI statement should match"
    assert len(ai_sketch.key_steps) > 0, "AI should have steps"

    print(f"  ✓ AI generator with fallback works")


def test_exporter_functionality():
    """Test exporter core functionality."""
    from src.proof_sketcher.exporter.html import HTMLExporter
    from src.proof_sketcher.exporter.markdown import MarkdownExporter
    from src.proof_sketcher.exporter.models import ExportContext, ExportOptions
    from src.proof_sketcher.generator.models import ProofSketch, ProofStep

    # Create test sketch
    sketch = ProofSketch(
        theorem_name="test_export",
        theorem_statement="∀ (n : Nat), n = n",
        introduction="This theorem shows reflexivity",
        key_steps=[
            ProofStep(
                step_number=1,
                description="Apply reflexivity",
                mathematical_content="n = n",
                tactics=["rfl"],
            )
        ],
        conclusion="Reflexivity is established",
    )

    with tempfile.TemporaryDirectory() as tmpdir:
        output_dir = Path(tmpdir)

        # Test markdown export
        options = ExportOptions(output_dir=output_dir)
        md_exporter = MarkdownExporter(options)
        context = ExportContext(
            format="markdown", output_dir=output_dir, sketches=[sketch]
        )

        result = md_exporter.export_single(sketch, context)
        assert result.success, "Markdown export should succeed"
        assert len(result.files_created) == 1, "Should create one file"

        md_file = result.files_created[0]
        content = md_file.read_text()
        assert "test_export" in content, "Should contain theorem name"
        assert "∀ (n : Nat), n = n" in content, "Should contain statement"
        assert "```lean\n\n```" not in content, "Should not have empty code blocks"

        print(f"  ✓ Markdown export works")

        # Test HTML export
        html_exporter = HTMLExporter(options)
        html_context = ExportContext(
            format="html", output_dir=output_dir, sketches=[sketch]
        )

        result = html_exporter.export_single(sketch, html_context)
        assert result.success, "HTML export should succeed"

        html_file = result.files_created[0]
        content = html_file.read_text()
        assert "test_export" in content, "HTML should contain theorem name"

        print(f"  ✓ HTML export works")


def test_integration_pipeline():
    """Test complete integration pipeline."""
    from src.proof_sketcher.exporter.markdown import MarkdownExporter
    from src.proof_sketcher.exporter.models import ExportContext, ExportOptions
    from src.proof_sketcher.generator.offline import OfflineGenerator
    from src.proof_sketcher.parser.lean_parser import LeanParser

    # Create test file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write(
            """
/-- Addition is commutative -/
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih => simp [succ_add, ih]
"""
        )
        test_file = Path(f.name)

    try:
        # Parse
        parser = LeanParser()
        parse_result = parser.parse_file(test_file)
        assert parse_result.success, "Parse should succeed"
        assert len(parse_result.theorems) == 1, "Should find one theorem"

        theorem = parse_result.theorems[0]
        assert theorem.statement != "", "Statement should not be empty"

        # Generate
        generator = OfflineGenerator()
        sketch = generator.generate_proof_sketch(theorem)
        assert (
            sketch.theorem_statement == theorem.statement
        ), "Statement should be preserved"

        # Export
        with tempfile.TemporaryDirectory() as tmpdir:
            options = ExportOptions(output_dir=Path(tmpdir))
            exporter = MarkdownExporter(options)
            context = ExportContext(
                format="markdown", output_dir=Path(tmpdir), sketches=[sketch]
            )

            result = exporter.export_single(sketch, context)
            assert result.success, "Export should succeed"

            output_file = result.files_created[0]
            content = output_file.read_text()
            assert theorem.name in content, "Should contain theorem name"
            assert theorem.statement in content, "Should contain statement"
            assert "```lean\n\n```" not in content, "Should not have empty code blocks"

            print(f"  ✓ Complete pipeline works")
            print(f"  ✓ No empty statements in output")

    finally:
        test_file.unlink()


def test_error_handling():
    """Test error handling across components."""
    from src.proof_sketcher.generator.offline import OfflineGenerator
    from src.proof_sketcher.parser.lean_parser import LeanParser
    from src.proof_sketcher.parser.models import TheoremInfo

    # Test parser with non-existent file
    parser = LeanParser()
    result = parser.parse_file(Path("/nonexistent/file.lean"))
    assert not result.success, "Should fail gracefully"
    assert len(result.errors) > 0, "Should have error messages"

    # Test generator with empty theorem
    generator = OfflineGenerator()
    empty_theorem = TheoremInfo(name="", statement="", proof="")

    # Should not crash
    sketch = generator.generate_proof_sketch(empty_theorem)
    assert sketch.theorem_name == "", "Should handle empty name"
    assert sketch.theorem_statement == "", "Should handle empty statement"
    assert len(sketch.key_steps) > 0, "Should generate some steps"

    print(f"  ✓ Error handling works")


def test_regression_empty_statements():
    """Regression test for the empty statements bug (DEBT-001)."""
    from src.proof_sketcher.exporter.markdown import MarkdownExporter
    from src.proof_sketcher.exporter.models import ExportContext, ExportOptions
    from src.proof_sketcher.generator.offline import OfflineGenerator
    from src.proof_sketcher.parser.lean_parser import LeanParser

    # Create simple test file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write("theorem simple_test : 1 + 1 = 2 := by norm_num")
        test_file = Path(f.name)

    try:
        # Parse
        parser = LeanParser()
        result = parser.parse_file(test_file)
        assert result.success, "Parse should succeed"
        theorem = result.theorems[0]

        # CRITICAL: Statement must not be empty
        assert theorem.statement != "", "Statement MUST NOT be empty"
        assert theorem.statement != "Unknown", "Statement MUST NOT be 'Unknown'"
        assert "1 + 1 = 2" in theorem.statement, "Statement should contain math"

        # Generate
        generator = OfflineGenerator()
        sketch = generator.generate_proof_sketch(theorem)
        assert (
            sketch.theorem_statement == theorem.statement
        ), "Statement must be preserved"

        # Export
        with tempfile.TemporaryDirectory() as tmpdir:
            options = ExportOptions(output_dir=Path(tmpdir))
            exporter = MarkdownExporter(options)
            context = ExportContext(
                format="markdown", output_dir=Path(tmpdir), sketches=[sketch]
            )

            result = exporter.export_single(sketch, context)
            assert result.success, "Export should succeed"

            content = result.files_created[0].read_text()

            # CRITICAL: No empty code blocks
            assert "```lean\n\n```" not in content, "MUST NOT have empty code blocks"
            assert "```lean\n\n\n```" not in content, "MUST NOT have empty code blocks"
            assert theorem.statement in content, "Statement must appear in output"

            print(f"  ✓ Empty statements bug FIXED")
            print(f"  ✓ Statement in output: {theorem.statement}")

    finally:
        test_file.unlink()


def main():
    """Run all tests."""
    print("Proof Sketcher Test Suite")
    print("=" * 60)

    tests = [
        ("Parser Functionality", test_parser_functionality),
        ("Generator Functionality", test_generator_functionality),
        ("Exporter Functionality", test_exporter_functionality),
        ("Integration Pipeline", test_integration_pipeline),
        ("Error Handling", test_error_handling),
        ("Regression: Empty Statements", test_regression_empty_statements),
    ]

    passed = 0
    failed = 0

    for test_name, test_func in tests:
        if run_test(test_name, test_func):
            passed += 1
        else:
            failed += 1

    print(f"\n{'='*60}")
    print(f"TEST SUMMARY")
    print(f"{'='*60}")
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")
    print(f"Total:  {passed + failed}")

    if failed == 0:
        print("\n🎉 ALL TESTS PASSED!")
        return 0
    else:
        print(f"\n❌ {failed} TESTS FAILED!")
        return 1


if __name__ == "__main__":
    sys.exit(main())
