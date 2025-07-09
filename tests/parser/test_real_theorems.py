"""
Test parsing real Lean theorems to ensure parser works correctly.
This is the critical test that currently fails - empty statements.
"""

import pytest
from pathlib import Path
from src.proof_sketcher.parser.lean_parser import LeanParser
from src.proof_sketcher.parser.models import TheoremInfo, ParseResult

# Real Lean theorem test cases
REAL_LEAN_THEOREMS = [
    {
        "name": "simple_theorem",
        "content": "theorem nat_add_comm (a b : Nat) : a + b = b + a := by simp",
        "expected": {
            "name": "nat_add_comm",
            "statement_contains": ["a + b = b + a", "Nat"],
            "params": ["a", "b"],
            "has_proof": True
        }
    },
    {
        "name": "with_docstring",
        "content": '''
/-- Multiplication distributes over addition -/
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => simp
  | succ a ih => simp [succ_mul, ih, add_assoc]
''',
        "expected": {
            "name": "mul_add",
            "statement_contains": ["a * (b + c) = a * b + a * c", "Nat"],
            "docstring": "Multiplication distributes over addition",
            "params": ["a", "b", "c"]
        }
    },
    {
        "name": "simple_equality",
        "content": "theorem zero_add (n : Nat) : 0 + n = n := by simp",
        "expected": {
            "name": "zero_add",
            "statement_contains": ["0 + n = n", "Nat"],
            "params": ["n"]
        }
    },
    {
        "name": "lemma_type",
        "content": "lemma succ_add (n m : Nat) : (n + 1) + m = n + (m + 1) := by rw [add_assoc]",
        "expected": {
            "name": "succ_add",
            "statement_contains": ["(n + 1) + m = n + (m + 1)", "Nat"],
            "params": ["n", "m"]
        }
    },
    {
        "name": "complex_proof",
        "content": '''
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => simp
  | succ a ih => 
    simp [succ_add]
    rw [ih]
''',
        "expected": {
            "name": "add_assoc",
            "statement_contains": ["(a + b) + c = a + (b + c)", "Nat"],
            "params": ["a", "b", "c"]
        }
    }
]

@pytest.fixture
def parser():
    """Create a parser instance for testing."""
    return LeanParser()

@pytest.fixture
def tmp_lean_file(tmp_path):
    """Create a temporary Lean file for testing."""
    def _create_file(content: str) -> Path:
        lean_file = tmp_path / "test.lean"
        lean_file.write_text(content)
        return lean_file
    return _create_file

class TestRealTheoremParsing:
    """Test parsing real Lean theorems."""
    
    @pytest.mark.parametrize("theorem_data", REAL_LEAN_THEOREMS)
    def test_parse_real_theorem(self, theorem_data, parser, tmp_lean_file):
        """Test parsing real Lean theorems."""
        # Create temporary file with theorem
        lean_file = tmp_lean_file(theorem_data["content"])
        
        # Parse the file
        result = parser.parse_file(lean_file)
        
        # Basic result checks
        assert isinstance(result, ParseResult)
        assert result.success, f"Parse failed: {result.errors}"
        
        # Should find exactly one theorem
        assert len(result.theorems) == 1, f"Expected 1 theorem, got {len(result.theorems)}"
        theorem = result.theorems[0]
        
        # Check theorem structure
        assert isinstance(theorem, TheoremInfo)
        
        # CRITICAL: Statement must not be empty!
        assert theorem.statement != "", f"Statement is empty for theorem {theorem.name}"
        assert theorem.statement != "Unknown", f"Statement is 'Unknown' for theorem {theorem.name}"
        assert theorem.statement is not None, f"Statement is None for theorem {theorem.name}"
        
        # Check expected values
        expected = theorem_data["expected"]
        
        # Name should match
        assert theorem.name == expected["name"], f"Name mismatch: expected {expected['name']}, got {theorem.name}"
        
        # Statement should contain expected text
        statement_lower = theorem.statement.lower()
        for expected_text in expected["statement_contains"]:
            assert expected_text.lower() in statement_lower, f"Statement '{theorem.statement}' should contain '{expected_text}'"
        
        # Check docstring if expected
        if "docstring" in expected:
            assert theorem.docstring is not None, "Expected docstring but got None"
            assert expected["docstring"] in theorem.docstring, f"Docstring '{theorem.docstring}' should contain '{expected['docstring']}'"
        
        # Check proof if expected
        if expected.get("has_proof", False):
            assert theorem.proof is not None, "Expected proof but got None"
            assert len(theorem.proof.strip()) > 0, "Proof should not be empty"
        
        # Print for debugging
        print(f"\n=== Theorem: {theorem.name} ===")
        print(f"Statement: {theorem.statement}")
        print(f"Proof: {theorem.proof}")
        print(f"Docstring: {theorem.docstring}")
        print(f"Dependencies: {theorem.dependencies}")
    
    def test_empty_file(self, parser, tmp_lean_file):
        """Parser should handle empty files gracefully."""
        lean_file = tmp_lean_file("")
        result = parser.parse_file(lean_file)
        
        assert isinstance(result, ParseResult)
        assert result.success
        assert len(result.theorems) == 0
        assert len(result.errors) == 0
    
    def test_comment_only_file(self, parser, tmp_lean_file):
        """Parser should handle files with only comments."""
        content = """
-- This is a comment
/-- This is a doc comment -/
-- Another comment
"""
        lean_file = tmp_lean_file(content)
        result = parser.parse_file(lean_file)
        
        assert isinstance(result, ParseResult)
        assert result.success
        assert len(result.theorems) == 0
    
    def test_multiple_theorems(self, parser, tmp_lean_file):
        """Parser should handle multiple theorems in one file."""
        content = """
theorem first_theorem (n : Nat) : n + 0 = n := by simp

theorem second_theorem (a b : Nat) : a + b = b + a := by simp
"""
        lean_file = tmp_lean_file(content)
        result = parser.parse_file(lean_file)
        
        assert isinstance(result, ParseResult)
        assert result.success
        assert len(result.theorems) == 2
        
        # Check both theorems
        theorem_names = [t.name for t in result.theorems]
        assert "first_theorem" in theorem_names
        assert "second_theorem" in theorem_names
        
        # Both should have non-empty statements
        for theorem in result.theorems:
            assert theorem.statement != ""
            assert theorem.statement != "Unknown"
            assert theorem.statement is not None
    
    def test_malformed_theorem(self, parser, tmp_lean_file):
        """Parser should handle malformed theorems gracefully."""
        content = """
theorem broken_theorem  -- Missing everything
theorem incomplete : -- Missing proof
theorem another_broken (n : Nat) -- Missing type and proof
"""
        lean_file = tmp_lean_file(content)
        result = parser.parse_file(lean_file)
        
        assert isinstance(result, ParseResult)
        # Should either succeed with partial results or fail gracefully
        if result.success:
            # If it succeeds, any found theorems should have proper structure
            for theorem in result.theorems:
                assert theorem.name != ""
                assert theorem.statement != ""
        else:
            # If it fails, should have error messages
            assert len(result.errors) > 0
    
    def test_theorem_with_imports(self, parser, tmp_lean_file):
        """Parser should handle theorems with imports."""
        content = """
import Mathlib.Data.Nat.Basic

theorem with_imports (n : Nat) : n + 0 = n := by simp
"""
        lean_file = tmp_lean_file(content)
        result = parser.parse_file(lean_file)
        
        assert isinstance(result, ParseResult)
        assert result.success
        assert len(result.theorems) == 1
        
        theorem = result.theorems[0]
        assert theorem.name == "with_imports"
        assert theorem.statement != ""
        assert theorem.statement != "Unknown"
    
    def test_nonexistent_file(self, parser):
        """Parser should handle non-existent files gracefully."""
        nonexistent = Path("/nonexistent/file.lean")
        result = parser.parse_file(nonexistent)
        
        assert isinstance(result, ParseResult)
        assert not result.success
        assert len(result.errors) > 0
        assert "not found" in result.errors[0].message.lower()
    
    def test_non_lean_file(self, parser, tmp_path):
        """Parser should reject non-Lean files."""
        py_file = tmp_path / "test.py"
        py_file.write_text("print('hello')")
        
        result = parser.parse_file(py_file)
        
        assert isinstance(result, ParseResult)
        assert not result.success
        assert len(result.errors) > 0
        assert "not a lean file" in result.errors[0].message.lower()


class TestParserDiagnostics:
    """Test parser diagnostics and debugging."""
    
    def test_basic_parsing_fallback(self, parser, tmp_lean_file):
        """Test that basic parsing fallback works when Lean is not available."""
        content = "theorem simple (n : Nat) : n + 0 = n := by simp"
        lean_file = tmp_lean_file(content)
        
        # Force basic parsing by making Lean unavailable
        parser.config.lean_executable = "/nonexistent/lean"
        
        result = parser.parse_file(lean_file)
        
        assert isinstance(result, ParseResult)
        # Should either succeed with basic parsing or fail gracefully
        if result.success:
            assert len(result.theorems) == 1
            theorem = result.theorems[0]
            assert theorem.name == "simple"
            assert theorem.statement != ""
            print(f"Basic parsing result: {theorem.statement}")
        else:
            print(f"Basic parsing failed: {result.errors}")
    
    def test_debug_statement_extraction(self, parser, tmp_lean_file):
        """Debug statement extraction for simple theorems."""
        simple_cases = [
            "theorem test1 (n : Nat) : n = n := by rfl",
            "theorem test2 : 1 + 1 = 2 := by simp",
            "theorem test3 (a b : Nat) : a + b = b + a := by simp"
        ]
        
        for content in simple_cases:
            lean_file = tmp_lean_file(content)
            result = parser.parse_file(lean_file)
            
            print(f"\n=== Testing: {content} ===")
            print(f"Success: {result.success}")
            print(f"Theorems found: {len(result.theorems)}")
            
            if result.theorems:
                theorem = result.theorems[0]
                print(f"Name: {theorem.name}")
                print(f"Statement: '{theorem.statement}'")
                print(f"Proof: '{theorem.proof}'")
            
            if result.errors:
                print(f"Errors: {result.errors}")


if __name__ == "__main__":
    # Run tests directly
    pytest.main([__file__, "-v", "-s"])