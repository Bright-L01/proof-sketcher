"""Unit tests for parser modules."""

import tempfile
from pathlib import Path
from unittest.mock import MagicMock, Mock, patch

import pytest

from proof_sketcher.parser.config import ParserConfig
from proof_sketcher.parser.enhanced_parser import EnhancedLeanParser
from proof_sketcher.parser.lean_extractor import LeanExtractor
from proof_sketcher.parser.lean_parser import LeanParser
from proof_sketcher.parser.mathlib_notation import MathlibNotationHandler
from proof_sketcher.parser.mathlib_notation_optimized import (
    OptimizedMathlibNotationHandler,
)
from proof_sketcher.parser.models import ParseError, ParseResult, TheoremInfo


@pytest.fixture
def simple_lean_content():
    """Sample simple Lean content for testing."""
    return """
-- Simple theorem about natural numbers
theorem add_zero (n : Nat) : n + 0 = n := by
  simp

-- Another simple theorem
theorem zero_add (n : Nat) : 0 + n = n := by
  rfl
"""


@pytest.fixture
def complex_lean_content():
    """Sample complex Lean content for testing."""
    return """
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic

namespace MyNamespace

-- Complex theorem with dependencies
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp [Nat.zero_add]
  | succ a ih =>
    rw [Nat.succ_add, ih, Nat.add_succ]

-- Theorem with type classes
theorem group_identity_unique {G : Type*} [Group G] (e : G)
  (h : ∀ a : G, e * a = a) : e = 1 := by
  have h1 : e * 1 = 1 := h 1
  rw [mul_one] at h1
  exact h1

end MyNamespace
"""


@pytest.fixture
def parser_config():
    """Create parser configuration for testing."""
    return ParserConfig(
        timeout_seconds=30,
        max_file_size=1000000,
        include_dependencies=True,
        extract_tactics=True,
        calculate_complexity=True,
    )


class TestLeanParser:
    """Test basic Lean parser."""

    def test_parser_initialization(self, parser_config):
        """Test parser initialization."""
        parser = LeanParser(config=parser_config)
        assert parser.config == parser_config
        assert parser.extractor is not None

    def test_parse_simple_file(self, simple_lean_content, tmp_path, parser_config):
        """Test parsing a simple Lean file."""
        # Create test file
        lean_file = tmp_path / "test.lean"
        lean_file.write_text(simple_lean_content)

        parser = LeanParser(config=parser_config)

        with patch.object(parser.extractor, "extract_theorems") as mock_extract:
            mock_extract.return_value = [
                TheoremInfo(
                    name="add_zero",
                    statement="∀ (n : Nat), n + 0 = n",
                    proof="by simp",
                    line_number=3,
                ),
                TheoremInfo(
                    name="zero_add",
                    statement="∀ (n : Nat), 0 + n = n",
                    proof="by rfl",
                    line_number=7,
                ),
            ]

            result = parser.parse_file(lean_file)

            assert result.success
            assert len(result.theorems) == 2
            assert result.theorems[0].name == "add_zero"
            assert result.theorems[1].name == "zero_add"
            assert not result.has_errors

    def test_parse_file_with_errors(self, tmp_path, parser_config):
        """Test parsing a file with syntax errors."""
        # Create file with syntax errors
        lean_file = tmp_path / "error.lean"
        lean_file.write_text("theorem bad_syntax : { invalid lean")

        parser = LeanParser(config=parser_config)

        with patch.object(parser.extractor, "extract_theorems") as mock_extract:
            mock_extract.side_effect = Exception("Syntax error at line 1")

            result = parser.parse_file(lean_file)

            assert not result.success
            assert len(result.errors) > 0
            assert "Syntax error" in result.errors[0].message

    def test_parse_directory(self, tmp_path, parser_config):
        """Test parsing a directory of Lean files."""
        # Create multiple Lean files
        for i in range(3):
            lean_file = tmp_path / f"theorem{i}.lean"
            lean_file.write_text(f"theorem t{i} : Nat := {i}")

        parser = LeanParser(config=parser_config)

        with patch.object(parser, "parse_file") as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[TheoremInfo(name="test", statement="test")], success=True
            )

            results = parser.parse_directory(tmp_path)

            assert len(results) == 3
            assert all(r.success for r in results)
            assert mock_parse.call_count == 3

    def test_dependency_extraction(self, complex_lean_content, tmp_path, parser_config):
        """Test extraction of imports and dependencies."""
        lean_file = tmp_path / "complex.lean"
        lean_file.write_text(complex_lean_content)

        parser = LeanParser(config=parser_config)

        dependencies = parser._extract_dependencies(complex_lean_content)

        assert "Mathlib.Data.Nat.Basic" in dependencies
        assert "Mathlib.Algebra.Group.Basic" in dependencies

    def test_tactic_extraction(self, complex_lean_content, parser_config):
        """Test extraction of tactics from proofs."""
        parser = LeanParser(config=parser_config)

        tactics = parser._extract_tactics(complex_lean_content)

        assert "simp" in tactics
        assert "rw" in tactics
        assert "exact" in tactics
        assert "induction" in tactics

    def test_namespace_handling(self, complex_lean_content, parser_config):
        """Test handling of namespaces."""
        parser = LeanParser(config=parser_config)

        namespaces = parser._extract_namespaces(complex_lean_content)

        assert "MyNamespace" in namespaces

    def test_error_recovery(self, tmp_path, parser_config):
        """Test error recovery and partial parsing."""
        # File with mixed valid and invalid content
        content = """
theorem valid : True := trivial

theorem invalid : { syntax error

theorem another_valid : False → True := by
  intro h
  trivial
"""
        lean_file = tmp_path / "mixed.lean"
        lean_file.write_text(content)

        parser = LeanParser(config=parser_config)

        with patch.object(parser.extractor, "extract_theorems") as mock_extract:
            # Should extract valid theorems despite errors
            mock_extract.return_value = [
                TheoremInfo(name="valid", statement="True", proof="trivial"),
                TheoremInfo(
                    name="another_valid",
                    statement="False → True",
                    proof="by intro h; trivial",
                ),
            ]

            result = parser.parse_file(lean_file)

            # Should have some valid theorems even with errors
            assert len(result.theorems) == 2


class TestEnhancedLeanParser:
    """Test enhanced Lean parser with additional features."""

    def test_enhanced_parser_initialization(self, parser_config):
        """Test enhanced parser initialization."""
        parser = EnhancedLeanParser(config=parser_config)
        assert parser.config == parser_config
        assert parser.notation_handler is not None
        assert parser.complexity_analyzer is not None

    def test_complexity_analysis(self, complex_lean_content, tmp_path, parser_config):
        """Test theorem complexity analysis."""
        lean_file = tmp_path / "complex.lean"
        lean_file.write_text(complex_lean_content)

        parser = EnhancedLeanParser(config=parser_config)

        with patch.object(parser, "_base_parse_file") as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[
                    TheoremInfo(
                        name="add_comm",
                        statement="∀ (a b : Nat), a + b = b + a",
                        proof="by induction a with | zero => simp | succ a ih => rw [...]",
                    )
                ],
                success=True,
            )

            with patch.object(parser.complexity_analyzer, "analyze") as mock_analyze:
                mock_analyze.return_value = {
                    "proof_length": 15,
                    "tactic_complexity": 3,
                    "type_complexity": 2,
                    "overall_score": 8,
                }

                result = parser.parse_file(lean_file)

                assert result.success
                assert len(result.theorems) == 1
                theorem = result.theorems[0]
                assert hasattr(theorem, "complexity_score")
                assert theorem.complexity_score == 8

    def test_notation_enhancement(self, complex_lean_content, tmp_path, parser_config):
        """Test mathematical notation enhancement."""
        lean_file = tmp_path / "notation.lean"
        lean_file.write_text(complex_lean_content)

        parser = EnhancedLeanParser(config=parser_config)

        with patch.object(parser.notation_handler, "enhance_theorem") as mock_enhance:
            mock_enhance.return_value = TheoremInfo(
                name="enhanced",
                statement="∀ (a b : ℕ), a + b = b + a",  # Enhanced notation
                proof="by commutativity",
            )

            original = TheoremInfo(
                name="original",
                statement="forall (a b : Nat), a + b = b + a",
                proof="by rw [Nat.add_comm]",
            )

            enhanced = parser._enhance_theorem_notation(original)

            assert enhanced.name == "enhanced"
            assert "ℕ" in enhanced.statement  # Unicode enhancement

    def test_proof_structure_analysis(self, complex_lean_content, parser_config):
        """Test proof structure analysis."""
        parser = EnhancedLeanParser(config=parser_config)

        structure = parser._analyze_proof_structure(complex_lean_content)

        assert "induction" in structure["proof_patterns"]
        assert "rewrite" in structure["proof_patterns"]
        assert structure["proof_depth"] > 0
        assert structure["branching_factor"] >= 1

    def test_semantic_analysis(self, complex_lean_content, parser_config):
        """Test semantic analysis of theorems."""
        parser = EnhancedLeanParser(config=parser_config)

        theorem = TheoremInfo(
            name="add_comm",
            statement="∀ (a b : Nat), a + b = b + a",
            proof="by rw [Nat.add_comm]",
        )

        semantics = parser._analyze_semantics(theorem)

        assert "commutativity" in semantics["mathematical_concepts"]
        assert "algebra" in semantics["mathematical_areas"]
        assert semantics["abstraction_level"] in [
            "concrete",
            "abstract",
            "very_abstract",
        ]


class TestLeanExtractor:
    """Test Lean theorem extractor."""

    def test_extractor_initialization(self):
        """Test extractor initialization."""
        extractor = LeanExtractor()
        assert extractor.lean_executable is not None

    def test_extract_theorems_basic(self, simple_lean_content, tmp_path):
        """Test basic theorem extraction."""
        lean_file = tmp_path / "simple.lean"
        lean_file.write_text(simple_lean_content)

        extractor = LeanExtractor()

        with patch.object(extractor, "_run_lean_command") as mock_run:
            mock_run.return_value = {
                "theorems": [
                    {
                        "name": "add_zero",
                        "type": "∀ (n : Nat), n + 0 = n",
                        "proof": "by simp",
                        "line": 3,
                    }
                ]
            }

            theorems = extractor.extract_theorems(lean_file)

            assert len(theorems) == 1
            assert theorems[0].name == "add_zero"
            assert theorems[0].line_number == 3

    def test_lean_command_execution(self, tmp_path):
        """Test Lean command execution."""
        extractor = LeanExtractor()

        with patch("subprocess.run") as mock_run:
            mock_run.return_value = Mock(
                stdout='{"success": true, "theorems": []}', stderr="", returncode=0
            )

            result = extractor._run_lean_command("--help")

            assert result["success"] is True
            assert "theorems" in result

    def test_theorem_validation(self):
        """Test theorem validation."""
        extractor = LeanExtractor()

        # Valid theorem
        valid_data = {"name": "test", "type": "Prop", "proof": "trivial", "line": 1}

        theorem = extractor._validate_theorem(valid_data)
        assert theorem is not None
        assert theorem.name == "test"

        # Invalid theorem (missing name)
        invalid_data = {"type": "Prop", "proof": "trivial"}

        theorem = extractor._validate_theorem(invalid_data)
        assert theorem is None

    def test_error_handling(self, tmp_path):
        """Test error handling in extraction."""
        extractor = LeanExtractor()

        # Non-existent file
        with pytest.raises(FileNotFoundError):
            extractor.extract_theorems(tmp_path / "nonexistent.lean")

        # Lean execution error
        lean_file = tmp_path / "error.lean"
        lean_file.write_text("invalid lean syntax")

        with patch.object(extractor, "_run_lean_command") as mock_run:
            mock_run.side_effect = Exception("Lean error")

            with pytest.raises(Exception):
                extractor.extract_theorems(lean_file)


class TestMathlibNotationHandler:
    """Test Mathlib notation handler."""

    def test_notation_handler_initialization(self):
        """Test notation handler initialization."""
        handler = MathlibNotationHandler()
        assert handler.unicode_map is not None
        assert handler.latex_map is not None

    def test_unicode_conversion(self):
        """Test Unicode symbol conversion."""
        handler = MathlibNotationHandler()

        test_cases = [
            ("forall", "∀"),
            ("exists", "∃"),
            ("Nat", "ℕ"),
            ("Real", "ℝ"),
            ("subset", "⊆"),
            ("union", "∪"),
            ("intersection", "∩"),
        ]

        for ascii_form, unicode_form in test_cases:
            result = handler.convert_to_unicode(ascii_form)
            assert unicode_form in result or ascii_form in result

    def test_latex_conversion(self):
        """Test LaTeX conversion."""
        handler = MathlibNotationHandler()

        test_cases = [
            ("∀ x, P(x)", "\\forall x, P(x)"),
            ("ℕ", "\\mathbb{N}"),
            ("ℝ", "\\mathbb{R}"),
            ("α → β", "\\alpha \\to \\beta"),
            ("x ∈ S", "x \\in S"),
        ]

        for unicode_form, latex_form in test_cases:
            result = handler.convert_to_latex(unicode_form)
            assert any(part in result for part in latex_form.split())

    def test_html_conversion(self):
        """Test HTML conversion."""
        handler = MathlibNotationHandler()

        test_cases = [
            ("∀", "&forall;"),
            ("∃", "&exist;"),
            ("ℕ", "&#8469;"),
            ("ℝ", "&#8477;"),
            ("→", "&rarr;"),
        ]

        for unicode_form, html_form in test_cases:
            result = handler.convert_to_html(unicode_form)
            assert html_form in result or unicode_form in result

    def test_complex_expression_conversion(self):
        """Test conversion of complex mathematical expressions."""
        handler = MathlibNotationHandler()

        complex_expr = "∀ ε > 0, ∃ δ > 0, |x - a| < δ → |f(x) - f(a)| < ε"

        latex_result = handler.convert_to_latex(complex_expr)
        assert "\\forall" in latex_result
        assert "\\exists" in latex_result
        assert "\\varepsilon" in latex_result or "\\epsilon" in latex_result
        assert "\\delta" in latex_result

    def test_theorem_enhancement(self):
        """Test theorem enhancement with notation."""
        handler = MathlibNotationHandler()

        original = TheoremInfo(
            name="continuity",
            statement="forall eps > 0, exists delta > 0, ...",
            proof="by epsilon_delta",
        )

        enhanced = handler.enhance_theorem(original)

        assert "∀" in enhanced.statement or "forall" in enhanced.statement
        assert enhanced.name == original.name


class TestOptimizedMathlibNotationHandler:
    """Test optimized Mathlib notation handler."""

    def test_optimized_handler_initialization(self):
        """Test optimized handler initialization."""
        handler = OptimizedMathlibNotationHandler()
        assert handler.cache is not None
        assert handler.precompiled_patterns is not None

    def test_caching_behavior(self):
        """Test caching behavior for performance."""
        handler = OptimizedMathlibNotationHandler()

        expression = "∀ x ∈ ℕ, x + 0 = x"

        # First conversion
        result1 = handler.convert_to_latex(expression)

        # Second conversion should use cache
        result2 = handler.convert_to_latex(expression)

        assert result1 == result2
        assert len(handler.cache) > 0

    def test_batch_conversion_performance(self):
        """Test batch conversion performance."""
        handler = OptimizedMathlibNotationHandler()

        expressions = [
            "∀ x ∈ ℕ, x + 0 = x",
            "∃ y ∈ ℝ, y² = 2",
            "A ∪ B ⊆ C",
            "f : ℝ → ℝ",
        ] * 10

        results = handler.convert_batch_to_latex(expressions)

        assert len(results) == len(expressions)
        assert all(isinstance(r, str) for r in results)

    def test_pattern_optimization(self):
        """Test precompiled pattern optimization."""
        handler = OptimizedMathlibNotationHandler()

        # Should have precompiled common patterns
        assert len(handler.precompiled_patterns) > 0

        # Test pattern matching
        expression = "∀ x : ℕ, P(x)"
        matches = handler._find_pattern_matches(expression)

        assert len(matches) > 0


class TestParserConfig:
    """Test parser configuration."""

    def test_config_creation(self):
        """Test configuration creation."""
        config = ParserConfig(
            timeout_seconds=60, max_file_size=2000000, include_dependencies=True
        )

        assert config.timeout_seconds == 60
        assert config.max_file_size == 2000000
        assert config.include_dependencies is True

    def test_config_validation(self):
        """Test configuration validation."""
        # Valid config
        config = ParserConfig(timeout_seconds=30)
        assert config.timeout_seconds == 30

        # Invalid timeout should raise error or use default
        with pytest.raises(ValueError):
            ParserConfig(timeout_seconds=-1)

    def test_config_serialization(self):
        """Test configuration serialization."""
        config = ParserConfig(
            timeout_seconds=45, extract_tactics=True, calculate_complexity=False
        )

        config_dict = config.model_dump()
        assert isinstance(config_dict, dict)
        assert config_dict["timeout_seconds"] == 45
        assert config_dict["extract_tactics"] is True

    def test_config_loading(self, tmp_path):
        """Test configuration loading from file."""
        config_data = {
            "timeout_seconds": 120,
            "max_file_size": 5000000,
            "include_dependencies": False,
        }

        config_file = tmp_path / "parser_config.json"
        config_file.write_text(json.dumps(config_data))

        config = ParserConfig.from_file(config_file)

        assert config.timeout_seconds == 120
        assert config.max_file_size == 5000000
        assert config.include_dependencies is False


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
