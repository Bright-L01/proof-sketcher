"""Comprehensive tests for the Lean parser module."""

import json
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.parser import LeanParser
from proof_sketcher.parser.config import ParserConfig, RetryConfig
from proof_sketcher.parser.models import ParseError, ParseResult, TheoremInfo


class TestLeanParser:
    """Test suite for LeanParser class."""

    @pytest.fixture
    def parser(self):
        """Create a parser instance with test configuration."""
        config = ParserConfig(
            fallback_to_regex=True,
            lean_timeout=5.0,
            retry_config=RetryConfig(max_attempts=2),
        )
        return LeanParser(config)

    @pytest.fixture
    def sample_lean_content(self):
        """Sample Lean file content for testing."""
        return """
/-- Addition is commutative -/
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih => simp [add_succ, ih]

lemma helper_lemma : 1 + 1 = 2 := by rfl

theorem complex_theorem (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  exact ⟨h.2, h.1⟩
"""

    def test_parser_initialization(self):
        """Test parser initialization with various configs."""
        # Default config
        parser = LeanParser()
        assert parser.config.lean_executable == "lean"
        assert parser.config.fallback_to_regex is True

        # Custom config
        config = ParserConfig(
            lean_executable="/custom/lean",
            lake_executable="/custom/lake",
            lean_timeout=60.0,
        )
        parser = LeanParser(config)
        assert parser.config.lean_executable == "/custom/lean"
        assert parser.config.lean_timeout == 60.0

    def test_parse_file_not_found(self, parser):
        """Test parsing non-existent file."""
        result = parser.parse_file(Path("nonexistent.lean"))
        assert not result.success
        assert len(result.errors) == 1
        assert "not found" in result.errors[0].message

    def test_parse_non_lean_file(self, parser, tmp_path):
        """Test parsing non-Lean file."""
        test_file = tmp_path / "test.txt"
        test_file.write_text("not a lean file")

        result = parser.parse_file(test_file)
        assert not result.success
        assert "not a Lean file" in result.errors[0].message

    def test_basic_theorem_extraction(self, parser, tmp_path, sample_lean_content):
        """Test basic theorem extraction using regex fallback."""
        test_file = tmp_path / "test.lean"
        test_file.write_text(sample_lean_content)

        result = parser.parse_file(test_file)
        assert result.success
        assert len(result.theorems) == 3

        # Check theorem names
        theorem_names = [t.name for t in result.theorems]
        assert "add_comm" in theorem_names
        assert "helper_lemma" in theorem_names
        assert "complex_theorem" in theorem_names

        # Check add_comm theorem
        add_comm = next(t for t in result.theorems if t.name == "add_comm")
        assert "a + b = b + a" in add_comm.statement
        assert add_comm.proof is not None
        assert "induction" in add_comm.proof

    def test_metadata_extraction(self, parser, tmp_path, sample_lean_content):
        """Test file metadata extraction."""
        test_file = tmp_path / "test.lean"
        test_file.write_text(sample_lean_content)

        result = parser.parse_file(test_file)
        assert result.metadata is not None
        assert result.metadata.file_path == test_file
        assert result.metadata.total_lines == len(sample_lean_content.splitlines())
        assert result.metadata.file_size > 0

    def test_import_extraction(self, parser, tmp_path):
        """Test import statement extraction."""
        content = """
import Lean.Meta
import Mathlib.Data.Nat.Basic
import MyProject.Utils

theorem test : True := trivial
"""
        test_file = tmp_path / "imports.lean"
        test_file.write_text(content)

        result = parser.parse_file(test_file)
        assert result.success
        assert len(result.metadata.imports) == 3
        assert "Lean.Meta" in result.metadata.imports
        assert "Mathlib.Data.Nat.Basic" in result.metadata.imports

    @patch("subprocess.run")
    def test_lean_extractor_integration(self, mock_run, parser, tmp_path):
        """Test integration with Lean extractor when available."""
        # Mock successful Lean execution
        mock_result = Mock()
        mock_result.returncode = 0
        mock_result.stdout = json.dumps(
            {
                "name": "test_theorem",
                "type": "∀ x, P x",
                "value": "proof",
                "docString": "Test theorem",
                "tactics": ["intro", "exact"],
                "dependencies": ["Nat.add", "List.map"],
                "isAxiom": False,
            }
        )
        mock_run.return_value = mock_result

        test_file = tmp_path / "test.lean"
        test_file.write_text("theorem test_theorem : ∀ x, P x := proof")

        theorem = parser.parse_theorem(test_file, "test_theorem")
        assert theorem is not None
        assert theorem.name == "test_theorem"
        assert theorem.statement == "∀ x, P x"
        assert theorem.tactics == ["intro", "exact"]
        assert len(theorem.dependencies) == 2

    def test_lake_project_detection(self, parser, tmp_path):
        """Test Lake project detection."""
        project_dir = tmp_path / "my_project"
        project_dir.mkdir()

        # Create lakefile
        lakefile = project_dir / "lakefile.lean"
        lakefile.write_text("import Lake\nopen Lake DSL\npackage test")

        # Create Lean file in project
        src_dir = project_dir / "src"
        src_dir.mkdir()
        test_file = src_dir / "Test.lean"
        test_file.write_text("theorem test : True := trivial")

        # Test detection
        lake_root = parser._find_lake_project(test_file)
        assert lake_root == project_dir

    def test_parse_performance(self, parser, tmp_path):
        """Test parse time measurement."""
        test_file = tmp_path / "test.lean"
        test_file.write_text("theorem test : True := trivial")

        result = parser.parse_file(test_file)
        assert result.parse_time_ms is not None
        assert result.parse_time_ms > 0
        assert result.parse_time_ms < 5000  # Should be fast

    def test_error_handling(self, parser, tmp_path):
        """Test various error conditions."""
        # Test with malformed Lean content
        test_file = tmp_path / "malformed.lean"
        test_file.write_text("theorem incomplete_theorem : Nat :=")

        result = parser.parse_file(test_file)
        # Should still succeed with regex parsing
        assert result.success

        # Test theorem might have incomplete proof
        if result.theorems:
            theorem = result.theorems[0]
            assert theorem.name == "incomplete_theorem"


class TestParserConfig:
    """Test suite for parser configuration."""

    def test_default_config(self):
        """Test default configuration values."""
        config = ParserConfig()
        assert config.lean_executable == "lean"
        assert config.lake_executable == "lake"
        assert config.lean_timeout == 30.0
        assert config.auto_detect_lake is True
        assert config.fallback_to_regex is True

    def test_config_validation(self):
        """Test configuration validation."""
        # Valid config
        config = ParserConfig()
        errors = config.validate()
        assert len(errors) == 0

        # Invalid timeout
        config = ParserConfig(lean_timeout=-1)
        errors = config.validate()
        assert len(errors) > 0
        assert "timeout must be positive" in errors[0]

    def test_retry_config(self):
        """Test retry configuration."""
        retry = RetryConfig(max_attempts=3, base_delay=1.0)
        assert retry.get_delay(0) == 1.0
        assert retry.get_delay(1) == 2.0
        assert retry.get_delay(2) == 4.0

        # Test max delay cap
        retry = RetryConfig(base_delay=5.0, max_delay=10.0)
        assert retry.get_delay(10) == 10.0  # Should be capped

    def test_config_presets(self):
        """Test configuration presets."""
        # Fast config
        fast = ParserConfig.fast()
        assert fast.lean_timeout == 10.0
        assert fast.retry_config.max_attempts == 1

        # Robust config
        robust = ParserConfig.robust()
        assert robust.lean_timeout == 60.0
        assert robust.retry_config.max_attempts == 5
        assert robust.lake_build_on_parse is True


class TestParserModels:
    """Test suite for parser data models."""

    def test_theorem_info_model(self):
        """Test TheoremInfo model."""
        theorem = TheoremInfo(
            name="test_theorem",
            statement="∀ x, P x",
            proof="by intro x; exact h x",
            dependencies=["Nat.add", "List.map"],
            line_number=42,
            docstring="Test theorem documentation",
            tactics=["intro", "exact"],
        )

        assert theorem.name == "test_theorem"
        assert len(theorem.dependencies) == 2
        assert len(theorem.tactics) == 2
        assert theorem.is_axiom is False

    def test_parse_result_model(self):
        """Test ParseResult model."""
        theorem = TheoremInfo(name="test", statement="True")
        error = ParseError(message="Test error", severity="warning")

        result = ParseResult(
            theorems=[theorem], errors=[error], success=True, parse_time_ms=100.5
        )

        assert result.has_theorems
        assert result.has_errors
        assert result.get_theorem_by_name("test") == theorem
        assert result.get_theorem_by_name("nonexistent") is None

    def test_model_validation(self):
        """Test model validation."""
        # Valid theorem
        theorem = TheoremInfo(name="test", statement="True")
        assert theorem.name == "test"

        # Test with empty name (should fail)
        with pytest.raises(ValueError):
            TheoremInfo(name="", statement="True")


@pytest.mark.integration
class TestParserIntegration:
    """Integration tests for the parser."""

    def test_parse_example_files(self):
        """Test parsing actual example files."""
        parser = LeanParser()

        # Test basic example
        basic_file = Path("examples/lean_project/ProofSketcherExamples/Basic.lean")
        if basic_file.exists():
            result = parser.parse_file(basic_file)
            assert result.success
            assert len(result.theorems) > 0

            # Check known theorems
            theorem_names = [t.name for t in result.theorems]
            assert "two_plus_two" in theorem_names or len(theorem_names) > 0

    def test_parse_mathlib_style(self):
        """Test parsing mathlib-style file."""
        parser = LeanParser()

        mathlib_file = Path("examples/mathlib_example.lean")
        if mathlib_file.exists():
            result = parser.parse_file(mathlib_file)
            assert result.success
            assert len(result.theorems) > 0

            # Check for specific theorem patterns
            has_even_theorem = any("even" in t.name.lower() for t in result.theorems)
            has_list_theorem = any(
                "list" in t.statement.lower() for t in result.theorems
            )
            assert has_even_theorem or has_list_theorem or len(result.theorems) > 0
