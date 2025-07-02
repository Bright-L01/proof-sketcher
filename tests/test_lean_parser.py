"""Integration tests for the updated LeanParser with subprocess integration."""

import json
import subprocess
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.parser.config import ParserConfig, RetryConfig
from proof_sketcher.parser.lean_parser import LeanParser


class TestLeanParserIntegration:
    """Integration tests for LeanParser with subprocess calls."""

    def test_parser_initialization_default_config(self):
        """Test parser initialization with default config."""
        parser = LeanParser()
        assert isinstance(parser.config, ParserConfig)
        assert parser.config.lean_executable == "lean"
        assert parser.extractor_path.name == "ExtractTheorem.lean"

    def test_parser_initialization_custom_config(self):
        """Test parser initialization with custom config."""
        config = ParserConfig.fast()
        parser = LeanParser(config)
        assert parser.config == config
        assert parser.config.lean_timeout == 10.0

    def test_parser_initialization_invalid_config(self):
        """Test parser initialization with invalid config."""
        from proof_sketcher.core.exceptions import ConfigValidationError
        config = ParserConfig(lean_timeout=-1.0)
        with pytest.raises(ConfigValidationError, match="lean_timeout must be positive"):
            LeanParser(config)

    def test_parse_file_nonexistent(self):
        """Test parsing non-existent file."""
        parser = LeanParser()
        result = parser.parse_file(Path("nonexistent.lean"))

        assert not result.success
        assert len(result.errors) == 1
        assert "File not found" in result.errors[0].message

    def test_parse_file_non_lean_extension(self, tmp_path):
        """Test parsing file with non-Lean extension."""
        test_file = tmp_path / "test.txt"
        test_file.write_text("not a lean file", encoding="utf-8")

        parser = LeanParser()
        result = parser.parse_file(test_file)

        assert not result.success
        assert "not a Lean file" in result.errors[0].message

    def test_parse_file_empty_lean_file(self, tmp_path):
        """Test parsing empty Lean file."""
        test_file = tmp_path / "empty.lean"
        test_file.write_text("", encoding="utf-8")

        parser = LeanParser()
        result = parser.parse_file(test_file)

        assert result.success
        assert len(result.theorems) == 0
        assert result.metadata is not None
        assert result.metadata.total_lines == 0

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_parse_file_with_lean_unavailable(self, mock_run, tmp_path):
        """Test parsing when Lean executable is unavailable."""
        # Mock Lean not available
        mock_run.side_effect = FileNotFoundError()

        content = """theorem test_theorem : True := trivial"""
        test_file = tmp_path / "test.lean"
        test_file.write_text(content, encoding="utf-8")

        config = ParserConfig(fallback_to_regex=True)
        parser = LeanParser(config)
        result = parser.parse_file(test_file)

        assert result.success
        assert len(result.theorems) == 1
        assert result.theorems[0].name == "test_theorem"
        # Should fall back to basic parsing
        assert "True" in result.theorems[0].statement

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_parse_file_with_lake_project(self, mock_run, tmp_path):
        """Test parsing with Lake project detection."""
        # Create a lakefile
        lakefile = tmp_path / "lakefile.lean"
        lakefile.write_text("import Lake", encoding="utf-8")

        # Create test file
        test_file = tmp_path / "Test.lean"
        test_file.write_text("theorem test : True := trivial", encoding="utf-8")

        # Mock subprocess calls
        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Lean 4.0.0")
            elif "lake" in args[0] and "build" in args[0]:
                return Mock(returncode=0, stdout="Build successful")
            else:
                # Mock Lean extractor call
                json_output = {
                    "name": "test",
                    "type": "True",
                    "dependencies": [],
                    "docString": None,
                    "success": True,
                }
                return Mock(returncode=0, stdout=json.dumps(json_output))

        mock_run.side_effect = mock_subprocess

        config = ParserConfig(lake_build_on_parse=True)
        parser = LeanParser(config)
        result = parser.parse_file(test_file)

        assert result.success
        # Should have called lake build
        lake_calls = [
            call
            for call in mock_run.call_args_list
            if any("lake" in str(arg) for arg in call[0])
        ]
        assert len(lake_calls) > 0

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_parse_theorem_success(self, mock_run, tmp_path):
        """Test successful single theorem parsing."""
        test_file = tmp_path / "test.lean"
        test_file.write_text(
            "theorem add_zero (n : Nat) : n + 0 = n := by simp", encoding="utf-8"
        )

        # Mock successful Lean extraction
        json_output = {
            "name": "add_zero",
            "type": "∀ (n : Nat), n + 0 = n",
            "dependencies": ["Nat.add_zero"],
            "docString": "Addition identity",
            "success": True,
        }

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Lean 4.0.0")
            else:
                return Mock(returncode=0, stdout=json.dumps(json_output))

        mock_run.side_effect = mock_subprocess

        parser = LeanParser()
        theorem = parser.parse_theorem(test_file, "add_zero")

        assert theorem is not None
        assert theorem.name == "add_zero"
        assert theorem.statement == "∀ (n : Nat), n + 0 = n"
        assert theorem.dependencies == ["Nat.add_zero"]
        assert theorem.docstring == "Addition identity"

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_parse_theorem_with_retry(self, mock_run, tmp_path):
        """Test theorem parsing with retry logic."""
        test_file = tmp_path / "test.lean"
        test_file.write_text("theorem test : True := trivial", encoding="utf-8")

        # First call times out, second succeeds
        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Lean 4.0.0")
            elif mock_run.call_count <= 2:  # First extractor call fails
                raise subprocess.TimeoutExpired("lean", 30)
            else:  # Second call succeeds
                json_output = {
                    "name": "test",
                    "type": "True",
                    "dependencies": [],
                    "success": True,
                }
                return Mock(returncode=0, stdout=json.dumps(json_output))

        mock_run.side_effect = mock_subprocess

        config = ParserConfig(retry_config=RetryConfig(max_attempts=2, base_delay=0.1))
        parser = LeanParser(config)

        with patch("time.sleep"):  # Speed up test
            theorem = parser.parse_theorem(test_file, "test")

        assert theorem is not None
        assert theorem.name == "test"
        # Should have been called multiple times due to retry
        assert mock_run.call_count >= 3  # version check + 2 extraction attempts

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_parse_theorem_timeout_exhausted(self, mock_run, tmp_path):
        """Test theorem parsing when all retry attempts are exhausted."""
        test_file = tmp_path / "test.lean"
        test_file.write_text("theorem test : True := trivial", encoding="utf-8")

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Lean 4.0.0")
            else:
                raise subprocess.TimeoutExpired("lean", 30)

        mock_run.side_effect = mock_subprocess

        config = ParserConfig(retry_config=RetryConfig(max_attempts=2, base_delay=0.1))
        parser = LeanParser(config)

        from proof_sketcher.core.exceptions import LeanTimeoutError
        
        with patch("time.sleep"):  # Speed up test
            with pytest.raises(LeanTimeoutError, match="Lean extraction timed out"):
                parser.parse_theorem(test_file, "test")

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_validate_lean_setup_success(self, mock_run):
        """Test successful Lean setup validation."""

        def mock_subprocess(*args, **kwargs):
            if "lean" in args[0] and "--version" in args[0]:
                return Mock(returncode=0, stdout="Lean (version 4.0.0)")
            elif "lake" in args[0] and "--version" in args[0]:
                return Mock(returncode=0, stdout="Lake version 4.0.0")
            return Mock(returncode=1)

        mock_run.side_effect = mock_subprocess

        parser = LeanParser()
        is_valid = parser.validate_lean_setup()

        assert is_valid is True

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_validate_lean_setup_lean_not_found(self, mock_run):
        """Test Lean setup validation when Lean is not found."""
        mock_run.side_effect = FileNotFoundError()

        parser = LeanParser()
        is_valid = parser.validate_lean_setup()

        assert is_valid is False

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_validate_lean_setup_version_check_timeout(self, mock_run):
        """Test Lean setup validation with version check timeout."""
        mock_run.side_effect = subprocess.TimeoutExpired("lean", 10)

        parser = LeanParser()
        is_valid = parser.validate_lean_setup()

        assert is_valid is False

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_check_executables_available(self, mock_run):
        """Test checking executable availability."""
        mock_run.return_value = Mock(returncode=0, stdout="version info")

        parser = LeanParser()
        assert parser.check_lean_available() is True
        assert parser.check_lake_available() is True

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_check_executables_not_available(self, mock_run):
        """Test checking executable availability when not found."""
        mock_run.side_effect = FileNotFoundError()

        parser = LeanParser()
        assert parser.check_lean_available() is False
        assert parser.check_lake_available() is False

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_get_versions(self, mock_run):
        """Test getting version information."""

        def mock_subprocess(*args, **kwargs):
            if "lean" in args[0]:
                return Mock(returncode=0, stdout="Lean (version 4.0.0)")
            elif "lake" in args[0]:
                return Mock(returncode=0, stdout="Lake version 4.0.0")
            return Mock(returncode=1)

        mock_run.side_effect = mock_subprocess

        parser = LeanParser()
        lean_version = parser.get_lean_version()
        lake_version = parser.get_lake_version()

        assert lean_version == "Lean (version 4.0.0)"
        assert lake_version == "Lake version 4.0.0"

    def test_parse_file_performance_tracking(self, tmp_path):
        """Test that parse time is tracked."""
        test_file = tmp_path / "test.lean"
        test_file.write_text("-- Simple file", encoding="utf-8")

        parser = LeanParser()
        result = parser.parse_file(test_file)

        assert result.parse_time_ms is not None
        assert result.parse_time_ms >= 0

    @patch("proof_sketcher.parser.lean_parser.subprocess.run")
    def test_parse_file_json_decode_error(self, mock_run, tmp_path):
        """Test handling of JSON decode errors from Lean extractor."""
        test_file = tmp_path / "test.lean"
        test_file.write_text("theorem test : True := trivial", encoding="utf-8")

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Lean 4.0.0")
            else:
                # Return invalid JSON
                return Mock(returncode=0, stdout="invalid json output")

        mock_run.side_effect = mock_subprocess

        parser = LeanParser()
        result = parser.parse_file(test_file)

        # Should fall back to basic parsing
        assert result.success
        assert len(result.theorems) == 1
        assert result.theorems[0].name == "test"

    def test_parse_file_with_imports(self, tmp_path):
        """Test parsing file with import statements."""
        content = """import Mathlib.Algebra.Basic
import Mathlib.Logic.Basic

-- Some content here
"""
        test_file = tmp_path / "with_imports.lean"
        test_file.write_text(content, encoding="utf-8")

        parser = LeanParser()
        result = parser.parse_file(test_file)

        assert result.success
        assert result.metadata is not None
        assert len(result.metadata.imports) == 2
        assert "Mathlib.Algebra.Basic" in result.metadata.imports
        assert "Mathlib.Logic.Basic" in result.metadata.imports

    def test_parse_simple_theorem(self, tmp_path):
        """Test parsing a simple theorem."""
        content = """-- A simple theorem
theorem add_zero (n : ℕ) : n + 0 = n := by simp
"""
        test_file = tmp_path / "simple_theorem.lean"
        test_file.write_text(content, encoding="utf-8")

        parser = LeanParser()
        result = parser.parse_file(test_file)

        assert result.success
        assert result.has_theorems
        assert len(result.theorems) == 1

        theorem = result.theorems[0]
        assert theorem.name == "add_zero"
        assert "(n : ℕ)" in theorem.statement
        assert "n + 0 = n" in theorem.statement
        assert theorem.proof == "by simp"
        assert theorem.line_number == 2

    def test_parse_multiple_theorems(self, tmp_path):
        """Test parsing multiple theorems."""
        content = """theorem thm1 : True := trivial

lemma lem1 (p : Prop) : p → p := fun h => h

theorem thm2 : False → True := fun _ => trivial
"""
        test_file = tmp_path / "multiple_theorems.lean"
        test_file.write_text(content, encoding="utf-8")

        parser = LeanParser()
        result = parser.parse_file(test_file)

        assert result.success
        assert len(result.theorems) == 3

        names = [t.name for t in result.theorems]
        assert "thm1" in names
        assert "lem1" in names
        assert "thm2" in names

    def test_parse_multiline_theorem(self, tmp_path):
        """Test parsing a multiline theorem."""
        content = """theorem complex_theorem
  (n m : ℕ)
  (h : n > 0) :
  n + m = m + n :=
by
  rw [Nat.add_comm]
"""
        test_file = tmp_path / "multiline.lean"
        test_file.write_text(content, encoding="utf-8")

        parser = LeanParser()
        result = parser.parse_file(test_file)

        assert result.success
        assert len(result.theorems) == 1

        theorem = result.theorems[0]
        assert theorem.name == "complex_theorem"
        assert "(n m : ℕ)" in theorem.statement
        assert "n + m = m + n" in theorem.statement

    def test_extract_imports(self):
        """Test import extraction."""
        parser = LeanParser()
        content = """import Mathlib.Algebra.Basic
import Mathlib.Logic.Basic
-- import Commented.Import

variable (x : ℕ)
"""
        imports = parser._extract_imports(content)
        assert len(imports) == 2
        assert "Mathlib.Algebra.Basic" in imports
        assert "Mathlib.Logic.Basic" in imports
        assert "Commented.Import" not in imports
