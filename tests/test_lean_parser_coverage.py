"""Comprehensive test suite to improve LeanParser coverage.

This test file focuses on testing the uncovered methods and edge cases
to bring the parser coverage from 14% to a target of 85%+.
"""

import json
import subprocess
import tempfile
import time
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock
from datetime import datetime

import pytest

from proof_sketcher.core.exceptions import (
    ConfigValidationError,
    LeanTimeoutError,
    ParserError,
)
from proof_sketcher.parser.config import ParserConfig, RetryConfig
from proof_sketcher.parser.lean_parser import LeanParser
from proof_sketcher.parser.models import ParseError, TheoremInfo


class TestLeanParserCoverageImprovement:
    """Test suite to improve LeanParser coverage."""

    @pytest.fixture
    def parser(self):
        """Create a LeanParser instance with default config."""
        return LeanParser()

    @pytest.fixture
    def custom_parser(self):
        """Create a LeanParser instance with custom config."""
        config = ParserConfig(
            lean_timeout=20.0,
            auto_detect_lake=True,
            extract_dependencies=True,
            extract_docstrings=True,
        )
        return LeanParser(config)

    @pytest.fixture
    def lean_content_simple(self):
        """Simple Lean content for testing."""
        return '''-- Simple test theorem
theorem simple_test : True :=
  trivial
'''

    @pytest.fixture
    def lean_content_complex(self):
        """Complex Lean content with multiple theorems."""
        return '''import Mathlib.Tactic

-- A simple theorem
theorem test_theorem (n : ℕ) : n + 0 = n := by
  rw [add_zero]

-- Another theorem with proof
theorem another_test : ∀ x : ℕ, x + 1 > x := by
  intro x
  exact Nat.lt_succ_self x

-- Axiom example
axiom custom_axiom : True

-- Definition
def my_function (x : ℕ) : ℕ := x + 1
'''

    @pytest.fixture
    def lean_content_with_imports(self):
        """Lean content with imports."""
        return '''import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Custom.Module

theorem imported_theorem : True := trivial
'''

    def test_parser_initialization_with_invalid_config(self):
        """Test parser initialization with invalid configuration."""
        config = ParserConfig(lean_timeout=-1.0)
        with pytest.raises(ConfigValidationError) as exc_info:
            LeanParser(config)
        
        assert "lean_timeout must be positive" in str(exc_info.value)
        assert exc_info.value.error_code == "parser_config_invalid"

    def test_parse_file_with_exception_handling(self, tmp_path):
        """Test parse_file exception handling."""
        parser = LeanParser()
        test_file = tmp_path / "test.lean"
        test_file.write_text("theorem test : True := trivial", encoding="utf-8")
        
        # Mock file operations to raise exception
        with patch.object(Path, 'read_text', side_effect=PermissionError("Access denied")):
            result = parser.parse_file(test_file)
            
            assert not result.success
            assert len(result.errors) == 1
            assert "Parsing failed" in result.errors[0].message
            assert result.parse_time_ms is not None

    def test_parse_file_with_lake_project_detection(self, tmp_path):
        """Test parse_file with Lake project detection."""
        # Create a Lake project structure
        project_dir = tmp_path / "test_project"
        project_dir.mkdir()
        
        # Create lakefile.lean
        lakefile = project_dir / "lakefile.lean"
        lakefile.write_text("package «TestProject» where\n  version := \"0.1.0\"")
        
        # Create lean file in project
        lean_file = project_dir / "Test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        parser = LeanParser(ParserConfig(auto_detect_lake=True))
        
        with patch.object(parser, '_setup_lake_project') as mock_setup:
            mock_setup.return_value = []
            result = parser.parse_file(lean_file)
            
            # Should have called Lake setup
            mock_setup.assert_called_once_with(lean_file)

    def test_parse_file_enhanced_vs_basic_theorems(self, tmp_path, lean_content_simple):
        """Test parse_file choosing between enhanced and basic parsing."""
        test_file = tmp_path / "test.lean"
        test_file.write_text(lean_content_simple)
        
        parser = LeanParser()
        
        with patch.object(parser, '_can_use_lean_extractor', return_value=True), \
             patch.object(parser, '_extract_all_theorems_with_lean') as mock_extract:
            
            # Mock enhanced extraction returning empty results
            mock_extract.return_value = ([], [])
            
            with patch.object(parser, '_extract_theorems_basic') as mock_basic:
                mock_basic.return_value = [
                    TheoremInfo(name="simple_test", statement="True")
                ]
                
                result = parser.parse_file(test_file)
                
                # Should fall back to basic parsing when enhanced returns empty
                assert len(result.theorems) == 1
                assert result.theorems[0].name == "simple_test"

    def test_parse_theorem_fallback_to_basic(self, tmp_path, lean_content_simple):
        """Test parse_theorem fallback when Lean extractor unavailable."""
        test_file = tmp_path / "test.lean"
        test_file.write_text(lean_content_simple)
        
        parser = LeanParser()
        
        with patch.object(parser, '_can_use_lean_extractor', return_value=False), \
             patch.object(parser, '_extract_theorems_basic') as mock_basic:
            
            mock_basic.return_value = [
                TheoremInfo(name="simple_test", statement="True")
            ]
            
            result = parser.parse_theorem(test_file, "simple_test")
            
            assert result is not None
            assert result.name == "simple_test"
            mock_basic.assert_called_once()

    def test_parse_theorem_not_found_in_basic(self, tmp_path, lean_content_simple):
        """Test parse_theorem when theorem not found in basic parsing."""
        test_file = tmp_path / "test.lean"
        test_file.write_text(lean_content_simple)
        
        parser = LeanParser()
        
        with patch.object(parser, '_can_use_lean_extractor', return_value=False), \
             patch.object(parser, '_extract_theorems_basic') as mock_basic:
            
            mock_basic.return_value = [
                TheoremInfo(name="other_theorem", statement="False")
            ]
            
            result = parser.parse_theorem(test_file, "nonexistent_theorem")
            assert result is None

    def test_parse_theorem_with_successful_extraction(self, tmp_path):
        """Test parse_theorem with successful Lean extraction."""
        test_file = tmp_path / "test.lean"
        test_file.write_text("theorem test : True := trivial")
        
        parser = LeanParser()
        
        mock_theorem = TheoremInfo(name="test", statement="True")
        
        with patch.object(parser, '_can_use_lean_extractor', return_value=True), \
             patch.object(parser, '_extract_single_theorem_with_lean') as mock_extract:
            
            mock_extract.return_value = mock_theorem
            
            result = parser.parse_theorem(test_file, "test")
            
            assert result == mock_theorem
            mock_extract.assert_called_once_with(test_file, "test")

    def test_parse_theorem_retry_on_exception(self, tmp_path):
        """Test parse_theorem retry logic on general exceptions."""
        test_file = tmp_path / "test.lean" 
        test_file.write_text("theorem test : True := trivial")
        
        config = ParserConfig(retry_config=RetryConfig(max_attempts=3, base_delay=0.1))
        parser = LeanParser(config)
        
        with patch.object(parser, '_can_use_lean_extractor', return_value=True), \
             patch.object(parser, '_extract_single_theorem_with_lean') as mock_extract, \
             patch('time.sleep'):  # Speed up test
            
            # First two attempts fail, third succeeds
            mock_extract.side_effect = [
                RuntimeError("First failure"),
                RuntimeError("Second failure"), 
                TheoremInfo(name="test", statement="True")
            ]
            
            result = parser.parse_theorem(test_file, "test")
            
            assert result is not None
            assert result.name == "test"
            assert mock_extract.call_count == 3

    def test_parse_theorem_all_retries_fail(self, tmp_path):
        """Test parse_theorem when all retry attempts fail."""
        test_file = tmp_path / "test.lean"
        test_file.write_text("theorem test : True := trivial")
        
        config = ParserConfig(retry_config=RetryConfig(max_attempts=2, base_delay=0.1))
        parser = LeanParser(config)
        
        with patch.object(parser, '_can_use_lean_extractor', return_value=True), \
             patch.object(parser, '_extract_single_theorem_with_lean') as mock_extract, \
             patch('time.sleep'):  # Speed up test
            
            mock_extract.side_effect = RuntimeError("Persistent failure")
            
            result = parser.parse_theorem(test_file, "test")
            
            assert result is None
            assert mock_extract.call_count == 2

    def test_validate_lean_setup_lean_not_available(self):
        """Test validate_lean_setup when Lean executable not found."""
        parser = LeanParser()
        
        with patch.object(parser, 'check_lean_available', return_value=False):
            result = parser.validate_lean_setup()
            assert result is False

    def test_validate_lean_setup_extractor_missing(self):
        """Test validate_lean_setup when extractor script missing."""
        parser = LeanParser()
        
        with patch.object(parser, 'check_lean_available', return_value=True), \
             patch('pathlib.Path.exists', return_value=False):
            
            result = parser.validate_lean_setup()
            assert result is False

    def test_validate_lean_setup_version_check_failed(self):
        """Test validate_lean_setup when version check fails."""
        parser = LeanParser()
        
        with patch.object(parser, 'check_lean_available', return_value=True), \
             patch('pathlib.Path.exists', return_value=True), \
             patch('subprocess.run') as mock_run:
            
            mock_run.return_value = Mock(returncode=1, stderr="Version check failed")
            
            result = parser.validate_lean_setup()
            assert result is False

    def test_validate_lean_setup_timeout(self):
        """Test validate_lean_setup when version check times out."""
        parser = LeanParser()
        
        with patch.object(parser, 'check_lean_available', return_value=True), \
             patch('pathlib.Path.exists', return_value=True), \
             patch('subprocess.run', side_effect=subprocess.TimeoutExpired("lean", 30)):
            
            result = parser.validate_lean_setup()
            assert result is False

    def test_validate_lean_setup_exception(self):
        """Test validate_lean_setup with unexpected exception."""
        parser = LeanParser()
        
        with patch.object(parser, 'check_lean_available', side_effect=RuntimeError("Unexpected error")):
            result = parser.validate_lean_setup()
            assert result is False

    def test_validate_lean_setup_success_with_lake_warning(self):
        """Test validate_lean_setup success with Lake unavailable warning."""
        parser = LeanParser(ParserConfig(auto_detect_lake=True))
        
        with patch.object(parser, 'check_lean_available', return_value=True), \
             patch.object(parser, 'check_lake_available', return_value=False), \
             patch('pathlib.Path.exists', return_value=True), \
             patch('subprocess.run') as mock_run:
            
            mock_run.return_value = Mock(returncode=0, stdout="Lean 4.0.0")
            
            result = parser.validate_lean_setup()
            assert result is True  # Should still succeed even without Lake

    def test_can_use_lean_extractor_true(self):
        """Test _can_use_lean_extractor returns True when conditions met."""
        parser = LeanParser()
        
        with patch.object(parser, 'check_lean_available', return_value=True), \
             patch('pathlib.Path.exists', return_value=True):
            
            result = parser._can_use_lean_extractor()
            assert result is True

    def test_can_use_lean_extractor_false(self):
        """Test _can_use_lean_extractor returns False when conditions not met."""
        parser = LeanParser()
        
        with patch.object(parser, 'check_lean_available', return_value=False):
            result = parser._can_use_lean_extractor()
            assert result is False

    def test_create_metadata(self, tmp_path, lean_content_with_imports):
        """Test _create_metadata method."""
        test_file = tmp_path / "test.lean"
        test_file.write_text(lean_content_with_imports)
        
        parser = LeanParser()
        metadata = parser._create_metadata(test_file, lean_content_with_imports)
        
        assert metadata.file_path == test_file
        assert metadata.file_size > 0
        assert isinstance(metadata.last_modified, datetime)
        assert len(metadata.imports) == 3
        assert "Mathlib.Data.Nat.Basic" in metadata.imports
        assert metadata.total_lines > 0

    def test_find_lake_project_found(self, tmp_path):
        """Test _find_lake_project when lakefile exists."""
        # Create project structure
        project_dir = tmp_path / "my_project"
        project_dir.mkdir()
        lakefile = project_dir / "lakefile.lean"
        lakefile.write_text("package MyProject")
        
        lean_file = project_dir / "subdir" / "Test.lean"
        lean_file.parent.mkdir(parents=True)
        lean_file.write_text("theorem test : True := trivial")
        
        parser = LeanParser()
        result = parser._find_lake_project(lean_file)
        
        assert result == project_dir

    def test_find_lake_project_not_found(self, tmp_path):
        """Test _find_lake_project when no lakefile exists."""
        lean_file = tmp_path / "Test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        parser = LeanParser()
        result = parser._find_lake_project(lean_file)
        
        assert result is None

    def test_extract_imports(self, lean_content_with_imports):
        """Test _extract_imports method."""
        parser = LeanParser()
        imports = parser._extract_imports(lean_content_with_imports)
        
        assert len(imports) == 3
        assert "Mathlib.Data.Nat.Basic" in imports
        assert "Mathlib.Tactic.Ring" in imports
        assert "Custom.Module" in imports

    def test_extract_imports_no_imports(self):
        """Test _extract_imports with content that has no imports."""
        content = "theorem test : True := trivial"
        parser = LeanParser()
        imports = parser._extract_imports(content)
        
        assert imports == []

    def test_extract_theorems_basic(self, lean_content_complex):
        """Test _extract_theorems_basic method."""
        parser = LeanParser()
        theorems = parser._extract_theorems_basic(lean_content_complex)
        
        assert len(theorems) >= 2  # Should find test_theorem and another_test
        theorem_names = [t.name for t in theorems]
        assert "test_theorem" in theorem_names
        assert "another_test" in theorem_names
        
        # Check theorem details
        test_theorem = next(t for t in theorems if t.name == "test_theorem")
        assert "n + 0 = n" in test_theorem.statement
        assert not test_theorem.is_axiom

    def test_extract_theorems_basic_with_axiom(self):
        """Test _extract_theorems_basic with axiom keyword (axioms not detected by basic parsing)."""
        content = '''
axiom custom_axiom : True
theorem test_theorem : True := trivial
'''
        parser = LeanParser()
        theorems = parser._extract_theorems_basic(content)
        
        # Basic parsing only detects theorem/lemma, not axiom
        theorem_names = [t.name for t in theorems]
        assert "test_theorem" in theorem_names
        assert "custom_axiom" not in theorem_names  # axioms not detected by basic parsing

    def test_extract_statement_simple(self):
        """Test _extract_statement with simple single-line statement."""
        lines = ["theorem simple : True := trivial"]
        parser = LeanParser()
        
        statement = parser._extract_statement(lines, 0)
        assert statement == "True"

    def test_extract_statement_multiline(self):
        """Test _extract_statement with multiline statement."""
        lines = [
            "theorem complex (n m : ℕ) :",
            "  n + m = m + n :="
        ]
        parser = LeanParser()
        
        statement = parser._extract_statement(lines, 0)
        assert "n + m = m + n" in statement

    def test_extract_statement_with_comments(self):
        """Test _extract_statement with comments (comments are preserved in basic parsing)."""
        lines = [
            "theorem test : -- this is a comment",
            "  True := -- another comment",
            "  trivial"
        ]
        parser = LeanParser()
        
        statement = parser._extract_statement(lines, 0)
        # Basic parsing preserves comments, only splits on :=
        assert "-- this is a comment" in statement
        assert "True" in statement

    def test_extract_proof_simple(self):
        """Test _extract_proof with simple proof."""
        lines = ["theorem test : True := trivial"]
        parser = LeanParser()
        
        proof = parser._extract_proof(lines, 0)
        assert proof == "trivial"

    def test_extract_proof_multiline_by(self):
        """Test _extract_proof with multiline 'by' proof."""
        lines = [
            "theorem test : True := by",
            "  trivial",
            "",
            "theorem next : False := sorry"
        ]
        parser = LeanParser()
        
        proof = parser._extract_proof(lines, 0)
        assert "by" in proof
        assert "trivial" in proof
        assert "sorry" not in proof  # Should stop at next theorem

    def test_extract_proof_multiline_structure(self):
        """Test _extract_proof with structured proof."""
        lines = [
            "theorem test : P ∧ Q := ⟨",
            "  proof_of_p,",
            "  proof_of_q⟩"
        ]
        parser = LeanParser()
        
        proof = parser._extract_proof(lines, 0)
        assert "⟨" in proof
        assert "proof_of_p" in proof
        assert "proof_of_q⟩" in proof

    def test_extract_proof_no_proof(self):
        """Test _extract_proof when no proof present."""
        lines = ["theorem test : True"]
        parser = LeanParser()
        
        proof = parser._extract_proof(lines, 0)
        assert proof is None

    def test_check_lean_available_true(self):
        """Test check_lean_available returns True when Lean found."""
        parser = LeanParser()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)
            result = parser.check_lean_available()
            assert result is True

    def test_check_lean_available_false(self):
        """Test check_lean_available returns False when Lean not found."""
        parser = LeanParser()
        
        with patch('subprocess.run', side_effect=FileNotFoundError):
            result = parser.check_lean_available()
            assert result is False

    def test_check_lake_available_true(self):
        """Test check_lake_available returns True when Lake found."""
        parser = LeanParser()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)
            result = parser.check_lake_available()
            assert result is True

    def test_check_lake_available_false(self):
        """Test check_lake_available returns False when Lake not found."""
        parser = LeanParser()
        
        with patch('subprocess.run', side_effect=FileNotFoundError):
            result = parser.check_lake_available()
            assert result is False

    def test_get_lean_version_success(self):
        """Test get_lean_version returns version string."""
        parser = LeanParser()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0, 
                stdout="Lean (version 4.5.0, commit 12345abcd, Release)"
            )
            version = parser.get_lean_version()
            assert version == "Lean (version 4.5.0, commit 12345abcd, Release)"

    def test_get_lean_version_failure(self):
        """Test get_lean_version returns None on failure."""
        parser = LeanParser()
        
        with patch('subprocess.run', side_effect=FileNotFoundError):
            version = parser.get_lean_version()
            assert version is None

    def test_get_lake_version_success(self):
        """Test get_lake_version returns version string."""
        parser = LeanParser()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Lake version 4.5.0 (Lean version 4.5.0)"
            )
            version = parser.get_lake_version()
            assert version == "Lake version 4.5.0 (Lean version 4.5.0)"

    def test_get_lake_version_failure(self):
        """Test get_lake_version returns None on failure."""
        parser = LeanParser()
        
        with patch('subprocess.run', side_effect=FileNotFoundError):
            version = parser.get_lake_version()
            assert version is None


class TestLeanParserLakeProjectSetup:
    """Test Lake project setup functionality."""

    @pytest.fixture
    def parser_with_lake(self):
        """Parser configured for Lake project detection."""
        config = ParserConfig(auto_detect_lake=True)
        return LeanParser(config)

    def test_setup_lake_project_no_project_found(self, parser_with_lake, tmp_path):
        """Test _setup_lake_project when no Lake project found."""
        lean_file = tmp_path / "standalone.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch.object(parser_with_lake, '_find_lake_project', return_value=None):
            errors = parser_with_lake._setup_lake_project(lean_file)
            assert errors == []

    def test_setup_lake_project_build_disabled(self, tmp_path):
        """Test _setup_lake_project when Lake build is disabled."""
        config = ParserConfig(auto_detect_lake=True, lake_build_on_parse=False)
        parser = LeanParser(config)
        
        project_dir = tmp_path / "project" 
        project_dir.mkdir()
        lean_file = project_dir / "Test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch.object(parser, '_find_lake_project', return_value=project_dir):
            errors = parser._setup_lake_project(lean_file)
            assert errors == []

    def test_setup_lake_project_build_success(self, tmp_path):
        """Test _setup_lake_project with successful Lake build."""
        config = ParserConfig(auto_detect_lake=True, lake_build_on_parse=True)
        parser = LeanParser(config)
        
        project_dir = tmp_path / "project"
        project_dir.mkdir()
        
        # Create lakefile.lean to make it a Lake project
        lakefile = project_dir / "lakefile.lean"
        lakefile.write_text("package TestProject")
        
        lean_file = project_dir / "Test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch.object(parser, 'check_lake_available', return_value=True), \
             patch('subprocess.run') as mock_run:
            
            mock_run.return_value = Mock(returncode=0, stdout="Build successful")
            
            errors = parser._setup_lake_project(lean_file)
            assert errors == []
            
            # Verify Lake build was called
            mock_run.assert_called_once()
            call_args = mock_run.call_args[0][0]
            assert "lake" in call_args
            assert "build" in call_args

    def test_setup_lake_project_build_failure(self, tmp_path):
        """Test _setup_lake_project with Lake build failure."""
        config = ParserConfig(auto_detect_lake=True, lake_build_on_parse=True)
        parser = LeanParser(config)
        
        project_dir = tmp_path / "project"
        project_dir.mkdir()
        
        # Create lakefile.lean to make it a Lake project
        lakefile = project_dir / "lakefile.lean"
        lakefile.write_text("package TestProject")
        
        lean_file = project_dir / "Test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch.object(parser, 'check_lake_available', return_value=True), \
             patch('subprocess.run') as mock_run:
            
            mock_run.return_value = Mock(
                returncode=1, 
                stderr="Build failed: dependency not found"
            )
            
            errors = parser._setup_lake_project(lean_file)
            assert len(errors) == 1
            assert "Lake build failed" in errors[0].message

    def test_setup_lake_project_build_timeout(self, tmp_path):
        """Test _setup_lake_project with Lake build timeout."""
        config = ParserConfig(auto_detect_lake=True, lake_build_on_parse=True)
        parser = LeanParser(config)
        
        project_dir = tmp_path / "project"
        project_dir.mkdir()
        
        # Create lakefile.lean to make it a Lake project
        lakefile = project_dir / "lakefile.lean"
        lakefile.write_text("package TestProject")
        
        lean_file = project_dir / "Test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch.object(parser, 'check_lake_available', return_value=True), \
             patch('subprocess.run', side_effect=subprocess.TimeoutExpired("lake", 60)):
            
            errors = parser._setup_lake_project(lean_file)
            assert len(errors) == 1
            assert "Lake build timed out" in errors[0].message


class TestLeanParserLeanExtraction:
    """Test Lean extraction functionality."""

    @pytest.fixture
    def parser_with_lean(self):
        """Parser that can use Lean extractor."""
        parser = LeanParser()
        with patch.object(parser, '_can_use_lean_extractor', return_value=True):
            yield parser

    def test_extract_all_theorems_with_lean_success(self, parser_with_lean, tmp_path):
        """Test _extract_all_theorems_with_lean with successful extraction."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        basic_theorems = [TheoremInfo(name="test", statement="True", proof="trivial")]
        
        mock_json_output = {
            "test": {
                "name": "test",
                "type": "True", 
                "value": "trivial",
                "dependencies": [],
                "line_number": 1
            }
        }
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout=json.dumps(mock_json_output)
            )
            
            theorems, errors = parser_with_lean._extract_all_theorems_with_lean(
                lean_file, basic_theorems
            )
            
            assert len(theorems) == 1
            assert theorems[0].name == "test"
            assert theorems[0].proof == "trivial"
            assert errors == []

    def test_extract_all_theorems_with_lean_json_error(self, parser_with_lean, tmp_path):
        """Test _extract_all_theorems_with_lean with JSON decode error."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        basic_theorems = [TheoremInfo(name="test", statement="True", proof="trivial")]
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="invalid json {"
            )
            
            theorems, errors = parser_with_lean._extract_all_theorems_with_lean(
                lean_file, basic_theorems
            )
            
            # Falls back to basic theorems when JSON parsing fails
            assert len(theorems) == 1
            assert theorems[0].name == "test"
            # No errors are returned for JSON decode issues in this implementation
            assert len(errors) == 0

    def test_extract_single_theorem_with_lean_success(self, parser_with_lean, tmp_path):
        """Test _extract_single_theorem_with_lean with successful extraction."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        mock_json_output = {
            "name": "test",
            "type": "True",
            "value": "trivial", 
            "dependencies": ["Lean.Core"],
            "line_number": 1
        }
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout=json.dumps(mock_json_output)
            )
            
            theorem = parser_with_lean._extract_single_theorem_with_lean(lean_file, "test")
            
            assert theorem is not None
            assert theorem.name == "test"
            assert theorem.statement == "True"
            assert theorem.proof == "trivial"
            assert "Lean.Core" in theorem.dependencies

    def test_extract_single_theorem_with_lean_not_found(self, parser_with_lean, tmp_path):
        """Test _extract_single_theorem_with_lean when theorem not found."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem other : False := sorry")
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=1,
                stderr="Theorem 'test' not found"
            )
            
            theorem = parser_with_lean._extract_single_theorem_with_lean(lean_file, "test")
            assert theorem is None

    def test_extract_single_theorem_with_lean_timeout(self, parser_with_lean, tmp_path):
        """Test _extract_single_theorem_with_lean with timeout."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch('subprocess.run', side_effect=subprocess.TimeoutExpired("lean", 30)):
            with pytest.raises(subprocess.TimeoutExpired):
                parser_with_lean._extract_single_theorem_with_lean(lean_file, "test")