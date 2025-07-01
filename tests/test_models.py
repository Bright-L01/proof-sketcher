"""Tests for Pydantic models."""

from datetime import datetime

import pytest

from proof_sketcher.parser.models import (
    FileMetadata,
    ParseError,
    ParseResult,
    TheoremInfo,
)


class TestTheoremInfo:
    """Tests for TheoremInfo model."""

    def test_theorem_info_creation(self):
        """Test basic theorem info creation."""
        theorem = TheoremInfo(name="test_theorem", statement="∀ n : ℕ, n + 0 = n")
        assert theorem.name == "test_theorem"
        assert theorem.statement == "∀ n : ℕ, n + 0 = n"
        assert theorem.proof is None
        assert theorem.dependencies == []
        assert theorem.visibility == "public"

    def test_theorem_info_with_proof(self):
        """Test theorem info with proof."""
        theorem = TheoremInfo(
            name="add_zero",
            statement="∀ n : ℕ, n + 0 = n",
            proof="by simp",
            dependencies=["Nat.add_zero"],
            line_number=10,
            namespace="MyNamespace",
        )
        assert theorem.proof == "by simp"
        assert theorem.dependencies == ["Nat.add_zero"]
        assert theorem.line_number == 10
        assert theorem.namespace == "MyNamespace"

    def test_theorem_info_validation(self):
        """Test validation of theorem info."""
        with pytest.raises(ValueError):
            TheoremInfo()  # Missing required fields


class TestParseError:
    """Tests for ParseError model."""

    def test_parse_error_creation(self):
        """Test basic parse error creation."""
        error = ParseError(message="Syntax error")
        assert error.message == "Syntax error"
        assert error.error_type == "parse_error"
        assert error.severity == "error"

    def test_parse_error_with_location(self):
        """Test parse error with location info."""
        error = ParseError(
            message="Expected ':'",
            line_number=15,
            column=23,
            error_type="syntax_error",
            severity="warning",
        )
        assert error.line_number == 15
        assert error.column == 23
        assert error.error_type == "syntax_error"
        assert error.severity == "warning"


class TestFileMetadata:
    """Tests for FileMetadata model."""

    def test_file_metadata_creation(self, tmp_path):
        """Test file metadata creation."""
        test_file = tmp_path / "test.lean"
        test_file.write_text("-- Test file", encoding="utf-8")

        metadata = FileMetadata(
            file_path=test_file,
            file_size=100,
            last_modified=datetime.now(),
            imports=["Mathlib.Algebra.Basic"],
            total_lines=5,
        )

        assert metadata.file_path == test_file
        assert metadata.file_size == 100
        assert metadata.imports == ["Mathlib.Algebra.Basic"]
        assert metadata.total_lines == 5


class TestParseResult:
    """Tests for ParseResult model."""

    def test_empty_parse_result(self):
        """Test empty parse result."""
        result = ParseResult()
        assert result.theorems == []
        assert result.errors == []
        assert result.warnings == []
        assert result.success is True
        assert not result.has_errors
        assert not result.has_theorems

    def test_parse_result_with_theorems(self):
        """Test parse result with theorems."""
        theorem1 = TheoremInfo(name="thm1", statement="P → P")
        theorem2 = TheoremInfo(name="thm2", statement="P ∨ ¬P")

        result = ParseResult(theorems=[theorem1, theorem2])
        assert len(result.theorems) == 2
        assert result.has_theorems
        assert result.get_theorem_by_name("thm1") == theorem1
        assert result.get_theorem_by_name("nonexistent") is None

    def test_parse_result_with_errors(self):
        """Test parse result with errors."""
        error = ParseError(message="Test error")
        result = ParseResult(errors=[error], success=False)

        assert result.has_errors
        assert not result.success
        assert len(result.errors) == 1

    def test_parse_result_to_dict(self):
        """Test conversion to dictionary."""
        theorem = TheoremInfo(name="test", statement="P")
        result = ParseResult(theorems=[theorem])

        result_dict = result.to_dict()
        assert isinstance(result_dict, dict)
        assert "theorems" in result_dict
        assert len(result_dict["theorems"]) == 1
