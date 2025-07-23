"""Pydantic models for theorem parsing and representation."""

from __future__ import annotations

from datetime import datetime
from pathlib import Path
from typing import Any

from pydantic import BaseModel, Field


class TheoremInfo(BaseModel):
    """Information about a single theorem extracted from Lean code."""

    name: str = Field(..., description="The theorem name")
    statement: str = Field(..., description="The theorem statement/type")
    proof: str | None = Field(None, description="The proof body if available")
    dependencies: list[str] = Field(
        default_factory=list, description="List of dependencies"
    )
    line_number: int | None = Field(None, description="Line number in source file")
    docstring: str | None = Field(None, description="Associated documentation")
    namespace: str | None = Field(None, description="Lean namespace")
    visibility: str = Field(
        "public", description="Visibility (public, private, protected)"
    )
    tactics: list[str] = Field(
        default_factory=list, description="Tactics used in the proo"
    )
    is_axiom: bool = Field(False, description="Whether this is an axiom")
    file_path: Path | None = Field(None, description="Path to source file")
    start_line: int | None = Field(None, description="Start line in source file")
    end_line: int | None = Field(None, description="End line in source file")

    class Config:
        """Pydantic configuration."""

        str_strip_whitespace = True
        validate_assignment = True


class ParseError(BaseModel):
    """Information about a parsing error."""

    message: str = Field(..., description="Error message")
    line_number: int | None = Field(
        None, description="Line number where error occurred"
    )
    column: int | None = Field(None, description="Column where error occurred")
    error_type: str = Field("parse_error", description="Type of error")
    severity: str = Field("error", description="Severity level (error, warning, info)")

    @classmethod
    def from_exception(cls, exc: Exception) -> "ParseError":
        """Create ParseError from an exception.

        Args:
            exc: Exception to convert

        Returns:
            ParseError instance
        """
        from ..core.exceptions import ParserError

        if isinstance(exc, ParserError):
            return cls(
                message=exc.message,
                error_type=exc.error_code or "parse_error",
                line_number=exc.details.get("line_number"),
                column=exc.details.get("column"),
                severity=exc.details.get("severity", "error"),
            )
        else:
            return cls(
                message=str(exc),
                error_type=exc.__class__.__name__.lower(),
                line_number=None,
                column=None,
                severity="error",
            )


class FileMetadata(BaseModel):
    """Metadata about the parsed Lean file."""

    file_path: Path = Field(..., description="Path to the Lean file")
    file_size: int = Field(..., description="File size in bytes")
    last_modified: datetime = Field(..., description="Last modification time")
    lean_version: str | None = Field(None, description="Lean version if detected")
    imports: list[str] = Field(default_factory=list, description="Import statements")
    total_lines: int = Field(0, description="Total lines in file")

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True


class ParseResult(BaseModel):
    """Result of parsing a Lean file."""

    theorems: list[TheoremInfo] = Field(
        default_factory=list, description="Extracted theorems"
    )
    errors: list[ParseError] = Field(default_factory=list, description="Parsing errors")
    warnings: list[ParseError] = Field(
        default_factory=list, description="Parsing warnings"
    )
    metadata: FileMetadata | None = Field(None, description="File metadata")
    parse_time_ms: float | None = Field(None, description="Parse time in milliseconds")
    success: bool = Field(True, description="Whether parsing was successful")

    @property
    def has_errors(self) -> bool:
        """Check if there are any errors."""
        return len(self.errors) > 0

    @property
    def has_theorems(self) -> bool:
        """Check if any theorems were found."""
        return len(self.theorems) > 0

    def get_theorem_by_name(self, name: str) -> TheoremInfo | None:
        """Get a theorem by name."""
        for theorem in self.theorems:
            if theorem.name == name:
                return theorem
        return None

    def to_dict(self) -> dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return self.dict(by_alias=True)

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True
        validate_assignment = True


class ParserConfig(BaseModel):
    """Basic parser configuration for mathematical notation handling."""

    def convert_to_latex(self, expr: str) -> str:
        """Convert mathematical expression to LaTeX format.

        Args:
            expr: Mathematical expression string

        Returns:
            LaTeX-formatted string
        """
        # Basic LaTeX conversion for common mathematical symbols
        latex_mappings = {
            "∀": r"\forall",
            "∃": r"\exists",
            "ℕ": r"\mathbb{N}",
            "ℝ": r"\mathbb{R}",
            "→": r"\rightarrow",
            "∧": r"\land",
            "∨": r"\lor",
            "¬": r"\neg",
            "⊣": r"\dashv",
            "∇": r"\nabla",
            "×": r"\times",
            "⨆": r"\bigsqcup",
            "⋃": r"\bigcup",
            "∫": r"\int",
            "π": r"\pi",
        }

        result = expr
        for symbol, latex in latex_mappings.items():
            result = result.replace(symbol, latex)

        return result
