"""Centralized exception definitions for Proof Sketcher.

This module defines the exception hierarchy used throughout the application.
All custom exceptions should inherit from ProofSketcherError.
"""

from typing import Any, Dict, Optional


class ProofSketcherError(Exception):
    """Base exception for all Proof Sketcher errors.

    Attributes:
        message: Human-readable error message
        details: Optional dictionary with additional error context
        error_code: Optional error code for programmatic handling
    """

    def __init__(
        self,
        message: str,
        details: Optional[Dict[str, Any]] = None,
        error_code: Optional[str] = None,
    ):
        """Initialize the error.

        Args:
            message: Human-readable error message
            details: Optional dictionary with additional error context
            error_code: Optional error code for programmatic handling
        """
        super().__init__(message)
        self.message = message
        self.details = details or {}
        self.error_code = error_code

    def __str__(self) -> str:
        """Return string representation of the error."""
        if self.error_code:
            return f"[{self.error_code}] {self.message}"
        return self.message


# Parser Exceptions
class ParserError(ProofSketcherError):
    """Base exception for parser-related errors."""

    pass


class LeanExecutableError(ParserError):
    """Raised when Lean executable is not found or fails."""

    pass


class LeanSyntaxError(ParserError):
    """Raised when Lean file contains syntax errors."""

    pass


class LeanTimeoutError(ParserError):
    """Raised when Lean parsing times out."""

    pass


# Generator Exceptions
class GeneratorError(ProofSketcherError):
    """Base exception for generator-related errors."""

    pass


class AIExecutableError(GeneratorError):
    """Raised when AI CLI tool is not found or fails."""

    pass


class AITimeoutError(GeneratorError):
    """Raised when AI generation times out."""

    pass


class PromptError(GeneratorError):
    """Raised when prompt template processing fails."""

    pass


# Animator Exceptions
class AnimatorError(ProofSketcherError):
    """Base exception for animator-related errors."""

    pass


class AnimationTimeoutError(AnimatorError):
    """Raised when animation generation times out."""

    pass


class MCPConnectionError(AnimatorError):
    """Raised when MCP server connection fails."""

    pass


class SceneGenerationError(AnimatorError):
    """Raised when scene generation fails."""

    pass


# Exporter Exceptions
class ExporterError(ProofSketcherError):
    """Base exception for exporter-related errors."""

    pass


class TemplateError(ExporterError):
    """Raised when template processing fails."""

    pass


class ExportFormatError(ExporterError):
    """Raised when export format is unsupported or invalid."""

    pass


class FileWriteError(ExporterError):
    """Raised when file writing operations fail."""

    pass


# Configuration Exceptions
class ConfigError(ProofSketcherError):
    """Base exception for configuration-related errors."""

    pass


class ConfigNotFoundError(ConfigError):
    """Raised when configuration file is not found."""

    pass


class ConfigValidationError(ConfigError):
    """Raised when configuration validation fails."""

    pass


# Cache Exceptions
class CacheError(ProofSketcherError):
    """Base exception for cache-related errors."""

    pass


class CacheKeyError(CacheError):
    """Raised when cache key generation fails."""

    pass


class CacheReadError(CacheError):
    """Raised when cache read operation fails."""

    pass


class CacheWriteError(CacheError):
    """Raised when cache write operation fails."""

    pass


# Validation Exceptions
class ValidationError(ProofSketcherError):
    """Base exception for validation errors."""

    pass


class ModelValidationError(ValidationError):
    """Raised when model validation fails."""

    pass


class InputValidationError(ValidationError):
    """Raised when input validation fails."""

    pass
