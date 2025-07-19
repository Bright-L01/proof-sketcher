"""Core exceptions for Proof Sketcher."""

from typing import Any


class ProofSketcherError(Exception):
    """Base exception for all Proof Sketcher errors."""
    
    def __init__(self, message: str, details: dict[str, Any] | None = None):
        """Initialize with message and optional details."""
        super().__init__(message)
        self.details = details or {}


class ConfigError(ProofSketcherError):
    """Base configuration error."""


class ConfigNotFoundError(ConfigError):
    """Configuration file not found."""


class ConfigValidationError(ConfigError):
    """Configuration validation failed."""


# Parser exceptions
class ParserError(ProofSketcherError):
    """Base parser error."""


class FileParseError(ParserError):
    """Error parsing Lean file."""
    
    def __init__(self, file_path: str, message: str, line_number: int | None = None):
        """Initialize with file details."""
        details = {"file_path": file_path}
        if line_number is not None:
            details["line_number"] = line_number
        super().__init__(message, details)


class LSPError(ParserError):
    """Error with LSP operations."""


class LSPConnectionError(LSPError):
    """Failed to connect to LSP server."""


class LSPTimeoutError(LSPError):
    """LSP operation timed out."""


# Generator exceptions
class GeneratorError(ProofSketcherError):
    """Base generator error."""


class GenerationFailedError(GeneratorError):
    """Failed to generate proof sketch."""


# Exporter exceptions
class ExporterError(ProofSketcherError):
    """Base exporter error."""


class ExportFailedError(ExporterError):
    """Failed to export proof sketch."""
    
    def __init__(self, format: str, message: str, file_path: str | None = None):
        """Initialize with export details."""
        details = {"format": format}
        if file_path:
            details["file_path"] = file_path
        super().__init__(message, details)


# Resource exceptions
class ResourceError(ProofSketcherError):
    """Base resource error."""


class ResourceLimitExceeded(ResourceError):
    """Resource limit exceeded."""
    
    def __init__(self, resource_type: str, limit: Any, current: Any):
        """Initialize with resource details."""
        message = f"{resource_type} limit exceeded: {current} > {limit}"
        details = {
            "resource_type": resource_type,
            "limit": limit,
            "current": current
        }
        super().__init__(message, details)


class RateLimitExceeded(ResourceLimitExceeded):
    """Rate limit exceeded."""
    
    def __init__(self, calls: int, window: float):
        """Initialize with rate limit details."""
        super().__init__("Rate", f"{calls} calls/{window}s", "exceeded")


# Input validation exceptions  
class ValidationError(ProofSketcherError):
    """Input validation error."""


class InvalidPathError(ValidationError):
    """Invalid file path."""


class InvalidTheoremNameError(ValidationError):
    """Invalid theorem name."""
