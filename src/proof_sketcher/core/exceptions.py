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


class FormulaExtractionError(AnimatorError):
    """Raised when formula extraction fails."""

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


# Batch Processing Exceptions
class BatchProcessingError(ProofSketcherError):
    """Base exception for batch processing errors."""

    pass


class BatchFileError(BatchProcessingError):
    """Raised when individual file processing fails in batch mode."""

    pass


# Resource Management Exceptions
class ResourceError(ProofSketcherError):
    """Base exception for resource-related errors."""

    def __init__(
        self,
        message: str,
        details: Optional[Dict[str, Any]] = None,
        error_code: Optional[str] = None,
        context: Optional[Dict[str, Any]] = None,
    ):
        """Initialize resource error.
        
        Args:
            message: Error message
            details: Additional error context
            error_code: Optional error code
            context: Additional context (alias for details)
        """
        # Merge context into details for backward compatibility
        if context and details:
            details.update(context)
        elif context:
            details = context
            
        super().__init__(message, details, error_code)
        self.context = details or {}


class DiskSpaceError(ResourceError):
    """Raised when disk space is insufficient."""

    def __init__(
        self,
        message: str,
        required_space: Optional[int] = None,
        available_space: Optional[int] = None,
        details: Optional[Dict[str, Any]] = None,
        error_code: Optional[str] = None,
    ):
        """Initialize disk space error.
        
        Args:
            message: Error message
            required_space: Required space in bytes
            available_space: Available space in bytes
            details: Additional error context
            error_code: Optional error code
        """
        # Add space info to context
        if details is None:
            details = {}
        
        if required_space:
            details["required_space_mb"] = required_space // (1024 * 1024)
        if available_space:
            details["available_space_mb"] = available_space // (1024 * 1024)
            
        super().__init__(message, details, error_code)
        self.required_space = required_space
        self.available_space = available_space
        self.context = details


class MemoryError(ResourceError):
    """Raised when memory usage exceeds limits."""

    def __init__(
        self,
        message: str,
        context: Optional[Dict[str, Any]] = None,
        details: Optional[Dict[str, Any]] = None,
        error_code: Optional[str] = None,
    ):
        """Initialize memory error.
        
        Args:
            message: Error message
            context: Memory usage context
            details: Additional error context
            error_code: Optional error code
        """
        super().__init__(message, details, error_code)
        self.context = context or {}
    
    def get_full_message(self) -> str:
        """Get full error message with recovery suggestions."""
        base_msg = str(self)
        suggestions = [
            "Close other applications to free memory",
            "Reduce batch size if processing multiple files",
            "Consider using streaming mode for large files"
        ]
        return f"{base_msg}\n\nSuggestions:\n" + "\n".join(f"- {s}" for s in suggestions)


class NetworkError(ResourceError):
    """Raised when network operations fail."""

    def __init__(
        self,
        message: str,
        operation: Optional[str] = None,
        context: Optional[Dict[str, Any]] = None,
        details: Optional[Dict[str, Any]] = None,
        error_code: Optional[str] = None,
    ):
        """Initialize network error.
        
        Args:
            message: Error message
            operation: The network operation that failed
            context: Additional context (alias for details)
            details: Additional error context
            error_code: Optional error code
        """
        # Merge context into details for backward compatibility
        if context and details:
            details.update(context)
        elif context:
            details = context
            
        super().__init__(message, details, error_code)
        self.operation = operation
        self.context = details or {}
        
        # Add recovery strategies for network errors
        self.recovery_strategies = [
            type('RecoveryStrategy', (), {'value': 'retry'}),
            type('RecoveryStrategy', (), {'value': 'fallback'}),
            type('RecoveryStrategy', (), {'value': 'cache'})
        ]


class ErrorHandler:
    """Simple error handler for managing and logging errors."""

    def __init__(self, auto_recover: bool = True):
        """Initialize error handler.
        
        Args:
            auto_recover: Whether to attempt automatic recovery
        """
        self.auto_recover = auto_recover
        self.logger = self._setup_logger()
        self.error_counts = {}
        self.recovery_counts = {}

    def _setup_logger(self):
        """Set up logger for error handling."""
        import logging
        logger = logging.getLogger(f"{__name__}.ErrorHandler")
        return logger

    def handle(self, error: Exception, context: Optional[Dict[str, Any]] = None) -> Optional[Any]:
        """Handle an error with optional context.
        
        Args:
            error: The exception to handle
            context: Additional context for error handling
            
        Returns:
            None or recovery result if auto_recover is enabled
        """
        error_type = type(error).__name__
        self.error_counts[error_type] = self.error_counts.get(error_type, 0) + 1
        
        if isinstance(error, ProofSketcherError):
            self.logger.error(f"ProofSketcherError: {error}")
            if hasattr(error, 'details') and error.details:
                self.logger.debug(f"Error details: {error.details}")
        else:
            self.logger.error(f"Unexpected error: {error}")
        
        if context:
            self.logger.debug(f"Error context: {context}")
        
        return None
    
    def handle_error(self, error: Exception, auto_recover: bool = True, context: Optional[Dict[str, Any]] = None) -> Optional[Any]:
        """Handle error with recovery attempts (alias for handle method)."""
        result = self.handle(error, context)
        
        # Track recovery attempts
        if auto_recover and self.auto_recover:
            error_type = type(error).__name__
            recovery_count = self.recovery_counts.get(error_type, 0)
            if recovery_count < 3:  # Max 3 recovery attempts per error type
                self.recovery_counts[error_type] = recovery_count + 1
                
        return result
    
    def _wrap_error(self, original_error: Exception) -> ProofSketcherError:
        """Wrap a standard exception into a ProofSketcherError."""
        if isinstance(original_error, ConnectionError):
            return NetworkError(str(original_error), operation="connection")
        elif isinstance(original_error, FileNotFoundError):
            error = ParserError(str(original_error), error_code="FILE_NOT_FOUND")
            error.category = type('Category', (), {'value': 'parse'})()
            return error
        elif isinstance(original_error, (MemoryError, OSError)):
            return ResourceError(str(original_error))
        else:
            return ProofSketcherError(str(original_error))
    
    def get_error_summary(self) -> Dict[str, Any]:
        """Get summary of error handling statistics."""
        return {
            "total_errors": sum(self.error_counts.values()),
            "total_recoveries": sum(self.recovery_counts.values()),
            "error_counts": self.error_counts.copy(),
            "recovery_counts": self.recovery_counts.copy()
        }


# Alias for backward compatibility with generator.offline
GenerationError = GeneratorError


def handle_error(
    error: Exception,
    context: Optional[Dict[str, Any]] = None,
    auto_recover: bool = True
) -> Optional[Any]:
    """Simple error handler for backward compatibility.
    
    Args:
        error: The exception to handle
        context: Additional context (unused in simple implementation)
        auto_recover: Whether to attempt recovery (unused in simple implementation)
        
    Returns:
        None (simple implementation just logs the error)
    """
    import logging
    logger = logging.getLogger(__name__)
    
    if isinstance(error, ProofSketcherError):
        logger.error(f"ProofSketcherError: {error}")
    else:
        logger.error(f"Unexpected error: {error}")
    
    return None
