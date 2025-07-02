"""Comprehensive error handling system for Proof Sketcher.

Features:
- Hierarchical error classification
- Helpful error messages with context
- Recovery strategies and fallback options
- Error aggregation and reporting
- Integration with logging system
"""

import logging
import traceback
from enum import Enum
from typing import Dict, List, Optional, Any, Union, Callable
from pathlib import Path


class ErrorSeverity(str, Enum):
    """Error severity levels."""
    CRITICAL = "critical"  # System cannot continue
    HIGH = "high"         # Major functionality broken
    MEDIUM = "medium"     # Some features affected
    LOW = "low"          # Minor issues, warnings


class ErrorCategory(str, Enum):
    """Error categories for classification."""
    PARSE = "parse"           # Lean file parsing errors
    GENERATION = "generation" # AI generation errors
    ANIMATION = "animation"   # Animation creation errors
    EXPORT = "export"        # Output generation errors
    SYSTEM = "system"        # System-level errors
    NETWORK = "network"      # Network connectivity errors
    RESOURCE = "resource"    # Resource management errors
    VALIDATION = "validation" # Input validation errors


class RecoveryStrategy(str, Enum):
    """Available recovery strategies."""
    RETRY = "retry"                    # Retry operation
    FALLBACK = "fallback"             # Use fallback method
    SKIP = "skip"                     # Skip and continue
    CACHE = "cache"                   # Use cached result
    OFFLINE = "offline"               # Switch to offline mode
    MANUAL = "manual"                 # Require manual intervention
    ABORT = "abort"                   # Cannot recover


class ProofSketcherError(Exception):
    """Base exception class for all Proof Sketcher errors."""
    
    def __init__(
        self,
        message: str,
        *,
        category: ErrorCategory,
        severity: ErrorSeverity = ErrorSeverity.MEDIUM,
        recovery_strategies: Optional[List[RecoveryStrategy]] = None,
        context: Optional[Dict[str, Any]] = None,
        cause: Optional[Exception] = None,
        help_text: Optional[str] = None,
        suggestions: Optional[List[str]] = None
    ):
        """Initialize error with comprehensive context.
        
        Args:
            message: Primary error message
            category: Error category for classification
            severity: How severe this error is
            recovery_strategies: Available recovery options
            context: Additional context information
            cause: Original exception that caused this error
            help_text: Detailed help information
            suggestions: List of specific suggestions to fix the issue
        """
        super().__init__(message)
        self.category = category
        self.severity = severity
        self.recovery_strategies = recovery_strategies or []
        self.context = context or {}
        self.cause = cause
        self.help_text = help_text
        self.suggestions = suggestions or []
        
        # Add traceback if there's a cause
        if cause:
            self.cause_traceback = traceback.format_exception(type(cause), cause, cause.__traceback__)
        else:
            self.cause_traceback = None
    
    def get_full_message(self) -> str:
        """Get comprehensive error message with all context."""
        lines = [f"[{self.category.value.upper()}] {self}"]
        
        if self.context:
            lines.append("Context:")
            for key, value in self.context.items():
                lines.append(f"  {key}: {value}")
        
        if self.cause:
            lines.append(f"Caused by: {type(self.cause).__name__}: {self.cause}")
        
        if self.suggestions:
            lines.append("Suggestions:")
            for suggestion in self.suggestions:
                lines.append(f"  • {suggestion}")
        
        if self.help_text:
            lines.append(f"Help: {self.help_text}")
        
        if self.recovery_strategies:
            strategies = ", ".join(s.value for s in self.recovery_strategies)
            lines.append(f"Recovery options: {strategies}")
        
        return "\n".join(lines)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert error to dictionary for serialization."""
        return {
            "type": type(self).__name__,
            "message": str(self),
            "category": self.category.value,
            "severity": self.severity.value,
            "recovery_strategies": [s.value for s in self.recovery_strategies],
            "context": self.context,
            "cause": str(self.cause) if self.cause else None,
            "help_text": self.help_text,
            "suggestions": self.suggestions
        }


class ParseError(ProofSketcherError):
    """Errors related to parsing Lean files."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            category=ErrorCategory.PARSE,
            **kwargs
        )


class LeanSyntaxError(ParseError):
    """Lean file has syntax errors."""
    
    def __init__(
        self,
        message: str,
        file_path: Optional[Path] = None,
        line_number: Optional[int] = None,
        column: Optional[int] = None,
        **kwargs: Any
    ) -> None:
        context = kwargs.get('context', {})
        if file_path:
            context['file_path'] = str(file_path)
        if line_number:
            context['line_number'] = line_number
        if column:
            context['column'] = column
            
        super().__init__(
            message,
            context=context,
            recovery_strategies=[RecoveryStrategy.MANUAL, RecoveryStrategy.SKIP],
            suggestions=[
                "Check Lean syntax in the specified file and line",
                "Use 'lean --check' to validate the file",
                "Ensure all imports are available"
            ],
            help_text="Lean syntax errors must be fixed manually before processing.",
            **kwargs
        )


class LeanNotFoundError(ParseError):
    """Lean executable not found."""
    
    def __init__(self, **kwargs: Any) -> None:
        super().__init__(
            "Lean executable not found in PATH",
            severity=ErrorSeverity.HIGH,
            recovery_strategies=[RecoveryStrategy.OFFLINE, RecoveryStrategy.MANUAL],
            suggestions=[
                "Install Lean 4 from https://leanprover.github.io/lean4/doc/quickstart.html",
                "Ensure 'lean' is in your PATH",
                "Use --offline mode for basic functionality"
            ],
            help_text="Proof Sketcher requires Lean 4 for parsing .lean files. Use offline mode for basic AST-based explanations.",
            **kwargs
        )


class GenerationError(ProofSketcherError):
    """Errors related to AI generation."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            category=ErrorCategory.GENERATION,
            **kwargs
        )


class NetworkError(ProofSketcherError):
    """Network connectivity issues."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            category=ErrorCategory.NETWORK,
            severity=ErrorSeverity.HIGH,
            recovery_strategies=[RecoveryStrategy.RETRY, RecoveryStrategy.CACHE, RecoveryStrategy.OFFLINE],
            suggestions=[
                "Check internet connectivity",
                "Verify API credentials",
                "Use cached responses if available",
                "Switch to offline mode"
            ],
            help_text="Network issues can often be resolved by retrying or using cached content.",
            **kwargs
        )


class APIError(GenerationError):
    """API-related errors."""
    
    def __init__(
        self,
        message: str,
        status_code: Optional[int] = None,
        api_response: Optional[str] = None,
        **kwargs: Any
    ) -> None:
        context = kwargs.get('context', {})
        if status_code:
            context['status_code'] = status_code
        if api_response:
            context['api_response'] = api_response[:500]  # Truncate long responses
            
        recovery_strategies = [RecoveryStrategy.RETRY, RecoveryStrategy.CACHE]
        if status_code and status_code >= 500:
            # Server error - retry makes sense
            recovery_strategies.insert(0, RecoveryStrategy.RETRY)
        elif status_code and 400 <= status_code < 500:
            # Client error - manual intervention needed
            recovery_strategies = [RecoveryStrategy.MANUAL, RecoveryStrategy.CACHE]
            
        super().__init__(
            message,
            context=context,
            recovery_strategies=recovery_strategies,
            suggestions=[
                "Check API rate limits and quotas",
                "Verify request format and parameters",
                "Use cached response if available"
            ],
            **kwargs
        )


class AnimationError(ProofSketcherError):
    """Errors related to animation generation."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            category=ErrorCategory.ANIMATION,
            **kwargs
        )


class ManimError(AnimationError):
    """Manim-related errors."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            recovery_strategies=[RecoveryStrategy.FALLBACK, RecoveryStrategy.SKIP],
            suggestions=[
                "Check Manim installation and dependencies",
                "Use fallback static animation generation",
                "Skip animation generation and continue with text output"
            ],
            help_text="Animation failures don't stop proof generation. Static fallbacks are available.",
            **kwargs
        )


class ExportError(ProofSketcherError):
    """Errors related to output generation."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            category=ErrorCategory.EXPORT,
            **kwargs
        )


class TemplateError(ExportError):
    """Template-related errors."""
    
    def __init__(
        self,
        message: str,
        template_name: Optional[str] = None,
        **kwargs: Any
    ) -> None:
        context = kwargs.get('context', {})
        if template_name:
            context['template_name'] = template_name
            
        super().__init__(
            message,
            context=context,
            recovery_strategies=[RecoveryStrategy.FALLBACK, RecoveryStrategy.MANUAL],
            suggestions=[
                "Check template syntax and variables",
                "Ensure all required template data is provided",
                "Use default template as fallback"
            ],
            **kwargs
        )


class ResourceError(ProofSketcherError):
    """Resource management errors."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            category=ErrorCategory.RESOURCE,
            **kwargs
        )


class DiskSpaceError(ResourceError):
    """Insufficient disk space."""
    
    def __init__(
        self,
        message: str,
        required_space: Optional[int] = None,
        available_space: Optional[int] = None,
        **kwargs: Any
    ) -> None:
        context = kwargs.get('context', {})
        if required_space:
            context['required_space_mb'] = required_space // (1024 * 1024)
        if available_space:
            context['available_space_mb'] = available_space // (1024 * 1024)
            
        super().__init__(
            message,
            context=context,
            severity=ErrorSeverity.HIGH,
            recovery_strategies=[RecoveryStrategy.MANUAL, RecoveryStrategy.ABORT],
            suggestions=[
                "Free up disk space by removing unnecessary files",
                "Choose a different output directory",
                "Reduce output quality or skip animations"
            ],
            **kwargs
        )


class MemoryError(ResourceError):
    """Memory-related errors."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            severity=ErrorSeverity.HIGH,
            recovery_strategies=[RecoveryStrategy.RETRY, RecoveryStrategy.MANUAL],
            suggestions=[
                "Close other applications to free memory",
                "Process files in smaller batches",
                "Reduce animation quality or skip animations"
            ],
            **kwargs
        )


class ValidationError(ProofSketcherError):
    """Input validation errors."""
    
    def __init__(self, message: str, **kwargs: Any) -> None:
        super().__init__(
            message,
            category=ErrorCategory.VALIDATION,
            recovery_strategies=[RecoveryStrategy.MANUAL],
            **kwargs
        )


class ErrorHandler:
    """Global error handler with logging and recovery."""
    
    def __init__(self, logger: Optional[logging.Logger] = None):
        """Initialize error handler.
        
        Args:
            logger: Logger instance for error reporting
        """
        self.logger = logger or logging.getLogger(__name__)
        self.error_counts: Dict[str, int] = {}
        self.recovery_attempts: Dict[str, int] = {}
        
    def handle_error(
        self,
        error: Exception,
        context: Optional[Dict[str, Any]] = None,
        auto_recover: bool = True
    ) -> Optional[Any]:
        """Handle an error with optional auto-recovery.
        
        Args:
            error: The error that occurred
            context: Additional context information
            auto_recover: Whether to attempt automatic recovery
            
        Returns:
            Recovery result if successful, None otherwise
        """
        # Convert to ProofSketcherError if needed
        if not isinstance(error, ProofSketcherError):
            error = self._wrap_error(error, context)
        
        # Log the error
        self._log_error(error)
        
        # Track error counts
        error_key = f"{type(error).__name__}:{str(error)[:100]}"
        self.error_counts[error_key] = self.error_counts.get(error_key, 0) + 1
        
        # Attempt recovery if enabled
        if auto_recover and error.recovery_strategies:
            return self._attempt_recovery(error)
        
        return None
    
    def _wrap_error(self, error: Exception, context: Optional[Dict[str, Any]] = None) -> ProofSketcherError:
        """Wrap a generic exception in ProofSketcherError."""
        error_type = type(error).__name__
        
        # Map common errors to specific types
        if "network" in str(error).lower() or "connection" in str(error).lower():
            return NetworkError(str(error), cause=error, context=context)
        elif "file" in str(error).lower() or "path" in str(error).lower():
            return ParseError(str(error), cause=error, context=context)
        elif "memory" in str(error).lower():
            return MemoryError(str(error), cause=error, context=context)
        else:
            return ProofSketcherError(
                str(error),
                category=ErrorCategory.SYSTEM,
                cause=error,
                context=context
            )
    
    def _log_error(self, error: ProofSketcherError) -> None:
        """Log error with appropriate level."""
        if error.severity == ErrorSeverity.CRITICAL:
            self.logger.critical(error.get_full_message())
        elif error.severity == ErrorSeverity.HIGH:
            self.logger.error(error.get_full_message())
        elif error.severity == ErrorSeverity.MEDIUM:
            self.logger.warning(error.get_full_message())
        else:
            self.logger.info(error.get_full_message())
    
    def _attempt_recovery(self, error: ProofSketcherError) -> Optional[Any]:
        """Attempt to recover from an error."""
        recovery_key = f"{type(error).__name__}:{error.category.value}"
        attempts = self.recovery_attempts.get(recovery_key, 0)
        
        # Limit recovery attempts to prevent infinite loops
        if attempts >= 3:
            self.logger.warning(f"Maximum recovery attempts reached for {recovery_key}")
            return None
        
        self.recovery_attempts[recovery_key] = attempts + 1
        
        for strategy in error.recovery_strategies:
            try:
                result = self._execute_recovery_strategy(strategy, error)
                if result is not None:
                    self.logger.info(f"Successfully recovered using {strategy.value} strategy")
                    return result
            except Exception as e:
                self.logger.warning(f"Recovery strategy {strategy.value} failed: {e}")
        
        return None
    
    def _execute_recovery_strategy(
        self,
        strategy: RecoveryStrategy,
        error: ProofSketcherError
    ) -> Optional[Any]:
        """Execute a specific recovery strategy."""
        if strategy == RecoveryStrategy.CACHE:
            # Try to find cached result
            return self._try_cache_recovery(error)
        elif strategy == RecoveryStrategy.FALLBACK:
            # Use fallback method
            return self._try_fallback_recovery(error)
        elif strategy == RecoveryStrategy.OFFLINE:
            # Switch to offline mode
            return self._try_offline_recovery(error)
        else:
            # Other strategies require external intervention
            return None
    
    def _try_cache_recovery(self, error: ProofSketcherError) -> Optional[Any]:
        """Attempt cache-based recovery."""
        # This would integrate with the cache system
        # For now, return None as cache integration is handled elsewhere
        return None
    
    def _try_fallback_recovery(self, error: ProofSketcherError) -> Optional[Any]:
        """Attempt fallback recovery."""
        # This would use fallback methods specific to each error type
        # Implementation depends on the specific subsystem
        return None
    
    def _try_offline_recovery(self, error: ProofSketcherError) -> Optional[Any]:
        """Attempt offline mode recovery."""
        # This would switch to offline mode and retry
        # Implementation depends on offline mode capabilities
        return None
    
    def get_error_summary(self) -> Dict[str, Any]:
        """Get summary of errors and recovery attempts."""
        return {
            "error_counts": dict(self.error_counts),
            "recovery_attempts": dict(self.recovery_attempts),
            "total_errors": sum(self.error_counts.values()),
            "total_recoveries": sum(self.recovery_attempts.values())
        }
    
    def reset_stats(self) -> None:
        """Reset error tracking statistics."""
        self.error_counts.clear()
        self.recovery_attempts.clear()


# Global error handler instance
global_error_handler = ErrorHandler()


def handle_error(
    error: Exception,
    context: Optional[Dict[str, Any]] = None,
    auto_recover: bool = True
) -> Optional[Any]:
    """Convenience function for global error handling."""
    return global_error_handler.handle_error(error, context, auto_recover)


def create_helpful_error(
    error_class: type,
    message: str,
    **kwargs: Any
) -> ProofSketcherError:
    """Create a helpful error with context-appropriate suggestions."""
    if issubclass(error_class, ProofSketcherError):
        return error_class(message, **kwargs)
    else:
        # Wrap in generic ProofSketcherError
        return ProofSketcherError(message, category=ErrorCategory.SYSTEM, **kwargs)