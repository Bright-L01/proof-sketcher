"""Error handling utilities and patterns for Proof Sketcher."""

from __future__ import annotations

import functools
import logging
import sys
import traceback
from contextlib import contextmanager
from typing import Any, Callable, TypeVar

from .exceptions import ProofSketcherError

T = TypeVar("T")


def setup_error_logger(name: str) -> logging.Logger:
    """Set up a logger with proper error formatting.

    Args:
        name: Logger name (usually __name__)

    Returns:
        Configured logger
    """
    logger = logging.getLogger(name)

    if not logger.handlers:
        handler = logging.StreamHandler(sys.stderr)
        formatter = logging.Formatter(
            "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
        )
        handler.setFormatter(formatter)
        logger.addHandler(handler)
        logger.setLevel(logging.INFO)

    return logger


@contextmanager
def error_context(operation: str, logger: logging.Logger | None = None):
    """Context manager for consistent error handling.

    Args:
        operation: Description of the operation being performed
        logger: Optional logger for error messages

    Example:
        with error_context("parsing file", logger):
            # code that might raise exceptions
    """
    try:
        yield
    except ProofSketcherError:
        # Re-raise our own exceptions
        raise
    except Exception as e:
        if logger:
            logger.error(f"Error during {operation}: {e}", exc_info=True)

        # Wrap unexpected exceptions
        raise ProofSketcherError(
            f"Unexpected error during {operation}: {e}",
            details={
                "operation": operation,
                "original_error": str(e),
                "traceback": traceback.format_exc(),
            },
        ) from e


def handle_errors(
    default_return: Any = None,
    logger: logging.Logger | None = None,
    reraise: bool = False,
):
    """Decorator for consistent error handling in functions.

    Args:
        default_return: Value to return on error
        logger: Logger for error messages
        reraise: Whether to re-raise exceptions after logging

    Example:
        @handle_errors(default_return=None, logger=logger)
        def process_theorem(theorem):
            # code that might raise exceptions
    """

    def decorator(func: Callable[..., T]) -> Callable[..., T | Any]:
        @functools.wraps(func)
        def wrapper(*args, **kwargs) -> T | Any:
            operation = f"{func.__module__}.{func.__name__}"

            try:
                return func(*args, **kwargs)
            except ProofSketcherError as e:
                if logger:
                    logger.error(
                        f"Error in {operation}: {e}", extra={"details": e.details}
                    )
                if reraise:
                    raise
                return default_return
            except Exception as e:
                if logger:
                    logger.error(f"Unexpected error in {operation}: {e}", exc_info=True)
                if reraise:
                    raise ProofSketcherError(
                        f"Unexpected error in {operation}",
                        details={
                            "function": operation,
                            "error": str(e),
                            "traceback": traceback.format_exc(),
                        },
                    ) from e
                return default_return

        return wrapper

    return decorator


class ErrorAccumulator:
    """Accumulate errors without stopping execution.

    Useful for batch operations where you want to collect all errors
    before reporting them.

    Example:
        accumulator = ErrorAccumulator()

        for item in items:
            with accumulator.capture(f"processing {item}"):
                process_item(item)

        if accumulator.has_errors:
            accumulator.raise_all()
    """

    def __init__(self, logger: logging.Logger | None = None):
        """Initialize error accumulator.

        Args:
            logger: Optional logger for immediate error logging
        """
        self.errors: list[tuple[str, Exception]] = []
        self.logger = logger

    @contextmanager
    def capture(self, context: str):
        """Capture errors in a context.

        Args:
            context: Description of what's being done
        """
        try:
            yield
        except Exception as e:
            self.add_error(context, e)
            if self.logger:
                self.logger.error(f"Error in {context}: {e}")

    def add_error(self, context: str, error: Exception):
        """Add an error to the accumulator.

        Args:
            context: Description of where the error occurred
            error: The exception that was raised
        """
        self.errors.append((context, error))

    @property
    def has_errors(self) -> bool:
        """Check if any errors have been accumulated."""
        return len(self.errors) > 0

    @property
    def error_count(self) -> int:
        """Get the number of accumulated errors."""
        return len(self.errors)

    def get_summary(self) -> str:
        """Get a summary of all errors."""
        if not self.errors:
            return "No errors"

        lines = [f"Found {len(self.errors)} errors:"]
        for context, error in self.errors:
            lines.append(f"  - {context}: {error}")

        return "\n".join(lines)

    def raise_all(self):
        """Raise an exception with all accumulated errors."""
        if not self.errors:
            return

        if len(self.errors) == 1:
            _, error = self.errors[0]
            raise error

        raise ProofSketcherError(
            f"Multiple errors occurred ({len(self.errors)} total)",
            details={
                "errors": [
                    {"context": context, "error": str(error)}
                    for context, error in self.errors
                ],
                "summary": self.get_summary(),
            },
        )

    def clear(self):
        """Clear all accumulated errors."""
        self.errors.clear()
