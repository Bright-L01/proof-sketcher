"""Core data models shared across Proof Sketcher modules.

This module contains base models and common data structures used
throughout the application.
"""

from abc import abstractmethod
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, Generic, List, Optional, TypeVar

from pydantic import BaseModel, Field, field_validator

from .exceptions import ValidationError

T = TypeVar("T")


class BaseConfig(BaseModel):
    """Base configuration model that all configs inherit from."""

    class Config:
        """Pydantic configuration."""

        validate_assignment = True
        use_enum_values = False
        arbitrary_types_allowed = True

    def merge_with(self, other: Optional["BaseConfig"]) -> "BaseConfig":
        """Merge this config with another, with other taking precedence.

        Args:
            other: Configuration to merge with

        Returns:
            New configuration with merged values
        """
        if not other:
            return self.model_copy()

        # Get non-None values from other
        other_dict = {k: v for k, v in other.model_dump().items() if v is not None}

        # Create new instance with merged values
        return self.__class__(**{**self.model_dump(), **other_dict})


class TimestampedModel(BaseModel):
    """Base model with timestamp fields."""

    created_at: datetime = Field(default_factory=datetime.utcnow)
    updated_at: Optional[datetime] = None

    def touch(self) -> None:
        """Update the updated_at timestamp."""
        self.updated_at = datetime.utcnow()


class CacheableModel(BaseModel):
    """Base model for cacheable objects."""

    @abstractmethod
    def get_cache_key(self) -> str:
        """Generate a unique cache key for this object.

        Returns:
            Cache key string
        """
        pass

    def get_cache_ttl(self) -> Optional[int]:
        """Get time-to-live for cache in seconds.

        Returns:
            TTL in seconds, None for no expiration
        """
        return None


class Result(BaseModel, Generic[T]):
    """Generic result wrapper for operations that can fail."""

    success: bool
    data: Optional[T] = None
    error: Optional[str] = None
    details: Dict[str, Any] = Field(default_factory=dict)

    @classmethod
    def ok(cls, data: T, **details: Any) -> "Result[T]":
        """Create a successful result.

        Args:
            data: Result data
            **details: Additional details

        Returns:
            Successful result
        """
        return cls(success=True, data=data, details=details)

    @classmethod
    def fail(cls, error: str, **details: Any) -> "Result[T]":
        """Create a failed result.

        Args:
            error: Error message
            **details: Additional details

        Returns:
            Failed result
        """
        return cls(success=False, error=error, details=details)


class ProcessingStatus(str, Enum):
    """Status of a processing operation."""

    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"


class ProcessingResult(TimestampedModel):
    """Result of a processing operation."""

    id: str
    status: ProcessingStatus = ProcessingStatus.PENDING
    progress: float = Field(default=0.0, ge=0.0, le=100.0)
    message: Optional[str] = None
    result_data: Optional[Dict[str, Any]] = None
    error_data: Optional[Dict[str, Any]] = None

    def update_progress(self, progress: float, message: Optional[str] = None) -> None:
        """Update processing progress.

        Args:
            progress: Progress percentage (0-100)
            message: Optional status message
        """
        self.progress = max(0.0, min(100.0, progress))
        if message:
            self.message = message
        self.touch()

    def mark_completed(self, result_data: Optional[Dict[str, Any]] = None) -> None:
        """Mark processing as completed.

        Args:
            result_data: Optional result data
        """
        self.status = ProcessingStatus.COMPLETED
        self.progress = 100.0
        if result_data:
            self.result_data = result_data
        self.touch()

    def mark_failed(
        self, error: str, error_data: Optional[Dict[str, Any]] = None
    ) -> None:
        """Mark processing as failed.

        Args:
            error: Error message
            error_data: Optional error details
        """
        self.status = ProcessingStatus.FAILED
        self.message = error
        if error_data:
            self.error_data = error_data
        self.touch()


class FileReference(BaseModel):
    """Reference to a file with metadata."""

    path: Path
    mime_type: Optional[str] = None
    size_bytes: Optional[int] = None
    checksum: Optional[str] = None
    metadata: Dict[str, Any] = Field(default_factory=dict)

    @field_validator("path")
    def validate_path(cls, v: Path) -> Path:
        """Ensure path is absolute."""
        return v.absolute()

    def exists(self) -> bool:
        """Check if the referenced file exists."""
        return self.path.exists()

    def read_text(self, encoding: str = "utf-8") -> str:
        """Read file contents as text."""
        return self.path.read_text(encoding=encoding)

    def read_bytes(self) -> bytes:
        """Read file contents as bytes."""
        return self.path.read_bytes()


class BatchProcessingRequest(BaseModel):
    """Request for batch processing operations."""

    items: List[Any]
    parallel: bool = False
    max_workers: Optional[int] = None
    fail_fast: bool = True
    progress_callback: Optional[Any] = None  # Callable[[float, str], None]

    @field_validator("max_workers")
    def validate_max_workers(cls, v: Optional[int]) -> Optional[int]:
        """Validate max_workers is positive."""
        if v is not None and v <= 0:
            raise ValidationError(
                "max_workers must be positive",
                details={"value": v, "constraint": "positive integer"}
            )
        return v


class ValidationResult(BaseModel):
    """Result of a validation operation."""

    valid: bool
    errors: List[str] = Field(default_factory=list)
    warnings: List[str] = Field(default_factory=list)

    def add_error(self, error: str) -> None:
        """Add an error message."""
        self.errors.append(error)
        self.valid = False

    def add_warning(self, warning: str) -> None:
        """Add a warning message."""
        self.warnings.append(warning)

    def merge(self, other: "ValidationResult") -> None:
        """Merge another validation result into this one."""
        self.valid = self.valid and other.valid
        self.errors.extend(other.errors)
        self.warnings.extend(other.warnings)
