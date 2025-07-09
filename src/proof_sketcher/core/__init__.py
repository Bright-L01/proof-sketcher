"""Core module for Proof Sketcher.

This module contains shared components used across all other modules:
- Base exceptions
- Shared interfaces and protocols
- Common data models
- Utility functions
"""

from .exceptions import (
    AIExecutableError,
    AITimeoutError,
    AnimationTimeoutError,
    AnimatorError,
    CacheError,
    ConfigError,
    ExporterError,
    GeneratorError,
    LeanExecutableError,
    ParserError,
    ProofSketcherError,
    TemplateError,
    ValidationError,
)
from .interfaces import IAnimator, ICache, IConfigurable, IExporter, IGenerator, IParser
from .models import (
    BaseConfig,
    BatchProcessingRequest,
    CacheableModel,
    FileReference,
    ProcessingResult,
    ProcessingStatus,
    Result,
    TimestampedModel,
    ValidationResult,
)
from .utils import (
    calculate_hash,
    chunk_list,
    deep_merge,
    ensure_directory,
    flatten_dict,
    format_duration,
    generate_cache_key,
    get_timestamp,
    retry_with_backoff,
    sanitize_filename,
    truncate_text,
)

__all__ = [
    # Exceptions
    "ProofSketcherError",
    "ParserError",
    "GeneratorError",
    "AnimatorError",
    "ExporterError",
    "ConfigError",
    "CacheError",
    "ValidationError",
    "LeanExecutableError",
    "AIExecutableError",
    "AITimeoutError",
    "AnimationTimeoutError",
    "TemplateError",
    # Interfaces
    "IParser",
    "IGenerator",
    "IAnimator",
    "IExporter",
    "ICache",
    "IConfigurable",
    # Models
    "BaseConfig",
    "TimestampedModel",
    "CacheableModel",
    "Result",
    "ProcessingStatus",
    "ProcessingResult",
    "FileReference",
    "BatchProcessingRequest",
    "ValidationResult",
    # Utils
    "generate_cache_key",
    "sanitize_filename",
    "ensure_directory",
    "format_duration",
    "truncate_text",
    "deep_merge",
    "retry_with_backof",
    "get_timestamp",
    "calculate_hash",
    "chunk_list",
    "flatten_dict",
]
