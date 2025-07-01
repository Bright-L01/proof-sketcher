"""Core module for Proof Sketcher.

This module contains shared components used across all other modules:
- Base exceptions
- Shared interfaces and protocols
- Common data models
- Utility functions
"""

from .exceptions import (
    ProofSketcherError,
    ParserError,
    GeneratorError,
    AnimatorError,
    ExporterError,
    ConfigError,
    CacheError,
    ValidationError,
    LeanExecutableError,
    AIExecutableError,
    AITimeoutError,
    AnimationTimeoutError,
    TemplateError,
)

from .interfaces import (
    IParser,
    IGenerator,
    IAnimator,
    IExporter,
    ICache,
    IConfigurable,
)

from .models import (
    BaseConfig,
    TimestampedModel,
    CacheableModel,
    Result,
    ProcessingStatus,
    ProcessingResult,
    FileReference,
    BatchProcessingRequest,
    ValidationResult,
)

from .utils import (
    generate_cache_key,
    sanitize_filename,
    ensure_directory,
    format_duration,
    truncate_text,
    deep_merge,
    retry_with_backoff,
    get_timestamp,
    calculate_hash,
    chunk_list,
    flatten_dict,
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
    "retry_with_backoff",
    "get_timestamp",
    "calculate_hash",
    "chunk_list",
    "flatten_dict",
]