"""Configuration classes for the Lean parser."""

from dataclasses import dataclass
from pathlib import Path
from typing import Optional


@dataclass
class RetryConfig:
    """Configuration for retry behavior."""

    max_attempts: int = 3
    base_delay: float = 1.0  # seconds
    max_delay: float = 10.0  # seconds
    exponential_base: float = 2.0

    def get_delay(self, attempt: int) -> float:
        """Calculate delay for given attempt number (0-indexed)."""
        delay = self.base_delay * (self.exponential_base**attempt)
        return min(delay, self.max_delay)


@dataclass
class ParserConfig:
    """Configuration for the Lean parser."""

    # Executable paths
    lean_executable: str = "lean"
    lake_executable: str = "lake"

    # Timeout settings (in seconds)
    lean_timeout: float = 30.0
    lake_timeout: float = 60.0
    version_check_timeout: float = 10.0

    # Retry configuration
    retry_config: Optional[RetryConfig] = None

    # Lake project settings
    auto_detect_lake: bool = True
    lake_build_on_parse: bool = False  # Whether to run lake build before parsing

    # Parser behavior
    fallback_to_regex: bool = True  # Fall back to regex parsing if Lean fails
    extract_dependencies: bool = True
    extract_docstrings: bool = True

    # Working directory
    working_dir: Optional[Path] = None

    def __post_init__(self) -> None:
        """Initialize retry config if not provided."""
        if self.retry_config is None:
            self.retry_config = RetryConfig()

    def validate(self) -> list[str]:
        """Validate configuration and return list of errors."""
        errors = []

        if self.lean_timeout <= 0:
            errors.append("lean_timeout must be positive")

        if self.lake_timeout <= 0:
            errors.append("lake_timeout must be positive")

        if self.version_check_timeout <= 0:
            errors.append("version_check_timeout must be positive")

        if self.retry_config is not None:
            if self.retry_config.max_attempts < 1:
                errors.append("retry_config.max_attempts must be at least 1")

            if self.retry_config.base_delay <= 0:
                errors.append("retry_config.base_delay must be positive")

        if self.working_dir and not self.working_dir.exists():
            errors.append(f"working_dir does not exist: {self.working_dir}")

        return errors

    @classmethod
    def default(cls) -> "ParserConfig":
        """Create default configuration."""
        return cls()

    @classmethod
    def fast(cls) -> "ParserConfig":
        """Create configuration optimized for speed."""
        return cls(
            lean_timeout=10.0,
            lake_timeout=30.0,
            retry_config=RetryConfig(max_attempts=1),
            lake_build_on_parse=False,
            fallback_to_regex=True,
        )

    @classmethod
    def robust(cls) -> "ParserConfig":
        """Create configuration optimized for reliability."""
        return cls(
            lean_timeout=60.0,
            lake_timeout=120.0,
            retry_config=RetryConfig(max_attempts=5, base_delay=2.0, max_delay=30.0),
            lake_build_on_parse=True,
            fallback_to_regex=True,
        )
