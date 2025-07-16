"""Core exceptions for Proof Sketcher."""


class ProofSketcherError(Exception):
    """Base exception for all Proof Sketcher errors."""

    pass


class ConfigError(ProofSketcherError):
    """Base configuration error."""

    pass


class ConfigNotFoundError(ConfigError):
    """Configuration file not found."""

    pass


class ConfigValidationError(ConfigError):
    """Configuration validation failed."""

    pass
