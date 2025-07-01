"""Core interfaces and protocols for Proof Sketcher.

This module defines abstract base classes and protocols that establish
contracts for implementations across the application.
"""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import TYPE_CHECKING, Any, Dict, List, Optional, Protocol, runtime_checkable

from pydantic import BaseModel

if TYPE_CHECKING:
    from ..animator.models import AnimationConfig, AnimationResponse
    from ..exporter.models import ExportResult
    from ..generator.models import GenerationConfig, ProofSketch
    from ..parser.models import ParseResult, TheoremInfo


# Parser Interfaces
@runtime_checkable
class IParser(Protocol):
    """Protocol for theorem parsers."""

    def parse_file(self, file_path: Path) -> "ParseResult":
        """Parse a file and extract theorems.

        Args:
            file_path: Path to the file to parse

        Returns:
            ParseResult containing extracted theorems
        """
        ...

    def parse_theorem(
        self, file_path: Path, theorem_name: str
    ) -> Optional["TheoremInfo"]:
        """Parse a specific theorem from a file.

        Args:
            file_path: Path to the file containing the theorem
            theorem_name: Name of the theorem to extract

        Returns:
            TheoremInfo if found, None otherwise
        """
        ...


# Generator Interfaces
class IGenerator(ABC):
    """Abstract base class for proof explanation generators."""

    @abstractmethod
    def generate_proof_sketch(
        self,
        theorem: "TheoremInfo",
        config: Optional["GenerationConfig"] = None,
        mathematical_context: Optional[str] = None,
    ) -> "ProofSketch":
        """Generate a proof sketch for a theorem.

        Args:
            theorem: Theorem information
            config: Optional generation configuration
            mathematical_context: Optional mathematical context

        Returns:
            Generated proof sketch
        """
        pass

    @abstractmethod
    def generate_eli5_explanation(
        self,
        theorem: "TheoremInfo",
        config: Optional["GenerationConfig"] = None,
    ) -> str:
        """Generate an ELI5 explanation for a theorem.

        Args:
            theorem: Theorem information
            config: Optional generation configuration

        Returns:
            Simple explanation text
        """
        pass


# Animator Interfaces
@runtime_checkable
class IAnimator(Protocol):
    """Protocol for proof animators."""

    async def animate_proof(
        self,
        proof_sketch: "ProofSketch",
        config: Optional["AnimationConfig"] = None,
    ) -> "AnimationResponse":
        """Create an animation for a proof sketch.

        Args:
            proof_sketch: Proof sketch to animate
            config: Optional animation configuration

        Returns:
            Animation response with paths to generated files
        """
        ...


# Exporter Interfaces
class IExporter(ABC):
    """Abstract base class for exporters."""

    @abstractmethod
    def export_single(
        self,
        proof_sketch: "ProofSketch",
        animation_path: Optional[Path] = None,
    ) -> "ExportResult":
        """Export a single proof sketch.

        Args:
            proof_sketch: Proof sketch to export
            animation_path: Optional path to animation file

        Returns:
            Export result with created files
        """
        pass

    @abstractmethod
    def export_batch(
        self,
        proof_sketches: List["ProofSketch"],
        animations: Optional[Dict[str, Path]] = None,
    ) -> "ExportResult":
        """Export multiple proof sketches.

        Args:
            proof_sketches: List of proof sketches to export
            animations: Optional mapping of theorem names to animation paths

        Returns:
            Export result with created files
        """
        pass


# Cache Interfaces
@runtime_checkable
class ICache(Protocol):
    """Protocol for cache implementations."""

    def get(self, key: str) -> Optional[Any]:
        """Retrieve a value from cache.

        Args:
            key: Cache key

        Returns:
            Cached value if found, None otherwise
        """
        ...

    def set(self, key: str, value: Any, ttl: Optional[int] = None) -> None:
        """Store a value in cache.

        Args:
            key: Cache key
            value: Value to cache
            ttl: Optional time-to-live in seconds
        """
        ...

    def delete(self, key: str) -> bool:
        """Delete a value from cache.

        Args:
            key: Cache key

        Returns:
            True if deleted, False if not found
        """
        ...

    def clear(self) -> int:
        """Clear all cached values.

        Returns:
            Number of items cleared
        """
        ...


# Configuration Interfaces
class IConfigurable(ABC):
    """Interface for configurable components."""

    @abstractmethod
    def get_config(self) -> BaseModel:
        """Get current configuration."""
        pass

    @abstractmethod
    def update_config(self, config: BaseModel) -> None:
        """Update configuration.

        Args:
            config: New configuration
        """
        pass

    @abstractmethod
    def validate_config(self) -> List[str]:
        """Validate current configuration.

        Returns:
            List of validation errors, empty if valid
        """
        pass
