"""Simple generator for MVP - uses offline mode only."""

from typing import Optional

from ..parser.models import TheoremInfo
from .models import GenerationConfig, ProofSketch
from .offline import OfflineGenerator


class SimpleGenerator:
    """Simple generator that only uses offline mode for MVP."""

    def __init__(self) -> None:
        """Initialize simple generator with offline mode."""
        self.offline_generator = OfflineGenerator()

    def generate_offline(self, theorem: TheoremInfo) -> ProofSketch:
        """Generate proof sketch using offline mode.

        Args:
            theorem: Theorem to explain

        Returns:
            Generated proof sketch
        """
        return self.offline_generator.generate_proof_sketch(theorem)

    def generate_proof_sketch(
        self, theorem: TheoremInfo, config: Optional[GenerationConfig] = None
    ) -> ProofSketch:
        """Generate proof sketch (always uses offline mode for MVP).

        Args:
            theorem: Theorem to explain
            config: Generation config (ignored for MVP)

        Returns:
            Generated proof sketch
        """
        return self.generate_offline(theorem)
