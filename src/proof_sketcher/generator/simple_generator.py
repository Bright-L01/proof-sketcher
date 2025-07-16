"""Simple generator for MVP - uses offline mode only."""

from typing import Optional, Union

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
        
    def generate_educational_sketch(
        self,
        theorem: Union[TheoremInfo, "SemanticTheoremInfo"],
        target_level: str = "intermediate",
        config: Optional[GenerationConfig] = None
    ) -> ProofSketch:
        """Generate educational proof sketch (compatibility method).

        Args:
            theorem: Theorem to explain (any type)
            target_level: Target educational level (ignored in simple mode)
            config: Generation config (ignored for MVP)

        Returns:
            Generated proof sketch using offline mode
        """
        # Import here to avoid circular imports
        from ..parser.lsp_client import SemanticTheoremInfo
        
        # Convert SemanticTheoremInfo to TheoremInfo if needed
        if isinstance(theorem, SemanticTheoremInfo):
            base_theorem = TheoremInfo(
                name=theorem.name,
                statement=theorem.statement,
                proof=theorem.proof,
                dependencies=theorem.dependencies,
                line_number=theorem.line_number,
                docstring=theorem.docstring,
                namespace=theorem.namespace,
                visibility=theorem.visibility,
                tactics=theorem.tactics,
                is_axiom=theorem.is_axiom,
                file_path=theorem.file_path,
                start_line=theorem.start_line,
                end_line=theorem.end_line,
            )
            return self.generate_offline(base_theorem)
        else:
            return self.generate_offline(theorem)
