"""Unified animation interface with fallback support.

This module provides a single interface for creating visualizations,
automatically falling back from animations to static diagrams as needed.
"""

import logging
from pathlib import Path
from typing import Dict, Optional

from ..parser.models import TheoremInfo
from .manim_generator import ManimGenerator
from .static_generator import StaticDiagramGenerator


class Animator:
    """Unified animation interface with automatic fallback."""

    def __init__(self):
        """Initialize animator with all available backends."""
        self.logger = logging.getLogger(__name__)
        self.manim = ManimGenerator()
        self.static = StaticDiagramGenerator()

        # Log available backends
        if self.manim.manim_available:
            self.logger.info("Animator initialized with Manim support")
        else:
            self.logger.info("Animator initialized with static diagrams only")

    def create_visualization(
        self,
        theorem: TheoremInfo,
        output_dir: Path,
        prefer_animation: bool = True,
        output_format: str = "mp4",
    ) -> Dict[str, Optional[Path]]:
        """Create visualization (animation or static).

        Args:
            theorem: Theorem to visualize
            output_dir: Directory for output files
            prefer_animation: Whether to prefer animation over static
            output_format: Output format for animation (mp4, gif, etc.)

        Returns:
            Dictionary with visualization info:
                - type: "animation" or "static"
                - path: Path to generated file
                - error: Error message if any
        """
        result = {"type": None, "path": None, "error": None}

        # Ensure output directory exists
        output_dir.mkdir(parents=True, exist_ok=True)

        # Try animation first if preferred and available
        if prefer_animation and self.manim.manim_available:
            self.logger.debug(f"Attempting animation for {theorem.name}")

            # Determine animation output path
            if output_format == "gif":
                video_path = output_dir / f"{theorem.name}.gif"
            else:
                video_path = output_dir / f"{theorem.name}.mp4"

            try:
                animation = self.manim.generate_animation(theorem, video_path)

                if animation and animation.exists():
                    result["type"] = "animation"
                    result["path"] = animation
                    self.logger.info(f"Successfully created animation: {animation}")
                    return result
                else:
                    self.logger.warning(
                        "Animation generation returned no file, falling back"
                    )

            except Exception as e:
                self.logger.warning(f"Animation failed: {e}, falling back")
                result["error"] = str(e)

        # Fallback to static diagram
        self.logger.debug(f"Creating static diagram for {theorem.name}")
        diagram_path = output_dir / f"{theorem.name}.png"

        try:
            diagram = self.static.generate_diagram(theorem, diagram_path)

            result["type"] = "static"
            result["path"] = diagram
            self.logger.info(f"Successfully created static diagram: {diagram}")

        except Exception as e:
            self.logger.error(f"Static diagram generation failed: {e}")
            result["error"] = str(e)

            # Create placeholder file as last resort
            placeholder_path = output_dir / f"{theorem.name}_placeholder.txt"
            placeholder_path.write_text(
                f"Visualization failed for theorem: {theorem.name}\n" f"Error: {e}\n"
            )
            result["type"] = "placeholder"
            result["path"] = placeholder_path

        return result

    def batch_visualize(
        self,
        theorems: list[TheoremInfo],
        output_dir: Path,
        prefer_animation: bool = True,
        max_concurrent: int = 4,
    ) -> Dict[str, Dict]:
        """Create visualizations for multiple theorems.

        Args:
            theorems: List of theorems to visualize
            output_dir: Output directory
            prefer_animation: Whether to prefer animations
            max_concurrent: Maximum concurrent visualizations

        Returns:
            Dictionary mapping theorem names to visualization results
        """
        results = {}

        # Process theorems (could be parallelized in future)
        for theorem in theorems:
            self.logger.info(f"Visualizing theorem: {theorem.name}")
            result = self.create_visualization(theorem, output_dir, prefer_animation)
            results[theorem.name] = result

        # Summary statistics
        animation_count = sum(1 for r in results.values() if r["type"] == "animation")
        static_count = sum(1 for r in results.values() if r["type"] == "static")
        error_count = sum(1 for r in results.values() if r["error"])

        self.logger.info(
            f"Batch visualization complete: "
            f"{animation_count} animations, "
            f"{static_count} static diagrams, "
            f"{error_count} errors"
        )

        return results

    def get_capabilities(self) -> Dict[str, bool]:
        """Get current visualization capabilities.

        Returns:
            Dictionary of available features
        """
        return {
            "animation": self.manim.manim_available,
            "static": True,  # Always available
            "formats": {
                "mp4": self.manim.manim_available,
                "gif": self.manim.manim_available,
                "png": True,
                "svg": False,  # Could be added later
            },
        }
