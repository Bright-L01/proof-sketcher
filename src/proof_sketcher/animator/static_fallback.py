"""
Static Visualization Fallback

This module creates high-quality static visualizations when Manim animation
fails or is not available, providing a reliable backup visualization system.
"""

import colorsys
import logging
import textwrap
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

try:
    import matplotlib

    matplotlib.use("Agg")  # Use non-interactive backend
    import matplotlib.patches as mpatches
    import matplotlib.pyplot as plt
    import numpy as np
    from matplotlib.patches import Arrow, Circle, FancyBboxPatch

    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

from ..utils.security import sanitize_filename


class StaticVisualizer:
    """Create high-quality static visualizations for mathematical proofs."""

    def __init__(self):
        """Initialize the static visualizer."""
        self.logger = logging.getLogger(__name__)

        if not MATPLOTLIB_AVAILABLE:
            self.logger.warning(
                "Matplotlib not available - static visualizations disabled"
            )

        # Visual configuration
        self.config = {
            "figure_size": (14, 10),
            "dpi": 300,
            "title_fontsize": 20,
            "statement_fontsize": 14,
            "step_fontsize": 12,
            "annotation_fontsize": 10,
            "title_color": "#2E3440",
            "statement_color": "#5E81AC",
            "step_color": "#D08770",
            "background_color": "#ECEFF4",
            "accent_color": "#A3BE8C",
            "error_color": "#BF616A",
            "box_alpha": 0.8,
            "text_wrap_width": 60,
        }

        # Color palette for different elements
        self.colors = self._generate_color_palette()

    def _generate_color_palette(self) -> Dict[str, str]:
        """Generate a harmonious color palette.

        Returns:
            Dictionary of color names to hex codes
        """
        # Nordic color scheme
        return {
            "primary": "#2E3440",  # Dark blue-gray
            "secondary": "#3B4252",  # Medium blue-gray
            "accent1": "#5E81AC",  # Blue
            "accent2": "#81A1C1",  # Light blue
            "accent3": "#88C0D0",  # Cyan
            "accent4": "#8FBCBB",  # Teal
            "success": "#A3BE8C",  # Green
            "warning": "#EBCB8B",  # Yellow
            "error": "#BF616A",  # Red
            "orange": "#D08770",  # Orange
            "purple": "#B48EAD",  # Purple
            "background": "#ECEFF4",  # Light gray
            "surface": "#E5E9F0",  # Medium light gray
            "text": "#2E3440",  # Dark text
        }

    def create_proof_diagram(
        self,
        theorem: Dict[str, Any],
        sketch: Dict[str, Any],
        output_path: str,
        config: Optional[Dict[str, Any]] = None,
    ) -> bool:
        """Create comprehensive static proof diagram.

        Args:
            theorem: Theorem information dictionary
            sketch: Proof sketch with steps
            output_path: Path for output image
            config: Optional visual configuration

        Returns:
            True if successful, False otherwise
        """
        if not MATPLOTLIB_AVAILABLE:
            self.logger.error("Matplotlib not available for static visualization")
            return False

        try:
            # Apply custom configuration
            if config:
                self.config.update(config)

            # Sanitize output path
            safe_output_path = sanitize_filename(output_path)

            # Create figure
            fig, ax = self._setup_figure()

            # Draw diagram elements
            self._draw_title(ax, theorem)
            self._draw_statement(ax, theorem)
            self._draw_proof_steps(ax, sketch)
            self._draw_conclusion(ax)
            self._add_decorative_elements(ax)

            # Save with high quality
            plt.savefig(
                safe_output_path,
                dpi=self.config["dpi"],
                bbox_inches="tight",
                facecolor=self.config["background_color"],
                edgecolor="none",
                pad_inches=0.3,
            )
            plt.close(fig)

            self.logger.info(f"Static diagram saved to {safe_output_path}")
            return True

        except Exception as e:
            self.logger.exception(f"Failed to create static diagram: {e}")
            return False

    def _setup_figure(self) -> Tuple[Any, Any]:
        """Set up matplotlib figure and axis.

        Returns:
            Tuple of (figure, axis)
        """
        fig, ax = plt.subplots(figsize=self.config["figure_size"])
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 10)
        ax.axis("off")
        ax.set_facecolor(self.config["background_color"])
        return fig, ax

    def _draw_title(self, ax: Any, theorem: Dict[str, Any]) -> None:
        """Draw theorem title.

        Args:
            ax: Matplotlib axis
            theorem: Theorem information
        """
        title = theorem.get("name", "Unknown Theorem")

        # Title background
        title_box = FancyBboxPatch(
            (0.5, 8.5),
            9,
            1,
            boxstyle="round,pad=0.15",
            facecolor=self.colors["primary"],
            edgecolor=self.colors["secondary"],
            linewidth=2,
            alpha=self.config["box_alpha"],
        )
        ax.add_patch(title_box)

        # Title text
        ax.text(
            5,
            9,
            title,
            fontsize=self.config["title_fontsize"],
            ha="center",
            va="center",
            color="white",
            weight="bold",
            family="serif",
        )

    def _draw_statement(self, ax: Any, theorem: Dict[str, Any]) -> None:
        """Draw theorem statement.

        Args:
            ax: Matplotlib axis
            theorem: Theorem information
        """
        statement = theorem.get("statement", "No statement available")

        # Wrap long statements
        wrapped_statement = textwrap.fill(
            statement, width=self.config["text_wrap_width"]
        )

        # Statement background
        statement_height = max(1.2, len(wrapped_statement.split("\n")) * 0.3 + 0.6)
        statement_box = FancyBboxPatch(
            (0.5, 7.5 - statement_height),
            9,
            statement_height,
            boxstyle="round,pad=0.1",
            facecolor=self.colors["accent1"],
            edgecolor=self.colors["accent2"],
            linewidth=1.5,
            alpha=self.config["box_alpha"],
        )
        ax.add_patch(statement_box)

        # Statement text
        ax.text(
            5,
            7.5 - statement_height / 2,
            wrapped_statement,
            fontsize=self.config["statement_fontsize"],
            ha="center",
            va="center",
            color="white",
            weight="normal",
            family="serif",
        )

    def _draw_proof_steps(self, ax: Any, sketch: Dict[str, Any]) -> None:
        """Draw proof steps with visual flow.

        Args:
            ax: Matplotlib axis
            sketch: Proof sketch information
        """
        steps = sketch.get("key_steps", []) if sketch else []

        if not steps:
            # No steps available
            no_steps_box = FancyBboxPatch(
                (1, 4),
                8,
                1,
                boxstyle="round,pad=0.1",
                facecolor=self.colors["surface"],
                edgecolor=self.colors["text"],
                linewidth=1,
                alpha=0.5,
            )
            ax.add_patch(no_steps_box)

            ax.text(
                5,
                4.5,
                "Proof steps not available",
                fontsize=self.config["step_fontsize"],
                ha="center",
                va="center",
                color=self.colors["text"],
                style="italic",
            )
            return

        # Calculate layout for steps
        max_steps = min(len(steps), 4)  # Limit display to 4 steps
        step_height = 0.8
        step_spacing = 0.3
        start_y = 6.5

        for i, step in enumerate(steps[:max_steps]):
            y_pos = start_y - i * (step_height + step_spacing)

            # Step number circle
            step_circle = Circle(
                (1.2, y_pos),
                0.2,
                facecolor=self.colors["accent3"],
                edgecolor=self.colors["accent4"],
                linewidth=2,
            )
            ax.add_patch(step_circle)

            # Step number
            ax.text(
                1.2,
                y_pos,
                str(i + 1),
                fontsize=self.config["step_fontsize"],
                ha="center",
                va="center",
                color=self.colors["primary"],
                weight="bold",
            )

            # Step description
            description = step.get("description", f"Step {i + 1}")
            wrapped_desc = textwrap.fill(description, width=50)

            # Step box
            step_box = FancyBboxPatch(
                (1.8, y_pos - step_height / 2),
                7.7,
                step_height,
                boxstyle="round,pad=0.08",
                facecolor=self.colors["warning"],
                edgecolor=self.colors["orange"],
                linewidth=1,
                alpha=self.config["box_alpha"],
            )
            ax.add_patch(step_box)

            # Step text
            ax.text(
                5.65,
                y_pos,
                wrapped_desc,
                fontsize=self.config["step_fontsize"],
                ha="center",
                va="center",
                color=self.colors["primary"],
                weight="normal",
            )

            # Mathematical content if available
            math_content = step.get("mathematical_content", "")
            if math_content and len(math_content) < 50:
                ax.text(
                    8.8,
                    y_pos,
                    f"${math_content}$",
                    fontsize=self.config["annotation_fontsize"],
                    ha="center",
                    va="center",
                    color=self.colors["accent1"],
                    style="italic",
                )

            # Arrow to next step
            if i < max_steps - 1 and i < len(steps) - 1:
                arrow_y = y_pos - step_height / 2 - step_spacing / 2
                ax.annotate(
                    "",
                    xy=(1.2, arrow_y - 0.1),
                    xytext=(1.2, arrow_y + 0.1),
                    arrowprops=dict(
                        arrowstyle="->", color=self.colors["accent3"], lw=2
                    ),
                )

        # Show remaining steps indicator
        if len(steps) > max_steps:
            remaining = len(steps) - max_steps
            ax.text(
                5,
                start_y - max_steps * (step_height + step_spacing) - 0.3,
                f"... and {remaining} more step{'s' if remaining > 1 else ''}",
                fontsize=self.config["annotation_fontsize"],
                ha="center",
                va="center",
                color=self.colors["text"],
                style="italic",
            )

    def _draw_conclusion(self, ax: Any) -> None:
        """Draw QED conclusion.

        Args:
            ax: Matplotlib axis
        """
        # QED symbol with decorative background
        qed_circle = Circle(
            (5, 1.5),
            0.4,
            facecolor=self.colors["success"],
            edgecolor=self.colors["accent4"],
            linewidth=3,
            alpha=self.config["box_alpha"],
        )
        ax.add_patch(qed_circle)

        # QED text
        ax.text(
            5,
            1.5,
            "∎",
            fontsize=32,
            ha="center",
            va="center",
            color="white",
            weight="bold",
        )

        # "Proof Complete" text
        ax.text(
            5,
            0.8,
            "Proof Complete",
            fontsize=self.config["annotation_fontsize"],
            ha="center",
            va="center",
            color=self.colors["success"],
            weight="bold",
            style="italic",
        )

    def _add_decorative_elements(self, ax: Any) -> None:
        """Add decorative visual elements.

        Args:
            ax: Matplotlib axis
        """
        # Corner decorations
        for corner_x, corner_y in [(0.2, 9.8), (9.8, 9.8), (0.2, 0.2), (9.8, 0.2)]:
            decoration = Circle(
                (corner_x, corner_y), 0.1, facecolor=self.colors["accent2"], alpha=0.3
            )
            ax.add_patch(decoration)

    def create_simple_diagram(
        self,
        theorem_name: str,
        statement: str,
        output_path: str,
        steps: Optional[List[str]] = None,
    ) -> bool:
        """Create simple diagram for basic theorems.

        Args:
            theorem_name: Name of theorem
            statement: Mathematical statement
            output_path: Output file path
            steps: Optional proof steps

        Returns:
            True if successful
        """
        if not MATPLOTLIB_AVAILABLE:
            return False

        try:
            theorem = {"name": theorem_name, "statement": statement}
            sketch = {"key_steps": [{"description": step} for step in (steps or [])]}

            return self.create_proof_diagram(theorem, sketch, output_path)

        except Exception as e:
            self.logger.exception(f"Failed to create simple diagram: {e}")
            return False

    def create_error_diagram(
        self, error_message: str, output_path: str, context: Optional[str] = None
    ) -> bool:
        """Create error visualization diagram.

        Args:
            error_message: Error message to display
            output_path: Output file path
            context: Optional context information

        Returns:
            True if successful
        """
        if not MATPLOTLIB_AVAILABLE:
            return False

        try:
            fig, ax = self._setup_figure()

            # Error title
            error_box = FancyBboxPatch(
                (1, 6),
                8,
                2,
                boxstyle="round,pad=0.2",
                facecolor=self.colors["error"],
                edgecolor=self.colors["primary"],
                linewidth=2,
                alpha=0.9,
            )
            ax.add_patch(error_box)

            # Error icon
            ax.text(
                5,
                7.5,
                "⚠",
                fontsize=48,
                ha="center",
                va="center",
                color="white",
                weight="bold",
            )

            # Error message
            wrapped_error = textwrap.fill(error_message, width=40)
            ax.text(
                5,
                6.5,
                wrapped_error,
                fontsize=self.config["statement_fontsize"],
                ha="center",
                va="center",
                color="white",
                weight="normal",
            )

            # Context if provided
            if context:
                wrapped_context = textwrap.fill(context, width=50)
                ax.text(
                    5,
                    3,
                    wrapped_context,
                    fontsize=self.config["annotation_fontsize"],
                    ha="center",
                    va="center",
                    color=self.colors["text"],
                    style="italic",
                )

            plt.savefig(
                sanitize_filename(output_path),
                dpi=self.config["dpi"],
                bbox_inches="tight",
                facecolor=self.config["background_color"],
            )
            plt.close(fig)

            return True

        except Exception as e:
            self.logger.exception(f"Failed to create error diagram: {e}")
            return False

    def is_available(self) -> bool:
        """Check if static visualization is available.

        Returns:
            True if matplotlib is available
        """
        return MATPLOTLIB_AVAILABLE

    def get_supported_formats(self) -> List[str]:
        """Get list of supported output formats.

        Returns:
            List of file extensions
        """
        if not MATPLOTLIB_AVAILABLE:
            return []

        return [".png", ".jpg", ".jpeg", ".pdf", ".svg", ".eps"]
