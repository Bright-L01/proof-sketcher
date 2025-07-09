"""Manim-based animation generator with graceful fallback.

This module generates animations using Manim if available,
with robust error handling and timeout protection.
"""

import logging
import subprocess
import tempfile
from pathlib import Path
from typing import Optional

from ..parser.models import TheoremInfo


class ManimGenerator:
    """Generate animations with Manim."""

    def __init__(self):
        """Initialize Manim generator and check availability."""
        self.logger = logging.getLogger(__name__)
        self.manim_available = self._check_manim()

    def _check_manim(self) -> bool:
        """Check if Manim is available."""
        try:
            result = subprocess.run(
                ["manim", "--version"],
                capture_output=True,
                text=True,
                timeout=5,
            )
            if result.returncode == 0:
                self.logger.info(f"Manim available: {result.stdout.strip()}")
                return True
            else:
                self.logger.warning("Manim command failed")
                return False
        except (subprocess.SubprocessError, FileNotFoundError) as e:
            self.logger.warning(f"Manim not available: {e}")
            return False

    def generate_animation(
        self, theorem: TheoremInfo, output_path: Path
    ) -> Optional[Path]:
        """Generate animation or return None.

        Args:
            theorem: Theorem to animate
            output_path: Path for output file

        Returns:
            Path to generated animation or None if failed
        """
        if not self.manim_available:
            self.logger.debug("Manim not available, skipping animation")
            return None

        try:
            # Create Manim scene code
            scene_code = self._create_scene(theorem)

            # Write to temp file
            with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False) as f:
                f.write(scene_code)
                scene_file = Path(f.name)

            # Ensure output directory exists
            output_path.parent.mkdir(parents=True, exist_ok=True)

            # Run Manim with timeout
            self.logger.info(f"Generating animation for {theorem.name}")
            result = subprocess.run(
                [
                    "manim",
                    "-ql",  # Low quality for speed
                    "-o",
                    output_path.name,
                    "--output_dir",
                    str(output_path.parent),
                    str(scene_file),
                    "TheoremScene",
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )

            # Clean up temp file
            scene_file.unlink(missing_ok=True)

            if result.returncode == 0:
                self.logger.info(f"Animation generated: {output_path}")
                return output_path
            else:
                self.logger.warning(f"Manim failed: {result.stderr or 'Unknown error'}")
                return None

        except subprocess.TimeoutExpired:
            self.logger.warning("Manim timed out after 30 seconds")
            return None
        except Exception as e:
            self.logger.error(f"Animation generation failed: {e}")
            return None

    def _create_scene(self, theorem: TheoremInfo) -> str:
        """Create Manim scene code for theorem.

        Args:
            theorem: Theorem to create scene for

        Returns:
            Python code for Manim scene
        """
        # Escape LaTeX special characters
        escaped_name = self._escape_latex(theorem.name)
        escaped_statement = self._escape_latex(theorem.statement[:200])  # Truncate

        return f"""from manim import *

class TheoremScene(Scene):
    def construct(self):
        # Title
        title = Text("{escaped_name}", font_size=36, color=BLUE)
        self.play(Write(title))
        self.wait(1)
        self.play(title.animate.to_edge(UP))
        
        # Statement
        statement_text = r"{escaped_statement}"
        if len(statement_text) > 50:
            statement_text = statement_text[:50] + "..."
        
        statement = Tex(statement_text, font_size=24)
        statement.scale(0.8)
        statement.move_to(CENTER)
        self.play(Write(statement))
        self.wait(2)
        
        # Add a simple visualization
        circle = Circle(radius=1, color=YELLOW)
        circle.move_to(DOWN * 2)
        self.play(Create(circle))
        self.play(circle.animate.scale(1.5))
        self.wait(1)
        
        # QED
        qed = Text("QED", font_size=48, color=GREEN)
        qed.move_to(DOWN * 2)
        self.play(
            FadeOut(circle),
            FadeIn(qed)
        )
        self.wait(1)
        
        # Fade out
        self.play(FadeOut(title), FadeOut(statement), FadeOut(qed))
"""

    def _escape_latex(self, text: str) -> str:
        """Escape LaTeX special characters.

        Args:
            text: Text to escape

        Returns:
            Escaped text safe for LaTeX
        """
        # Basic escaping for common LaTeX issues
        replacements = {
            "\\": "\\\\",
            "{": "\\{",
            "}": "\\}",
            "_": "\\_",
            "^": "\\^",
            "&": "\\&",
            "%": "\\%",
            "$": "\\$",
            "#": "\\#",
            "~": "\\~",
        }

        result = text
        for char, replacement in replacements.items():
            result = result.replace(char, replacement)

        return result
