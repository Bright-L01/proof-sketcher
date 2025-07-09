"""Base exporter class for all export formats.

This module provides the abstract base class that all exporters
must inherit from, ensuring consistent interface across formats.
"""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import Optional

import jinja2

from ..parser.models import TheoremInfo


class BaseExporter(ABC):
    """Base class for all exporters."""

    def __init__(self):
        """Initialize base exporter with Jinja2 environment."""
        # Setup Jinja2
        template_dir = Path(__file__).parent / "templates"
        self.env = jinja2.Environment(
            loader=jinja2.FileSystemLoader(template_dir),
            autoescape=jinja2.select_autoescape(["html"]),
        )

    @abstractmethod
    def export(
        self,
        theorem: TheoremInfo,
        explanation: str,
        visualization: Optional[Path],
        output_path: Path,
    ) -> Path:
        """Export theorem documentation.

        Args:
            theorem: Theorem information
            explanation: Natural language explanation
            visualization: Path to visualization file (optional)
            output_path: Where to save the export

        Returns:
            Path to the exported file
        """
        pass

    def _ensure_output_dir(self, output_path: Path) -> None:
        """Ensure output directory exists.

        Args:
            output_path: Path to output file
        """
        output_path.parent.mkdir(parents=True, exist_ok=True)
