"""HTML format exporter for theorem documentation.

This module exports theorems to HTML format with proper styling,
MathJax support, and embedded visualizations.
"""

import shutil
from datetime import datetime
from pathlib import Path
from typing import Dict, Optional

from .base_exporter import BaseExporter
from ..core.alpha_warning import add_alpha_warning_html
from ..parser.models import TheoremInfo


class HTMLExporter(BaseExporter):
    """Export to HTML format."""

    def export(
        self,
        theorem: TheoremInfo,
        explanation: str,
        visualization: Optional[Path],
        output_path: Path,
    ) -> Path:
        """Export theorem to HTML format.

        Args:
            theorem: Theorem information
            explanation: Natural language explanation
            visualization: Path to visualization file
            output_path: Where to save the HTML

        Returns:
            Path to exported HTML file
        """
        self._ensure_output_dir(output_path)

        # Prepare context for template
        context = {
            "theorem": theorem,
            "explanation": explanation,
            "visualization": self._prepare_visualization(visualization, output_path),
            "generated_at": datetime.now().isoformat(),
        }

        # Render template
        template = self.env.get_template("theorem.html")
        html = template.render(**context)

        # Add alpha warning to HTML
        html = add_alpha_warning_html(html)

        # Write output
        output_path.write_text(html, encoding="utf-8")

        # Copy assets
        self._copy_assets(output_path.parent)

        return output_path

    def _prepare_visualization(
        self, viz_path: Optional[Path], output_path: Path
    ) -> Optional[Dict[str, str]]:
        """Prepare visualization for HTML embedding.

        Args:
            viz_path: Path to visualization file
            output_path: HTML output path

        Returns:
            Dictionary with visualization info or None
        """
        if not viz_path or not viz_path.exists():
            return None

        # Copy visualization to output directory
        viz_dir = output_path.parent / "media"
        viz_dir.mkdir(exist_ok=True)

        dest = viz_dir / viz_path.name
        shutil.copy2(viz_path, dest)

        return {
            "path": f"media/{viz_path.name}",
            "type": "video" if viz_path.suffix == ".mp4" else "image",
        }

    def _copy_assets(self, output_dir: Path) -> None:
        """Copy CSS and other assets to output directory.

        Args:
            output_dir: Output directory
        """
        assets_src = Path(__file__).parent / "templates" / "assets"
        assets_dest = output_dir / "assets"

        if assets_src.exists():
            if assets_dest.exists():
                shutil.rmtree(assets_dest)
            shutil.copytree(assets_src, assets_dest)
