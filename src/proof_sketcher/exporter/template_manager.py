"""Template management for exporters."""

import logging
from pathlib import Path
from typing import Any, Dict, Optional

from jinja2 import Environment, FileSystemLoader, Template, TemplateNotFound

from .models import ExportFormat, TemplateType


class TemplateManager:
    """Manages templates for different export formats."""

    def __init__(self, template_dir: Optional[Path] = None):
        """Initialize template manager.

        Args:
            template_dir: Base directory for templates
        """
        self.template_dir = template_dir or self._get_default_template_dir()
        self.logger = logging.getLogger(__name__)
        self._environments: Dict[ExportFormat, Environment] = {}
        self._template_cache: Dict[str, Template] = {}

    def get_template(
        self,
        format: ExportFormat,
        template_type: TemplateType,
        custom_name: Optional[str] = None,
    ) -> Template:
        """Get a template for the specified format and type.

        Args:
            format: Export format
            template_type: Type of template
            custom_name: Custom template name (overrides default)

        Returns:
            Loaded template

        Raises:
            TemplateNotFound: If template doesn't exist
        """
        template_name = (
            custom_name or f"{template_type.value}.{self._get_extension(format)}"
        )
        cache_key = f"{format.value}/{template_name}"

        # Check cache
        if cache_key in self._template_cache:
            return self._template_cache[cache_key]

        # Get environment for format
        env = self._get_environment(format)

        # Load template
        try:
            template = env.get_template(template_name)
            self._template_cache[cache_key] = template
            return template
        except TemplateNotFound:
            self.logger.error(
                f"Template not found: {template_name} for format {format.value}"
            )
            raise

    def render_template(
        self,
        format: ExportFormat,
        template_type: TemplateType,
        context: Dict[str, Any],
        custom_name: Optional[str] = None,
    ) -> str:
        """Render a template with the given context.

        Args:
            format: Export format
            template_type: Type of template
            context: Template context
            custom_name: Custom template name

        Returns:
            Rendered template string
        """
        template = self.get_template(format, template_type, custom_name)
        return template.render(**context)

    def get_asset_dir(self, format: ExportFormat, asset_type: str) -> Optional[Path]:
        """Get directory for static assets.

        Args:
            format: Export format
            asset_type: Type of asset (css, js, images)

        Returns:
            Path to asset directory if exists
        """
        asset_dir = self.template_dir / format.value / "assets" / asset_type
        return asset_dir if asset_dir.exists() else None

    def register_custom_template(
        self, format: ExportFormat, template_name: str, template_content: str
    ) -> None:
        """Register a custom template programmatically.

        Args:
            format: Export format
            template_name: Template name
            template_content: Template content
        """
        env = self._get_environment(format)
        template = env.from_string(template_content)
        cache_key = f"{format.value}/{template_name}"
        self._template_cache[cache_key] = template

    def _get_environment(self, format: ExportFormat) -> Environment:
        """Get or create Jinja2 environment for format.

        Args:
            format: Export format

        Returns:
            Jinja2 environment
        """
        if format not in self._environments:
            template_path = self.template_dir / format.value

            # Create environment with custom settings
            env = Environment(
                loader=FileSystemLoader(template_path),
                autoescape=format == ExportFormat.HTML,
                trim_blocks=True,
                lstrip_blocks=True,
            )

            # Add custom filters
            env.filters.update(self._get_custom_filters(format))

            # Add custom globals
            env.globals.update(self._get_custom_globals(format))

            self._environments[format] = env

        return self._environments[format]

    def _get_extension(self, format: ExportFormat) -> str:
        """Get file extension for template format.

        Args:
            format: Export format

        Returns:
            File extension
        """
        extensions = {
            ExportFormat.HTML: "html.jinja2",
            ExportFormat.MARKDOWN: "md.jinja2",
            ExportFormat.PDF: "tex.jinja2",
            ExportFormat.JUPYTER: "ipynb.jinja2",
        }
        return extensions.get(format, "txt.jinja2")

    def _get_default_template_dir(self) -> Path:
        """Get default template directory.

        Returns:
            Path to template directory
        """
        # Look for templates in package
        package_dir = Path(__file__).parent
        template_dir = package_dir / "templates"

        if not template_dir.exists():
            # Fall back to project root
            project_root = package_dir.parent.parent.parent
            template_dir = project_root / "templates"

        return template_dir

    def _get_custom_filters(self, format: ExportFormat) -> Dict[str, Any]:
        """Get custom Jinja2 filters for format.

        Args:
            format: Export format

        Returns:
            Dictionary of custom filters
        """
        filters = {
            "latex_escape": self._latex_escape,
            "markdown_escape": self._markdown_escape,
            "slugify": self._slugify,
            "format_date": self._format_date,
        }

        if format == ExportFormat.HTML:
            filters.update(
                {
                    "highlight_code": self._highlight_code_html,
                    "render_math": self._render_math_html,
                }
            )
        elif format == ExportFormat.MARKDOWN:
            filters.update(
                {"indent": self._indent_text, "code_block": self._format_code_block_md}
            )
        elif format == ExportFormat.PDF:
            filters.update(
                {
                    "tex_math": self._format_tex_math,
                    "tex_verbatim": self._format_tex_verbatim,
                }
            )

        return filters

    def _get_custom_globals(self, format: ExportFormat) -> Dict[str, Any]:
        """Get custom Jinja2 globals for format.

        Args:
            format: Export format

        Returns:
            Dictionary of custom globals
        """
        return {
            "format": format.value,
            "now": self._get_current_time,
            "version": "0.1.0",
        }

    # Filter implementations

    @staticmethod
    def _latex_escape(text: str) -> str:
        """Escape text for LaTeX."""
        replacements = {
            "\\": r"\textbackslash{}",
            "{": r"\{",
            "}": r"\}",
            "$": r"\$",
            "&": r"\&",
            "#": r"\#",
            "^": r"\^{}",
            "_": r"\_",
            "~": r"\~{}",
            "%": r"\%",
        }
        for old, new in replacements.items():
            text = text.replace(old, new)
        return text

    @staticmethod
    def _markdown_escape(text: str) -> str:
        """Escape text for Markdown."""
        # Escape markdown special characters
        chars_to_escape = ["*", "_", "`", "[", "]", "(", ")", "#", "+", "-", "!"]
        for char in chars_to_escape:
            text = text.replace(char, f"\\{char}")
        return text

    @staticmethod
    def _slugify(text: str) -> str:
        """Convert text to URL-safe slug."""
        import re

        text = text.lower()
        text = re.sub(r"[^\w\s-]", "", text)
        text = re.sub(r"[-\s]+", "-", text)
        return text.strip("-")

    @staticmethod
    def _format_date(timestamp: str, format: str = "%Y-%m-%d %H:%M") -> str:
        """Format ISO timestamp."""
        from datetime import datetime

        dt = datetime.fromisoformat(timestamp)
        return dt.strftime(format)

    @staticmethod
    def _highlight_code_html(code: str, language: str = "lean") -> str:
        """Highlight code for HTML output."""
        # Simple implementation - in production, use pygments
        escaped = code.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
        return f'<pre><code class="language-{language}">{escaped}</code></pre>'

    @staticmethod
    def _render_math_html(math: str, display: bool = False) -> str:
        """Render math for HTML (KaTeX/MathJax compatible)."""
        if display:
            return f'<div class="math display">\\[{math}\\]</div>'
        else:
            return f'<span class="math inline">\\({math}\\)</span>'

    @staticmethod
    def _indent_text(text: str, level: int = 2) -> str:
        """Indent text by specified level."""
        indent = " " * level
        return "\n".join(indent + line for line in text.splitlines())

    @staticmethod
    def _format_code_block_md(code: str, language: str = "lean") -> str:
        """Format code block for Markdown."""
        return f"```{language}\n{code}\n```"

    @staticmethod
    def _format_tex_math(math: str, display: bool = False) -> str:
        """Format math for LaTeX."""
        if display:
            return f"\\[{math}\\]"
        else:
            return f"${math}$"

    @staticmethod
    def _format_tex_verbatim(text: str) -> str:
        """Format verbatim text for LaTeX."""
        return f"\\begin{{verbatim}}\n{text}\n\\end{{verbatim}}"

    @staticmethod
    def _get_current_time() -> str:
        """Get current time as ISO string."""
        from datetime import datetime

        return datetime.now().isoformat()
