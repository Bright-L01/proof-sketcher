"""Template management for exporters.

Features:
- Template caching with invalidation
- Theme support (light/dark modes)
- Asset path resolution
- Template validation
- Custom filter registry
"""

import hashlib
import logging
import os
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from jinja2 import Environment, FileSystemLoader, Template, TemplateNotFound, meta

from .models import ExportFormat, TemplateType


class TemplateManager:
    """Enhanced template manager with caching, themes, and validation.
    
    Features:
    - Intelligent template caching with file modification tracking
    - Theme support for light/dark modes
    - Asset path resolution with CDN fallbacks  
    - Template validation and dependency analysis
    - Custom filter and global registration
    """

    def __init__(self, template_dir: Optional[Path] = None):
        """Initialize template manager.

        Args:
            template_dir: Base directory for templates
        """
        self.template_dir = template_dir or self._get_default_template_dir()
        self.logger = logging.getLogger(__name__)
        
        # Environment and template caching
        self._environments: Dict[ExportFormat, Environment] = {}
        self._template_cache: Dict[str, Tuple[Template, float]] = {}  # (template, mtime)
        self._template_dependencies: Dict[str, Set[str]] = {}
        
        # Theme and asset management
        self._current_theme = "light"
        self._theme_assets: Dict[str, Dict[str, str]] = {}
        self._asset_cache: Dict[str, str] = {}
        
        # Validation and debugging
        self._validation_cache: Dict[str, bool] = {}
        self._debug_mode = os.getenv('TEMPLATE_DEBUG', 'false').lower() == 'true'
        
        # Initialize themes
        self._load_themes()

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

        # Check cache with modification time validation
        if cache_key in self._template_cache:
            cached_template, cached_mtime = self._template_cache[cache_key]
            template_path = self.template_dir / format.value / template_name
            
            if template_path.exists():
                current_mtime = template_path.stat().st_mtime
                if current_mtime <= cached_mtime:
                    self.logger.debug(f"Using cached template: {cache_key}")
                    return cached_template
                else:
                    self.logger.debug(f"Template modified, invalidating cache: {cache_key}")
                    del self._template_cache[cache_key]

        # Get environment for format
        env = self._get_environment(format)

        # Load and cache template
        try:
            template = env.get_template(template_name)
            
            # Cache with modification time
            template_path = self.template_dir / format.value / template_name
            if template_path.exists():
                mtime = template_path.stat().st_mtime
                self._template_cache[cache_key] = (template, mtime)
                
                # Analyze template dependencies
                self._analyze_template_dependencies(cache_key, template)
            
            self.logger.debug(f"Loaded and cached template: {cache_key}")
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
        self._template_cache[cache_key] = (template, time.time())

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

    # Enhanced template management methods

    def set_theme(self, theme: str) -> None:
        """Set current theme.
        
        Args:
            theme: Theme name ('light', 'dark', etc.)
        """
        if theme != self._current_theme:
            self._current_theme = theme
            self.logger.info(f"Changed theme to: {theme}")
            
            # Invalidate asset cache to reload theme-specific assets
            self._asset_cache.clear()

    def get_theme(self) -> str:
        """Get current theme.
        
        Returns:
            Current theme name
        """
        return self._current_theme

    def validate_template(self, format: ExportFormat, template_type: TemplateType) -> bool:
        """Validate template syntax and dependencies.
        
        Args:
            format: Export format
            template_type: Template type
            
        Returns:
            True if template is valid
        """
        try:
            template = self.get_template(format, template_type)
            
            # Check template syntax by parsing
            source = template.source
            env = self._get_environment(format)
            parsed = env.parse(source)
            
            # Check for required variables
            variables = meta.find_undeclared_variables(parsed)
            required_vars = self._get_required_variables(template_type)
            
            missing_vars = required_vars - variables
            if missing_vars:
                self.logger.warning(f"Template missing required variables: {missing_vars}")
                return False
                
            cache_key = f"{format.value}/{template_type.value}"
            self._validation_cache[cache_key] = True
            return True
            
        except Exception as e:
            self.logger.error(f"Template validation failed: {e}")
            return False

    def get_asset_url(self, format: ExportFormat, asset_path: str, use_cdn: bool = False) -> str:
        """Get URL for static asset with CDN fallback.
        
        Args:
            format: Export format
            asset_path: Relative asset path
            use_cdn: Whether to use CDN URLs
            
        Returns:
            Asset URL
        """
        cache_key = f"{format.value}/{asset_path}/{self._current_theme}"
        
        if cache_key in self._asset_cache:
            return self._asset_cache[cache_key]
        
        # Check for theme-specific asset
        theme_path = f"themes/{self._current_theme}/{asset_path}"
        theme_asset = self.template_dir / format.value / "assets" / theme_path
        
        if theme_asset.exists():
            url = f"assets/{theme_path}"
        else:
            # Fall back to default asset
            default_asset = self.template_dir / format.value / "assets" / asset_path
            if default_asset.exists():
                url = f"assets/{asset_path}"
            elif use_cdn:
                url = self._get_cdn_url(asset_path)
            else:
                self.logger.warning(f"Asset not found: {asset_path}")
                url = asset_path
        
        # Add cache-busting hash
        if not use_cdn:
            url = self._add_cache_buster(url, format)
        
        self._asset_cache[cache_key] = url
        return url

    def clear_cache(self) -> None:
        """Clear all template and asset caches."""
        self._template_cache.clear()
        self._asset_cache.clear()
        self._validation_cache.clear()
        self.logger.info("Cleared all template caches")

    def get_cache_stats(self) -> Dict[str, int]:
        """Get cache statistics.
        
        Returns:
            Dictionary with cache statistics
        """
        return {
            "templates_cached": len(self._template_cache),
            "assets_cached": len(self._asset_cache),
            "validations_cached": len(self._validation_cache),
            "environments_loaded": len(self._environments)
        }

    def _load_themes(self) -> None:
        """Load available themes from theme directories."""
        themes_dir = self.template_dir / "themes"
        if themes_dir.exists():
            for theme_dir in themes_dir.iterdir():
                if theme_dir.is_dir():
                    theme_name = theme_dir.name
                    self._theme_assets[theme_name] = {}
                    
                    # Load theme assets
                    for asset_file in theme_dir.rglob("*"):
                        if asset_file.is_file():
                            rel_path = asset_file.relative_to(theme_dir)
                            self._theme_assets[theme_name][str(rel_path)] = str(asset_file)
            
            self.logger.debug(f"Loaded themes: {list(self._theme_assets.keys())}")

    def _analyze_template_dependencies(self, cache_key: str, template: Template) -> None:
        """Analyze template dependencies.
        
        Args:
            cache_key: Template cache key
            template: Template instance
        """
        try:
            # Parse template to find dependencies
            env = template.environment
            parsed = env.parse(template.source)
            
            # Find included/extended templates
            dependencies = set()
            for node in parsed.find_all((meta.Include, meta.Extends)):
                if hasattr(node, 'template'):
                    dependencies.add(node.template.value)
            
            self._template_dependencies[cache_key] = dependencies
            
        except Exception as e:
            self.logger.debug(f"Failed to analyze dependencies for {cache_key}: {e}")

    def _get_required_variables(self, template_type: TemplateType) -> Set[str]:
        """Get required variables for template type.
        
        Args:
            template_type: Template type
            
        Returns:
            Set of required variable names
        """
        required_vars = {
            TemplateType.INDEX: {'project_name', 'theorems', 'timestamp'},
            TemplateType.THEOREM: {'theorem_name', 'introduction', 'key_steps', 'conclusion'},
        }
        
        return required_vars.get(template_type, set())

    def _get_cdn_url(self, asset_path: str) -> str:
        """Get CDN URL for asset.
        
        Args:
            asset_path: Asset path
            
        Returns:
            CDN URL
        """
        # Common CDN mappings
        cdn_mappings = {
            'css/katex.min.css': 'https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/katex.min.css',
            'js/katex.min.js': 'https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/katex.min.js',
            'js/katex-auto-render.min.js': 'https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/contrib/auto-render.min.js',
            'css/prism.css': 'https://cdn.jsdelivr.net/npm/prismjs@1.29.0/themes/prism.min.css',
            'js/prism.js': 'https://cdn.jsdelivr.net/npm/prismjs@1.29.0/components/prism-core.min.js'
        }
        
        return cdn_mappings.get(asset_path, f"https://cdn.example.com/{asset_path}")

    def _add_cache_buster(self, url: str, format: ExportFormat) -> str:
        """Add cache-busting parameter to URL.
        
        Args:
            url: Asset URL
            format: Export format
            
        Returns:
            URL with cache buster
        """
        try:
            asset_file = self.template_dir / format.value / url
            if asset_file.exists():
                # Use file modification time as cache buster
                mtime = int(asset_file.stat().st_mtime)
                separator = '&' if '?' in url else '?'
                return f"{url}{separator}v={mtime}"
        except (OSError, ValueError):
            pass
            
        return url

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
            "asset_url": lambda path: self.get_asset_url(format, path),
            "theme_asset": lambda path: self.get_asset_url(format, path, use_cdn=False),
        }

        if format == ExportFormat.HTML:
            filters.update(
                {
                    "highlight_code": self._highlight_code_html,
                    "render_math": self._render_math_html,
                    "minify_css": self._minify_css,
                    "minify_js": self._minify_js,
                }
            )
        elif format == ExportFormat.MARKDOWN:
            filters.update(
                {
                    "indent": self._indent_text, 
                    "code_block": self._format_code_block_md,
                    "collapsible": self._format_collapsible_md,
                    "github_badge": self._format_github_badge,
                }
            )
        elif format == ExportFormat.PDF:
            filters.update(
                {
                    "tex_math": self._format_tex_math,
                    "tex_verbatim": self._format_tex_verbatim,
                }
            )

        return filters

    # Additional filter implementations

    @staticmethod
    def _minify_css(css: str) -> str:
        """Minify CSS content."""
        import re
        # Remove comments
        css = re.sub(r'/\*.*?\*/', '', css, flags=re.DOTALL)
        # Remove extra whitespace
        css = re.sub(r'\s+', ' ', css)
        css = re.sub(r'\s*([{}:;,>+~])\s*', r'\1', css)
        return css.strip()

    @staticmethod
    def _minify_js(js: str) -> str:
        """Minify JavaScript content."""
        import re
        # Remove single-line comments
        js = re.sub(r'//.*$', '', js, flags=re.MULTILINE)
        # Remove multi-line comments
        js = re.sub(r'/\*.*?\*/', '', js, flags=re.DOTALL)
        # Remove extra whitespace
        js = re.sub(r'\s+', ' ', js)
        return js.strip()

    @staticmethod
    def _format_collapsible_md(content: str, summary: str, open: bool = False) -> str:
        """Format collapsible section for GitHub markdown."""
        open_attr = " open" if open else ""
        return f"<details{open_attr}>\n<summary>{summary}</summary>\n\n{content}\n\n</details>"

    @staticmethod
    def _format_github_badge(text: str, value: str, color: str = "blue") -> str:
        """Format GitHub badge."""
        return f"![{text}](https://img.shields.io/badge/{text}-{value}-{color})"
