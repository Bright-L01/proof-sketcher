"""Real tests for template manager matching actual implementation."""

import pytest
from pathlib import Path
from unittest.mock import Mock, patch

from proof_sketcher.exporter.models import ExportFormat, TemplateType
from proof_sketcher.exporter.template_manager import TemplateManager
from jinja2 import TemplateNotFound


@pytest.fixture
def template_manager(tmp_path):
    """Create a template manager with test templates."""
    # Create test templates
    templates_dir = tmp_path / "templates"
    
    # HTML templates
    html_dir = templates_dir / "html"
    html_dir.mkdir(parents=True)
    (html_dir / "theorem.html.jinja2").write_text(
        "<h1>{{ theorem_name }}</h1>\n{{ content }}"
    )
    (html_dir / "index.html.jinja2").write_text(
        "<h1>Index</h1>\n{% for t in theorems %}{{ t.name }}{% endfor %}"
    )
    
    # Markdown templates
    md_dir = templates_dir / "markdown"
    md_dir.mkdir(parents=True)
    (md_dir / "theorem.md.jinja2").write_text(
        "# {{ theorem_name }}\n\n{{ content }}"
    )
    
    # PDF templates
    pdf_dir = templates_dir / "pdf"
    pdf_dir.mkdir(parents=True)
    (pdf_dir / "theorem.tex.jinja2").write_text(
        "\\section{{{ theorem_name }}}\n{{ content }}"
    )
    
    # Themes directory
    themes_dir = templates_dir / "themes"
    themes_dir.mkdir(parents=True)
    (themes_dir / "dark.css").write_text("body { background: #000; }")
    (themes_dir / "light.css").write_text("body { background: #fff; }")
    
    # Assets
    assets_dir = html_dir / "assets"
    assets_dir.mkdir(exist_ok=True)
    css_dir = assets_dir / "css"
    css_dir.mkdir(exist_ok=True)
    (css_dir / "style.css").write_text("body { margin: 0; }")
    
    return TemplateManager(template_dir=templates_dir)


class TestTemplateManagerReal:
    """Test TemplateManager actual implementation."""
    
    def test_initialization(self, tmp_path):
        """Test template manager initialization."""
        tm = TemplateManager()
        assert tm.template_dir.name == "templates"
        assert tm._current_theme == "light"
        assert isinstance(tm._template_cache, dict)
        
        # Custom directory
        custom_dir = tmp_path / "custom"
        custom_dir.mkdir()
        tm = TemplateManager(template_dir=custom_dir)
        assert tm.template_dir == custom_dir
        
    def test_get_template(self, template_manager):
        """Test getting templates."""
        # Get HTML theorem template
        template = template_manager.get_template(
            ExportFormat.HTML, TemplateType.THEOREM
        )
        assert template is not None
        assert "theorem_name" in template.source
        
        # Get markdown template
        template = template_manager.get_template(
            ExportFormat.MARKDOWN, TemplateType.THEOREM
        )
        assert template is not None
        
        # Test caching
        template2 = template_manager.get_template(
            ExportFormat.HTML, TemplateType.THEOREM
        )
        # Should be cached
        assert template2 is not None
        
    def test_get_template_not_found(self, template_manager):
        """Test handling of missing templates."""
        with pytest.raises(TemplateNotFound):
            template_manager.get_template(
                ExportFormat.HTML, TemplateType.THEOREM,
                custom_name="nonexistent.html.jinja2"
            )
            
    def test_render_template(self, template_manager):
        """Test template rendering."""
        context = {
            "theorem_name": "Pythagorean Theorem",
            "content": "a² + b² = c²"
        }
        
        # Render HTML
        html = template_manager.render_template(
            ExportFormat.HTML, TemplateType.THEOREM, context
        )
        assert "<h1>Pythagorean Theorem</h1>" in html
        assert "a² + b² = c²" in html
        
        # Render Markdown
        md = template_manager.render_template(
            ExportFormat.MARKDOWN, TemplateType.THEOREM, context
        )
        assert "# Pythagorean Theorem" in md
        
        # Render PDF
        tex = template_manager.render_template(
            ExportFormat.PDF, TemplateType.THEOREM, context
        )
        assert "\\section{Pythagorean Theorem}" in tex
        
    def test_get_asset_dir(self, template_manager):
        """Test getting asset directories."""
        # Get CSS directory
        css_dir = template_manager.get_asset_dir(ExportFormat.HTML, "css")
        assert css_dir is not None
        assert css_dir.exists()
        assert (css_dir / "style.css").exists()
        
        # Non-existent asset type
        none_dir = template_manager.get_asset_dir(ExportFormat.HTML, "nonexistent")
        assert none_dir is None
        
    def test_themes(self, template_manager):
        """Test theme management."""
        # Default theme
        assert template_manager.get_theme() == "light"
        
        # Set theme
        template_manager.set_theme("dark")
        assert template_manager.get_theme() == "dark"
        assert template_manager._current_theme == "dark"
        
        # Theme assets should be loaded
        assert "dark" in template_manager._theme_assets
        
    def test_validate_template(self, template_manager):
        """Test template validation."""
        # Valid template
        assert template_manager.validate_template(
            ExportFormat.HTML, TemplateType.THEOREM
        ) is True
        
        # Validate non-existent template
        # Should return False or raise exception
        result = template_manager.validate_template(
            ExportFormat.HTML, "nonexistent"
        )
        assert result is False
        
    def test_cache_operations(self, template_manager):
        """Test cache operations."""
        # Load some templates to populate cache
        template_manager.render_template(
            ExportFormat.HTML, TemplateType.THEOREM, {"theorem_name": "test"}
        )
        template_manager.render_template(
            ExportFormat.MARKDOWN, TemplateType.THEOREM, {"theorem_name": "test"}
        )
        
        # Get cache stats
        stats = template_manager.get_cache_stats()
        assert "total_cached" in stats
        assert stats["total_cached"] >= 2
        
        # Clear cache
        template_manager.clear_cache()
        stats = template_manager.get_cache_stats()
        assert stats["total_cached"] == 0
        
    def test_get_asset_url(self, template_manager):
        """Test asset URL generation."""
        # Local asset
        url = template_manager.get_asset_url(
            ExportFormat.HTML, "css/style.css", use_cdn=False
        )
        assert "css/style.css" in url
        
        # CDN asset
        cdn_url = template_manager.get_asset_url(
            ExportFormat.HTML, "css/style.css", use_cdn=True
        )
        assert "cdn" in cdn_url.lower() or "cloudflare" in cdn_url.lower()
        
    def test_register_custom_template(self, template_manager, tmp_path):
        """Test registering custom templates."""
        # Create custom template
        custom_template = tmp_path / "custom.html.jinja2"
        custom_template.write_text("<div>{{ custom_var }}</div>")
        
        # Register it
        template_manager.register_custom_template(
            ExportFormat.HTML, "custom", str(custom_template)
        )
        
        # Should be able to use it
        result = template_manager.render_template(
            ExportFormat.HTML, "custom", {"custom_var": "Hello"}
        )
        assert "<div>Hello</div>" in result
        
    def test_custom_filters(self, template_manager):
        """Test custom Jinja filters."""
        # Get environment to check filters
        env = template_manager._get_environment(ExportFormat.HTML)
        
        # Check standard filters exist
        assert 'truncate' in env.filters  # Built-in
        
        # HTML should have custom filters
        filters = template_manager._get_custom_filters(ExportFormat.HTML)
        assert len(filters) > 0
        
    def test_minification_filters(self, template_manager):
        """Test CSS and JS minification."""
        # Test CSS minification
        css = """
        body {
            margin: 0;
            padding: 0;
        }
        """
        minified_css = template_manager._minify_css(css)
        assert "body{" in minified_css
        assert "\n" not in minified_css.strip()
        
        # Test JS minification  
        js = """
        function test() {
            console.log('hello');
        }
        """
        minified_js = template_manager._minify_js(js)
        assert "function test" in minified_js
        assert "\n" not in minified_js.strip()
        
    def test_markdown_helpers(self, template_manager):
        """Test markdown-specific helpers."""
        # Collapsible section
        collapsible = template_manager._format_collapsible_md(
            "Content here", "Click to expand"
        )
        assert "<details>" in collapsible
        assert "<summary>Click to expand</summary>" in collapsible
        
        # GitHub badge
        badge = template_manager._format_github_badge("coverage", "95%", "green")
        assert "shields.io" in badge
        assert "coverage-95%25-green" in badge
        
    def test_template_dependencies(self, template_manager):
        """Test template dependency tracking."""
        # Load a template
        template = template_manager.get_template(
            ExportFormat.HTML, TemplateType.THEOREM
        )
        
        # Dependencies should be tracked
        cache_key = "html/theorem.html.jinja2"
        assert cache_key in template_manager._template_cache
        
    def test_required_variables(self, template_manager):
        """Test getting required variables for templates."""
        # Get required vars for theorem template
        required = template_manager._get_required_variables(TemplateType.THEOREM)
        # Should return a set of required variable names
        assert isinstance(required, set)
        
    def test_template_modification_detection(self, template_manager, tmp_path):
        """Test that modified templates are reloaded."""
        # Render template first time
        result1 = template_manager.render_template(
            ExportFormat.HTML, TemplateType.THEOREM,
            {"theorem_name": "Test", "content": "Content"}
        )
        
        # Modify template
        template_path = template_manager.template_dir / "html" / "theorem.html.jinja2"
        template_path.write_text("<h2>{{ theorem_name }}</h2>")  # Changed h1 to h2
        
        # Clear the cache entry to force reload
        template_manager.clear_cache()
        
        # Render again - should use new template
        result2 = template_manager.render_template(
            ExportFormat.HTML, TemplateType.THEOREM,
            {"theorem_name": "Test", "content": "Content"}
        )
        
        assert "<h1>" in result1
        assert "<h2>" in result2
        
    def test_debug_mode(self, template_manager):
        """Test debug mode functionality."""
        # Enable debug mode
        with patch.dict('os.environ', {'TEMPLATE_DEBUG': 'true'}):
            tm = TemplateManager(template_dir=template_manager.template_dir)
            assert tm._debug_mode is True
            
    def test_error_handling(self, template_manager):
        """Test error handling in template operations."""
        # Render with invalid context (should handle gracefully)
        result = template_manager.render_template(
            ExportFormat.HTML, TemplateType.THEOREM,
            {}  # Missing required variables
        )
        # Should still render but with empty values
        assert "<h1></h1>" in result
        
    def test_custom_globals(self, template_manager):
        """Test custom global functions in templates."""
        # Get environment
        env = template_manager._get_environment(ExportFormat.HTML)
        
        # Check globals
        assert 'now' in env.globals or 'get_current_time' in env.globals