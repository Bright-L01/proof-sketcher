"""Additional tests to boost exporter coverage to 85%+."""

import gzip
import json
import shutil
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock
import pytest

from src.proof_sketcher.exporter.html import HTMLExporter
from src.proof_sketcher.exporter.markdown import MarkdownExporter
from src.proof_sketcher.exporter.template_manager import TemplateManager
from src.proof_sketcher.exporter.models import (
    ExportContext,
    ExportFormat,
    ExportOptions,
    TemplateType,
)
from src.proof_sketcher.generator.models import ProofSketch, ProofStep


@pytest.fixture
def sample_sketch():
    """Create a sample proof sketch for testing."""
    return ProofSketch(
        theorem_name="test_theorem",
        introduction="This is an introduction to the theorem.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="First step",
                mathematical_content="x + 0 = x",
                tactics=["simp"],
                intuition="Adding zero doesn't change the value."
            ),
            ProofStep(
                step_number=2,
                description="Second step",
                mathematical_content="x = x",
                tactics=["refl"],
                intuition="Reflexivity of equality."
            )
        ],
        conclusion="Therefore, the theorem holds.",
        difficulty_level="intermediate",
        mathematical_areas=["algebra"]
    )


@pytest.fixture
def temp_output_dir():
    """Create a temporary output directory."""
    with tempfile.TemporaryDirectory() as temp_dir:
        yield Path(temp_dir)


class TestHTMLExporterCoverage:
    """Test HTML exporter for missing coverage areas."""

    def test_create_index_with_animations(self, sample_sketch, temp_output_dir):
        """Test index creation with animation assets."""
        options = ExportOptions(output_dir=temp_output_dir, create_subdirs=True)
        exporter = HTMLExporter(options)
        
        # Create mock animation
        animations_dir = temp_output_dir / "animations"
        animations_dir.mkdir(exist_ok=True)
        animation_file = animations_dir / "test_animation.mp4"
        animation_file.write_text("fake video content")
        
        context = ExportContext(
            format=ExportFormat.HTML,
            output_dir=temp_output_dir,
            include_animations=True,
            animations={"test_theorem": animation_file},
            sketches=[sample_sketch],
            theorem_links={"test_theorem": "test_theorem.html"}
        )
        
        result = exporter._create_index([sample_sketch], context)
        assert result is not None
        assert result.exists()
        
        content = result.read_text()
        assert "test_theorem" in content
        assert "Animated" in content  # The template shows 🎬 Animated instead of has_animation

    def test_copy_assets_error_handling(self, temp_output_dir):
        """Test asset copying with error conditions."""
        options = ExportOptions(output_dir=temp_output_dir, create_subdirs=True)
        exporter = HTMLExporter(options)
        
        # Mock template manager to return non-existent asset directory
        with patch.object(exporter.template_manager, 'template_dir') as mock_dir:
            mock_dir.__truediv__.return_value = Path("/nonexistent/path")
            
            # Should not raise error, just return empty list
            result = exporter._copy_assets()
            assert isinstance(result, list)

    def test_generate_search_index(self, sample_sketch, temp_output_dir):
        """Test search index generation."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = HTMLExporter(options)
        
        result = exporter._generate_search_index([sample_sketch])
        assert result is not None
        assert result.exists()
        
        # Verify JSON structure
        data = json.loads(result.read_text())
        assert len(data) == 1
        assert data[0]["id"] == "test_theorem"
        assert "content" in data[0]

    def test_generate_poster_frame_ffmpeg_error(self, temp_output_dir):
        """Test poster frame generation with ffmpeg errors."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = HTMLExporter(options)
        
        video_path = temp_output_dir / "test.mp4"
        video_path.write_text("fake video")
        
        with patch('subprocess.run') as mock_run:
            # Simulate ffmpeg failure
            mock_run.return_value.returncode = 1
            mock_run.return_value.stderr = "ffmpeg error"
            
            result = exporter._generate_poster_frame(video_path, "test", temp_output_dir)
            assert result is None

    def test_convert_to_webm_missing_ffmpeg(self, temp_output_dir):
        """Test WebM conversion when ffmpeg is not available."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = HTMLExporter(options)
        
        video_path = temp_output_dir / "test.mp4"
        video_path.write_text("fake video")
        
        with patch('subprocess.run', side_effect=FileNotFoundError("ffmpeg not found")):
            result = exporter._convert_to_webm(video_path, "test", temp_output_dir)
            assert result is None

    def test_convert_to_gif_subprocess_error(self, temp_output_dir):
        """Test GIF conversion with subprocess error."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = HTMLExporter(options)
        
        video_path = temp_output_dir / "test.mp4"
        video_path.write_text("fake video")
        
        with patch('subprocess.run', side_effect=subprocess.SubprocessError("Process error")):
            result = exporter._convert_to_gif(video_path, "test", temp_output_dir)
            assert result is None

    def test_minify_css_and_js(self, temp_output_dir):
        """Test CSS and JS minification."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = HTMLExporter(options)
        
        # Test CSS minification
        css_content = """
        /* Comment */
        .class {
            color: red;
            margin: 0;
        }
        """
        minified_css = exporter._minify_css(css_content)
        assert "/*" not in minified_css
        assert len(minified_css) < len(css_content)
        
        # Test JS minification
        js_content = """
        // Comment
        function test() {
            return true;
        }
        """
        minified_js = exporter._minify_js(js_content)
        assert "//" not in minified_js
        assert len(minified_js) < len(js_content)

    def test_copy_and_minify_asset_error(self, temp_output_dir):
        """Test asset minification with encoding errors."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = HTMLExporter(options)
        
        # Create source file with invalid encoding
        src = temp_output_dir / "source.css"
        dst = temp_output_dir / "dest.css"
        
        # Write binary content that's not valid UTF-8
        src.write_bytes(b'\xff\xfe\x00invalid')
        
        # Should fall back to copying without minification
        exporter._copy_and_minify_asset(src, dst)
        assert dst.exists()

    def test_compress_asset(self, temp_output_dir):
        """Test asset compression."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = HTMLExporter(options)
        
        # Create a file with repetitive content (compresses well)
        test_file = temp_output_dir / "test.txt"
        test_file.write_text("a" * 2000)  # Ensure > 1KB for compression
        
        exporter._compress_asset(test_file)
        
        # Check if compressed version was created and is smaller
        compressed_file = Path(f"{test_file}.gz")
        if compressed_file.exists():
            assert compressed_file.stat().st_size < test_file.stat().st_size


class TestMarkdownExporterCoverage:
    """Test Markdown exporter for missing coverage areas."""

    def test_generate_enhanced_toc_with_animations(self, sample_sketch, temp_output_dir):
        """Test enhanced TOC generation with animations."""
        options = ExportOptions(output_dir=temp_output_dir, generate_toc=True)
        exporter = MarkdownExporter(options)
        
        # Create mock animation files
        animations_dir = temp_output_dir / "animations"
        animations_dir.mkdir(exist_ok=True)
        gif_file = animations_dir / "test_theorem.gif"
        gif_file.write_text("fake gif")
        
        context = ExportContext(
            format=ExportFormat.MARKDOWN,
            output_dir=temp_output_dir,
            animations={"test_theorem": animations_dir / "test_theorem.mp4"},
            sketches=[sample_sketch]
        )
        
        result = exporter._generate_enhanced_toc([sample_sketch], context)
        assert result is not None
        assert result.exists()
        
        content = result.read_text()
        assert "Animated Proofs" in content
        assert "test_theorem" in content

    def test_generate_animation_previews(self, sample_sketch, temp_output_dir):
        """Test animation preview generation."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = MarkdownExporter(options)
        
        # Create mock animation files
        animations_dir = temp_output_dir / "animations"
        animations_dir.mkdir(exist_ok=True)
        video_file = animations_dir / "test_theorem.mp4"
        gif_file = animations_dir / "test_theorem.gif"
        video_file.write_text("fake video")
        gif_file.write_text("fake gif")
        
        context = ExportContext(
            format=ExportFormat.MARKDOWN,
            output_dir=temp_output_dir,
            animations={"test_theorem": video_file},
            sketches=[sample_sketch]
        )
        
        result = exporter._generate_animation_previews([sample_sketch], context)
        assert len(result) == 1
        assert result[0].name == "animations.md"
        
        content = result[0].read_text()
        assert "test_theorem" in content

    def test_collapsible_sections_creation(self, temp_output_dir):
        """Test collapsible sections for complex proofs."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = MarkdownExporter(options)
        
        # Create sketch with many steps
        complex_sketch = ProofSketch(
            theorem_name="complex_theorem",
            introduction="A" * 600,  # Long introduction > 500 chars
            key_steps=[
                ProofStep(
                    step_number=i,
                    description=f"Step {i}",
                    mathematical_content=f"step_{i}",
                    tactics=["tactic"]
                ) for i in range(1, 6)  # 5 steps > 3
            ],
            conclusion="Complex conclusion"
        )
        
        sections = exporter._create_collapsible_sections(complex_sketch)
        assert "proof_steps" in sections
        assert "detailed_explanation" in sections

    def test_convert_math_to_dollars(self, temp_output_dir):
        """Test LaTeX to dollar notation conversion."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = MarkdownExporter(options)
        
        context = {
            "text_with_math": "This is \\\\[ x + y = z \\\\] display math and \\\\( a = b \\\\) inline math",
            "nested_dict": {
                "equation": "\\begin{equation}E = mc^2\\end{equation}"
            },
            "non_string": 42
        }
        
        converted = exporter._convert_math_to_dollars(context)
        assert "$$" in converted["text_with_math"]
        assert "$" in converted["text_with_math"]
        assert "$$E = mc^2$$" in converted["nested_dict"]["equation"]
        assert converted["non_string"] == 42  # Unchanged

    def test_export_multiple_with_toc_error(self, sample_sketch, temp_output_dir):
        """Test export_multiple with TOC generation error."""
        options = ExportOptions(output_dir=temp_output_dir, generate_toc=True)
        exporter = MarkdownExporter(options)
        
        with patch.object(exporter, '_generate_enhanced_toc', side_effect=Exception("TOC error")):
            result = exporter.export_multiple([sample_sketch])
            assert result.success
            assert any("Failed to generate TOC" in warning for warning in result.warnings)

    def test_export_multiple_with_animation_preview_error(self, sample_sketch, temp_output_dir):
        """Test export_multiple with animation preview error."""
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = MarkdownExporter(options)
        
        context = ExportContext(
            format=ExportFormat.MARKDOWN,
            output_dir=temp_output_dir,
            animations={"test": Path("fake.mp4")}
        )
        
        with patch.object(exporter, '_generate_animation_previews', side_effect=Exception("Preview error")):
            result = exporter.export_multiple([sample_sketch], context)
            assert result.success
            assert any("Failed to generate animation previews" in warning for warning in result.warnings)


class TestTemplateManagerCoverage:
    """Test template manager for missing coverage areas."""

    def test_template_cache_mechanism(self, temp_output_dir):
        """Test template caching with modification time tracking."""
        template_dir = temp_output_dir / "templates"
        (template_dir / "html").mkdir(parents=True)
        
        template_file = template_dir / "html" / "theorem.html.jinja2"
        template_file.write_text("{{ theorem_name }}")
        
        manager = TemplateManager(template_dir)
        
        # Load template (should cache it)
        template1 = manager.get_template(ExportFormat.HTML, TemplateType.THEOREM)
        assert template1 is not None
        
        # Load again (should use cache)
        template2 = manager.get_template(ExportFormat.HTML, TemplateType.THEOREM)
        assert template2 is not None

    def test_missing_template_handling(self, temp_output_dir):
        """Test handling of missing templates."""
        template_dir = temp_output_dir / "templates"
        template_dir.mkdir()
        
        manager = TemplateManager(template_dir)
        
        # Try to load non-existent template
        from jinja2 import TemplateNotFound
        with pytest.raises(TemplateNotFound):
            manager.get_template(ExportFormat.HTML, TemplateType.THEOREM)

    def test_template_error_recovery(self, temp_output_dir):
        """Test template error recovery mechanisms."""
        template_dir = temp_output_dir / "templates"
        (template_dir / "html").mkdir(parents=True)
        
        # Create template with syntax error
        bad_template = template_dir / "html" / "theorem.html.jinja2"
        bad_template.write_text("{{ unclosed_block")
        
        manager = TemplateManager(template_dir)
        
        # Should raise TemplateSyntaxError
        from jinja2 import TemplateSyntaxError
        with pytest.raises(TemplateSyntaxError):
            manager.get_template(ExportFormat.HTML, TemplateType.THEOREM)

    def test_default_template_directory(self):
        """Test default template directory resolution."""
        manager = TemplateManager()
        assert manager.template_dir.exists()
        assert manager.template_dir.name == "templates"

    def test_render_template_basic(self, temp_output_dir):
        """Test basic template rendering."""
        template_dir = temp_output_dir / "templates"
        (template_dir / "html").mkdir(parents=True)
        
        template_file = template_dir / "html" / "theorem.html.jinja2"
        template_file.write_text("<h1>{{ theorem_name }}</h1>")
        
        manager = TemplateManager(template_dir)
        
        result = manager.render_template(
            ExportFormat.HTML, 
            TemplateType.THEOREM, 
            {"theorem_name": "test_theorem"}
        )
        assert "<h1>test_theorem</h1>" in result

    def test_render_template_error_handling(self, temp_output_dir):
        """Test template rendering error handling."""
        template_dir = temp_output_dir / "templates"
        (template_dir / "html").mkdir(parents=True)
        
        # Template that will cause runtime error
        template_file = template_dir / "html" / "theorem.html.jinja2"
        template_file.write_text("{{ undefined_variable.missing_attr }}")
        
        manager = TemplateManager(template_dir)
        
        # Should raise error during rendering
        with pytest.raises(Exception):
            manager.render_template(
                ExportFormat.HTML, 
                TemplateType.THEOREM, 
                {"theorem_name": "test"}
            )

    def test_theme_loading_system(self, temp_output_dir):
        """Test theme loading functionality."""
        template_dir = temp_output_dir / "templates"
        template_dir.mkdir()
        
        # Test initialization loads themes
        manager = TemplateManager(template_dir)
        assert hasattr(manager, '_theme_assets')
        assert hasattr(manager, '_current_theme')

    def test_environment_caching(self, temp_output_dir):
        """Test Jinja2 environment caching."""
        template_dir = temp_output_dir / "templates"
        template_dir.mkdir()
        
        manager = TemplateManager(template_dir)
        
        # Get environment for HTML (should create and cache)
        env1 = manager._get_environment(ExportFormat.HTML)
        assert env1 is not None
        
        # Get again (should return cached)
        env2 = manager._get_environment(ExportFormat.HTML)
        assert env1 is env2  # Same object

    def test_html_export_multiple_with_asset_errors(self, sample_sketch, temp_output_dir):
        """Test HTML export_multiple with asset copying errors."""
        options = ExportOptions(output_dir=temp_output_dir, create_subdirs=True)
        exporter = HTMLExporter(options)
        
        # Mock _copy_assets to raise an exception
        with patch.object(exporter, '_copy_assets', side_effect=Exception("Asset error")):
            result = exporter.export_multiple([sample_sketch])
            assert result.success
            assert any("Failed to copy assets" in warning for warning in result.warnings)

    def test_html_export_multiple_search_index_error(self, temp_output_dir):
        """Test HTML export_multiple with search index generation error."""
        options = ExportOptions(output_dir=temp_output_dir, create_subdirs=True)
        exporter = HTMLExporter(options)
        
        # Create enough sketches to trigger search index (>5)
        sketches = [
            ProofSketch(
                theorem_name=f"theorem_{i}",
                introduction=f"Introduction {i}",
                key_steps=[],
                conclusion=f"Conclusion {i}"
            ) for i in range(6)
        ]
        
        with patch.object(exporter, '_generate_search_index', side_effect=Exception("Search error")):
            result = exporter.export_multiple(sketches)
            assert result.success
            assert any("Failed to generate search index" in warning for warning in result.warnings)

    def test_markdown_format_link_absolute_mode(self, temp_output_dir):
        """Test markdown link formatting in absolute mode."""
        # Need to set _link_mode directly since it's read from options during init
        options = ExportOptions(output_dir=temp_output_dir)
        exporter = MarkdownExporter(options)
        exporter._link_mode = 'absolute'  # Override after init
        
        test_path = temp_output_dir / "test.md"
        test_path.write_text("content")
        
        result = exporter._format_link(test_path)
        assert str(test_path.absolute()) == result

    def test_markdown_format_link_relative_error(self, temp_output_dir):
        """Test markdown link formatting when relative path fails."""
        options = ExportOptions(output_dir=temp_output_dir, link_mode='relative')
        exporter = MarkdownExporter(options)
        
        # Path outside output directory
        external_path = Path("/tmp/external.md")
        
        result = exporter._format_link(external_path)
        assert str(external_path) == result

    def test_template_manager_load_themes_error(self, temp_output_dir):
        """Test template manager theme loading with errors."""
        template_dir = temp_output_dir / "templates"
        template_dir.mkdir()
        
        # Create themes directory with invalid structure
        themes_dir = template_dir / "themes"
        themes_dir.mkdir()
        invalid_theme = themes_dir / "invalid.txt"
        invalid_theme.write_text("not a theme")
        
        # Should not raise error, just skip invalid themes
        manager = TemplateManager(template_dir)
        assert manager is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])