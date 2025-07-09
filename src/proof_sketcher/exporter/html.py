"""HTML exporter for generating web documentation."""

import gzip
import hashlib
import json
import logging
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional

from ..generator.models import ProofSketch
from .base import BaseExporterImpl
from .models import (
    ExportContext,
    ExportFormat,
    ExportOptions,
    ExportResult,
    TemplateType,
)
from .template_manager import TemplateManager


class HTMLExporter(BaseExporterImpl):
    """Exporter for HTML format with doc-gen4 compatibility.

    Features:
    - Full doc-gen4 CSS class compatibility
    - Responsive video embedding with fallbacks
    - Asset optimization (minification, compression)
    - Multiple source format support
    - Cross-reference support
    """

    def __init__(
        self,
        options: Optional[ExportOptions] = None,
        template_manager: Optional[TemplateManager] = None,
    ):
        """Initialize HTML exporter.

        Args:
            options: Export options
            template_manager: Template manager
        """
        super().__init__(ExportFormat.HTML, options, template_manager)
        self.logger = logging.getLogger(__name__)

        # Asset optimization settings
        self._minify_assets = getattr(options, "minify_assets", True)
        self._compress_assets = getattr(options, "compress_assets", True)
        self._generate_poster_frames = getattr(options, "generate_poster_frames", True)

        # Doc-gen4 compatibility
        self._doc_gen4_classes = {
            "theorem": "decl",
            "proo": "proo",
            "step": "step",
            "formula": "expr",
            "navigation": "nav",
            "toc": "toc",
            "code": "code",
            "math": "math-display",
        }

    def _export_sketch(self, sketch: ProofSketch, context: ExportContext) -> List[Path]:
        """Export a single proof sketch to HTML.

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            List of created files
        """
        created_files = []

        # Generate output filename
        output_file = self._generate_filename(sketch.theorem_name, "html")

        # Create template context with HTML-specific additions
        template_context = self._create_template_context_html(sketch, context)

        # Check for animation with responsive embedding
        if context.include_animations and sketch.theorem_name in context.animations:
            animation_path = context.animations[sketch.theorem_name]

            # Copy animation to output directory with responsive support
            if animation_path.exists():
                animation_assets = self._copy_animation_responsive(
                    animation_path, sketch.theorem_name
                )
                template_context["animation_assets"] = animation_assets
                created_files.extend(
                    [asset["path"] for asset in animation_assets.values()]
                )

        # Render theorem template
        html_content = self.template_manager.render_template(
            ExportFormat.HTML, TemplateType.THEOREM, template_context
        )

        # Write output file
        output_file.write_text(html_content, encoding="utf-8")
        created_files.append(output_file)

        self.logger.info(f"Exported {sketch.theorem_name} to {output_file}")

        return created_files

    def _create_index(
        self, sketches: List[ProofSketch], context: ExportContext
    ) -> Optional[Path]:
        """Create an index HTML file.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Path to index file
        """
        index_file = self.options.output_dir / "index.html"

        # Prepare theorem list for index
        theorem_list = []
        for sketch in sketches:
            theorem_data = {
                "name": sketch.theorem_name,
                "statement": getattr(sketch, "theorem_statement", ""),
                "url": context.theorem_links.get(sketch.theorem_name, "#"),
                "summary": (
                    sketch.introduction[:200] + "..."
                    if len(sketch.introduction) > 200
                    else sketch.introduction
                ),
                "step_count": len(sketch.key_steps),
                "has_animation": sketch.theorem_name in context.animations,
            }
            theorem_list.append(theorem_data)

        # Sort by name
        theorem_list.sort(key=lambda x: x["name"])

        # Create index context
        index_context = {
            "project_name": context.project_name,
            "theorem_count": len(sketches),
            "theorems": theorem_list,
            "timestamp": (
                context.timestamp.isoformat() if context.include_timestamps else None
            ),
            "has_animations": bool(context.animations),
            "author": context.author,
            "version": context.version,
        }

        # Render index template
        index_html = self.template_manager.render_template(
            ExportFormat.HTML, TemplateType.INDEX, index_context
        )

        # Write index file
        index_file.write_text(index_html, encoding="utf-8")

        self.logger.info(f"Created index at {index_file}")

        return index_file

    def export_multiple(
        self, sketches: List[ProofSketch], context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export multiple sketches with additional HTML features.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Export result
        """
        # Call parent implementation
        result = super().export_multiple(sketches, context)

        # Copy static assets
        if result.success and self.options.create_subdirs:
            try:
                asset_files = self._copy_assets()
                result.files_created.extend(asset_files)
            except Exception as e:
                result.warnings.append(f"Failed to copy assets: {e}")

        # Generate search index
        if result.success and len(sketches) > 5:
            try:
                search_file = self._generate_search_index(sketches)
                if search_file:
                    result.files_created.append(search_file)
            except Exception as e:
                result.warnings.append(f"Failed to generate search index: {e}")

        return result

    def _create_template_context_html(
        self, sketch: ProofSketch, context: ExportContext
    ) -> dict:
        """Create template context with HTML-specific additions.

        Args:
            sketch: Proof sketch
            context: Export context

        Returns:
            Template context dictionary
        """
        # Get base context from parent
        base_context = super()._create_template_context(sketch, context)

        # Add HTML-specific fields with doc-gen4 compatibility
        base_context["syntax_theme"] = (
            self.options.syntax_highlighting and "monokai" or "none"
        )
        base_context["math_renderer"] = "katex"  # or "mathjax"
        base_context["doc_gen4_classes"] = self._doc_gen4_classes
        base_context["responsive_design"] = True
        base_context["asset_hashes"] = self._get_asset_hashes()

        # Add navigation
        all_names = [s.theorem_name for s in context.sketches]
        current_index = (
            all_names.index(sketch.theorem_name)
            if sketch.theorem_name in all_names
            else -1
        )

        if current_index > 0:
            prev_sketch = context.sketches[current_index - 1]
            base_context["prev_theorem"] = {
                "name": prev_sketch.theorem_name,
                "url": context.theorem_links.get(prev_sketch.theorem_name),
            }

        if 0 <= current_index < len(all_names) - 1:
            next_sketch = context.sketches[current_index + 1]
            base_context["next_theorem"] = {
                "name": next_sketch.theorem_name,
                "url": context.theorem_links.get(next_sketch.theorem_name),
            }

        base_context["index_url"] = "index.html"

        # Add dependencies with cross-references
        if self.options.generate_links:
            # ProofSketch doesn't have dependencies attribute
            base_context["dependencies"] = []
            base_context["cross_references"] = self._generate_cross_references(
                sketch, context
            )

        return base_context

    def _copy_animation(self, source: Path, theorem_name: str) -> Path:
        """Copy animation file to output directory.

        Args:
            source: Source animation file
            theorem_name: Theorem name for naming

        Returns:
            Destination path
        """
        animations_dir = self.options.output_dir / "animations"
        animations_dir.mkdir(exist_ok=True)

        # Generate unique filename
        extension = source.suffix
        dest_filename = f"{self._sanitize_filename(theorem_name)}_animation{extension}"
        dest_path = animations_dir / dest_filename

        # Copy file
        shutil.copy2(source, dest_path)

        return dest_path

    def _copy_animation_responsive(
        self, source: Path, theorem_name: str
    ) -> Dict[str, Dict]:
        """Copy animation with responsive embedding support.

        Creates multiple formats and poster frames for responsive design.

        Args:
            source: Source animation file
            theorem_name: Theorem name for naming

        Returns:
            Dictionary of animation assets by type
        """
        animations_dir = self.options.output_dir / "animations"
        animations_dir.mkdir(exist_ok=True)

        sanitized_name = self._sanitize_filename(theorem_name)
        assets = {}

        # Copy original video
        original_dest = animations_dir / f"{sanitized_name}_animation{source.suffix}"
        shutil.copy2(source, original_dest)

        assets["video"] = {
            "path": original_dest,
            "url": f"animations/{original_dest.name}",
            "type": "video/mp4" if source.suffix.lower() == ".mp4" else "video/webm",
            "size": original_dest.stat().st_size,
        }

        # Generate poster frame if enabled
        if self._generate_poster_frames:
            poster_path = self._generate_poster_frame(
                source, sanitized_name, animations_dir
            )
            if poster_path:
                assets["poster"] = {
                    "path": poster_path,
                    "url": f"animations/{poster_path.name}",
                    "type": "image/jpeg",
                    "size": poster_path.stat().st_size,
                }

        # Generate fallback formats if needed
        if source.suffix.lower() == ".mp4":
            webm_path = self._convert_to_webm(source, sanitized_name, animations_dir)
            if webm_path:
                assets["webm"] = {
                    "path": webm_path,
                    "url": f"animations/{webm_path.name}",
                    "type": "video/webm",
                    "size": webm_path.stat().st_size,
                }

        # Generate animated GIF fallback
        gif_path = self._convert_to_gif(source, sanitized_name, animations_dir)
        if gif_path:
            assets["gif"] = {
                "path": gif_path,
                "url": f"animations/{gif_path.name}",
                "type": "image/gi",
                "size": gif_path.stat().st_size,
            }

        return assets

    def _generate_poster_frame(
        self, video_path: Path, name: str, output_dir: Path
    ) -> Optional[Path]:
        """Generate poster frame from video.

        Args:
            video_path: Path to video file
            name: Base name for poster
            output_dir: Output directory

        Returns:
            Path to poster image or None if failed
        """
        try:
            poster_path = output_dir / f"{name}_poster.jpg"

            # Use ffmpeg to extract frame at 1 second
            cmd = [
                "ffmpeg",
                "-i",
                str(video_path),
                "-ss",
                "00:00:01",
                "-vframes",
                "1",
                "-q:v",
                "2",
                str(poster_path),
                "-y",
            ]

            result = subprocess.run(cmd, capture_output=True, text=True)
            if result.returncode == 0 and poster_path.exists():
                self.logger.debug(f"Generated poster frame: {poster_path}")
                return poster_path
            else:
                self.logger.warning(f"Failed to generate poster frame: {result.stderr}")

        except (subprocess.SubprocessError, FileNotFoundError) as e:
            self.logger.warning(f"ffmpeg not available for poster generation: {e}")

        return None

    def _convert_to_webm(
        self, source: Path, name: str, output_dir: Path
    ) -> Optional[Path]:
        """Convert video to WebM format.

        Args:
            source: Source video file
            name: Base name
            output_dir: Output directory

        Returns:
            Path to WebM file or None if failed
        """
        try:
            webm_path = output_dir / f"{name}_animation.webm"

            cmd = [
                "ffmpeg",
                "-i",
                str(source),
                "-c:v",
                "libvpx-vp9",
                "-cr",
                "30",
                "-b:v",
                "0",
                "-c:a",
                "libopus",
                str(webm_path),
                "-y",
            ]

            result = subprocess.run(cmd, capture_output=True, text=True)
            if result.returncode == 0 and webm_path.exists():
                self.logger.debug(f"Generated WebM: {webm_path}")
                return webm_path

        except (subprocess.SubprocessError, FileNotFoundError):
            self.logger.debug("ffmpeg not available for WebM conversion")

        return None

    def _convert_to_gif(
        self, source: Path, name: str, output_dir: Path
    ) -> Optional[Path]:
        """Convert video to animated GIF.

        Args:
            source: Source video file
            name: Base name
            output_dir: Output directory

        Returns:
            Path to GIF file or None if failed
        """
        try:
            gif_path = output_dir / f"{name}_animation.gif"

            # Generate optimized GIF with palette
            cmd = [
                "ffmpeg",
                "-i",
                str(source),
                "-v",
                "fps=10,scale=640:-1:flags=lanczos,palettegen=stats_mode=dif",
                "-t",
                "10",  # Limit to 10 seconds
                str(gif_path),
                "-y",
            ]

            result = subprocess.run(cmd, capture_output=True, text=True)
            if result.returncode == 0 and gif_path.exists():
                self.logger.debug(f"Generated GIF: {gif_path}")
                return gif_path

        except (subprocess.SubprocessError, FileNotFoundError):
            self.logger.debug("ffmpeg not available for GIF conversion")

        return None

    def _generate_cross_references(
        self, sketch: ProofSketch, context: ExportContext
    ) -> List[Dict]:
        """Generate cross-references for doc-gen4 compatibility.

        Args:
            sketch: Current proof sketch
            context: Export context

        Returns:
            List of cross-reference dictionaries
        """
        cross_refs = []

        # Find references in the proof text
        for other_sketch in context.sketches:
            if other_sketch.theorem_name != sketch.theorem_name:
                # Check if referenced in content
                if (
                    other_sketch.theorem_name.lower() in sketch.introduction.lower()
                    or any(
                        other_sketch.theorem_name.lower() in step.description.lower()
                        for step in sketch.key_steps
                    )
                ):
                    cross_refs.append(
                        {
                            "name": other_sketch.theorem_name,
                            "url": context.theorem_links.get(
                                other_sketch.theorem_name, "#"
                            ),
                            "type": "theorem",
                            "statement": getattr(other_sketch, "theorem_statement", ""),
                        }
                    )

        return cross_refs

    def _get_asset_hashes(self) -> Dict[str, str]:
        """Get hashes of static assets for cache busting.

        Returns:
            Dictionary mapping asset paths to hashes
        """
        hashes = {}
        asset_dir = self.template_manager.template_dir / "html" / "assets"

        if asset_dir.exists():
            for asset_file in asset_dir.rglob("*"):
                if asset_file.is_file():
                    try:
                        content = asset_file.read_bytes()
                        hash_value = hashlib.md5(
                            content, usedforsecurity=False
                        ).hexdigest()[:8]
                        rel_path = asset_file.relative_to(asset_dir)
                        hashes[str(rel_path)] = hash_value
                    except (OSError, IOError):
                        continue

        return hashes

    def _generate_search_index(self, sketches: List[ProofSketch]) -> Optional[Path]:
        """Generate search index for client-side search.

        Args:
            sketches: List of proof sketches

        Returns:
            Path to search index file
        """
        search_data = []

        for sketch in sketches:
            # Create search entry
            entry = {
                "id": sketch.theorem_name,
                "title": sketch.theorem_name,
                "statement": getattr(sketch, "theorem_statement", ""),
                "content": sketch.introduction,
                "url": self._get_output_url(sketch),
                "keywords": getattr(sketch, "key_insights", []),
            }

            # Add step descriptions to searchable content
            step_text = " ".join(step.description for step in sketch.key_steps)
            entry["content"] += " " + step_text

            search_data.append(entry)

        # Write search index
        search_file = self.options.output_dir / "search-index.json"
        search_file.write_text(
            json.dumps(search_data, indent=2, ensure_ascii=False), encoding="utf-8"
        )

        return search_file

    def _copy_assets(self) -> List[Path]:
        """Copy HTML-specific assets with optimization.

        Returns:
            List of copied files
        """
        copied = super()._copy_assets()

        # Copy and optimize additional HTML resources
        resources = [
            ("css/doc-gen4.css", "css/doc-gen4.css"),
            ("css/theorem.css", "css/theorem.css"),
            ("css/responsive.css", "css/responsive.css"),
            ("js/navigation.js", "js/navigation.js"),
            ("js/search.js", "js/search.js"),
            ("js/katex-auto-render.js", "js/katex-auto-render.js"),
            ("js/video-player.js", "js/video-player.js"),
            ("fonts/KaTeX_Main-Regular.woff2", "fonts/KaTeX_Main-Regular.woff2"),
        ]

        for src_rel, dst_rel in resources:
            src = self.template_manager.template_dir / "html" / "assets" / src_rel
            if src.exists():
                dst = self.options.output_dir / dst_rel
                dst.parent.mkdir(parents=True, exist_ok=True)

                # Optimize asset if enabled
                if self._minify_assets and (
                    dst_rel.endswith(".css") or dst_rel.endswith(".js")
                ):
                    self._copy_and_minify_asset(src, dst)
                else:
                    shutil.copy2(src, dst)

                # Compress asset if enabled
                if (
                    self._compress_assets and dst.stat().st_size > 1024
                ):  # Only compress files > 1KB
                    self._compress_asset(dst)

                copied.append(dst)

        return copied

    def _copy_and_minify_asset(self, src: Path, dst: Path) -> None:
        """Copy and minify CSS/JS asset.

        Args:
            src: Source file path
            dst: Destination file path
        """
        try:
            content = src.read_text(encoding="utf-8")

            if dst.suffix == ".css":
                minified = self._minify_css(content)
            elif dst.suffix == ".js":
                minified = self._minify_js(content)
            else:
                minified = content

            dst.write_text(minified, encoding="utf-8")
            self.logger.debug(
                f"Minified {
                    src.name}: {
                    len(content)} → {
                    len(minified)} chars"
            )

        except (UnicodeDecodeError, OSError) as e:
            self.logger.warning(f"Failed to minify {src}: {e}, copying as-is")
            shutil.copy2(src, dst)

    def _minify_css(self, content: str) -> str:
        """Basic CSS minification.

        Args:
            content: CSS content

        Returns:
            Minified CSS
        """
        import re

        # Remove comments
        content = re.sub(r"/\*.*?\*/", "", content, flags=re.DOTALL)

        # Remove extra whitespace
        content = re.sub(r"\s+", " ", content)
        content = re.sub(r"\s*([{}:;,>+~])\s*", r"\1", content)
        content = re.sub(r";\s*}", "}", content)

        return content.strip()

    def _minify_js(self, content: str) -> str:
        """Basic JavaScript minification.

        Args:
            content: JavaScript content

        Returns:
            Minified JavaScript
        """
        import re

        # Remove single-line comments (be careful with URLs)
        content = re.sub(r"//.*$", "", content, flags=re.MULTILINE)

        # Remove multi-line comments
        content = re.sub(r"/\*.*?\*/", "", content, flags=re.DOTALL)

        # Remove extra whitespace
        content = re.sub(r"\s+", " ", content)
        content = re.sub(r"\s*([{}:;,=()[\]+-/*])\s*", r"\1", content)

        return content.strip()

    def _compress_asset(self, file_path: Path) -> None:
        """Compress asset using gzip.

        Args:
            file_path: Path to file to compress
        """
        try:
            with open(file_path, "rb") as f_in:
                with gzip.open(f"{file_path}.gz", "wb") as f_out:
                    shutil.copyfileobj(f_in, f_out)

            # Only keep compressed version if it's significantly smaller
            original_size = file_path.stat().st_size
            compressed_size = Path(f"{file_path}.gz").stat().st_size

            if compressed_size < original_size * 0.8:  # 20% improvement threshold
                self.logger.debug(
                    f"Compressed {
                        file_path.name}: {original_size} → {compressed_size} bytes"
                )
            else:
                Path(f"{file_path}.gz").unlink()  # Remove if not beneficial

        except (OSError, IOError) as e:
            self.logger.warning(f"Failed to compress {file_path}: {e}")
