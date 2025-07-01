"""Data models for the exporter module."""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Set

from pydantic import BaseModel, Field

from ..generator.models import ProofSketch


class ExportFormat(str, Enum):
    """Supported export formats."""

    HTML = "html"
    MARKDOWN = "markdown"
    PDF = "pdf"
    JUPYTER = "jupyter"
    ALL = "all"


class TemplateType(str, Enum):
    """Types of templates used in export."""

    THEOREM = "theorem"
    PROOF_STEP = "proof_step"
    ANIMATION = "animation"
    INDEX = "index"
    LAYOUT = "layout"


@dataclass
class ExportContext:
    """Context information for export operations."""

    # Export metadata
    format: ExportFormat
    output_dir: Path
    timestamp: datetime = field(default_factory=datetime.now)

    # Content
    sketches: List[ProofSketch] = field(default_factory=list)
    animations: Dict[str, Path] = field(default_factory=dict)

    # Options
    include_animations: bool = True
    include_index: bool = True
    include_timestamps: bool = True
    create_subdirs: bool = True

    # Cross-references
    theorem_links: Dict[str, str] = field(default_factory=dict)
    dependency_graph: Dict[str, Set[str]] = field(default_factory=dict)

    # Custom metadata
    project_name: str = "Proof Sketcher Output"
    author: Optional[str] = None
    version: Optional[str] = None
    custom_metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class ExportResult:
    """Result of an export operation."""

    success: bool
    format: ExportFormat
    output_path: Path
    files_created: List[Path] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    errors: List[str] = field(default_factory=list)
    export_time: float = 0.0

    @property
    def main_file(self) -> Optional[Path]:
        """Get the main output file."""
        if self.files_created:
            # Return index file if available
            for file in self.files_created:
                if "index" in file.name:
                    return file
            # Otherwise return first file
            return self.files_created[0]
        return None


class TemplateContext(BaseModel):
    """Context data passed to templates."""

    # Core content
    theorem_name: str = Field(..., description="Theorem name")
    theorem_statement: str = Field(..., description="Theorem statement")
    explanation: str = Field(..., description="Natural language explanation")
    proof_steps: List[Dict[str, Any]] = Field(default_factory=list)

    # Optional content
    key_insights: List[str] = Field(default_factory=list)
    prerequisites: List[str] = Field(default_factory=list)
    visualization_hints: List[str] = Field(default_factory=list)

    # Media
    animation_path: Optional[str] = Field(None, description="Path to animation file")
    animation_thumbnail: Optional[str] = Field(None, description="Path to thumbnail")

    # Metadata
    timestamp: Optional[str] = Field(None, description="Generation timestamp")
    source_file: Optional[str] = Field(None, description="Source Lean file")
    dependencies: List[str] = Field(default_factory=list)

    # Navigation
    prev_theorem: Optional[Dict[str, str]] = Field(None)
    next_theorem: Optional[Dict[str, str]] = Field(None)
    index_url: Optional[str] = Field(None)

    # Formatting options
    syntax_theme: str = Field("monokai", description="Code syntax theme")
    math_renderer: str = Field("katex", description="Math rendering engine")

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True


class ExportOptions(BaseModel):
    """Options for export operations."""

    # Output control
    output_dir: Path = Field(Path("output"), description="Output directory")
    filename_pattern: str = Field(
        "{theorem_name}", description="Output filename pattern"
    )
    create_index: bool = Field(True, description="Create index file")
    create_subdirs: bool = Field(True, description="Create subdirectories for assets")

    # Content options
    include_source: bool = Field(True, description="Include source code")
    include_dependencies: bool = Field(True, description="Include dependency info")
    include_animations: bool = Field(
        True, description="Include animations if available"
    )
    embed_media: bool = Field(True, description="Embed media vs. link")
    include_timestamps: bool = Field(True, description="Include generation timestamps")

    # Formatting
    line_numbers: bool = Field(True, description="Show line numbers in code")
    syntax_highlighting: bool = Field(True, description="Enable syntax highlighting")
    collapsible_sections: bool = Field(True, description="Make sections collapsible")

    # Cross-references
    generate_links: bool = Field(True, description="Generate cross-reference links")
    link_mathlib: bool = Field(True, description="Link to mathlib documentation")

    # Performance
    parallel_export: bool = Field(True, description="Use parallel processing")
    compress_output: bool = Field(False, description="Compress output files")

    # Format-specific settings
    # HTML settings
    html_theme: str = Field("doc-gen4", description="HTML theme")
    html_syntax_style: str = Field(
        "monokai", description="Code syntax highlighting style"
    )
    html_embed_videos: bool = Field(True, description="Embed videos in HTML")

    # Markdown settings
    markdown_flavor: str = Field("github", description="Markdown flavor")
    markdown_math_style: str = Field("katex", description="Math rendering style")
    markdown_collapsible_proofs: bool = Field(
        True, description="Make proofs collapsible"
    )

    # PDF settings
    pdf_engine: str = Field("pdflatex", description="LaTeX engine")
    pdf_document_class: str = Field("article", description="LaTeX document class")
    pdf_font_size: int = Field(11, description="Base font size")

    # Jupyter settings
    jupyter_kernel: str = Field("python3", description="Jupyter kernel")
    jupyter_include_outputs: bool = Field(False, description="Include cell outputs")

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True


class BaseExporter(ABC):
    """Abstract base class for all exporters."""

    def __init__(self, options: Optional[ExportOptions] = None):
        """Initialize exporter with options.

        Args:
            options: Export options
        """
        self.options = options or ExportOptions()
        self._ensure_output_dir()

    @property
    @abstractmethod
    def format(self) -> ExportFormat:
        """Get the export format."""
        pass

    @abstractmethod
    def export_single(
        self, sketch: ProofSketch, context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export a single proof sketch.

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            Export result
        """
        pass

    @abstractmethod
    def export_multiple(
        self, sketches: List[ProofSketch], context: Optional[ExportContext] = None
    ) -> ExportResult:
        """Export multiple proof sketches.

        Args:
            sketches: List of proof sketches
            context: Export context

        Returns:
            Export result
        """
        pass

    def _ensure_output_dir(self) -> None:
        """Ensure output directory exists."""
        self.options.output_dir.mkdir(parents=True, exist_ok=True)

    def _generate_filename(self, name: str, extension: str) -> Path:
        """Generate output filename.

        Args:
            name: Base name (e.g., theorem name)
            extension: File extension

        Returns:
            Full path to output file
        """
        filename = self.options.filename_pattern.format(theorem_name=name)
        # Sanitize filename
        filename = "".join(c for c in filename if c.isalnum() or c in "._-")
        return self.options.output_dir / f"{filename}.{extension}"

    def _create_context(
        self, sketch: ProofSketch, animation_path: Optional[Path] = None
    ) -> TemplateContext:
        """Create template context from proof sketch.

        Args:
            sketch: Proof sketch
            animation_path: Optional animation file path

        Returns:
            Template context
        """
        return TemplateContext(
            theorem_name=sketch.theorem_name,
            theorem_statement="",  # ProofSketch doesn't have theorem_statement
            explanation=sketch.introduction,  # Use introduction instead
            proof_steps=[
                {
                    "description": step.description,
                    "mathematical_content": step.mathematical_content,
                    "reasoning": step.intuition
                    or "",  # Use intuition instead of reasoning
                    "prerequisites": [],  # ProofStep doesn't have prerequisites
                }
                for step in sketch.key_steps  # Use key_steps instead of steps
            ],
            key_insights=[],  # ProofSketch doesn't have key_insights
            visualization_hints=[],  # ProofSketch doesn't have visualization_hints
            animation_path=str(animation_path) if animation_path else None,
            timestamp=(
                datetime.now().isoformat()
                if hasattr(self.options, "include_timestamps")
                and self.options.include_timestamps
                else None
            ),
        )
