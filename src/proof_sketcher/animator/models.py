"""Models for animation system."""

import hashlib
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union

from pydantic import BaseModel, Field, field_validator


class AnimationQuality(str, Enum):
    """Animation quality presets."""

    LOW = "low"  # 480p, 15fps - for previews
    MEDIUM = "medium"  # 720p, 30fps - default
    HIGH = "high"  # 1080p, 60fps - for publication
    ULTRA = "ultra"  # 4K, 60fps - for demos


class AnimationStyle(str, Enum):
    """Animation visual style presets."""

    MODERN = "modern"  # Clean, minimal design
    CLASSIC = "classic"  # Traditional mathematical style
    ACCESSIBLE = "accessible"  # High contrast, large fonts
    DARK = "dark"  # Dark mode theme


class TransformationType(str, Enum):
    """Types of mathematical transformations for animation."""

    SUBSTITUTION = "substitution"  # Replace part of expression
    SIMPLIFICATION = "simplification"  # Simplify expression
    REWRITE = "rewrite"  # Apply rewrite rule
    EXPANSION = "expansion"  # Expand expression
    FACTORIZATION = "factorization"  # Factor expression
    EQUALITY_CHAIN = "equality_chain"  # Chain of equalities
    CASE_SPLIT = "case_split"  # Split into cases
    INDUCTION_STEP = "induction_step"  # Induction reasoning


class AnimationConfig(BaseModel):
    """Configuration for animation generation."""

    # Video settings
    quality: AnimationQuality = Field(
        AnimationQuality.MEDIUM, description="Video quality"
    )
    fps: int = Field(30, ge=15, le=120, description="Frames per second")
    width: int = Field(1280, ge=480, description="Video width in pixels")
    height: int = Field(720, ge=270, description="Video height in pixels")

    # Style settings
    style: AnimationStyle = Field(AnimationStyle.MODERN, description="Visual style")
    background_color: str = Field("#FFFFFF", description="Background color (hex)")
    text_color: str = Field("#000000", description="Text color (hex)")
    accent_color: str = Field("#3498DB", description="Accent color (hex)")

    # Font settings
    math_font: str = Field("Computer Modern", description="LaTeX font for math")
    text_font: str = Field("Arial", description="Font for text")
    font_size: int = Field(36, ge=12, le=72, description="Base font size")

    # Timing settings
    base_duration: float = Field(30.0, ge=10.0, description="Base duration in seconds")
    step_duration: float = Field(15.0, ge=5.0, description="Duration per proof step")
    max_duration: float = Field(
        720.0, ge=60.0, description="Maximum duration (12 minutes)"
    )
    transition_time: float = Field(
        1.5, ge=0.5, le=5.0, description="Transition duration"
    )
    pause_time: float = Field(2.0, ge=0.5, le=10.0, description="Pause between steps")

    # Animation behavior
    show_step_numbers: bool = Field(True, description="Show step numbers")
    highlight_changes: bool = Field(True, description="Highlight transformations")
    include_narration: bool = Field(False, description="Include text narration")
    chapter_markers: bool = Field(
        True, description="Add chapter markers for long videos"
    )
    
    # Resource limits for production
    max_memory_mb: int = Field(1024, ge=128, description="Maximum memory usage in MB")
    max_processing_time: int = Field(300, ge=60, description="Maximum processing time in seconds")

    @field_validator("background_color", "text_color", "accent_color")
    @classmethod
    def validate_hex_color(cls, v: str) -> str:
        """Validate hex color format."""
        if not v.startswith("#") or len(v) != 7:
            raise ValueError("Color must be in #RRGGBB format")
        try:
            int(v[1:], 16)
        except ValueError:
            raise ValueError("Invalid hex color") from None
        return v

    @classmethod
    def preview(cls) -> "AnimationConfig":
        """Create config optimized for previews."""
        return cls.model_validate({
            "quality": AnimationQuality.LOW,
            "fps": 15,
            "width": 640,
            "height": 360,
            "base_duration": 15.0,
            "step_duration": 8.0,
            "max_duration": 120.0,
        })

    @classmethod
    def publication(cls) -> "AnimationConfig":
        """Create config optimized for publication."""
        return cls.model_validate({
            "quality": AnimationQuality.HIGH,
            "fps": 60,
            "width": 1920,
            "height": 1080,
            "base_duration": 45.0,
            "step_duration": 20.0,
            "max_duration": 900.0,
        })

    @classmethod
    def accessible(cls) -> "AnimationConfig":
        """Create config optimized for accessibility."""
        return cls.model_validate({
            "style": AnimationStyle.ACCESSIBLE,
            "background_color": "#000000",
            "text_color": "#FFFFFF",
            "accent_color": "#FFFF00",
            "font_size": 48,
            "transition_time": 3.0,
            "pause_time": 4.0,
        })


class FormulaComponent(BaseModel):
    """A component of a mathematical formula."""

    latex: str = Field(..., description="LaTeX representation")
    position: Tuple[float, float] = Field((0.0, 0.0), description="Position on screen")
    highlight: bool = Field(False, description="Whether to highlight this component")
    color: Optional[str] = Field(None, description="Custom color for this component")

    class Config:
        """Pydantic configuration."""

        str_strip_whitespace = True


class AnimationScene(BaseModel):
    """Description of a single animation scene."""

    scene_id: str = Field(..., description="Unique scene identifier")
    title: str = Field(..., description="Scene title")
    duration: float = Field(..., ge=1.0, description="Scene duration in seconds")

    # Mathematical content
    initial_formula: str = Field(..., description="Starting formula (LaTeX)")
    final_formula: str = Field(..., description="Ending formula (LaTeX)")
    intermediate_formulas: List[str] = Field(
        default_factory=list, description="Intermediate steps"
    )

    # Animation details
    transformation_type: TransformationType = Field(
        ..., description="Type of transformation"
    )
    highlighted_parts: List[str] = Field(
        default_factory=list, description="Parts to highlight"
    )
    narration_text: Optional[str] = Field(None, description="Narration for this scene")

    # Timing
    fade_in_time: float = Field(1.0, description="Fade in duration")
    fade_out_time: float = Field(1.0, description="Fade out duration")
    pause_before: float = Field(0.0, description="Pause before scene")
    pause_after: float = Field(2.0, description="Pause after scene")

    class Config:
        """Pydantic configuration."""

        str_strip_whitespace = True


class AnimationSegment(BaseModel):
    """A segment of a longer animation (for chapter support)."""

    segment_id: str = Field(..., description="Unique segment identifier")
    title: str = Field(..., description="Segment title")
    scenes: List[AnimationScene] = Field(..., description="Scenes in this segment")
    total_duration: float = Field(0.0, description="Total segment duration")

    def calculate_duration(self) -> float:
        """Calculate total duration of all scenes."""
        total = sum(scene.duration for scene in self.scenes)
        self.total_duration = total
        return total

    @property
    def scene_count(self) -> int:
        """Get number of scenes in segment."""
        return len(self.scenes)

    class Config:
        """Pydantic configuration."""

        str_strip_whitespace = True


class AnimationRequest(BaseModel):
    """Request for animation generation."""

    # Identification
    theorem_name: str = Field(..., description="Name of theorem being animated")
    request_id: str = Field(..., description="Unique request identifier")

    # Content
    segments: List[AnimationSegment] = Field(..., description="Animation segments")
    config: AnimationConfig = Field(
        default_factory=lambda: AnimationConfig.model_validate({}), description="Animation configuration"
    )

    # Metadata
    created_at: datetime = Field(
        default_factory=datetime.now, description="Request creation time"
    )
    estimated_duration: float = Field(0.0, description="Estimated total duration")

    def calculate_estimated_duration(self) -> float:
        """Calculate estimated total duration."""
        total = sum(segment.calculate_duration() for segment in self.segments)

        # Add time for segment transitions
        if len(self.segments) > 1:
            total += (len(self.segments) - 1) * 3.0  # 3 seconds between segments

        self.estimated_duration = min(total, self.config.max_duration)
        return self.estimated_duration

    def get_cache_key(self) -> str:
        """Generate cache key for this request."""
        content = f"{self.theorem_name}:{len(self.segments)}:{self.estimated_duration}"

        # Include key config elements
        config_content = f"{self.config.quality.value}:{self.config.style.value}:{self.config.width}x{self.config.height}"
        content += f":{config_content}"

        # Include scene content hash
        scene_content = ""
        for segment in self.segments:
            for scene in segment.scenes:
                scene_content += f"{scene.initial_formula}→{scene.final_formula}"

        if scene_content:
            scene_hash = hashlib.md5(scene_content.encode(), usedforsecurity=False).hexdigest()[:8]
            content += f":{scene_hash}"

        return hashlib.sha256(content.encode()).hexdigest()

    @property
    def total_scenes(self) -> int:
        """Get total number of scenes across all segments."""
        return sum(segment.scene_count for segment in self.segments)

    @property
    def needs_segmentation(self) -> bool:
        """Check if animation needs to be segmented due to length."""
        return self.estimated_duration > self.config.max_duration * 0.8

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True
        json_encoders = {datetime: lambda dt: dt.isoformat()}


class AnimationResponse(BaseModel):
    """Response from animation generation."""

    # Output files
    video_path: Optional[Path] = Field(None, description="Path to generated video")
    thumbnail_path: Optional[Path] = Field(None, description="Path to thumbnail image")
    preview_image_path: Optional[Path] = Field(
        None, description="Path to preview image"
    )
    segments_paths: List[Path] = Field(
        default_factory=list, description="Paths to segment videos"
    )

    # Basic metadata
    duration: float = Field(0.0, description="Animation duration in seconds")
    frame_count: int = Field(0, description="Number of frames in animation")
    size_bytes: int = Field(0, description="File size in bytes")
    
    # Extended metadata
    actual_duration: Optional[float] = Field(None, description="Actual video duration")
    file_size_mb: Optional[float] = Field(None, description="Video file size in MB")
    generation_time_ms: Optional[float] = Field(
        None, description="Generation time in milliseconds"
    )

    # Status
    success: bool = Field(True, description="Whether generation was successful")
    error_message: Optional[str] = Field(
        None, description="Error message if generation failed"
    )
    warnings: List[str] = Field(default_factory=list, description="Generation warnings")
    cached: bool = Field(
        False, description="Whether the result was retrieved from cache"
    )
    
    # Additional metadata
    metadata: Dict[str, Any] = Field(default_factory=dict, description="Additional metadata")

    # Additional outputs
    chapter_markers: List[Tuple[float, str]] = Field(
        default_factory=list, description="Chapter markers (time, title)"
    )
    generated_at: datetime = Field(
        default_factory=datetime.now, description="Generation timestamp"
    )

    @property
    def has_video(self) -> bool:
        """Check if video was successfully generated."""
        return self.video_path is not None and self.video_path.exists()

    @property
    def has_preview(self) -> bool:
        """Check if preview image was generated."""
        return self.preview_image_path is not None and self.preview_image_path.exists()

    @property
    def has_segments(self) -> bool:
        """Check if segmented videos were generated."""
        return len(self.segments_paths) > 0 and all(
            p.exists() for p in self.segments_paths
        )

    def get_playback_info(self) -> Dict[str, Union[str, float, List[Dict[str, Any]]]]:
        """Get information for video playback."""
        info = {
            "video_path": str(self.video_path) if self.video_path else None,
            "duration": self.actual_duration or self.duration,
            "file_size_mb": self.file_size_mb,
            "quality": self.metadata.get("quality", "medium"),
            "style": self.metadata.get("style", "modern"),
        }

        if self.chapter_markers:
            info["chapters"] = [
                {"time": time, "title": title} for time, title in self.chapter_markers
            ]

        if self.segments_paths:
            info["segments"] = [
                {"path": str(path), "index": i}
                for i, path in enumerate(self.segments_paths)
            ]

        return info

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True
        json_encoders = {datetime: lambda dt: dt.isoformat(), Path: lambda p: str(p)}


class ManimConfig(BaseModel):
    """Configuration for Manim MCP server."""

    # Server settings
    server_host: str = Field("localhost", description="MCP server host")
    server_port: int = Field(8000, ge=1024, le=65535, description="MCP server port")
    server_timeout: float = Field(
        300.0, ge=30.0, description="Server timeout in seconds"
    )

    # Connection settings
    max_connections: int = Field(
        5, ge=1, le=20, description="Maximum concurrent connections"
    )
    connection_timeout: float = Field(30.0, ge=5.0, description="Connection timeout")
    retry_attempts: int = Field(3, ge=1, le=10, description="Number of retry attempts")
    retry_delay: float = Field(2.0, ge=0.5, description="Delay between retries")

    # Server lifecycle
    auto_start: bool = Field(
        True, description="Automatically start server if not running"
    )
    auto_restart: bool = Field(
        True, description="Automatically restart server on failure"
    )
    health_check_interval: float = Field(
        30.0, ge=10.0, description="Health check interval"
    )

    # Manim settings
    manim_executable: str = Field("manim", description="Path to Manim executable")
    output_dir: Optional[Path] = Field(None, description="Output directory for videos")
    temp_dir: Optional[Path] = Field(
        None, description="Temporary directory for processing"
    )
    keep_temp_files: bool = Field(
        False, description="Keep temporary files for debugging"
    )

    # Performance
    max_concurrent_renders: int = Field(
        2, ge=1, le=8, description="Maximum concurrent renders"
    )
    render_timeout: float = Field(
        600.0, ge=60.0, description="Render timeout per scene"
    )
    memory_limit_mb: int = Field(2048, ge=512, description="Memory limit for renders")

    def get_server_url(self) -> str:
        """Get full server URL."""
        return f"http://{self.server_host}:{self.server_port}"

    @classmethod
    def development(cls) -> "ManimConfig":
        """Create config for development."""
        return cls.model_validate({
            "server_timeout": 60.0,
            "max_concurrent_renders": 1,
            "render_timeout": 120.0,
            "keep_temp_files": True,
        })

    @classmethod
    def production(cls) -> "ManimConfig":
        """Create config for production."""
        return cls.model_validate({
            "server_timeout": 600.0,
            "max_concurrent_renders": 4,
            "render_timeout": 1200.0,
            "memory_limit_mb": 4096,
            "health_check_interval": 60.0,
        })

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True


# Exception classes are imported from core.exceptions
