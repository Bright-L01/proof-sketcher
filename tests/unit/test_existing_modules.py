"""Unit tests for existing modules that we know exist."""

import json
import tempfile
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

# Import existing modules we know exist
from proof_sketcher.core.utils import (
    generate_cache_key,
    sanitize_filename,
    truncate_text,
    format_duration,
    flatten_dict,
    deep_merge,
    chunk_list,
    calculate_hash
)
from proof_sketcher.core.exceptions import (
    ProofSketcherError,
    ValidationError,
    InputValidationError,
    ProcessingError,
    ExportError,
    AnimationError,
    ConfigurationError,
    MemoryError
)
from proof_sketcher.core.interfaces import (
    Generator,
    Parser,
    Exporter,
    Animator,
    CacheInterface
)
from proof_sketcher.core.models import (
    ProcessingStats,
    CacheStats,
    GenerationContext,
    ExportContext
)
from proof_sketcher.parser.models import (
    TheoremInfo,
    ParseResult,
    ParseError
)
from proof_sketcher.generator.models import (
    ProofSketch,
    ProofStep,
    CacheEntry,
    GenerationRequest,
    GenerationResponse
)
from proof_sketcher.exporter.models import (
    ExportOptions,
    ExportResult,
    ExportFormat
)
from proof_sketcher.animator.models import (
    AnimationRequest,
    AnimationResponse,
    AnimationSegment,
    AnimationScene
)


class TestCoreUtils:
    """Test core utility functions."""
    
    def test_generate_cache_key(self):
        """Test cache key generation."""
        # Test basic functionality
        key1 = generate_cache_key("test", "data")
        key2 = generate_cache_key("test", "data")
        assert key1 == key2  # Should be deterministic
        assert len(key1) == 64  # SHA256 hex length
        
        # Test different inputs produce different keys
        key3 = generate_cache_key("different", "data")
        assert key1 != key3
        
        # Test with keyword arguments
        key4 = generate_cache_key(a="test", b="data")
        key5 = generate_cache_key(b="data", a="test")
        assert key4 == key5  # Order shouldn't matter for kwargs
    
    def test_sanitize_filename(self):
        """Test filename sanitization."""
        # Test basic sanitization
        result = sanitize_filename("test file.txt")
        assert result == "test_file.txt"
        
        # Test with invalid characters
        result = sanitize_filename("file<>:\"/\\|?*.txt")
        assert "<" not in result
        assert ">" not in result
        assert all(c not in result for c in '<>:"/\\|?*')
        
        # Test length limiting
        long_name = "a" * 300
        result = sanitize_filename(long_name)
        assert len(result) <= 255
        
        # Test empty input
        result = sanitize_filename("")
        assert len(result) > 0  # Should provide default
    
    def test_truncate_text(self):
        """Test text truncation."""
        # Test normal truncation
        text = "This is a long text that should be truncated"
        result = truncate_text(text, 20)
        assert len(result) <= 20
        assert result.endswith("...")
        
        # Test text shorter than limit
        short_text = "Short"
        result = truncate_text(short_text, 20)
        assert result == short_text
        
        # Test with zero length
        result = truncate_text("test", 0)
        assert result == ""
    
    def test_format_duration(self):
        """Test duration formatting."""
        # Test milliseconds
        result = format_duration(0.5)
        assert "500ms" in result or "0.5s" in result
        
        # Test seconds
        result = format_duration(5.5)
        assert "5.5s" in result or "5s" in result
        
        # Test minutes
        result = format_duration(125)
        assert "m" in result
        
        # Test hours
        result = format_duration(7200)
        assert "h" in result
    
    def test_flatten_dict(self):
        """Test dictionary flattening."""
        nested = {
            "a": 1,
            "b": {"c": 2, "d": {"e": 3}}
        }
        
        flattened = flatten_dict(nested)
        
        assert "a" in flattened
        assert "b.c" in flattened or "b_c" in flattened
        assert flattened["a"] == 1
        assert 2 in flattened.values()
        assert 3 in flattened.values()
    
    def test_deep_merge(self):
        """Test deep dictionary merging."""
        dict1 = {"a": 1, "b": {"c": 2}}
        dict2 = {"b": {"d": 3}, "e": 4}
        
        result = deep_merge(dict1, dict2)
        
        assert result["a"] == 1
        assert result["e"] == 4
        assert "c" in result["b"]
        assert "d" in result["b"]
    
    def test_chunk_list(self):
        """Test list chunking."""
        data = list(range(10))
        
        # Test normal chunking
        chunks = chunk_list(data, 3)
        assert len(chunks) == 4  # 3, 3, 3, 1
        assert chunks[0] == [0, 1, 2]
        assert chunks[-1] == [9]
        
        # Test chunk size larger than list
        chunks = chunk_list(data, 20)
        assert len(chunks) == 1
        assert chunks[0] == data
        
        # Test empty list
        chunks = chunk_list([], 3)
        assert len(chunks) == 0
    
    def test_calculate_hash(self):
        """Test hash calculation."""
        data = b"test data"
        
        hash1 = calculate_hash(data)
        hash2 = calculate_hash(data)
        
        assert hash1 == hash2  # Deterministic
        assert len(hash1) == 64  # SHA256 hex
        assert all(c in "0123456789abcdef" for c in hash1)
        
        # Different data should produce different hash
        hash3 = calculate_hash(b"different data")
        assert hash1 != hash3


class TestCoreExceptions:
    """Test core exception classes."""
    
    def test_proof_sketcher_error(self):
        """Test base ProofSketcherError."""
        error = ProofSketcherError("Test message", error_code="TEST_001")
        
        assert str(error) == "Test message"
        assert error.error_code == "TEST_001"
        assert error.details == {}
        
        # Test with details
        error_with_details = ProofSketcherError(
            "Test with details",
            details={"file": "test.lean", "line": 10},
            error_code="TEST_002"
        )
        
        assert error_with_details.details["file"] == "test.lean"
        assert error_with_details.details["line"] == 10
    
    def test_validation_error(self):
        """Test ValidationError."""
        error = ValidationError("Invalid input", field="theorem_name")
        
        assert isinstance(error, ProofSketcherError)
        assert "Invalid input" in str(error)
        assert error.field == "theorem_name"
    
    def test_processing_error(self):
        """Test ProcessingError."""
        error = ProcessingError("Processing failed", stage="generation")
        
        assert isinstance(error, ProofSketcherError)
        assert error.stage == "generation"
    
    def test_export_error(self):
        """Test ExportError."""
        error = ExportError("Export failed", format="HTML")
        
        assert isinstance(error, ProofSketcherError)
        assert error.format == "HTML"
    
    def test_animation_error(self):
        """Test AnimationError."""
        error = AnimationError("Animation failed", scene_type="proof_step")
        
        assert isinstance(error, ProofSketcherError)
        assert error.scene_type == "proof_step"
    
    def test_configuration_error(self):
        """Test ConfigurationError."""
        error = ConfigurationError("Invalid config", config_key="generation.model")
        
        assert isinstance(error, ProofSketcherError)
        assert error.config_key == "generation.model"


class TestCoreModels:
    """Test core model classes."""
    
    def test_processing_stats(self):
        """Test ProcessingStats model."""
        stats = ProcessingStats(
            files_processed=10,
            theorems_found=25,
            sketches_generated=20,
            exports_created=15,
            total_time=120.5
        )
        
        assert stats.files_processed == 10
        assert stats.theorems_found == 25
        assert stats.success_rate == 0.8  # 20/25
        assert stats.average_time_per_file == 12.05  # 120.5/10
    
    def test_cache_stats(self):
        """Test CacheStats model."""
        stats = CacheStats(
            total_entries=100,
            total_size_mb=50.5,
            hits=75,
            misses=25
        )
        
        assert stats.hit_rate == 0.75  # 75/100
        assert stats.miss_rate == 0.25  # 25/100
        assert stats.average_entry_size_kb == 530.48  # (50.5 * 1024) / 100
    
    def test_generation_context(self):
        """Test GenerationContext model."""
        context = GenerationContext(
            model="claude-3",
            temperature=0.7,
            max_tokens=2000,
            style="detailed"
        )
        
        assert context.model == "claude-3"
        assert context.temperature == 0.7
        assert context.max_tokens == 2000
        assert context.style == "detailed"
        
        # Test serialization
        context_dict = context.model_dump()
        assert isinstance(context_dict, dict)
        assert context_dict["model"] == "claude-3"


class TestParserModels:
    """Test parser model classes."""
    
    def test_theorem_info(self):
        """Test TheoremInfo model."""
        theorem = TheoremInfo(
            name="add_comm",
            statement="∀ (a b : ℕ), a + b = b + a",
            proof="by rw [Nat.add_comm]",
            line_number=10,
            docstring="Addition is commutative"
        )
        
        assert theorem.name == "add_comm"
        assert theorem.statement == "∀ (a b : ℕ), a + b = b + a"
        assert theorem.line_number == 10
        
        # Test optional fields
        assert theorem.docstring == "Addition is commutative"
        assert theorem.dependencies == []  # Default
        assert theorem.tactics == []  # Default
    
    def test_parse_result(self):
        """Test ParseResult model."""
        theorems = [
            TheoremInfo(name="test1", statement="P", proof="trivial"),
            TheoremInfo(name="test2", statement="Q", proof="assumption")
        ]
        
        result = ParseResult(
            theorems=theorems,
            success=True,
            file_path=Path("test.lean")
        )
        
        assert result.success
        assert len(result.theorems) == 2
        assert result.has_theorems
        assert not result.has_errors
        
        # Test theorem lookup
        found = result.get_theorem_by_name("test1")
        assert found is not None
        assert found.name == "test1"
        
        # Test non-existent theorem
        not_found = result.get_theorem_by_name("nonexistent")
        assert not_found is None
    
    def test_parse_error(self):
        """Test ParseError model."""
        error = ParseError(
            message="Syntax error",
            line_number=5,
            column=10,
            error_type="syntax",
            severity="error"
        )
        
        assert error.message == "Syntax error"
        assert error.line_number == 5
        assert error.column == 10
        assert error.error_type == "syntax"
        assert error.severity == "error"


class TestGeneratorModels:
    """Test generator model classes."""
    
    def test_proof_step(self):
        """Test ProofStep model."""
        step = ProofStep(
            step_number=1,
            description="Apply commutativity",
            mathematical_content="a + b = b + a",
            reasoning="By the commutative property of addition",
            tactics_used=["rw", "simp"],
            intuition="Order doesn't matter in addition"
        )
        
        assert step.step_number == 1
        assert step.description == "Apply commutativity"
        assert "rw" in step.tactics_used
        assert "simp" in step.tactics_used
    
    def test_proof_sketch(self):
        """Test ProofSketch model."""
        steps = [
            ProofStep(
                step_number=1,
                description="Step 1",
                mathematical_content="Math content",
                reasoning="Because...",
                tactics_used=["simp"],
                intuition="Intuitive explanation"
            )
        ]
        
        sketch = ProofSketch(
            theorem_name="test_theorem",
            theorem_statement="∀ n : ℕ, n + 0 = n",
            introduction="This theorem proves...",
            key_steps=steps,
            conclusion="Therefore...",
            difficulty_level="easy",
            key_insights=["Identity element"],
            mathematical_context="Arithmetic"
        )
        
        assert sketch.theorem_name == "test_theorem"
        assert len(sketch.key_steps) == 1
        assert sketch.difficulty_level == "easy"
        assert "Identity element" in sketch.key_insights
        
        # Test step count
        assert sketch.step_count == 1
    
    def test_generation_request(self):
        """Test GenerationRequest model."""
        theorem = TheoremInfo(name="test", statement="P", proof="trivial")
        
        request = GenerationRequest(
            theorem=theorem,
            context=GenerationContext(model="claude-3"),
            options={"style": "detailed"}
        )
        
        assert request.theorem.name == "test"
        assert request.context.model == "claude-3"
        assert request.options["style"] == "detailed"
    
    def test_generation_response(self):
        """Test GenerationResponse model."""
        sketch = ProofSketch(
            theorem_name="test",
            theorem_statement="P",
            introduction="Test",
            key_steps=[],
            conclusion="Done",
            difficulty_level="trivial"
        )
        
        response = GenerationResponse(
            success=True,
            proof_sketch=sketch,
            generation_time=2.5,
            token_usage=1500
        )
        
        assert response.success
        assert response.proof_sketch.theorem_name == "test"
        assert response.generation_time == 2.5
        assert response.token_usage == 1500


class TestExporterModels:
    """Test exporter model classes."""
    
    def test_export_options(self):
        """Test ExportOptions model."""
        options = ExportOptions(
            output_dir=Path("/tmp/output"),
            format=ExportFormat.HTML,
            include_animations=True,
            include_css=True,
            include_mathjax=True,
            template_name="custom_template"
        )
        
        assert options.output_dir == Path("/tmp/output")
        assert options.format == ExportFormat.HTML
        assert options.include_animations
        assert options.template_name == "custom_template"
    
    def test_export_result(self):
        """Test ExportResult model."""
        result = ExportResult(
            success=True,
            format=ExportFormat.MARKDOWN,
            output_files=[Path("theorem1.md"), Path("theorem2.md")],
            metadata={"theorems_exported": 2, "total_size": "50KB"},
            export_time=1.5
        )
        
        assert result.success
        assert result.format == ExportFormat.MARKDOWN
        assert len(result.output_files) == 2
        assert result.metadata["theorems_exported"] == 2
        assert result.export_time == 1.5


class TestAnimatorModels:
    """Test animator model classes."""
    
    def test_animation_segment(self):
        """Test AnimationSegment model."""
        segment = AnimationSegment(
            type="transformation",
            duration=3.0,
            content="a + b → b + a",
            description="Show commutativity transformation"
        )
        
        assert segment.type == "transformation"
        assert segment.duration == 3.0
        assert segment.content == "a + b → b + a"
    
    def test_animation_scene(self):
        """Test AnimationScene model."""
        segments = [
            AnimationSegment(
                type="introduction",
                duration=2.0,
                content="Introduction text",
                description="Scene introduction"
            ),
            AnimationSegment(
                type="proof_step",
                duration=4.0,
                content="Proof content",
                description="Main proof step"
            )
        ]
        
        scene = AnimationScene(
            title="Proof Animation",
            segments=segments,
            total_duration=6.0,
            style="mathematical"
        )
        
        assert scene.title == "Proof Animation"
        assert len(scene.segments) == 2
        assert scene.total_duration == 6.0
        assert scene.style == "mathematical"
    
    def test_animation_request(self):
        """Test AnimationRequest model."""
        sketch = ProofSketch(
            theorem_name="test",
            theorem_statement="P",
            introduction="Test",
            key_steps=[],
            conclusion="Done",
            difficulty_level="trivial"
        )
        
        request = AnimationRequest(
            proof_sketch=sketch,
            animation_style="step_by_step",
            duration_seconds=30,
            quality="high"
        )
        
        assert request.proof_sketch.theorem_name == "test"
        assert request.animation_style == "step_by_step"
        assert request.duration_seconds == 30
        assert request.quality == "high"
    
    def test_animation_response(self):
        """Test AnimationResponse model."""
        response = AnimationResponse(
            success=True,
            video_path=Path("/tmp/animation.mp4"),
            thumbnail_path=Path("/tmp/thumbnail.png"),
            duration=30.5,
            file_size_mb=5.2
        )
        
        assert response.success
        assert response.video_path == Path("/tmp/animation.mp4")
        assert response.duration == 30.5
        assert response.file_size_mb == 5.2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])