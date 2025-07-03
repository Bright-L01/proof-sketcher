#!/usr/bin/env python3
"""Comprehensive tests for the centralized error handling system.

Tests all custom exceptions, error hierarchies, and error handling utilities.
"""

import pytest
from typing import Dict, Any, Optional

from src.proof_sketcher.core.exceptions import (
    ProofSketcherError,
    ParserError, LeanSyntaxError, LeanTimeoutError, LeanExecutableError,
    GeneratorError, PromptError, AITimeoutError,
    AnimatorError, AnimationTimeoutError,
    ExporterError, ExportFormatError, TemplateError,
    ConfigError, ConfigNotFoundError, ConfigValidationError,
    CacheError, CacheKeyError, CacheReadError, CacheWriteError,
    ValidationError, ModelValidationError, InputValidationError,
    BatchProcessingError, BatchFileError
)


class TestProofSketcherError:
    """Test the base ProofSketcherError class."""
    
    def test_basic_error_creation(self):
        """Test creating a basic error."""
        error = ProofSketcherError("Something went wrong")
        assert str(error) == "Something went wrong"
        assert error.message == "Something went wrong"
        assert error.details == {}
        assert error.error_code is None
    
    def test_error_with_details(self):
        """Test error with additional details."""
        details = {"file": "test.lean", "line": 42}
        error = ProofSketcherError("Parse failed", details=details)
        assert error.details == details
        assert error.details["file"] == "test.lean"
        assert error.details["line"] == 42
    
    def test_error_with_code(self):
        """Test error with error code."""
        error = ProofSketcherError("Network error", error_code="NET_001")
        assert error.error_code == "NET_001"
        assert str(error) == "[NET_001] Network error"
    
    def test_error_with_all_fields(self):
        """Test error with all optional fields."""
        details = {"status": 500, "endpoint": "/api/generate"}
        error = ProofSketcherError(
            "API request failed",
            details=details,
            error_code="API_500"
        )
        assert error.message == "API request failed"
        assert error.details["status"] == 500
        assert error.error_code == "API_500"
        assert str(error) == "[API_500] API request failed"


class TestParserErrors:
    """Test parser-related exceptions."""
    
    def test_parser_error_base(self):
        """Test base parser error."""
        error = ParserError("Failed to parse file")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Failed to parse file"
    
    def test_lean_syntax_error(self):
        """Test Lean syntax error."""
        error = LeanSyntaxError(
            "Invalid theorem syntax",
            details={"line": 10, "column": 5}
        )
        assert isinstance(error, ParserError)
        assert error.details["line"] == 10
        assert error.details["column"] == 5
    
    def test_lean_timeout_error(self):
        """Test Lean timeout error."""
        error = LeanTimeoutError(
            "Lean process timed out",
            details={"timeout_seconds": 30, "file": "complex.lean"}
        )
        assert isinstance(error, ParserError)
        assert error.details["timeout_seconds"] == 30
    
    def test_lean_executable_error(self):
        """Test Lean executable error."""
        error = LeanExecutableError(
            "lean not found in PATH",
            details={"searched_paths": ["/usr/bin", "/usr/local/bin"]}
        )
        assert isinstance(error, ParserError)
        assert len(error.details["searched_paths"]) == 2


class TestGeneratorErrors:
    """Test generator-related exceptions."""
    
    def test_generator_error_base(self):
        """Test base generator error."""
        error = GeneratorError("Generation failed")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Generation failed"
    
    def test_prompt_error(self):
        """Test prompt error."""
        error = PromptError(
            "Prompt construction failed",
            details={"tokens": 150000, "max_tokens": 100000},
            error_code="PROMPT_ERROR"
        )
        assert isinstance(error, GeneratorError)
        assert error.details["tokens"] == 150000
        assert error.error_code == "PROMPT_ERROR"
        assert str(error) == "[PROMPT_ERROR] Prompt construction failed"
    
    def test_ai_timeout_error(self):
        """Test AI timeout error."""
        error = AITimeoutError(
            "AI service timed out after 120s",
            details={"theorem": "complex_proof", "elapsed": 120.5}
        )
        assert isinstance(error, GeneratorError)
        assert error.details["elapsed"] == 120.5


class TestAnimatorErrors:
    """Test animator-related exceptions."""
    
    def test_animator_error_base(self):
        """Test base animator error."""
        error = AnimatorError("Animation failed")
        assert isinstance(error, ProofSketcherError)
    
    def test_animation_render_error(self):
        """Test animation render error using AnimatorError."""
        error = AnimatorError(
            "Failed to render frame 42",
            details={"frame": 42, "total_frames": 100, "error": "Memory exhausted"}
        )
        assert isinstance(error, ProofSketcherError)
        assert error.details["frame"] == 42
    
    def test_animation_timeout_error(self):
        """Test animation timeout error."""
        error = AnimationTimeoutError(
            "Animation generation exceeded time limit",
            details={"timeout": 300, "progress": "50%"}
        )
        assert isinstance(error, AnimatorError)
        assert error.details["timeout"] == 300


class TestExporterErrors:
    """Test exporter-related exceptions."""
    
    def test_exporter_error_base(self):
        """Test base exporter error."""
        error = ExporterError("Export failed")
        assert isinstance(error, ProofSketcherError)
    
    def test_export_format_error(self):
        """Test export format error."""
        error = ExportFormatError(
            "Unsupported export format",
            details={"format": "docx", "supported": ["html", "pdf", "md"]}
        )
        assert isinstance(error, ExporterError)
        assert error.details["format"] == "docx"
        assert "html" in error.details["supported"]
    
    def test_template_error(self):
        """Test template error."""
        error = TemplateError(
            "Template rendering failed",
            details={"template": "proof.html.j2", "error": "Variable 'theorem' not found"}
        )
        assert isinstance(error, ExporterError)
        assert error.details["template"] == "proof.html.j2"


class TestConfigErrors:
    """Test configuration-related exceptions."""
    
    def test_config_error_base(self):
        """Test base config error."""
        error = ConfigError("Configuration invalid")
        assert isinstance(error, ProofSketcherError)
    
    def test_config_not_found_error(self):
        """Test config not found error."""
        error = ConfigNotFoundError(
            "Configuration file not found",
            details={"path": "~/.proof_sketcher/config.yaml"}
        )
        assert isinstance(error, ConfigError)
        assert "config.yaml" in error.details["path"]
    
    def test_config_validation_error(self):
        """Test config validation error."""
        error = ConfigValidationError(
            "Invalid configuration value",
            details={"field": "max_workers", "value": -1, "expected": "positive integer"}
        )
        assert isinstance(error, ConfigError)
        assert error.details["field"] == "max_workers"
        assert error.details["value"] == -1


class TestCacheErrors:
    """Test cache-related exceptions."""
    
    def test_cache_error_base(self):
        """Test base cache error."""
        error = CacheError("Cache operation failed")
        assert isinstance(error, ProofSketcherError)
    
    def test_cache_key_error(self):
        """Test cache key error."""
        error = CacheKeyError(
            "Invalid cache key",
            details={"key": "theorem::", "reason": "Empty component"}
        )
        assert isinstance(error, CacheError)
        assert error.details["reason"] == "Empty component"
    
    def test_cache_read_error(self):
        """Test cache read error."""
        error = CacheReadError(
            "Failed to read from cache",
            details={"file": "cache.db", "error": "Corrupted data"}
        )
        assert isinstance(error, CacheError)
        assert error.details["error"] == "Corrupted data"
    
    def test_cache_write_error(self):
        """Test cache write error."""
        error = CacheWriteError(
            "Failed to write to cache",
            details={"reason": "Disk full", "required_space_mb": 100}
        )
        assert isinstance(error, CacheError)
        assert error.details["required_space_mb"] == 100


class TestValidationErrors:
    """Test validation-related exceptions."""
    
    def test_validation_error_base(self):
        """Test base validation error."""
        error = ValidationError("Validation failed")
        assert isinstance(error, ProofSketcherError)
    
    def test_model_validation_error(self):
        """Test model validation error."""
        error = ModelValidationError(
            "ProofSketch validation failed",
            details={
                "field": "difficulty_level",
                "value": "expert",
                "allowed": ["beginner", "intermediate", "advanced"]
            }
        )
        assert isinstance(error, ValidationError)
        assert error.details["value"] == "expert"
        assert "beginner" in error.details["allowed"]
    
    def test_input_validation_error(self):
        """Test input validation error."""
        error = InputValidationError(
            "Invalid input file",
            details={"file": "test.txt", "expected": ".lean files"}
        )
        assert isinstance(error, ValidationError)
        assert error.details["file"] == "test.txt"


class TestBatchProcessingErrors:
    """Test batch processing-related exceptions."""
    
    def test_batch_processing_error_base(self):
        """Test base batch processing error."""
        error = BatchProcessingError("Batch processing failed")
        assert isinstance(error, ProofSketcherError)
    
    def test_batch_file_error(self):
        """Test batch file error."""
        error = BatchFileError(
            "Failed to process file in batch",
            details={
                "file": "theorem42.lean",
                "batch_id": "batch_001",
                "error": "Timeout"
            }
        )
        assert isinstance(error, BatchProcessingError)
        assert error.details["file"] == "theorem42.lean"
        assert error.details["batch_id"] == "batch_001"


class TestErrorHierarchy:
    """Test the error hierarchy relationships."""
    
    def test_all_errors_inherit_from_base(self):
        """Test that all custom errors inherit from ProofSketcherError."""
        error_classes = [
            ParserError, LeanSyntaxError, LeanTimeoutError, LeanExecutableError,
            GeneratorError, PromptError, AITimeoutError,
            AnimatorError, AnimationTimeoutError,
            ExporterError, ExportFormatError, TemplateError,
            ConfigError, ConfigNotFoundError, ConfigValidationError,
            CacheError, CacheKeyError, CacheReadError, CacheWriteError,
            ValidationError, ModelValidationError, InputValidationError,
            BatchProcessingError, BatchFileError
        ]
        
        for error_class in error_classes:
            error = error_class("test")
            assert isinstance(error, ProofSketcherError)
            assert isinstance(error, Exception)
    
    def test_specific_inheritance_chains(self):
        """Test specific inheritance relationships."""
        # Parser errors
        assert issubclass(LeanSyntaxError, ParserError)
        assert issubclass(LeanTimeoutError, ParserError)
        assert issubclass(LeanExecutableError, ParserError)
        
        # Generator errors
        assert issubclass(PromptError, GeneratorError)
        assert issubclass(AITimeoutError, GeneratorError)
        
        # Animator errors
        assert issubclass(AnimationTimeoutError, AnimatorError)
        
        # Exporter errors
        assert issubclass(ExportFormatError, ExporterError)
        assert issubclass(TemplateError, ExporterError)
        
        # Config errors
        assert issubclass(ConfigNotFoundError, ConfigError)
        assert issubclass(ConfigValidationError, ConfigError)
        
        # Cache errors
        assert issubclass(CacheKeyError, CacheError)
        assert issubclass(CacheReadError, CacheError)
        assert issubclass(CacheWriteError, CacheError)
        
        # Validation errors
        assert issubclass(ModelValidationError, ValidationError)
        assert issubclass(InputValidationError, ValidationError)
        
        # Batch processing errors
        assert issubclass(BatchFileError, BatchProcessingError)


class TestErrorUsagePatterns:
    """Test common error usage patterns."""
    
    def test_raising_with_context(self):
        """Test raising errors with rich context."""
        try:
            raise PromptError(
                "Rate limit exceeded",
                details={
                    "endpoint": "/v1/messages",
                    "rate_limit": 100,
                    "retry_after": 60,
                    "request_id": "req_123"
                },
                error_code="RATE_LIMIT_429"
            )
        except PromptError as e:
            assert e.error_code == "RATE_LIMIT_429"
            assert e.details["retry_after"] == 60
            assert "429" in str(e)
    
    def test_error_chaining(self):
        """Test chaining errors with cause."""
        try:
            try:
                # Simulate a low-level error
                raise FileNotFoundError("config.yaml not found")
            except FileNotFoundError as e:
                # Wrap in our custom error
                raise ConfigNotFoundError(
                    "Failed to load configuration",
                    details={"searched_paths": [".", "~/.config", "/etc"]},
                    error_code="CFG_404"
                ) from e
        except ConfigNotFoundError as e:
            assert e.__cause__ is not None
            assert isinstance(e.__cause__, FileNotFoundError)
            assert e.error_code == "CFG_404"
    
    def test_catching_error_categories(self):
        """Test catching errors by category."""
        parser_errors = [
            LeanSyntaxError("syntax error"),
            LeanTimeoutError("timeout"),
            LeanExecutableError("not found")
        ]
        
        # All parser errors can be caught as ParserError
        for error in parser_errors:
            try:
                raise error
            except ParserError:
                pass  # Successfully caught
            except Exception:
                pytest.fail(f"Failed to catch {type(error).__name__} as ParserError")
    
    def test_error_details_access(self):
        """Test accessing error details safely."""
        error = ExportFormatError(
            "Invalid format",
            details={"format": "xyz", "supported": ["html", "pdf"]}
        )
        
        # Direct access
        assert error.details["format"] == "xyz"
        
        # Safe access for missing keys
        assert error.details.get("missing_key") is None
        assert error.details.get("missing_key", "default") == "default"
    
    def test_error_serialization(self):
        """Test that errors can be serialized for logging/reporting."""
        error = AnimatorError(
            "Render failed",
            details={
                "frame": 42,
                "resolution": "1920x1080",
                "memory_used_mb": 2048
            },
            error_code="ANIM_RENDER_001"
        )
        
        # Create a serializable representation
        error_dict = {
            "type": type(error).__name__,
            "message": error.message,
            "error_code": error.error_code,
            "details": error.details
        }
        
        assert error_dict["type"] == "AnimatorError"
        assert error_dict["error_code"] == "ANIM_RENDER_001"
        assert error_dict["details"]["frame"] == 42
        
        # Should be JSON serializable
        import json
        json_str = json.dumps(error_dict)
        assert "ANIM_RENDER_001" in json_str