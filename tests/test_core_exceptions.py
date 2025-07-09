"""Comprehensive unit tests for core exceptions module.

This module tests all exception classes and error handling functionality
to ensure robust error management throughout the application.
"""

import logging
import pytest
from typing import Dict, Any
from unittest.mock import patch, MagicMock

from proof_sketcher.core.exceptions import (
    # Base exceptions
    ProofSketcherError,
    
    # Parser exceptions
    ParserError,
    LeanExecutableError,
    LeanSyntaxError,
    LeanTimeoutError,
    
    # Generator exceptions
    GeneratorError,
    AIExecutableError,
    AITimeoutError,
    PromptError,
    GenerationError,  # Alias
    
    # Animator exceptions
    AnimatorError,
    AnimationTimeoutError,
    MCPConnectionError,
    SceneGenerationError,
    FormulaExtractionError,
    
    # Exporter exceptions
    ExporterError,
    TemplateError,
    ExportFormatError,
    FileWriteError,
    
    # Configuration exceptions
    ConfigError,
    ConfigNotFoundError,
    ConfigValidationError,
    
    # Cache exceptions
    CacheError,
    CacheKeyError,
    CacheReadError,
    CacheWriteError,
    
    # Validation exceptions
    ValidationError,
    ModelValidationError,
    InputValidationError,
    
    # Batch processing exceptions
    BatchProcessingError,
    BatchFileError,
    
    # Resource management exceptions
    ResourceError,
    DiskSpaceError,
    MemoryError,
    NetworkError,
    
    # Error handling
    ErrorHandler,
    handle_error,
)


class TestProofSketcherError:
    """Test base ProofSketcherError class."""
    
    def test_basic_creation(self):
        """Test basic error creation."""
        error = ProofSketcherError("Test error")
        assert str(error) == "Test error"
        assert error.message == "Test error"
        assert error.details == {}
        assert error.error_code is None
    
    def test_with_details(self):
        """Test error creation with details."""
        details = {"file": "test.lean", "line": 42}
        error = ProofSketcherError("Parse error", details=details)
        
        assert error.message == "Parse error"
        assert error.details == details
        assert error.details["file"] == "test.lean"
        assert error.details["line"] == 42
    
    def test_with_error_code(self):
        """Test error creation with error code."""
        error = ProofSketcherError("Test error", error_code="TEST_001")
        assert str(error) == "[TEST_001] Test error"
        assert error.error_code == "TEST_001"
    
    def test_all_parameters(self):
        """Test error creation with all parameters."""
        details = {"context": "test"}
        error = ProofSketcherError(
            "Complete error",
            details=details,
            error_code="COMPLETE_001"
        )
        
        assert error.message == "Complete error"
        assert error.details == details
        assert error.error_code == "COMPLETE_001"
        assert str(error) == "[COMPLETE_001] Complete error"


class TestParserExceptions:
    """Test parser-related exceptions."""
    
    def test_parser_error(self):
        """Test base ParserError."""
        error = ParserError("Parser failed")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Parser failed"
    
    def test_lean_executable_error(self):
        """Test LeanExecutableError."""
        error = LeanExecutableError("Lean not found", error_code="LEAN_001")
        assert isinstance(error, ParserError)
        assert str(error) == "[LEAN_001] Lean not found"
    
    def test_lean_syntax_error(self):
        """Test LeanSyntaxError."""
        details = {"line": 15, "column": 23}
        error = LeanSyntaxError("Syntax error", details=details)
        assert isinstance(error, ParserError)
        assert error.details["line"] == 15
    
    def test_lean_timeout_error(self):
        """Test LeanTimeoutError."""
        error = LeanTimeoutError("Parsing timeout after 30s")
        assert isinstance(error, ParserError)
        assert "timeout" in str(error).lower()


class TestGeneratorExceptions:
    """Test generator-related exceptions."""
    
    def test_generator_error(self):
        """Test base GeneratorError."""
        error = GeneratorError("Generation failed")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Generation failed"
    
    def test_ai_executable_error(self):
        """Test AIExecutableError."""
        error = AIExecutableError("Claude CLI not found")
        assert isinstance(error, GeneratorError)
        assert "Claude CLI" in str(error)
    
    def test_ai_timeout_error(self):
        """Test AITimeoutError."""
        error = AITimeoutError("AI generation timeout")
        assert isinstance(error, GeneratorError)
        assert "timeout" in str(error).lower()
    
    def test_prompt_error(self):
        """Test PromptError."""
        error = PromptError("Template rendering failed")
        assert isinstance(error, GeneratorError)
        assert "Template" in str(error)
    
    def test_generation_error_alias(self):
        """Test GenerationError alias."""
        error = GenerationError("Generation failed")
        assert isinstance(error, GeneratorError)
        assert isinstance(error, ProofSketcherError)


class TestAnimatorExceptions:
    """Test animator-related exceptions."""
    
    def test_animator_error(self):
        """Test base AnimatorError."""
        error = AnimatorError("Animation failed")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Animation failed"
    
    def test_animation_timeout_error(self):
        """Test AnimationTimeoutError."""
        error = AnimationTimeoutError("Animation timeout")
        assert isinstance(error, AnimatorError)
        assert "timeout" in str(error).lower()
    
    def test_mcp_connection_error(self):
        """Test MCPConnectionError."""
        details = {"host": "localhost", "port": 8080}
        error = MCPConnectionError("MCP connection failed", details=details)
        assert isinstance(error, AnimatorError)
        assert error.details["host"] == "localhost"
    
    def test_scene_generation_error(self):
        """Test SceneGenerationError."""
        error = SceneGenerationError("Scene generation failed")
        assert isinstance(error, AnimatorError)
        assert "Scene" in str(error)
    
    def test_formula_extraction_error(self):
        """Test FormulaExtractionError."""
        error = FormulaExtractionError("Formula extraction failed")
        assert isinstance(error, AnimatorError)
        assert "Formula" in str(error)


class TestExporterExceptions:
    """Test exporter-related exceptions."""
    
    def test_exporter_error(self):
        """Test base ExporterError."""
        error = ExporterError("Export failed")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Export failed"
    
    def test_template_error(self):
        """Test TemplateError."""
        error = TemplateError("Template not found")
        assert isinstance(error, ExporterError)
        assert "Template" in str(error)
    
    def test_export_format_error(self):
        """Test ExportFormatError."""
        error = ExportFormatError("Unsupported format: xyz")
        assert isinstance(error, ExporterError)
        assert "format" in str(error).lower()
    
    def test_file_write_error(self):
        """Test FileWriteError."""
        error = FileWriteError("Cannot write to file")
        assert isinstance(error, ExporterError)
        assert "write" in str(error).lower()


class TestConfigurationExceptions:
    """Test configuration-related exceptions."""
    
    def test_config_error(self):
        """Test base ConfigError."""
        error = ConfigError("Config error")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Config error"
    
    def test_config_not_found_error(self):
        """Test ConfigNotFoundError."""
        error = ConfigNotFoundError("Config file not found")
        assert isinstance(error, ConfigError)
        assert "not found" in str(error)
    
    def test_config_validation_error(self):
        """Test ConfigValidationError."""
        error = ConfigValidationError("Invalid config value")
        assert isinstance(error, ConfigError)
        assert "Invalid" in str(error)


class TestCacheExceptions:
    """Test cache-related exceptions."""
    
    def test_cache_error(self):
        """Test base CacheError."""
        error = CacheError("Cache error")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Cache error"
    
    def test_cache_key_error(self):
        """Test CacheKeyError."""
        error = CacheKeyError("Invalid cache key")
        assert isinstance(error, CacheError)
        assert "key" in str(error).lower()
    
    def test_cache_read_error(self):
        """Test CacheReadError."""
        error = CacheReadError("Cannot read from cache")
        assert isinstance(error, CacheError)
        assert "read" in str(error).lower()
    
    def test_cache_write_error(self):
        """Test CacheWriteError."""
        error = CacheWriteError("Cannot write to cache")
        assert isinstance(error, CacheError)
        assert "write" in str(error).lower()


class TestValidationExceptions:
    """Test validation-related exceptions."""
    
    def test_validation_error(self):
        """Test base ValidationError."""
        error = ValidationError("Validation failed")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Validation failed"
    
    def test_model_validation_error(self):
        """Test ModelValidationError."""
        error = ModelValidationError("Model validation failed")
        assert isinstance(error, ValidationError)
        assert "Model" in str(error)
    
    def test_input_validation_error(self):
        """Test InputValidationError."""
        error = InputValidationError("Invalid input")
        assert isinstance(error, ValidationError)
        assert "input" in str(error).lower()


class TestBatchProcessingExceptions:
    """Test batch processing-related exceptions."""
    
    def test_batch_processing_error(self):
        """Test base BatchProcessingError."""
        error = BatchProcessingError("Batch processing failed")
        assert isinstance(error, ProofSketcherError)
        assert "Batch" in str(error)
    
    def test_batch_file_error(self):
        """Test BatchFileError."""
        error = BatchFileError("File processing failed")
        assert isinstance(error, BatchProcessingError)
        assert "File" in str(error)


class TestResourceManagementExceptions:
    """Test resource management exceptions."""
    
    def test_resource_error_basic(self):
        """Test basic ResourceError."""
        error = ResourceError("Resource error")
        assert isinstance(error, ProofSketcherError)
        assert str(error) == "Resource error"
        assert error.context == {}
    
    def test_resource_error_with_context(self):
        """Test ResourceError with context."""
        context = {"memory_mb": 512, "cpu_percent": 85}
        error = ResourceError("Resource limit exceeded", context=context)
        assert error.context == context
        assert error.details == context
    
    def test_resource_error_context_merge(self):
        """Test ResourceError context and details merge."""
        details = {"source": "test"}
        context = {"target": "test"}
        error = ResourceError("Test", details=details, context=context)
        
        # Context should be merged into details
        assert "source" in error.details
        assert "target" in error.details
        assert error.context["target"] == "test"
    
    def test_disk_space_error_basic(self):
        """Test basic DiskSpaceError."""
        error = DiskSpaceError("Insufficient disk space")
        assert isinstance(error, ResourceError)
        assert str(error) == "Insufficient disk space"
    
    def test_disk_space_error_with_sizes(self):
        """Test DiskSpaceError with space information."""
        required = 1024 * 1024 * 100  # 100MB
        available = 1024 * 1024 * 50   # 50MB
        
        error = DiskSpaceError(
            "Not enough space",
            required_space=required,
            available_space=available
        )
        
        assert error.required_space == required
        assert error.available_space == available
        assert error.context["required_space_mb"] == 100
        assert error.context["available_space_mb"] == 50
    
    def test_memory_error_basic(self):
        """Test basic MemoryError."""
        error = MemoryError("Memory limit exceeded")
        assert isinstance(error, ResourceError)
        assert str(error) == "Memory limit exceeded"
        assert error.context == {}
    
    def test_memory_error_with_context(self):
        """Test MemoryError with context."""
        context = {"current_memory_mb": 512, "limit_mb": 256}
        error = MemoryError("Memory limit exceeded", context=context)
        assert error.context == context
    
    def test_memory_error_full_message(self):
        """Test MemoryError full message with suggestions."""
        error = MemoryError("Memory limit exceeded")
        full_msg = error.get_full_message()
        
        assert "Memory limit exceeded" in full_msg
        assert "Suggestions:" in full_msg
        assert "Close other applications" in full_msg
        assert "Reduce batch size" in full_msg
        assert "streaming mode" in full_msg
    
    def test_network_error_basic(self):
        """Test basic NetworkError."""
        error = NetworkError("Connection failed")
        assert isinstance(error, ResourceError)
        assert str(error) == "Connection failed"
    
    def test_network_error_with_operation(self):
        """Test NetworkError with operation."""
        context = {"host": "api.claude.ai", "timeout": 30}
        error = NetworkError(
            "Connection timeout",
            operation="api_call",
            context=context
        )
        
        assert error.operation == "api_call"
        assert error.context["host"] == "api.claude.ai"
        assert hasattr(error, 'recovery_strategies')
        assert len(error.recovery_strategies) == 3
    
    def test_network_error_recovery_strategies(self):
        """Test NetworkError recovery strategies."""
        error = NetworkError("Connection failed")
        strategies = [s.value for s in error.recovery_strategies]
        
        assert "retry" in strategies
        assert "fallback" in strategies
        assert "cache" in strategies


class TestErrorHandler:
    """Test ErrorHandler class."""
    
    def test_initialization(self):
        """Test ErrorHandler initialization."""
        handler = ErrorHandler()
        assert handler.auto_recover is True
        assert isinstance(handler.error_counts, dict)
        assert isinstance(handler.recovery_counts, dict)
        assert len(handler.error_counts) == 0
    
    def test_initialization_no_auto_recover(self):
        """Test ErrorHandler with auto_recover disabled."""
        handler = ErrorHandler(auto_recover=False)
        assert handler.auto_recover is False
    
    @patch('logging.getLogger')
    def test_logger_setup(self, mock_get_logger):
        """Test logger setup."""
        mock_logger = MagicMock()
        mock_get_logger.return_value = mock_logger
        
        handler = ErrorHandler()
        assert handler.logger == mock_logger
        mock_get_logger.assert_called_once()
    
    def test_handle_proof_sketcher_error(self):
        """Test handling ProofSketcherError."""
        handler = ErrorHandler()
        error = ProofSketcherError("Test error", error_code="TEST_001")
        
        with patch.object(handler.logger, 'error') as mock_error:
            result = handler.handle(error)
            
            assert result is None
            mock_error.assert_called_once_with("ProofSketcherError: [TEST_001] Test error")
            assert handler.error_counts["ProofSketcherError"] == 1
    
    def test_handle_standard_exception(self):
        """Test handling standard exception."""
        handler = ErrorHandler()
        error = ValueError("Standard error")
        
        with patch.object(handler.logger, 'error') as mock_error:
            result = handler.handle(error)
            
            assert result is None
            mock_error.assert_called_once_with("Unexpected error: Standard error")
            assert handler.error_counts["ValueError"] == 1
    
    def test_handle_with_context(self):
        """Test handling error with context."""
        handler = ErrorHandler()
        error = ProofSketcherError("Test error")
        context = {"file": "test.lean", "operation": "parse"}
        
        with patch.object(handler.logger, 'debug') as mock_debug:
            handler.handle(error, context=context)
            
            mock_debug.assert_called_with(f"Error context: {context}")
    
    def test_handle_error_with_recovery(self):
        """Test handle_error method with recovery."""
        handler = ErrorHandler()
        error = NetworkError("Connection failed")
        
        # First attempt
        result1 = handler.handle_error(error, auto_recover=True)
        assert result1 is None
        assert handler.recovery_counts["NetworkError"] == 1
        
        # Second attempt
        result2 = handler.handle_error(error, auto_recover=True)
        assert handler.recovery_counts["NetworkError"] == 2
        
        # Multiple attempts should be limited
        for _ in range(5):
            handler.handle_error(error, auto_recover=True)
        
        # Should cap at 3 recovery attempts
        assert handler.recovery_counts["NetworkError"] == 3
    
    def test_wrap_error_connection_error(self):
        """Test wrapping ConnectionError."""
        handler = ErrorHandler()
        original = ConnectionError("Connection refused")
        wrapped = handler._wrap_error(original)
        
        assert isinstance(wrapped, NetworkError)
        assert wrapped.operation == "connection"
    
    def test_wrap_error_file_not_found(self):
        """Test wrapping FileNotFoundError."""
        handler = ErrorHandler()
        original = FileNotFoundError("File not found")
        wrapped = handler._wrap_error(original)
        
        assert isinstance(wrapped, ParserError)
        assert wrapped.details["category"] == "parse"
        assert wrapped.error_code == "FILE_NOT_FOUND"
    
    def test_wrap_error_memory_error(self):
        """Test wrapping MemoryError."""
        handler = ErrorHandler()
        original = MemoryError("Out of memory")
        wrapped = handler._wrap_error(original)
        
        assert isinstance(wrapped, ResourceError)
    
    def test_wrap_error_generic(self):
        """Test wrapping generic exception."""
        handler = ErrorHandler()
        original = RuntimeError("Runtime error")
        wrapped = handler._wrap_error(original)
        
        assert isinstance(wrapped, ProofSketcherError)
        assert str(wrapped) == "Runtime error"
    
    def test_error_summary(self):
        """Test error summary generation."""
        handler = ErrorHandler()
        
        # Handle some errors
        handler.handle(ValueError("Error 1"))
        handler.handle(ValueError("Error 2"))
        handler.handle(RuntimeError("Error 3"))
        
        # Trigger some recoveries
        handler.handle_error(NetworkError("Network error"), auto_recover=True)
        
        summary = handler.get_error_summary()
        
        assert summary["total_errors"] == 4
        assert summary["total_recoveries"] == 1
        assert summary["error_counts"]["ValueError"] == 2
        assert summary["error_counts"]["RuntimeError"] == 1
        assert summary["error_counts"]["NetworkError"] == 1
        assert summary["recovery_counts"]["NetworkError"] == 1


class TestGlobalErrorHandling:
    """Test global error handling functions."""
    
    @patch('logging.getLogger')
    def test_handle_error_function_proof_sketcher_error(self, mock_get_logger):
        """Test global handle_error function with ProofSketcherError."""
        mock_logger = MagicMock()
        mock_get_logger.return_value = mock_logger
        
        error = ProofSketcherError("Test error")
        result = handle_error(error)
        
        assert result is None
        mock_logger.error.assert_called_once_with("ProofSketcherError: Test error")
    
    @patch('logging.getLogger')
    def test_handle_error_function_standard_error(self, mock_get_logger):
        """Test global handle_error function with standard error."""
        mock_logger = MagicMock()
        mock_get_logger.return_value = mock_logger
        
        error = ValueError("Standard error")
        result = handle_error(error, context={"test": "context"})
        
        assert result is None
        mock_logger.error.assert_called_once_with("Unexpected error: Standard error")


class TestExceptionInheritance:
    """Test exception inheritance hierarchy."""
    
    def test_all_exceptions_inherit_from_base(self):
        """Test that all custom exceptions inherit from ProofSketcherError."""
        custom_exceptions = [
            ParserError, LeanExecutableError, LeanSyntaxError, LeanTimeoutError,
            GeneratorError, AIExecutableError, AITimeoutError, PromptError,
            AnimatorError, AnimationTimeoutError, MCPConnectionError,
            SceneGenerationError, FormulaExtractionError,
            ExporterError, TemplateError, ExportFormatError, FileWriteError,
            ConfigError, ConfigNotFoundError, ConfigValidationError,
            CacheError, CacheKeyError, CacheReadError, CacheWriteError,
            ValidationError, ModelValidationError, InputValidationError,
            BatchProcessingError, BatchFileError,
            ResourceError, DiskSpaceError, MemoryError, NetworkError,
        ]
        
        for exception_class in custom_exceptions:
            error = exception_class("Test message")
            assert isinstance(error, ProofSketcherError)
            assert isinstance(error, Exception)
    
    def test_exception_hierarchy_parser(self):
        """Test parser exception hierarchy."""
        error = LeanSyntaxError("Syntax error")
        assert isinstance(error, LeanSyntaxError)
        assert isinstance(error, ParserError)
        assert isinstance(error, ProofSketcherError)
    
    def test_exception_hierarchy_resource(self):
        """Test resource exception hierarchy."""
        error = DiskSpaceError("Disk full")
        assert isinstance(error, DiskSpaceError)
        assert isinstance(error, ResourceError)
        assert isinstance(error, ProofSketcherError)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])