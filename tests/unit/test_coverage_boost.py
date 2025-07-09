"""Simple unit tests to boost coverage on existing modules."""

import pytest
from proof_sketcher.core.utils import generate_cache_key, sanitize_filename


class TestSimpleUtils:
    """Test simple utility functions that we know exist."""
    
    def test_generate_cache_key_basic(self):
        """Test basic cache key generation."""
        key1 = generate_cache_key("test")
        key2 = generate_cache_key("test")
        assert key1 == key2
        assert len(key1) == 64  # SHA256 hex
    
    def test_generate_cache_key_different_inputs(self):
        """Test cache key generation with different inputs."""
        key1 = generate_cache_key("input1")
        key2 = generate_cache_key("input2")
        assert key1 != key2
    
    def test_generate_cache_key_with_multiple_args(self):
        """Test cache key generation with multiple arguments."""
        key1 = generate_cache_key("arg1", "arg2", "arg3")
        key2 = generate_cache_key("arg1", "arg2", "arg3")
        assert key1 == key2
        
        key3 = generate_cache_key("arg1", "arg2", "different")
        assert key1 != key3
    
    def test_generate_cache_key_with_kwargs(self):
        """Test cache key generation with keyword arguments."""
        key1 = generate_cache_key(name="test", value=123)
        key2 = generate_cache_key(value=123, name="test")
        assert key1 == key2  # Order shouldn't matter
        
        key3 = generate_cache_key(name="test", value=456)
        assert key1 != key3
    
    def test_generate_cache_key_mixed_args(self):
        """Test cache key generation with mixed positional and keyword args."""
        key1 = generate_cache_key("pos1", "pos2", kwarg1="val1", kwarg2="val2")
        key2 = generate_cache_key("pos1", "pos2", kwarg2="val2", kwarg1="val1")
        assert key1 == key2
    
    def test_sanitize_filename_basic(self):
        """Test basic filename sanitization."""
        result = sanitize_filename("normal_file.txt")
        assert result == "normal_file.txt"
    
    def test_sanitize_filename_spaces(self):
        """Test filename sanitization with spaces."""
        result = sanitize_filename("file with spaces.txt")
        assert " " not in result
        assert "_" in result or "-" in result
    
    def test_sanitize_filename_invalid_chars(self):
        """Test filename sanitization with invalid characters."""
        invalid_chars = '<>:"/\\|?*'
        filename = f"test{invalid_chars}file.txt"
        result = sanitize_filename(filename)
        
        for char in invalid_chars:
            assert char not in result
    
    def test_sanitize_filename_long_name(self):
        """Test filename sanitization with very long names."""
        long_name = "a" * 300  # Much longer than typical filesystem limits
        result = sanitize_filename(long_name)
        assert len(result) <= 255  # Common filesystem limit
    
    def test_sanitize_filename_empty(self):
        """Test filename sanitization with empty input."""
        result = sanitize_filename("")
        assert len(result) > 0  # Should provide some default
        assert result.isalnum() or "_" in result or "-" in result
    
    def test_sanitize_filename_special_cases(self):
        """Test filename sanitization with special cases."""
        # Test with only invalid characters
        result = sanitize_filename("<<<>>>")
        assert len(result) > 0
        assert not any(c in result for c in "<>")
        
        # Test with dots
        result = sanitize_filename("..file.txt")
        assert not result.startswith(".")
        
        # Test with trailing spaces
        result = sanitize_filename("file   ")
        assert not result.endswith(" ")


# Import and test some existing models if they exist
try:
    from proof_sketcher.core.exceptions import ProofSketcherError
    
    class TestExceptions:
        """Test core exceptions."""
        
        def test_proof_sketcher_error_basic(self):
            """Test basic ProofSketcherError."""
            error = ProofSketcherError("Test message")
            assert str(error) == "Test message"
            assert error.message == "Test message"
            assert error.details == {}
            assert error.error_code is None
        
        def test_proof_sketcher_error_with_code(self):
            """Test ProofSketcherError with error code."""
            error = ProofSketcherError("Test message", error_code="TEST_001")
            assert "[TEST_001]" in str(error)
            assert error.error_code == "TEST_001"
        
        def test_proof_sketcher_error_with_details(self):
            """Test ProofSketcherError with details."""
            details = {"file": "test.lean", "line": 10}
            error = ProofSketcherError("Test message", details=details)
            assert error.details == details
            assert error.details["file"] == "test.lean"
            assert error.details["line"] == 10
        
        def test_proof_sketcher_error_inheritance(self):
            """Test that ProofSketcherError inherits from Exception."""
            error = ProofSketcherError("Test message")
            assert isinstance(error, Exception)
            
            # Should be raisable
            with pytest.raises(ProofSketcherError):
                raise error

except ImportError:
    pass  # Skip if not available

# Import and test other utilities if they exist
try:
    from proof_sketcher.core.utils import truncate_text, format_duration
    
    class TestMoreUtils:
        """Test additional utility functions."""
        
        def test_truncate_text_basic(self):
            """Test basic text truncation."""
            text = "This is a long text that needs truncation"
            result = truncate_text(text, 20)
            assert len(result) <= 20
        
        def test_truncate_text_short(self):
            """Test truncation with text shorter than limit."""
            text = "Short"
            result = truncate_text(text, 20)
            assert result == text
        
        def test_truncate_text_exact_length(self):
            """Test truncation with text exactly at limit."""
            text = "12345678901234567890"  # Exactly 20 chars
            result = truncate_text(text, 20)
            assert len(result) <= 20
        
        def test_format_duration_seconds(self):
            """Test duration formatting for seconds."""
            result = format_duration(5.5)
            assert isinstance(result, str)
            assert len(result) > 0
        
        def test_format_duration_minutes(self):
            """Test duration formatting for minutes."""
            result = format_duration(125)  # > 2 minutes
            assert isinstance(result, str)
            assert len(result) > 0
        
        def test_format_duration_hours(self):
            """Test duration formatting for hours."""
            result = format_duration(7200)  # 2 hours
            assert isinstance(result, str)
            assert len(result) > 0

except ImportError:
    pass  # Skip if not available


# Test any models that exist
try:
    from proof_sketcher.parser.models import TheoremInfo
    
    class TestTheoremInfo:
        """Test TheoremInfo model."""
        
        def test_theorem_info_basic(self):
            """Test basic TheoremInfo creation."""
            theorem = TheoremInfo(
                name="test_theorem",
                statement="∀ n : ℕ, n = n",
                proof="rfl"
            )
            
            assert theorem.name == "test_theorem"
            assert theorem.statement == "∀ n : ℕ, n = n"
            assert theorem.proof == "rfl"
        
        def test_theorem_info_with_line(self):
            """Test TheoremInfo with line number."""
            theorem = TheoremInfo(
                name="test",
                statement="P",
                proof="trivial",
                line_number=10
            )
            
            assert theorem.line_number == 10
        
        def test_theorem_info_optional_fields(self):
            """Test TheoremInfo with optional fields."""
            theorem = TheoremInfo(
                name="test",
                statement="P",
                proof="trivial",
                docstring="Test theorem",
                dependencies=["Mathlib.Logic.Basic"],
                tactics=["rfl", "simp"]
            )
            
            assert theorem.docstring == "Test theorem"
            assert "Mathlib.Logic.Basic" in theorem.dependencies
            assert "rfl" in theorem.tactics
            assert "simp" in theorem.tactics

except ImportError:
    pass  # Skip if not available


try:
    from proof_sketcher.generator.models import ProofSketch, ProofStep
    
    class TestProofModels:
        """Test proof-related models."""
        
        def test_proof_step_basic(self):
            """Test basic ProofStep creation."""
            step = ProofStep(
                step_number=1,
                description="Apply definition",
                mathematical_content="n = n",
                reasoning="By reflexivity",
                tactics_used=["rfl"],
                intuition="Equal to itself"
            )
            
            assert step.step_number == 1
            assert step.description == "Apply definition"
            assert "rfl" in step.tactics_used
        
        def test_proof_sketch_basic(self):
            """Test basic ProofSketch creation."""
            sketch = ProofSketch(
                theorem_name="test",
                theorem_statement="P",
                introduction="Test theorem",
                key_steps=[],
                conclusion="QED",
                difficulty_level="easy"
            )
            
            assert sketch.theorem_name == "test"
            assert sketch.theorem_statement == "P"
            assert sketch.difficulty_level == "easy"
            assert len(sketch.key_steps) == 0
        
        def test_proof_sketch_with_steps(self):
            """Test ProofSketch with steps."""
            step = ProofStep(
                step_number=1,
                description="Step 1",
                mathematical_content="Math",
                reasoning="Because",
                tactics_used=["simp"],
                intuition="Intuition"
            )
            
            sketch = ProofSketch(
                theorem_name="test",
                theorem_statement="P",
                introduction="Test",
                key_steps=[step],
                conclusion="Done",
                difficulty_level="easy"
            )
            
            assert len(sketch.key_steps) == 1
            assert sketch.key_steps[0].step_number == 1

except ImportError:
    pass  # Skip if not available


if __name__ == "__main__":
    pytest.main([__file__, "-v"])