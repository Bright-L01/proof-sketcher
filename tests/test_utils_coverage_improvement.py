"""Additional tests to improve utils.py coverage to 100%."""

import json
from unittest.mock import Mock

from proof_sketcher.core.utils import _serialize_for_cache


class TestUtilsCoverageImprovement:
    """Test cases to cover the remaining uncovered lines in utils.py."""

    def test_serialize_for_cache_json_fallback(self):
        """Test JSON fallback in _serialize_for_cache (line 66)."""
        # Create an object that doesn't match any of the specific type checks
        # but is JSON serializable
        class CustomObject:
            def __init__(self):
                self.value = "test"
                
            def __str__(self):
                return f"CustomObject(value={self.value})"
        
        obj = CustomObject()
        result = _serialize_for_cache(obj)
        
        # Should use JSON fallback with default=str
        # The exact format may vary, but it should contain the string representation
        assert "CustomObject" in result
        assert "test" in result
        
    def test_serialize_for_cache_complex_object(self):
        """Test serialization of a complex object that requires JSON fallback."""
        # Use a set, which is not handled by the specific type checks
        obj = {1, 2, 3}
        result = _serialize_for_cache(obj)
        
        # Should serialize using JSON
        # Sets are not directly JSON serializable, so default=str will be used
        assert isinstance(result, str)
        # The string representation of a set
        assert "{" in result and "}" in result

    # Note: Line 231 in retry_with_backoff is unreachable code
    # It's a defensive "raise last_exception" after the loop that already
    # handles all cases. This is good defensive programming and doesn't
    # need to be covered.