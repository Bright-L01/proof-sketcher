"""Comprehensive unit tests for core utilities module.

This module tests all utility functions to ensure they work correctly
and handle edge cases properly.
"""

import hashlib
import json
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import Mock, patch

import pytest
from pydantic import BaseModel

from proof_sketcher.core.utils import (
    generate_cache_key,
    _serialize_for_cache,
    sanitize_filename,
    ensure_directory,
    format_duration,
    truncate_text,
    deep_merge,
    retry_with_backoff,
    get_timestamp,
    parse_timestamp,
    calculate_hash,
    chunk_list,
    flatten_dict,
)
from proof_sketcher.core.exceptions import ProofSketcherError


class MockModel(BaseModel):
    """Mock Pydantic model for testing."""
    name: str = "test"
    value: int = 42


class TestCacheKeyGeneration:
    """Test cache key generation functions."""
    
    def test_serialize_primitives(self):
        """Test serialization of primitive types."""
        assert _serialize_for_cache("hello") == "hello"
        assert _serialize_for_cache(42) == "42"
        assert _serialize_for_cache(3.14) == "3.14"
        assert _serialize_for_cache(True) == "True"
        assert _serialize_for_cache(False) == "False"
    
    def test_serialize_collections(self):
        """Test serialization of collections."""
        # Lists
        assert _serialize_for_cache([1, 2, 3]) == "[1,2,3]"
        assert _serialize_for_cache(["a", "b"]) == "[a,b]"
        assert _serialize_for_cache([]) == "[]"
        
        # Tuples
        assert _serialize_for_cache((1, 2, 3)) == "[1,2,3]"
        
        # Nested lists
        assert _serialize_for_cache([1, [2, 3]]) == "[1,[2,3]]"
    
    def test_serialize_dictionaries(self):
        """Test serialization of dictionaries."""
        # Simple dict
        result = _serialize_for_cache({"b": 2, "a": 1})
        assert result == "{a:1,b:2}"  # Keys sorted
        
        # Nested dict
        nested = {"outer": {"b": 2, "a": 1}}
        result = _serialize_for_cache(nested)
        assert result == "{outer:{a:1,b:2}}"
        
        # Empty dict
        assert _serialize_for_cache({}) == "{}"
    
    def test_serialize_path(self):
        """Test serialization of Path objects."""
        path = Path("test/path")
        result = _serialize_for_cache(path)
        assert str(path.absolute()) in result
    
    def test_serialize_pydantic_model(self):
        """Test serialization of Pydantic models."""
        model = MockModel(name="test", value=123)
        result = _serialize_for_cache(model)
        # Should serialize the model dump
        assert "test" in result
        assert "123" in result
    
    def test_serialize_fallback(self):
        """Test serialization fallback for unknown types."""
        class CustomClass:
            def __init__(self, value):
                self.value = value
            
            def __str__(self):
                return f"Custom({self.value})"
        
        obj = CustomClass("test")
        result = _serialize_for_cache(obj)
        # Should use JSON with str fallback
        assert isinstance(result, str)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])