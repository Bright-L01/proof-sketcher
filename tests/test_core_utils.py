"""Comprehensive tests for core utility functions."""

import hashlib
import json
import time
from datetime import datetime, timezone
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.core.utils import (
    calculate_hash,
    chunk_list,
    deep_merge,
    ensure_directory,
    flatten_dict,
    format_duration,
    generate_cache_key,
    get_timestamp,
    parse_timestamp,
    retry_with_backoff,
    sanitize_filename,
    truncate_text,
)


class TestGenerateCacheKey:
    """Test cache key generation."""

    def test_generate_cache_key_with_args(self):
        """Test cache key generation with positional arguments."""
        key1 = generate_cache_key("test", 123, True)
        key2 = generate_cache_key("test", 123, True)
        key3 = generate_cache_key("test", 123, False)
        
        assert key1 == key2  # Same inputs produce same key
        assert key1 != key3  # Different inputs produce different key
        assert len(key1) == 64  # SHA256 produces 64 char hex

    def test_generate_cache_key_with_kwargs(self):
        """Test cache key generation with keyword arguments."""
        key1 = generate_cache_key(name="test", value=123, enabled=True)
        key2 = generate_cache_key(value=123, name="test", enabled=True)  # Different order
        key3 = generate_cache_key(name="test", value=456, enabled=True)
        
        assert key1 == key2  # Order doesn't matter for kwargs
        assert key1 != key3  # Different values produce different key

    def test_generate_cache_key_mixed(self):
        """Test cache key generation with mixed arguments."""
        key = generate_cache_key("prefix", 42, suffix="test", active=True)
        assert isinstance(key, str)
        assert len(key) == 64

    def test_generate_cache_key_with_complex_types(self):
        """Test cache key generation with complex types."""
        key1 = generate_cache_key(
            ["a", "b", "c"],
            {"x": 1, "y": 2},
            path=Path("/test/path")
        )
        key2 = generate_cache_key(
            ["a", "b", "c"],
            {"y": 2, "x": 1},  # Different dict order
            path=Path("/test/path")
        )
        assert key1 == key2  # Dict ordering doesn't affect key

    def test_generate_cache_key_with_pydantic_model(self):
        """Test cache key generation with Pydantic models."""
        from pydantic import BaseModel
        
        class TestModel(BaseModel):
            name: str
            value: int
            
        model = TestModel(name="test", value=42)
        key = generate_cache_key(model)
        assert isinstance(key, str)
        assert len(key) == 64


class TestSanitizeFilename:
    """Test filename sanitization."""

    def test_sanitize_basic(self):
        """Test basic filename sanitization."""
        assert sanitize_filename("test.txt") == "test.txt"
        assert sanitize_filename("Test File.pdf") == "Test File.pdf"
        
    def test_sanitize_invalid_chars(self):
        """Test removal of invalid characters."""
        assert sanitize_filename("test<>file.txt") == "test__file.txt"
        assert sanitize_filename('test:"file".txt') == "test__file_.txt"
        assert sanitize_filename("test/file\\name.txt") == "test_file_name.txt"
        assert sanitize_filename("test|file*?.txt") == "test_file__.txt"
        
    def test_sanitize_unicode(self):
        """Test Unicode normalization."""
        assert sanitize_filename("café.txt") == "cafe.txt"
        assert sanitize_filename("naïve.txt") == "naive.txt"
        
    def test_sanitize_spaces_dots(self):
        """Test handling of spaces and dots."""
        assert sanitize_filename(" test.txt ") == "test.txt"
        assert sanitize_filename("..test..") == "test"
        assert sanitize_filename(".hidden") == "hidden"
        
    def test_sanitize_max_length(self):
        """Test filename truncation."""
        long_name = "a" * 300 + ".txt"
        result = sanitize_filename(long_name, max_length=255)
        assert len(result) == 255
        assert result.endswith(".txt")
        
        # Without extension
        long_name = "b" * 300
        result = sanitize_filename(long_name, max_length=100)
        assert len(result) == 100
        
    def test_sanitize_empty(self):
        """Test empty filename handling."""
        assert sanitize_filename("") == "unnamed"
        assert sanitize_filename("   ") == "unnamed"
        assert sanitize_filename("...") == "unnamed"


class TestEnsureDirectory:
    """Test directory creation."""

    def test_ensure_directory_new(self, tmp_path):
        """Test creating a new directory."""
        test_dir = tmp_path / "new" / "nested" / "dir"
        assert not test_dir.exists()
        
        result = ensure_directory(test_dir)
        assert result == test_dir
        assert test_dir.exists()
        assert test_dir.is_dir()
        
    def test_ensure_directory_existing(self, tmp_path):
        """Test with existing directory."""
        result = ensure_directory(tmp_path)
        assert result == tmp_path
        assert tmp_path.exists()
        
    def test_ensure_directory_string_path(self, tmp_path):
        """Test with string path."""
        test_dir = str(tmp_path / "string_dir")
        result = ensure_directory(test_dir)
        assert Path(result).exists()
        assert isinstance(result, Path)


class TestFormatDuration:
    """Test duration formatting."""

    def test_format_milliseconds(self):
        """Test formatting sub-second durations."""
        assert format_duration(0.001) == "1ms"
        assert format_duration(0.999) == "999ms"
        assert format_duration(0.5) == "500ms"
        
    def test_format_seconds(self):
        """Test formatting seconds."""
        assert format_duration(1.0) == "1.0s"
        assert format_duration(59.9) == "59.9s"
        assert format_duration(30.5) == "30.5s"
        
    def test_format_minutes(self):
        """Test formatting minutes."""
        assert format_duration(60) == "1m 0s"
        assert format_duration(90) == "1m 30s"
        assert format_duration(3599) == "59m 59s"
        
    def test_format_hours(self):
        """Test formatting hours."""
        assert format_duration(3600) == "1h 0m"
        assert format_duration(7200) == "2h 0m"
        assert format_duration(3661) == "1h 1m"
        assert format_duration(7890) == "2h 11m"


class TestTruncateText:
    """Test text truncation."""

    def test_truncate_short_text(self):
        """Test text that doesn't need truncation."""
        assert truncate_text("short", 10) == "short"
        assert truncate_text("exact", 5) == "exact"
        
    def test_truncate_long_text(self):
        """Test text truncation."""
        assert truncate_text("This is a long text", 10) == "This is..."
        assert truncate_text("Hello world", 8) == "Hello..."
        
    def test_truncate_custom_suffix(self):
        """Test custom suffix."""
        assert truncate_text("Long text here", 10, suffix=" [...]") == "Long [...]"
        assert truncate_text("Test", 10, suffix=" [more]") == "Test"
        
    def test_truncate_edge_cases(self):
        """Test edge cases."""
        assert truncate_text("test", 3, suffix="...") == "..."
        assert truncate_text("test", 2, suffix="...") == ".."
        assert truncate_text("", 10) == ""


class TestDeepMerge:
    """Test deep dictionary merging."""

    def test_deep_merge_simple(self):
        """Test simple dictionary merge."""
        base = {"a": 1, "b": 2}
        update = {"b": 3, "c": 4}
        result = deep_merge(base, update)
        
        assert result == {"a": 1, "b": 3, "c": 4}
        assert base == {"a": 1, "b": 2}  # Original unchanged
        
    def test_deep_merge_nested(self):
        """Test nested dictionary merge."""
        base = {
            "level1": {
                "level2": {"a": 1, "b": 2},
                "other": "value"
            }
        }
        update = {
            "level1": {
                "level2": {"b": 3, "c": 4}
            }
        }
        result = deep_merge(base, update)
        
        assert result == {
            "level1": {
                "level2": {"a": 1, "b": 3, "c": 4},
                "other": "value"
            }
        }
        
    def test_deep_merge_overwrites_non_dict(self):
        """Test that non-dict values are overwritten."""
        base = {"a": {"b": 2}, "c": [1, 2, 3]}
        update = {"a": "string", "c": [4, 5]}
        result = deep_merge(base, update)
        
        assert result == {"a": "string", "c": [4, 5]}


class TestRetryWithBackoff:
    """Test retry with exponential backoff."""

    def test_retry_success_first_try(self):
        """Test successful execution on first try."""
        mock_func = Mock(return_value="success")
        result = retry_with_backoff(mock_func)
        
        assert result == "success"
        assert mock_func.call_count == 1
        
    def test_retry_success_after_failures(self):
        """Test success after some failures."""
        mock_func = Mock(side_effect=[Exception("fail"), Exception("fail"), "success"])
        
        with patch("time.sleep") as mock_sleep:
            result = retry_with_backoff(mock_func, max_retries=3, base_delay=0.1)
            
        assert result == "success"
        assert mock_func.call_count == 3
        assert mock_sleep.call_count == 2
        
    def test_retry_all_failures(self):
        """Test when all retries fail."""
        mock_func = Mock(side_effect=Exception("always fails"))
        
        with patch("time.sleep"):
            with pytest.raises(Exception, match="always fails"):
                retry_with_backoff(mock_func, max_retries=2)
                
        assert mock_func.call_count == 3  # Initial + 2 retries
        
    def test_retry_exponential_backoff(self):
        """Test exponential backoff delays."""
        mock_func = Mock(side_effect=[Exception(), Exception(), Exception(), "success"])
        
        with patch("time.sleep") as mock_sleep:
            retry_with_backoff(
                mock_func,
                max_retries=3,
                base_delay=1.0,
                exponential_base=2.0
            )
            
        sleep_calls = [call[0][0] for call in mock_sleep.call_args_list]
        assert sleep_calls == [1.0, 2.0, 4.0]
        
    def test_retry_max_delay(self):
        """Test maximum delay limit."""
        mock_func = Mock(side_effect=[Exception(), Exception(), "success"])
        
        with patch("time.sleep") as mock_sleep:
            retry_with_backoff(
                mock_func,
                max_retries=2,
                base_delay=10.0,
                max_delay=15.0,
                exponential_base=2.0
            )
            
        sleep_calls = [call[0][0] for call in mock_sleep.call_args_list]
        assert sleep_calls == [10.0, 15.0]  # Second delay capped at max
        
    def test_retry_specific_exceptions(self):
        """Test retrying only specific exceptions."""
        mock_func = Mock(side_effect=[ValueError(), TypeError(), "success"])
        
        # Should retry ValueError but not TypeError
        with pytest.raises(TypeError):
            retry_with_backoff(
                mock_func,
                max_retries=3,
                exceptions=(ValueError,)
            )
            
        assert mock_func.call_count == 2  # Stopped at TypeError


class TestTimestampFunctions:
    """Test timestamp functions."""

    def test_get_timestamp(self):
        """Test getting current timestamp."""
        before = datetime.now(timezone.utc)
        timestamp = get_timestamp()
        after = datetime.now(timezone.utc)
        
        parsed = datetime.fromisoformat(timestamp)
        assert before <= parsed <= after
        assert parsed.tzinfo is not None
        
    def test_parse_timestamp(self):
        """Test parsing timestamps."""
        # ISO format with timezone
        dt = parse_timestamp("2023-12-25T10:30:00+00:00")
        assert dt.year == 2023
        assert dt.month == 12
        assert dt.day == 25
        assert dt.hour == 10
        assert dt.minute == 30
        
        # With Z suffix
        dt = parse_timestamp("2023-12-25T10:30:00Z")
        assert dt.tzinfo is not None
        
    def test_timestamp_round_trip(self):
        """Test timestamp serialization round trip."""
        original = datetime(2023, 12, 25, 10, 30, 0, tzinfo=timezone.utc)
        timestamp = original.isoformat()
        parsed = parse_timestamp(timestamp)
        assert parsed == original


class TestCalculateHash:
    """Test hash calculation."""

    def test_calculate_hash_string(self):
        """Test hashing strings."""
        hash1 = calculate_hash("test")
        hash2 = calculate_hash("test")
        hash3 = calculate_hash("different")
        
        assert hash1 == hash2  # Same input produces same hash
        assert hash1 != hash3  # Different input produces different hash
        assert len(hash1) == 64  # SHA256 produces 64 char hex
        
    def test_calculate_hash_bytes(self):
        """Test hashing bytes."""
        hash1 = calculate_hash(b"test")
        hash2 = calculate_hash("test")
        assert hash1 == hash2  # String and bytes of same content match
        
    def test_calculate_hash_algorithms(self):
        """Test different hash algorithms."""
        data = "test data"
        sha256 = calculate_hash(data, "sha256")
        sha512 = calculate_hash(data, "sha512")
        md5 = calculate_hash(data, "md5")
        
        assert len(sha256) == 64
        assert len(sha512) == 128
        assert len(md5) == 32
        assert sha256 != sha512 != md5


class TestChunkList:
    """Test list chunking."""

    def test_chunk_list_even(self):
        """Test chunking with even division."""
        lst = [1, 2, 3, 4, 5, 6]
        chunks = chunk_list(lst, 2)
        assert chunks == [[1, 2], [3, 4], [5, 6]]
        
    def test_chunk_list_uneven(self):
        """Test chunking with remainder."""
        lst = [1, 2, 3, 4, 5]
        chunks = chunk_list(lst, 2)
        assert chunks == [[1, 2], [3, 4], [5]]
        
    def test_chunk_list_large_size(self):
        """Test chunk size larger than list."""
        lst = [1, 2, 3]
        chunks = chunk_list(lst, 10)
        assert chunks == [[1, 2, 3]]
        
    def test_chunk_list_single(self):
        """Test chunk size of 1."""
        lst = [1, 2, 3]
        chunks = chunk_list(lst, 1)
        assert chunks == [[1], [2], [3]]
        
    def test_chunk_list_empty(self):
        """Test empty list."""
        chunks = chunk_list([], 5)
        assert chunks == []


class TestFlattenDict:
    """Test dictionary flattening."""

    def test_flatten_dict_simple(self):
        """Test flattening simple dictionary."""
        d = {"a": 1, "b": 2, "c": 3}
        result = flatten_dict(d)
        assert result == {"a": 1, "b": 2, "c": 3}
        
    def test_flatten_dict_nested(self):
        """Test flattening nested dictionary."""
        d = {
            "level1": {
                "level2": {
                    "value": 42
                },
                "other": "test"
            },
            "top": "level"
        }
        result = flatten_dict(d)
        assert result == {
            "level1.level2.value": 42,
            "level1.other": "test",
            "top": "level"
        }
        
    def test_flatten_dict_custom_separator(self):
        """Test custom separator."""
        d = {"a": {"b": {"c": 1}}}
        result = flatten_dict(d, separator="/")
        assert result == {"a/b/c": 1}
        
    def test_flatten_dict_empty(self):
        """Test empty dictionary."""
        result = flatten_dict({})
        assert result == {}
        
    def test_flatten_dict_mixed_types(self):
        """Test with various value types."""
        d = {
            "str": "value",
            "int": 42,
            "list": [1, 2, 3],
            "nested": {"bool": True}
        }
        result = flatten_dict(d)
        assert result == {
            "str": "value",
            "int": 42,
            "list": [1, 2, 3],
            "nested.bool": True
        }