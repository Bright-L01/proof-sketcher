"""Tests for generator caching functionality."""

import json
import tempfile
from datetime import datetime, timedelta
from pathlib import Path
from unittest.mock import Mock

from proof_sketcher.generator.cache import CachedClaudeGenerator, CacheManager
from proof_sketcher.generator.models import (
    CacheEntry,
    GenerationConfig,
    GenerationRequest,
    GenerationResponse,
    GenerationType,
)
from proof_sketcher.parser.models import TheoremInfo


class TestCacheManager:
    """Tests for CacheManager class."""

    def test_cache_manager_initialization(self):
        """Test cache manager initialization."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"

            cache = CacheManager(cache_dir=cache_dir, max_cache_size_mb=50)

            assert cache.cache_dir == cache_dir
            assert cache.max_cache_size_mb == 50
            assert cache.cache_dir.exists()
            assert cache.json_cache_dir.exists()
            assert cache.pickle_cache_dir.exists()

    def test_cache_put_and_get_json(self):
        """Test caching with JSON serialization."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)

            # Create test response
            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test_theorem",
                theorem_statement="P → Q",
            )

            response = GenerationResponse(
                request=request, content="This is a simple explanation.", success=True
            )

            cache_key = "test_key_123"

            # Put in cache
            success = cache.put(cache_key, response, ttl_hours=12)
            assert success is True

            # Get from cache
            cached_response = cache.get(cache_key)
            assert cached_response is not None
            assert cached_response.content == "This is a simple explanation."
            assert cached_response.success is True
            assert cached_response.request.theorem_name == "test_theorem"

    def test_cache_expiry(self):
        """Test cache entry expiry."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)

            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test",
                theorem_statement="P",
            )

            response = GenerationResponse(
                request=request, content="Test content", success=True
            )

            cache_key = "expired_key"

            # Create expired entry manually
            expired_time = datetime.now() - timedelta(hours=25)
            entry = CacheEntry(
                cache_key=cache_key,
                response=response,
                cached_at=expired_time,
                ttl_hours=24,
            )

            # Save entry
            json_path = cache.json_cache_dir / f"{cache_key}.json"
            with open(json_path, "w") as f:
                json.dump(entry.dict(), f, default=str)

            cache._metadata[cache_key] = {
                "cached_at": expired_time.isoformat(),
                "ttl_hours": 24,
                "generation_type": "eli5_explanation",
                "theorem_name": "test",
            }

            # Try to get expired entry
            cached_response = cache.get(cache_key)
            assert cached_response is None  # Should be None because it's expired

            # Entry should be cleaned up
            assert not json_path.exists()

    def test_cache_miss(self):
        """Test cache miss scenario."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)

            cached_response = cache.get("nonexistent_key")
            assert cached_response is None

    def test_cache_delete(self):
        """Test cache entry deletion."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)

            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test",
                theorem_statement="P",
            )

            response = GenerationResponse(
                request=request, content="Test content", success=True
            )

            cache_key = "delete_test"

            # Put and verify
            cache.put(cache_key, response)
            assert cache.get(cache_key) is not None

            # Delete and verify
            deleted = cache.delete(cache_key)
            assert deleted is True
            assert cache.get(cache_key) is None

            # Try to delete again
            deleted_again = cache.delete(cache_key)
            assert deleted_again is False

    def test_cache_clear(self):
        """Test clearing all cache entries."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)

            # Add multiple entries
            for i in range(3):
                request = GenerationRequest(
                    generation_type=GenerationType.ELI5_EXPLANATION,
                    theorem_name=f"test_{i}",
                    theorem_statement="P",
                )

                response = GenerationResponse(
                    request=request, content=f"Content {i}", success=True
                )

                cache.put(f"key_{i}", response)

            # Verify entries exist
            assert cache.get("key_0") is not None
            assert cache.get("key_1") is not None
            assert cache.get("key_2") is not None

            # Clear cache
            cleared_count = cache.clear()
            assert cleared_count == 3

            # Verify entries are gone
            assert cache.get("key_0") is None
            assert cache.get("key_1") is None
            assert cache.get("key_2") is None

    def test_cleanup_expired(self):
        """Test cleanup of expired entries."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)

            # Add fresh entry
            fresh_request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="fresh",
                theorem_statement="P",
            )

            fresh_response = GenerationResponse(
                request=fresh_request, content="Fresh content", success=True
            )

            cache.put("fresh_key", fresh_response, ttl_hours=24)

            # Add expired entry manually
            expired_request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="expired",
                theorem_statement="P",
            )

            expired_response = GenerationResponse(
                request=expired_request, content="Expired content", success=True
            )

            expired_time = datetime.now() - timedelta(hours=25)
            expired_entry = CacheEntry(
                cache_key="expired_key",
                response=expired_response,
                cached_at=expired_time,
                ttl_hours=24,
            )

            # Manually save expired entry
            json_path = cache.json_cache_dir / "expired_key.json"
            with open(json_path, "w") as f:
                json.dump(expired_entry.dict(), f, default=str)

            cache._metadata["expired_key"] = {
                "cached_at": expired_time.isoformat(),
                "ttl_hours": 24,
                "generation_type": "eli5_explanation",
                "theorem_name": "expired",
            }

            # Run cleanup
            removed_count = cache.cleanup_expired()
            assert removed_count == 1

            # Verify fresh entry still exists, expired is gone
            assert cache.get("fresh_key") is not None
            assert cache.get("expired_key") is None

    def test_cache_stats(self):
        """Test cache statistics."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir, max_cache_size_mb=100)

            # Add some entries
            for i in range(2):
                request = GenerationRequest(
                    generation_type=(
                        GenerationType.ELI5_EXPLANATION
                        if i == 0
                        else GenerationType.PROOF_SKETCH
                    ),
                    theorem_name=f"test_{i}",
                    theorem_statement="P",
                )

                response = GenerationResponse(
                    request=request, content=f"Content {i}", success=True
                )

                cache.put(f"key_{i}", response)

            stats = cache.get_cache_stats()

            assert stats["total_entries"] == 2
            assert stats["max_size_mb"] == 100
            assert stats["cache_dir"] == str(cache_dir)
            assert "size_mb" in stats
            assert "json_entries" in stats
            assert "pickle_entries" in stats
            assert "by_type" in stats

            # Check type distribution
            assert stats["by_type"]["eli5_explanation"] == 1
            assert stats["by_type"]["proof_sketch"] == 1


class TestCachedClaudeGenerator:
    """Tests for CachedClaudeGenerator wrapper."""

    def test_cached_generator_initialization(self):
        """Test cached generator initialization."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig()

        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)

            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)

            assert cached_gen.generator == mock_generator
            assert cached_gen.cache == cache_manager

    def test_generate_with_cache_hit(self):
        """Test generation with cache hit."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig()

        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)

            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)

            theorem = TheoremInfo(name="test_theorem", statement="∀ n : Nat, n + 0 = n")

            # First call - should call generator and cache result
            mock_generator.generate_eli5_explanation.return_value = (
                "Generated explanation"
            )

            result1 = cached_gen.generate_eli5_explanation(theorem)
            assert result1 == "Generated explanation"
            assert mock_generator.generate_eli5_explanation.call_count == 1

            # Second call - should use cache
            result2 = cached_gen.generate_eli5_explanation(theorem)
            assert result2 == "Generated explanation"
            assert (
                mock_generator.generate_eli5_explanation.call_count == 1
            )  # Not called again

    def test_generate_with_caching_disabled(self):
        """Test generation with caching disabled."""
        mock_generator = Mock()
        config = GenerationConfig(cache_responses=False)
        mock_generator.default_config = config

        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)

            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)

            theorem = TheoremInfo(name="test_theorem", statement="∀ n : Nat, n + 0 = n")

            mock_generator.generate_eli5_explanation.return_value = (
                "Generated explanation"
            )

            # Multiple calls should all hit the generator
            result1 = cached_gen.generate_eli5_explanation(theorem, config)
            result2 = cached_gen.generate_eli5_explanation(theorem, config)

            assert result1 == "Generated explanation"
            assert result2 == "Generated explanation"
            assert mock_generator.generate_eli5_explanation.call_count == 2

    def test_method_delegation(self):
        """Test that non-generation methods are delegated to the underlying generator."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig()
        mock_generator.check_claude_available.return_value = True
        mock_generator.get_claude_version.return_value = "1.0.0"

        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)

            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)

            # Test method delegation
            assert cached_gen.check_claude_available() is True
            assert cached_gen.get_claude_version() == "1.0.0"

            mock_generator.check_claude_available.assert_called_once()
            mock_generator.get_claude_version.assert_called_once()

    def test_cache_management_methods(self):
        """Test cache management methods."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig()

        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)

            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)

            # Test clear cache
            cleared = cached_gen.clear_cache()
            assert cleared == 0  # No entries to clear

            # Test get cache stats
            stats = cached_gen.get_cache_stats()
            assert isinstance(stats, dict)
            assert "total_entries" in stats
