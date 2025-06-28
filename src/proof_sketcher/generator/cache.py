"""Caching layer for Claude generation responses."""

import json
import logging
import pickle
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, Optional, Union

from .models import CacheEntry, GenerationRequest, GenerationResponse


class CacheError(Exception):
    """Base exception for cache-related errors."""

    pass


class CacheManager:
    """Manages caching of Claude generation responses."""

    def __init__(
        self,
        cache_dir: Optional[Path] = None,
        max_cache_size_mb: int = 100,
        cleanup_interval_hours: int = 24,
    ):
        """Initialize the cache manager.

        Args:
            cache_dir: Directory for cache storage. Defaults to ~/.proof_sketcher/cache
            max_cache_size_mb: Maximum cache size in MB
            cleanup_interval_hours: How often to run cleanup (in hours)
        """
        self.cache_dir = cache_dir or self._get_default_cache_dir()
        self.max_cache_size_mb = max_cache_size_mb
        self.cleanup_interval_hours = cleanup_interval_hours
        self.logger = logging.getLogger(__name__)

        # Ensure cache directory exists
        self.cache_dir.mkdir(parents=True, exist_ok=True)

        # Create subdirectories for different cache types
        self.json_cache_dir = self.cache_dir / "json"
        self.pickle_cache_dir = self.cache_dir / "pickle"
        self.metadata_file = self.cache_dir / "metadata.json"

        self.json_cache_dir.mkdir(exist_ok=True)
        self.pickle_cache_dir.mkdir(exist_ok=True)

        # Load metadata
        self._metadata = self._load_metadata()

        # Schedule cleanup if needed
        self._maybe_cleanup()

    def get(self, cache_key: str) -> Optional[GenerationResponse]:
        """Get a cached response by key.

        Args:
            cache_key: Cache key to look up

        Returns:
            Cached response if found and not expired, None otherwise
        """
        try:
            # Try JSON cache first (faster)
            json_path = self.json_cache_dir / f"{cache_key}.json"
            if json_path.exists():
                entry = self._load_json_entry(json_path)
                if entry and not entry.is_expired:
                    self.logger.debug(f"Cache hit (JSON): {cache_key}")
                    return entry.response
                elif entry and entry.is_expired:
                    self.logger.debug(f"Cache expired: {cache_key}")
                    self._delete_entry(cache_key)

            # Try pickle cache (fallback for complex objects)
            pickle_path = self.pickle_cache_dir / f"{cache_key}.pkl"
            if pickle_path.exists():
                entry = self._load_pickle_entry(pickle_path)
                if entry and not entry.is_expired:
                    self.logger.debug(f"Cache hit (pickle): {cache_key}")
                    return entry.response
                elif entry and entry.is_expired:
                    self.logger.debug(f"Cache expired: {cache_key}")
                    self._delete_entry(cache_key)

            self.logger.debug(f"Cache miss: {cache_key}")
            return None

        except Exception as e:
            self.logger.warning(f"Error reading cache entry {cache_key}: {e}")
            return None

    def put(
        self,
        cache_key: str,
        response: GenerationResponse,
        ttl_hours: Optional[int] = None,
    ) -> bool:
        """Store a response in cache.

        Args:
            cache_key: Cache key to store under
            response: Response to cache
            ttl_hours: TTL in hours (uses config default if None)

        Returns:
            True if successfully cached, False otherwise
        """
        try:
            ttl = ttl_hours or response.request.config.cache_ttl_hours

            entry = CacheEntry(cache_key=cache_key, response=response, ttl_hours=ttl)

            # Try to store as JSON first (more portable)
            try:
                json_path = self.json_cache_dir / f"{cache_key}.json"
                self._save_json_entry(json_path, entry)
                self.logger.debug(f"Cached as JSON: {cache_key}")
                stored = True
            except (TypeError, ValueError) as e:
                # Fall back to pickle for complex objects
                self.logger.debug(f"JSON serialization failed, using pickle: {e}")
                pickle_path = self.pickle_cache_dir / f"{cache_key}.pkl"
                self._save_pickle_entry(pickle_path, entry)
                self.logger.debug(f"Cached as pickle: {cache_key}")
                stored = True

            if stored:
                # Update metadata
                self._metadata[cache_key] = {
                    "cached_at": entry.cached_at.isoformat(),
                    "ttl_hours": ttl,
                    "generation_type": response.request.generation_type.value,
                    "theorem_name": response.request.theorem_name,
                }
                self._save_metadata()

                # Check cache size and cleanup if needed
                self._maybe_cleanup()

                return True

        except Exception as e:
            self.logger.error(f"Error caching response {cache_key}: {e}")
            return False

    def delete(self, cache_key: str) -> bool:
        """Delete a cache entry.

        Args:
            cache_key: Cache key to delete

        Returns:
            True if deleted, False if not found
        """
        return self._delete_entry(cache_key)

    def clear(self) -> int:
        """Clear all cache entries.

        Returns:
            Number of entries cleared
        """
        count = 0

        # Clear JSON cache
        for json_file in self.json_cache_dir.glob("*.json"):
            json_file.unlink()
            count += 1

        # Clear pickle cache
        for pickle_file in self.pickle_cache_dir.glob("*.pkl"):
            pickle_file.unlink()
            count += 1

        # Clear metadata
        self._metadata.clear()
        self._save_metadata()

        self.logger.info(f"Cleared {count} cache entries")
        return count

    def cleanup_expired(self) -> int:
        """Remove expired cache entries.

        Returns:
            Number of entries removed
        """
        removed_count = 0
        expired_keys = []

        # Check all entries in metadata
        for cache_key, meta in self._metadata.items():
            try:
                cached_at = datetime.fromisoformat(meta["cached_at"])
                ttl_hours = meta["ttl_hours"]
                expiry_time = cached_at + timedelta(hours=ttl_hours)

                if datetime.now() > expiry_time:
                    expired_keys.append(cache_key)
            except (KeyError, ValueError) as e:
                self.logger.warning(f"Invalid metadata for {cache_key}: {e}")
                expired_keys.append(cache_key)

        # Remove expired entries
        for cache_key in expired_keys:
            if self._delete_entry(cache_key):
                removed_count += 1

        if removed_count > 0:
            self.logger.info(f"Cleaned up {removed_count} expired cache entries")

        return removed_count

    def get_cache_size_mb(self) -> float:
        """Get current cache size in MB.

        Returns:
            Cache size in megabytes
        """
        total_size = 0

        for cache_file in self.cache_dir.rglob("*"):
            if cache_file.is_file():
                total_size += cache_file.stat().st_size

        return total_size / (1024 * 1024)

    def get_cache_stats(self) -> Dict[str, Union[int, float, str]]:
        """Get cache statistics.

        Returns:
            Dictionary with cache statistics
        """
        stats = {
            "total_entries": len(self._metadata),
            "size_mb": round(self.get_cache_size_mb(), 2),
            "max_size_mb": self.max_cache_size_mb,
            "cache_dir": str(self.cache_dir),
            "json_entries": len(list(self.json_cache_dir.glob("*.json"))),
            "pickle_entries": len(list(self.pickle_cache_dir.glob("*.pkl"))),
        }

        # Count by generation type
        type_counts = {}
        for meta in self._metadata.values():
            gen_type = meta.get("generation_type", "unknown")
            type_counts[gen_type] = type_counts.get(gen_type, 0) + 1

        stats["by_type"] = type_counts

        return stats

    def _get_default_cache_dir(self) -> Path:
        """Get default cache directory."""
        home = Path.home()
        return home / ".proof_sketcher" / "cache"

    def _load_metadata(self) -> Dict[str, Dict]:
        """Load cache metadata."""
        if self.metadata_file.exists():
            try:
                with open(self.metadata_file, "r") as f:
                    return json.load(f)
            except Exception as e:
                self.logger.warning(f"Failed to load cache metadata: {e}")

        return {}

    def _save_metadata(self) -> None:
        """Save cache metadata."""
        try:
            with open(self.metadata_file, "w") as f:
                json.dump(self._metadata, f, indent=2)
        except Exception as e:
            self.logger.error(f"Failed to save cache metadata: {e}")

    def _load_json_entry(self, path: Path) -> Optional[CacheEntry]:
        """Load a cache entry from JSON file."""
        try:
            with open(path, "r") as f:
                data = json.load(f)

            # Reconstruct the entry
            return CacheEntry(**data)

        except Exception as e:
            self.logger.warning(f"Failed to load JSON cache entry {path}: {e}")
            return None

    def _save_json_entry(self, path: Path, entry: CacheEntry) -> None:
        """Save a cache entry as JSON file."""
        with open(path, "w") as f:
            json.dump(entry.dict(), f, indent=2, default=str)

    def _load_pickle_entry(self, path: Path) -> Optional[CacheEntry]:
        """Load a cache entry from pickle file."""
        try:
            with open(path, "rb") as f:
                return pickle.load(f)
        except Exception as e:
            self.logger.warning(f"Failed to load pickle cache entry {path}: {e}")
            return None

    def _save_pickle_entry(self, path: Path, entry: CacheEntry) -> None:
        """Save a cache entry as pickle file."""
        with open(path, "wb") as f:
            pickle.dump(entry, f)

    def _delete_entry(self, cache_key: str) -> bool:
        """Delete a cache entry and its metadata."""
        deleted = False

        # Remove JSON file
        json_path = self.json_cache_dir / f"{cache_key}.json"
        if json_path.exists():
            json_path.unlink()
            deleted = True

        # Remove pickle file
        pickle_path = self.pickle_cache_dir / f"{cache_key}.pkl"
        if pickle_path.exists():
            pickle_path.unlink()
            deleted = True

        # Remove from metadata
        if cache_key in self._metadata:
            del self._metadata[cache_key]
            self._save_metadata()
            deleted = True

        return deleted

    def _maybe_cleanup(self) -> None:
        """Run cleanup if needed based on size or time."""
        # Check if we need size-based cleanup
        current_size = self.get_cache_size_mb()
        if current_size > self.max_cache_size_mb:
            self.logger.info(
                f"Cache size ({current_size:.1f}MB) exceeds limit ({self.max_cache_size_mb}MB)"
            )
            self._cleanup_by_size()

        # Check if we need time-based cleanup
        last_cleanup_file = self.cache_dir / ".last_cleanup"
        should_cleanup = True

        if last_cleanup_file.exists():
            try:
                last_cleanup = datetime.fromtimestamp(last_cleanup_file.stat().st_mtime)
                next_cleanup = last_cleanup + timedelta(
                    hours=self.cleanup_interval_hours
                )
                should_cleanup = datetime.now() > next_cleanup
            except Exception:
                pass

        if should_cleanup:
            expired_count = self.cleanup_expired()
            if expired_count > 0:
                # Update cleanup timestamp
                last_cleanup_file.touch()

    def _cleanup_by_size(self) -> None:
        """Remove oldest entries until under size limit."""
        # Sort entries by age (oldest first)
        entries_by_age = []
        for cache_key, meta in self._metadata.items():
            try:
                cached_at = datetime.fromisoformat(meta["cached_at"])
                entries_by_age.append((cached_at, cache_key))
            except (KeyError, ValueError):
                # Invalid metadata - mark for deletion
                entries_by_age.append((datetime.min, cache_key))

        entries_by_age.sort()

        # Remove oldest entries until under limit
        removed_count = 0
        for _, cache_key in entries_by_age:
            if (
                self.get_cache_size_mb() <= self.max_cache_size_mb * 0.8
            ):  # Leave some buffer
                break

            if self._delete_entry(cache_key):
                removed_count += 1

        if removed_count > 0:
            self.logger.info(
                f"Removed {removed_count} old entries to stay under size limit"
            )


class CachedClaudeGenerator:
    """Wrapper around ClaudeGenerator that adds caching."""

    def __init__(
        self,
        generator,  # ClaudeGenerator instance
        cache_manager: Optional[CacheManager] = None,
    ):
        """Initialize cached generator.

        Args:
            generator: ClaudeGenerator instance
            cache_manager: Cache manager (creates default if None)
        """
        self.generator = generator
        self.cache = cache_manager or CacheManager()
        self.logger = logging.getLogger(__name__)

    def generate_proof_sketch(self, theorem, config=None, mathematical_context=None):
        """Generate proof sketch with caching."""
        return self._generate_with_cache(
            lambda: self.generator.generate_proof_sketch(
                theorem, config, mathematical_context
            ),
            theorem,
            "proof_sketch",
            config,
            mathematical_context,
        )

    def generate_eli5_explanation(
        self, theorem, config=None, mathematical_context=None
    ):
        """Generate ELI5 explanation with caching."""
        return self._generate_with_cache(
            lambda: self.generator.generate_eli5_explanation(
                theorem, config, mathematical_context
            ),
            theorem,
            "eli5_explanation",
            config,
            mathematical_context,
        )

    def generate_tactic_explanation(
        self, theorem, config=None, mathematical_context=None
    ):
        """Generate tactic explanation with caching."""
        return self._generate_with_cache(
            lambda: self.generator.generate_tactic_explanation(
                theorem, config, mathematical_context
            ),
            theorem,
            "tactic_explanation",
            config,
            mathematical_context,
        )

    def generate_step_by_step(self, theorem, config=None, mathematical_context=None):
        """Generate step-by-step explanation with caching."""
        return self._generate_with_cache(
            lambda: self.generator.generate_step_by_step(
                theorem, config, mathematical_context
            ),
            theorem,
            "step_by_step",
            config,
            mathematical_context,
        )

    def _generate_with_cache(
        self, generator_func, theorem, generation_type, config, mathematical_context
    ):
        """Generate with caching support."""
        config = config or self.generator.default_config

        if not config.cache_responses:
            # Caching disabled, call directly
            return generator_func()

        # Create cache key
        request = GenerationRequest(
            generation_type=generation_type,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
            mathematical_context=mathematical_context,
            config=config,
        )

        cache_key = request.get_cache_key()

        # Try to get from cache
        cached_response = self.cache.get(cache_key)
        if cached_response:
            self.logger.debug(f"Using cached response for {theorem.name}")
            return cached_response.content

        # Generate new response
        result = generator_func()

        # Cache the result if it's a GenerationResponse
        if hasattr(result, "request"):
            # It's a GenerationResponse, cache it directly
            self.cache.put(cache_key, result)
        else:
            # It's raw content, wrap it in a response
            response = GenerationResponse(request=request, content=result, success=True)
            self.cache.put(cache_key, response)

        return result

    def clear_cache(self):
        """Clear all cached responses."""
        return self.cache.clear()

    def get_cache_stats(self):
        """Get cache statistics."""
        return self.cache.get_cache_stats()

    def __getattr__(self, name):
        """Delegate other methods to the underlying generator."""
        return getattr(self.generator, name)
