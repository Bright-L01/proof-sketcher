"""
Intelligent caching system with Redis backend - Milestone 3.2.1

This module provides a sophisticated caching layer with:
- Redis backend for distributed caching
- In-memory fallback for local development
- Intelligent cache invalidation
- Content-aware cache keys
- Performance monitoring
- TTL management with smart expiration
"""

import asyncio
import gzip
import hashlib
import json
import logging
import os

# SECURITY: Replace pickle with safe serialization
import tempfile
import threading
import time
from collections import OrderedDict
from dataclasses import asdict, dataclass
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Union

from ..utils.safe_serialization import SafeSerializer

try:
    import redis.asyncio as redis

    REDIS_AVAILABLE = True
except ImportError:
    REDIS_AVAILABLE = False

from ..generator.models import ProofSketch
from ..parser.models import TheoremInfo


@dataclass
class CacheEntry:
    """Cache entry with metadata."""

    key: str
    value: Any
    created_at: datetime
    last_accessed: datetime
    access_count: int
    ttl_seconds: int
    size_bytes: int
    tags: List[str] = None

    def is_expired(self) -> bool:
        """Check if cache entry is expired."""
        if self.ttl_seconds <= 0:
            return False
        return datetime.now() > self.created_at + timedelta(seconds=self.ttl_seconds)

    def update_access(self):
        """Update access statistics."""
        self.last_accessed = datetime.now()
        self.access_count += 1


class LRUCache:
    """Local LRU cache with size limits."""

    def __init__(self, max_size: int = 1000, max_memory_mb: int = 100):
        """Initialize LRU cache.

        Args:
            max_size: Maximum number of entries
            max_memory_mb: Maximum memory usage in MB
        """
        self.max_size = max_size
        self.max_memory_bytes = max_memory_mb * 1024 * 1024
        self.cache: OrderedDict[str, CacheEntry] = OrderedDict()
        self.current_memory = 0
        self.lock = threading.RLock()

    def get(self, key: str) -> Optional[Any]:
        """Get value from cache."""
        with self.lock:
            if key not in self.cache:
                return None

            entry = self.cache[key]

            # Check expiration
            if entry.is_expired():
                self._remove_entry(key)
                return None

            # Update access and move to end (most recently used)
            entry.update_access()
            self.cache.move_to_end(key)

            return entry.value

    def set(
        self, key: str, value: Any, ttl: int = 3600, tags: List[str] = None
    ) -> bool:
        """Set value in cache."""
        with self.lock:
            # SECURITY: Use safe serialization to estimate size
            try:
                with tempfile.NamedTemporaryFile(mode="w+b", delete=False) as tmp_file:
                    temp_path = Path(tmp_file.name)
                SafeSerializer.dump(value, temp_path, compress=False)
                size_bytes = temp_path.stat().st_size
                os.unlink(temp_path)
            except Exception:
                # Fallback size estimation
                size_bytes = len(str(value).encode("utf-8"))

            # Check if value is too large
            if size_bytes > self.max_memory_bytes:
                return False

            # Make room if needed
            self._make_room(size_bytes)

            # Create entry
            entry = CacheEntry(
                key=key,
                value=value,
                created_at=datetime.now(),
                last_accessed=datetime.now(),
                access_count=1,
                ttl_seconds=ttl,
                size_bytes=size_bytes,
                tags=tags or [],
            )

            # Remove old entry if exists
            if key in self.cache:
                self._remove_entry(key)

            # Add new entry
            self.cache[key] = entry
            self.current_memory += size_bytes

            return True

    def delete(self, key: str) -> bool:
        """Delete entry from cache."""
        with self.lock:
            if key in self.cache:
                self._remove_entry(key)
                return True
            return False

    def clear(self):
        """Clear all cache entries."""
        with self.lock:
            self.cache.clear()
            self.current_memory = 0

    def _remove_entry(self, key: str):
        """Remove entry and update memory tracking."""
        if key in self.cache:
            entry = self.cache.pop(key)
            self.current_memory -= entry.size_bytes

    def _make_room(self, needed_bytes: int):
        """Make room for new entry by evicting old ones."""
        # Remove expired entries first
        expired_keys = [key for key, entry in self.cache.items() if entry.is_expired()]
        for key in expired_keys:
            self._remove_entry(key)

        # Check size limit
        while (
            len(self.cache) >= self.max_size
            or self.current_memory + needed_bytes > self.max_memory_bytes
        ):
            if not self.cache:
                break
            # Remove least recently used entry
            lru_key = next(iter(self.cache))
            self._remove_entry(lru_key)

    def get_stats(self) -> Dict[str, Any]:
        """Get cache statistics."""
        with self.lock:
            total_accesses = sum(entry.access_count for entry in self.cache.values())
            return {
                "entries": len(self.cache),
                "memory_mb": self.current_memory / 1024 / 1024,
                "max_memory_mb": self.max_memory_bytes / 1024 / 1024,
                "memory_usage_percent": (self.current_memory / self.max_memory_bytes)
                * 100,
                "total_accesses": total_accesses,
                "avg_accesses_per_entry": (
                    total_accesses / len(self.cache) if self.cache else 0
                ),
            }


class SmartCache:
    """Intelligent caching system with Redis backend and local fallback."""

    def __init__(
        self,
        redis_url: str = "redis://localhost:6379",
        redis_db: int = 0,
        namespace: str = "proof_sketcher",
        local_cache_size: int = 1000,
        local_cache_memory_mb: int = 100,
        compression_threshold: int = 1024,
        enable_compression: bool = True,
    ):
        """Initialize smart cache.

        Args:
            redis_url: Redis connection URL
            redis_db: Redis database number
            namespace: Cache key namespace
            local_cache_size: Local cache max entries
            local_cache_memory_mb: Local cache max memory
            compression_threshold: Compress values larger than this
            enable_compression: Whether to enable compression
        """
        self.redis_url = redis_url
        self.redis_db = redis_db
        self.namespace = namespace
        self.compression_threshold = compression_threshold
        self.enable_compression = enable_compression

        self.redis_client: Optional[redis.Redis] = None
        self.redis_available = False

        # Local cache as fallback
        self.local_cache = LRUCache(local_cache_size, local_cache_memory_mb)

        # Performance tracking
        self.stats = {
            "hits": 0,
            "misses": 0,
            "redis_hits": 0,
            "local_hits": 0,
            "redis_errors": 0,
            "compression_saves": 0,
        }

        self.logger = logging.getLogger(__name__)

        # Initialize Redis connection
        asyncio.create_task(self._initialize_redis())

    async def _initialize_redis(self):
        """Initialize Redis connection."""
        if not REDIS_AVAILABLE:
            self.logger.warning("Redis not available, using local cache only")
            return

        try:
            self.redis_client = redis.Redis.from_url(
                self.redis_url,
                db=self.redis_db,
                decode_responses=False,  # Handle binary data
                socket_timeout=5,
                socket_connect_timeout=5,
                retry_on_timeout=True,
            )

            # Test connection
            await self.redis_client.ping()
            self.redis_available = True
            self.logger.info("Redis cache backend connected")

        except Exception as e:
            self.logger.warning(f"Redis connection failed: {e}, using local cache only")
            self.redis_available = False

    def generate_key(
        self, theorem: Union[TheoremInfo, Dict], operation: str = "sketch"
    ) -> str:
        """Generate cache key based on theorem content and operation.

        Args:
            theorem: Theorem object or dictionary
            operation: Type of operation (sketch, animation, export, etc.)

        Returns:
            Unique cache key
        """
        # Extract relevant data for cache key
        if isinstance(theorem, Theorem):
            data = {
                "name": theorem.name,
                "statement": theorem.statement,
                "file_path": str(theorem.file_path) if theorem.file_path else None,
                "operation": operation,
            }
        else:
            data = {
                "name": theorem.get("name", ""),
                "statement": theorem.get("statement", ""),
                "file_path": theorem.get("file_path", ""),
                "operation": operation,
            }

        # Add version info for cache invalidation
        data.update(
            {
                "cache_version": "2.0",
                "timestamp": time.time() // 3600,  # Hour-based cache invalidation
            }
        )

        # Create deterministic hash
        serialized = json.dumps(data, sort_keys=True)
        hash_obj = hashlib.sha256(serialized.encode())

        return f"{self.namespace}:{operation}:{hash_obj.hexdigest()[:16]}"

    def generate_export_key(
        self, sketch: ProofSketch, format_name: str, options: Dict = None
    ) -> str:
        """Generate cache key for export operations."""
        data = {
            "theorem_name": sketch.theorem_name,
            "introduction_hash": hashlib.sha256(
                sketch.introduction.encode()
            ).hexdigest()[:16],
            "steps_count": len(sketch.key_steps),
            "format": format_name,
            "options": options or {},
            "cache_version": "2.0",
        }

        serialized = json.dumps(data, sort_keys=True)
        hash_obj = hashlib.sha256(serialized.encode())

        return f"{self.namespace}:export:{format_name}:{hash_obj.hexdigest()[:16]}"

    async def get(self, key: str) -> Optional[Any]:
        """Get value from cache with Redis and local fallback.

        Args:
            key: Cache key

        Returns:
            Cached value or None if not found
        """
        # Try local cache first (fastest)
        value = self.local_cache.get(key)
        if value is not None:
            self.stats["hits"] += 1
            self.stats["local_hits"] += 1
            return value

        # Try Redis cache
        if self.redis_available and self.redis_client:
            try:
                redis_value = await self.redis_client.get(key)
                if redis_value is not None:
                    # Deserialize from Redis
                    deserialized = self._deserialize(redis_value)

                    # Store in local cache for future access
                    self.local_cache.set(key, deserialized, ttl=3600)

                    self.stats["hits"] += 1
                    self.stats["redis_hits"] += 1
                    return deserialized

            except Exception as e:
                self.logger.warning(f"Redis get error: {e}")
                self.stats["redis_errors"] += 1

        # Cache miss
        self.stats["misses"] += 1
        return None

    async def set(
        self,
        key: str,
        value: Any,
        ttl: int = 86400,
        tags: List[str] = None,
        local_only: bool = False,
    ) -> bool:
        """Set value in cache with Redis and local storage.

        Args:
            key: Cache key
            value: Value to cache
            ttl: Time to live in seconds
            tags: Optional tags for cache invalidation
            local_only: Store only in local cache

        Returns:
            True if successfully cached
        """
        success = False

        # Always store in local cache
        local_success = self.local_cache.set(key, value, ttl=ttl, tags=tags)
        if local_success:
            success = True

        # Store in Redis if available and not local_only
        if not local_only and self.redis_available and self.redis_client:
            try:
                serialized = self._serialize(value)

                # Set with TTL
                redis_success = await self.redis_client.setex(key, ttl, serialized)
                if redis_success:
                    success = True

                # Store tags for invalidation
                if tags:
                    await self._store_tags(key, tags, ttl)

            except Exception as e:
                self.logger.warning(f"Redis set error: {e}")
                self.stats["redis_errors"] += 1

        return success

    async def delete(self, key: str) -> bool:
        """Delete entry from both caches."""
        local_deleted = self.local_cache.delete(key)
        redis_deleted = False

        if self.redis_available and self.redis_client:
            try:
                redis_result = await self.redis_client.delete(key)
                redis_deleted = redis_result > 0
            except Exception as e:
                self.logger.warning(f"Redis delete error: {e}")
                self.stats["redis_errors"] += 1

        return local_deleted or redis_deleted

    async def clear(self, pattern: str = None):
        """Clear cache entries matching pattern."""
        # Clear local cache
        self.local_cache.clear()

        # Clear Redis cache
        if self.redis_available and self.redis_client:
            try:
                if pattern:
                    # Delete keys matching pattern
                    keys = await self.redis_client.keys(f"{self.namespace}:{pattern}*")
                    if keys:
                        await self.redis_client.delete(*keys)
                else:
                    # Clear all namespace keys
                    keys = await self.redis_client.keys(f"{self.namespace}:*")
                    if keys:
                        await self.redis_client.delete(*keys)
            except Exception as e:
                self.logger.warning(f"Redis clear error: {e}")
                self.stats["redis_errors"] += 1

    async def invalidate_by_tags(self, tags: List[str]):
        """Invalidate cache entries by tags."""
        if not self.redis_available or not self.redis_client:
            return

        try:
            keys_to_delete = set()

            for tag in tags:
                tag_key = f"{self.namespace}:tag:{tag}"
                tagged_keys = await self.redis_client.smembers(tag_key)
                keys_to_delete.update(tagged_keys)

                # Delete tag set
                await self.redis_client.delete(tag_key)

            # Delete tagged keys
            if keys_to_delete:
                await self.redis_client.delete(*keys_to_delete)

        except Exception as e:
            self.logger.warning(f"Tag invalidation error: {e}")
            self.stats["redis_errors"] += 1

    def _serialize(self, value: Any) -> bytes:
        """Serialize value for Redis storage."""
        try:
            # SECURITY: Use safe JSON serialization instead of pickle
            with tempfile.NamedTemporaryFile(mode="w+b", delete=False) as tmp_file:
                temp_path = Path(tmp_file.name)

            # Use SafeSerializer to write to temp file
            SafeSerializer.dump(value, temp_path, compress=False)

            # Read back as bytes
            serialized = temp_path.read_bytes()

            # Clean up temp file
            os.unlink(temp_path)

            # Compress if large enough and compression enabled
            if self.enable_compression and len(serialized) > self.compression_threshold:
                compressed = gzip.compress(serialized)
                if len(compressed) < len(serialized):
                    self.stats["compression_saves"] += 1
                    return b"compressed:" + compressed

            return serialized

        except Exception as e:
            self.logger.error(f"Serialization error: {e}")
            raise

    def _deserialize(self, data: bytes) -> Any:
        """Deserialize value from Redis storage using safe JSON deserialization."""
        try:
            # Check if compressed
            if data.startswith(b"compressed:"):
                compressed_data = data[11:]  # Remove 'compressed:' prefix
                decompressed = gzip.decompress(compressed_data)
                processed_data = decompressed
            else:
                processed_data = data

            # SECURITY: Use safe JSON deserialization instead of pickle
            with tempfile.NamedTemporaryFile(mode="w+b", delete=False) as tmp_file:
                temp_path = Path(tmp_file.name)

            # Write bytes to temp file
            temp_path.write_bytes(processed_data)

            # Use SafeSerializer to read from temp file
            result = SafeSerializer.load(temp_path, compress=False)

            # Clean up temp file
            os.unlink(temp_path)

            return result

        except Exception as e:
            self.logger.error(f"Deserialization error: {e}")
            raise

    async def _store_tags(self, key: str, tags: List[str], ttl: int):
        """Store tags for cache invalidation."""
        try:
            for tag in tags:
                tag_key = f"{self.namespace}:tag:{tag}"
                await self.redis_client.sadd(tag_key, key)
                await self.redis_client.expire(tag_key, ttl)
        except Exception as e:
            self.logger.warning(f"Tag storage error: {e}")

    def get_stats(self) -> Dict[str, Any]:
        """Get cache performance statistics."""
        total_requests = self.stats["hits"] + self.stats["misses"]
        hit_rate = (
            (self.stats["hits"] / total_requests) * 100 if total_requests > 0 else 0
        )

        cache_stats = {
            "hit_rate_percent": hit_rate,
            "total_requests": total_requests,
            "redis_available": self.redis_available,
            "local_cache": self.local_cache.get_stats(),
            **self.stats,
        }

        return cache_stats

    def reset_stats(self):
        """Reset performance statistics."""
        self.stats = {
            "hits": 0,
            "misses": 0,
            "redis_hits": 0,
            "local_hits": 0,
            "redis_errors": 0,
            "compression_saves": 0,
        }


# Global cache instance
_global_cache: Optional[SmartCache] = None


def get_cache() -> SmartCache:
    """Get global cache instance."""
    global _global_cache
    if _global_cache is None:
        _global_cache = SmartCache()
    return _global_cache


def configure_cache(**kwargs) -> SmartCache:
    """Configure global cache instance."""
    global _global_cache
    _global_cache = SmartCache(**kwargs)
    return _global_cache


# Decorators for automatic caching
def cached(
    ttl: int = 3600, key_func: Optional[callable] = None, tags: List[str] = None
):
    """Decorator for automatic function result caching.

    Args:
        ttl: Time to live in seconds
        key_func: Custom key generation function
        tags: Cache tags for invalidation
    """

    def decorator(func):
        async def async_wrapper(*args, **kwargs):
            cache = get_cache()

            # Generate cache key
            if key_func:
                key = key_func(*args, **kwargs)
            else:
                key_data = {
                    "function": f"{func.__module__}.{func.__name__}",
                    "args": str(args),
                    "kwargs": str(sorted(kwargs.items())),
                }
                key = hashlib.sha256(json.dumps(key_data).encode()).hexdigest()[:16]
                key = f"proof_sketcher:func:{key}"

            # Try cache first
            result = await cache.get(key)
            if result is not None:
                return result

            # Call function and cache result
            if asyncio.iscoroutinefunction(func):
                result = await func(*args, **kwargs)
            else:
                result = func(*args, **kwargs)

            await cache.set(key, result, ttl=ttl, tags=tags)
            return result

        def sync_wrapper(*args, **kwargs):
            # For synchronous functions, run in event loop
            return asyncio.run(async_wrapper(*args, **kwargs))

        if asyncio.iscoroutinefunction(func):
            return async_wrapper
        else:
            return sync_wrapper

    return decorator
