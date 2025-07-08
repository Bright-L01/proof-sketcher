"""Cache manager for efficient theorem processing with thread safety and validation."""

import gzip
import hashlib
import json
import logging
import pickle
import threading
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

# Validation imports removed - implement inline validation


class CacheError(Exception):
    """Cache-related errors."""
    pass


class CacheManager:
    """Thread-safe cache manager for processed theorems with TTL and compression."""

    def __init__(
        self, 
        cache_dir: Path, 
        ttl_days: int = 30,
        compress: bool = True,
        max_cache_size_mb: int = 1000
    ):
        """Initialize cache manager.

        Args:
            cache_dir: Directory for cache storage
            ttl_days: Time-to-live for cache entries in days
            compress: Whether to compress cached data
            max_cache_size_mb: Maximum cache size in MB
        """
        self.cache_dir = Path(cache_dir)
        self.ttl = timedelta(days=ttl_days)
        self.compress = compress
        self.max_cache_size_bytes = max_cache_size_mb * 1024 * 1024
        self.logger = logging.getLogger(__name__)
        
        # Thread safety
        self._lock = threading.RLock()
        
        # Initialize cache
        self._initialize_cache()
        
        # Load index
        self.index_file = self.cache_dir / "cache_index.json"
        self.index = self._load_index()
        
        # Perform initial cleanup
        self._cleanup_expired()

    def _initialize_cache(self) -> None:
        """Initialize cache directory with proper permissions."""
        try:
            self.cache_dir.mkdir(parents=True, exist_ok=True)
            
            # Create subdirectories for organization
            (self.cache_dir / "theorems").mkdir(exist_ok=True)
            (self.cache_dir / "visualizations").mkdir(exist_ok=True)
            (self.cache_dir / "exports").mkdir(exist_ok=True)
            
        except Exception as e:
            raise CacheError(f"Failed to initialize cache directory: {e}")

    def get_cache_key(
        self, 
        file_path: str, 
        theorem_name: str, 
        content: str,
        version: str = "1.0"
    ) -> str:
        """Generate deterministic cache key.

        Args:
            file_path: Path to Lean file
            theorem_name: Name of theorem
            content: Theorem content
            version: Cache version for invalidation

        Returns:
            Hexadecimal cache key
        """
        # Include version to allow cache invalidation on schema changes
        data = f"{version}:{file_path}:{theorem_name}:{content}"
        return hashlib.sha256(data.encode()).hexdigest()

    def get(self, key: str, category: str = "theorems") -> Optional[Any]:
        """Get cached item if valid.

        Args:
            key: Cache key
            category: Cache category (theorems/visualizations/exports)

        Returns:
            Cached data or None if not found/expired
        """
        with self._lock:
            if key not in self.index:
                return None
            
            entry = self.index[key]
            
            # Check if expired
            cached_time = datetime.fromisoformat(entry['timestamp'])
            if datetime.now() - cached_time > self.ttl:
                self.logger.debug(f"Cache entry {key} expired")
                self._invalidate(key)
                return None
            
            # Load cached data
            cache_file = self.cache_dir / category / f"{key}.pkl"
            if self.compress:
                cache_file = cache_file.with_suffix('.pkl.gz')
            
            try:
                if cache_file.exists():
                    if self.compress:
                        with gzip.open(cache_file, 'rb') as f:
                            data = pickle.load(f)
                    else:
                        with open(cache_file, 'rb') as f:
                            data = pickle.load(f)
                    
                    # Update access time
                    entry['last_accessed'] = datetime.now().isoformat()
                    self._save_index()
                    
                    return data
                else:
                    # Cache file missing, invalidate entry
                    self.logger.warning(f"Cache file missing for {key}")
                    self._invalidate(key)
                    return None
                    
            except Exception as e:
                self.logger.error(f"Failed to load cache {key}: {e}")
                self._invalidate(key)
                return None

    def set(
        self, 
        key: str, 
        value: Any, 
        category: str = "theorems",
        metadata: Optional[Dict] = None
    ) -> bool:
        """Cache an item with thread safety and size management.

        Args:
            key: Cache key
            value: Data to cache
            category: Cache category
            metadata: Additional metadata

        Returns:
            True if cached successfully
        """
        with self._lock:
            try:
                # Check cache size before adding
                if self._get_cache_size() > self.max_cache_size_bytes:
                    self.logger.info("Cache size limit reached, performing cleanup")
                    self._cleanup_by_lru()
                
                # Prepare cache file
                cache_dir = self.cache_dir / category
                cache_dir.mkdir(exist_ok=True)
                
                cache_file = cache_dir / f"{key}.pkl"
                if self.compress:
                    cache_file = cache_file.with_suffix('.pkl.gz')
                
                # Save data
                if self.compress:
                    with gzip.open(cache_file, 'wb') as f:
                        pickle.dump(value, f, protocol=pickle.HIGHEST_PROTOCOL)
                else:
                    with open(cache_file, 'wb') as f:
                        pickle.dump(value, f, protocol=pickle.HIGHEST_PROTOCOL)
                
                # Update index
                self.index[key] = {
                    'timestamp': datetime.now().isoformat(),
                    'last_accessed': datetime.now().isoformat(),
                    'category': category,
                    'size': cache_file.stat().st_size,
                    'metadata': metadata or {}
                }
                self._save_index()
                
                return True
                
            except Exception as e:
                self.logger.error(f"Failed to cache {key}: {e}")
                return False

    def invalidate(self, key: str) -> bool:
        """Manually invalidate a cache entry.

        Args:
            key: Cache key to invalidate

        Returns:
            True if invalidated successfully
        """
        with self._lock:
            return self._invalidate(key)

    def _invalidate(self, key: str) -> bool:
        """Internal invalidation without lock."""
        if key not in self.index:
            return False
        
        entry = self.index[key]
        category = entry.get('category', 'theorems')
        
        # Remove cache file
        cache_file = self.cache_dir / category / f"{key}.pkl"
        if self.compress:
            cache_file = cache_file.with_suffix('.pkl.gz')
        
        try:
            if cache_file.exists():
                cache_file.unlink()
        except Exception as e:
            self.logger.warning(f"Failed to remove cache file: {e}")
        
        # Remove from index
        del self.index[key]
        self._save_index()
        
        return True

    def clear_all(self) -> int:
        """Clear entire cache.

        Returns:
            Number of entries cleared
        """
        with self._lock:
            count = len(self.index)
            
            # Remove all cache files
            for category in ['theorems', 'visualizations', 'exports']:
                category_dir = self.cache_dir / category
                if category_dir.exists():
                    for cache_file in category_dir.glob('*.pkl*'):
                        try:
                            cache_file.unlink()
                        except Exception as e:
                            self.logger.warning(f"Failed to remove {cache_file}: {e}")
            
            # Clear index
            self.index = {}
            self._save_index()
            
            return count

    def get_statistics(self) -> Dict[str, Any]:
        """Get cache statistics.

        Returns:
            Dictionary of cache statistics
        """
        with self._lock:
            total_size = self._get_cache_size()
            
            # Count by category
            category_counts = {}
            category_sizes = {}
            
            for entry in self.index.values():
                category = entry.get('category', 'unknown')
                category_counts[category] = category_counts.get(category, 0) + 1
                category_sizes[category] = category_sizes.get(category, 0) + entry.get('size', 0)
            
            # Find oldest and newest entries
            timestamps = [
                datetime.fromisoformat(entry['timestamp']) 
                for entry in self.index.values()
            ]
            
            oldest = min(timestamps) if timestamps else None
            newest = max(timestamps) if timestamps else None
            
            return {
                'total_entries': len(self.index),
                'total_size_bytes': total_size,
                'total_size_mb': total_size / (1024 * 1024),
                'categories': category_counts,
                'category_sizes': category_sizes,
                'oldest_entry': oldest.isoformat() if oldest else None,
                'newest_entry': newest.isoformat() if newest else None,
                'ttl_days': self.ttl.days,
                'compression': self.compress,
            }

    def _load_index(self) -> Dict[str, Dict]:
        """Load cache index from disk."""
        if not self.index_file.exists():
            return {}
        
        try:
            with open(self.index_file, 'r') as f:
                return json.load(f)
        except Exception as e:
            self.logger.error(f"Failed to load cache index: {e}")
            return {}

    def _save_index(self) -> None:
        """Save cache index to disk."""
        try:
            with open(self.index_file, 'w') as f:
                json.dump(self.index, f, indent=2)
        except Exception as e:
            self.logger.error(f"Failed to save cache index: {e}")

    def _get_cache_size(self) -> int:
        """Calculate total cache size in bytes."""
        total_size = 0
        
        for category in ['theorems', 'visualizations', 'exports']:
            category_dir = self.cache_dir / category
            if category_dir.exists():
                for cache_file in category_dir.glob('*.pkl*'):
                    total_size += cache_file.stat().st_size
        
        # Include index file
        if self.index_file.exists():
            total_size += self.index_file.stat().st_size
        
        return total_size

    def _cleanup_expired(self) -> int:
        """Clean up expired cache entries.

        Returns:
            Number of entries removed
        """
        expired_keys = []
        now = datetime.now()
        
        for key, entry in self.index.items():
            cached_time = datetime.fromisoformat(entry['timestamp'])
            if now - cached_time > self.ttl:
                expired_keys.append(key)
        
        for key in expired_keys:
            self._invalidate(key)
        
        if expired_keys:
            self.logger.info(f"Cleaned up {len(expired_keys)} expired cache entries")
        
        return len(expired_keys)

    def _cleanup_by_lru(self) -> int:
        """Clean up cache using LRU policy to maintain size limit.

        Returns:
            Number of entries removed
        """
        # Sort entries by last access time
        sorted_entries = sorted(
            self.index.items(),
            key=lambda x: x[1].get('last_accessed', x[1]['timestamp'])
        )
        
        removed = 0
        current_size = self._get_cache_size()
        target_size = self.max_cache_size_bytes * 0.8  # Clean to 80% capacity
        
        for key, entry in sorted_entries:
            if current_size <= target_size:
                break
            
            entry_size = entry.get('size', 0)
            if self._invalidate(key):
                current_size -= entry_size
                removed += 1
        
        if removed:
            self.logger.info(f"Removed {removed} entries to maintain cache size")
        
        return removed

    def export_cache_info(self, output_file: Path) -> None:
        """Export cache information for debugging.

        Args:
            output_file: Path to export file
        """
        with self._lock:
            info = {
                'statistics': self.get_statistics(),
                'entries': []
            }
            
            for key, entry in self.index.items():
                info['entries'].append({
                    'key': key,
                    'timestamp': entry['timestamp'],
                    'last_accessed': entry.get('last_accessed'),
                    'category': entry.get('category'),
                    'size': entry.get('size'),
                    'metadata': entry.get('metadata', {})
                })
            
            with open(output_file, 'w') as f:
                json.dump(info, f, indent=2)

    def validate_cache(self) -> Tuple[int, int]:
        """Validate cache integrity.

        Returns:
            Tuple of (valid_entries, invalid_entries)
        """
        with self._lock:
            valid = 0
            invalid = 0
            invalid_keys = []
            
            for key, entry in self.index.items():
                category = entry.get('category', 'theorems')
                cache_file = self.cache_dir / category / f"{key}.pkl"
                if self.compress:
                    cache_file = cache_file.with_suffix('.pkl.gz')
                
                if cache_file.exists():
                    valid += 1
                else:
                    invalid += 1
                    invalid_keys.append(key)
            
            # Remove invalid entries
            for key in invalid_keys:
                del self.index[key]
            
            if invalid > 0:
                self._save_index()
                self.logger.warning(f"Removed {invalid} invalid cache entries")
            
            return valid, invalid