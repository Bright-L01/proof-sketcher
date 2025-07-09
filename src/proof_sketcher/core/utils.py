"""Core utility functions for Proof Sketcher.

This module contains shared utility functions used across the application.
"""

import hashlib
import json
import re
import unicodedata
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple, TypeVar, Union

from .exceptions import ProofSketcherError

T = TypeVar("T")


def generate_cache_key(*args: Any, **kwargs: Any) -> str:
    """Generate a deterministic cache key from arguments.

    Args:
        *args: Positional arguments to include in key
        **kwargs: Keyword arguments to include in key

    Returns:
        SHA256 hash as hex string
    """
    # Create a deterministic string representation
    key_parts = []

    # Add positional arguments
    for arg in args:
        key_parts.append(_serialize_for_cache(arg))

    # Add keyword arguments in sorted order
    for key in sorted(kwargs.keys()):
        key_parts.append(f"{key}={_serialize_for_cache(kwargs[key])}")

    # Join and hash
    key_string = "|".join(key_parts)
    return hashlib.sha256(key_string.encode()).hexdigest()


def _serialize_for_cache(obj: Any) -> str:
    """Serialize an object for cache key generation.

    Args:
        obj: Object to serialize

    Returns:
        String representation
    """
    if isinstance(obj, (str, int, float, bool)):
        return str(obj)
    elif isinstance(obj, (list, tuple)):
        return f"[{','.join(_serialize_for_cache(item) for item in obj)}]"
    elif isinstance(obj, dict):
        items = [f"{k}:{_serialize_for_cache(v)}" for k, v in sorted(obj.items())]
        return f"{{{','.join(items)}}}"
    elif isinstance(obj, Path):
        return str(obj.absolute())
    elif hasattr(obj, "model_dump"):
        # Pydantic model
        return _serialize_for_cache(obj.model_dump())
    else:
        # Fallback to JSON
        return json.dumps(obj, sort_keys=True, default=str)


def sanitize_filename(filename: str, max_length: int = 255) -> str:
    """Sanitize a string for use as a filename.

    Args:
        filename: Original filename
        max_length: Maximum length of the filename

    Returns:
        Sanitized filename
    """
    # Normalize unicode characters
    filename = unicodedata.normalize("NFKD", filename)

    # Remove non-ASCII characters
    filename = filename.encode("ascii", "ignore").decode("ascii")

    # Replace invalid characters
    filename = re.sub(r'[<>:"/\\|?*]', "_", filename)

    # Remove leading/trailing spaces and dots
    filename = filename.strip(" .")

    # Truncate if necessary
    if len(filename) > max_length:
        # Preserve extension if present
        parts = filename.rsplit(".", 1)
        if len(parts) == 2 and len(parts[1]) <= 4:
            name, ext = parts
            max_name_length = max_length - len(ext) - 1
            filename = f"{name[:max_name_length]}.{ext}"
        else:
            filename = filename[:max_length]

    # Ensure non-empty
    if not filename:
        filename = "unnamed"

    return filename


def ensure_directory(path: Union[str, Path]) -> Path:
    """Ensure a directory exists, creating it if necessary.

    Args:
        path: Directory path

    Returns:
        Path object for the directory

    Raises:
        OSError: If directory cannot be created
    """
    path = Path(path)
    path.mkdir(parents=True, exist_ok=True)
    return path


def format_duration(seconds: float) -> str:
    """Format a duration in seconds to a human-readable string.

    Args:
        seconds: Duration in seconds

    Returns:
        Formatted duration string
    """
    if seconds < 1:
        return f"{seconds*1000:.0f}ms"
    elif seconds < 60:
        return f"{seconds:.1f}s"
    elif seconds < 3600:
        minutes = seconds // 60
        secs = seconds % 60
        return f"{int(minutes)}m {int(secs)}s"
    else:
        hours = seconds // 3600
        minutes = (seconds % 3600) // 60
        return f"{int(hours)}h {int(minutes)}m"


def truncate_text(text: str, max_length: int, suffix: str = "...") -> str:
    """Truncate text to a maximum length.

    Args:
        text: Text to truncate
        max_length: Maximum length including suffix
        suffix: Suffix to add when truncating

    Returns:
        Truncated text
    """
    if len(text) <= max_length:
        return text

    if max_length <= len(suffix):
        return suffix[:max_length]

    return text[: max_length - len(suffix)] + suffix


def deep_merge(base: Dict[str, Any], update: Dict[str, Any]) -> Dict[str, Any]:
    """Deep merge two dictionaries.

    Args:
        base: Base dictionary
        update: Dictionary with updates

    Returns:
        Merged dictionary (new object)
    """
    result = base.copy()

    for key, value in update.items():
        if key in result and isinstance(result[key], dict) and isinstance(value, dict):
            result[key] = deep_merge(result[key], value)
        else:
            result[key] = value

    return result


def retry_with_backoff(
    func: Callable[..., T],
    max_retries: int = 3,
    base_delay: float = 1.0,
    max_delay: float = 60.0,
    exponential_base: float = 2.0,
    exceptions: Tuple[type[BaseException], ...] = (Exception,),
) -> T:
    """Retry a function with exponential backoff.

    Args:
        func: Function to retry
        max_retries: Maximum number of retries
        base_delay: Initial delay in seconds
        max_delay: Maximum delay in seconds
        exponential_base: Base for exponential backoff
        exceptions: Tuple of exceptions to catch

    Returns:
        Function result

    Raises:
        The last exception if all retries fail
    """
    import time

    last_exception = None
    delay = base_delay

    for attempt in range(max_retries + 1):
        try:
            return func()
        except exceptions as e:
            last_exception = e
            if attempt < max_retries:
                time.sleep(delay)
                delay = min(delay * exponential_base, max_delay)
            else:
                raise

    # Should never reach here, but satisfy type checker
    if last_exception is not None:
        raise last_exception
    else:
        raise ProofSketcherError(
            "Retry failed with no recorded exception",
            details={"max_retries": max_retries, "delay": delay},
            error_code="RETRY_FAILED",
        )


def get_timestamp() -> str:
    """Get current UTC timestamp in ISO format.

    Returns:
        ISO format timestamp string
    """
    return datetime.now(timezone.utc).isoformat()


def parse_timestamp(timestamp: str) -> datetime:
    """Parse an ISO format timestamp.

    Args:
        timestamp: ISO format timestamp string

    Returns:
        Datetime object
    """
    return datetime.fromisoformat(timestamp.replace("Z", "+00:00"))


def calculate_hash(data: Union[str, bytes], algorithm: str = "sha256") -> str:
    """Calculate hash of data.

    Args:
        data: Data to hash
        algorithm: Hash algorithm to use

    Returns:
        Hex digest of the hash
    """
    if isinstance(data, str):
        data = data.encode("utf-8")

    h = hashlib.new(algorithm)
    h.update(data)
    return h.hexdigest()


def chunk_list(lst: List[T], chunk_size: int) -> List[List[T]]:
    """Split a list into chunks of specified size.

    Args:
        lst: List to chunk
        chunk_size: Size of each chunk

    Returns:
        List of chunks
    """
    return [lst[i : i + chunk_size] for i in range(0, len(lst), chunk_size)]


def flatten_dict(
    d: Dict[str, Any], parent_key: str = "", separator: str = "."
) -> Dict[str, Any]:
    """Flatten a nested dictionary.

    Args:
        d: Dictionary to flatten
        parent_key: Parent key for recursion
        separator: Separator for nested keys

    Returns:
        Flattened dictionary
    """
    items: List[Tuple[str, Any]] = []

    for key, value in d.items():
        new_key = f"{parent_key}{separator}{key}" if parent_key else key

        if isinstance(value, dict):
            items.extend(flatten_dict(value, new_key, separator).items())
        else:
            items.append((new_key, value))

    return dict(items)
