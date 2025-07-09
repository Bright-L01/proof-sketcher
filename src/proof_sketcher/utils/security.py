"""Security utilities for input validation and sanitization."""

import os
import re
import shlex
from html import escape
from pathlib import Path
from typing import List, Optional, Union

from markupsafe import Markup


class SecurityError(Exception):
    """Base exception for security-related errors."""

    pass


class PathTraversalError(SecurityError):
    """Raised when path traversal is attempted."""

    pass


class InvalidInputError(SecurityError):
    """Raised when input validation fails."""

    pass


def validate_file_path(path: Union[str, Path], base_dir: Union[str, Path]) -> Path:
    """Validate and sanitize file paths to prevent path traversal.

    Args:
        path: Path to validate
        base_dir: Base directory that path must be within

    Returns:
        Validated absolute path

    Raises:
        PathTraversalError: If path traversal is attempted
        FileNotFoundError: If path doesn't exist
    """
    # Convert to Path objects and resolve to absolute paths
    clean_path = Path(path).resolve()
    base = Path(base_dir).resolve()

    # Prevent path traversal
    try:
        clean_path.relative_to(base)
    except ValueError:
        raise PathTraversalError(
            f"Path traversal attempt detected: {path} is not within {base_dir}"
        )

    # Check file exists and is readable
    if not clean_path.exists():
        raise FileNotFoundError(f"File not found: {path}")

    if not os.access(clean_path, os.R_OK):
        raise PermissionError(f"File not readable: {path}")

    return clean_path


def validate_theorem_name(name: str) -> str:
    """Validate theorem names to prevent injection.

    Args:
        name: Theorem name to validate

    Returns:
        Validated theorem name

    Raises:
        InvalidInputError: If name contains invalid characters
    """
    # Allow alphanumeric, underscore, dot for qualified names
    if not re.match(r"^[a-zA-Z_][a-zA-Z0-9_\.]*$", name):
        raise InvalidInputError(
            f"Invalid theorem name: {name}. "
            "Names must start with letter/underscore and contain only "
            "alphanumeric characters, underscores, and dots."
        )

    # Prevent excessively long names
    if len(name) > 256:
        raise InvalidInputError(f"Theorem name too long: {len(name)} > 256")

    return name


def safe_command_args(*args: Union[str, Path]) -> List[str]:
    """Safely quote command arguments for subprocess.

    Args:
        *args: Command arguments to quote

    Returns:
        List of safely quoted arguments
    """
    return [shlex.quote(str(arg)) for arg in args]


def safe_html(text: str) -> Markup:
    """Safely escape text for HTML output.

    Args:
        text: Text to escape

    Returns:
        Markup object safe for HTML rendering
    """
    return Markup(escape(text))  # nosec B704 - Text is already escaped


def validate_lean_code(code: str) -> str:
    """Validate Lean code input.

    Args:
        code: Lean code to validate

    Returns:
        Validated code

    Raises:
        InvalidInputError: If code contains suspicious patterns
    """
    # Check for suspicious patterns
    suspicious_patterns = [
        r"#eval.*system",  # System calls in eval
        r"#eval.*io",  # IO operations in eval
        r"import\s+Lean\.Environment",  # Direct environment access
    ]

    for pattern in suspicious_patterns:
        if re.search(pattern, code, re.IGNORECASE):
            raise InvalidInputError(
                f"Suspicious pattern detected in Lean code: {pattern}"
            )

    # Limit code size to prevent DoS
    max_size = 1024 * 1024  # 1MB
    if len(code) > max_size:
        raise InvalidInputError(f"Lean code too large: {len(code)} > {max_size}")

    return code


def sanitize_filename(filename: str) -> str:
    """Sanitize filename for safe filesystem operations.

    Args:
        filename: Filename to sanitize

    Returns:
        Sanitized filename
    """
    # Remove path separators and null bytes
    filename = filename.replace("/", "_").replace("\\", "_").replace("\0", "")

    # Remove other dangerous characters
    filename = re.sub(r'[<>:"|?*]', "_", filename)

    # Remove leading/trailing dots and spaces
    filename = filename.strip(". ")

    # Limit length
    if len(filename) > 255:
        name, ext = os.path.splitext(filename)
        filename = name[: 255 - len(ext)] + ext

    # Ensure not empty
    if not filename:
        filename = "unnamed"

    return filename


def validate_json_path(path: str) -> str:
    """Validate JSON path expressions.

    Args:
        path: JSON path to validate

    Returns:
        Validated path

    Raises:
        InvalidInputError: If path is invalid
    """
    # Basic validation for JSON paths
    if not re.match(r"^[\w\.\[\]]+$", path):
        raise InvalidInputError(f"Invalid JSON path: {path}")

    return path


def secure_pickle_load(data: bytes) -> object:
    """Securely load pickle data with restrictions.

    Args:
        data: Pickle data to load

    Returns:
        Unpickled object

    Raises:
        SecurityError: If pickle contains unsafe operations
    """
    import io
    import pickle  # nosec B403 - We implement secure restrictions below

    class RestrictedUnpickler(pickle.Unpickler):
        """Restrict pickle to safe operations only."""

        def find_class(self, module, name):
            # Only allow specific safe classes
            ALLOWED_MODULES = {
                "proof_sketcher.generator.models",
                "proof_sketcher.core.models",
                "proof_sketcher.parser.models",
                "proof_sketcher.animator.models",
                "datetime",
                "pathlib",
            }

            if module not in ALLOWED_MODULES:
                raise SecurityError(f"Unpickling objects from {module} is not allowed")

            return super().find_class(module, name)

    return RestrictedUnpickler(io.BytesIO(data)).load()


def validate_url(url: str) -> str:
    """Validate URL for safe external requests.

    Args:
        url: URL to validate

    Returns:
        Validated URL

    Raises:
        InvalidInputError: If URL is invalid or unsafe
    """
    from urllib.parse import urlparse

    try:
        parsed = urlparse(url)
    except Exception as e:
        raise InvalidInputError(f"Invalid URL: {e}")

    # Only allow HTTP(S)
    if parsed.scheme not in ("http", "https"):
        raise InvalidInputError(f"Only HTTP(S) URLs allowed, got: {parsed.scheme}")

    # Prevent localhost/internal network access
    hostname = parsed.hostname or ""
    if hostname in (
        "localhost",
        "127.0.0.1",
        "0.0.0.0",
    ):  # nosec B104 - Intentionally blocking these
        raise InvalidInputError("Access to localhost not allowed")

    # Check for internal IP ranges
    if hostname.startswith("192.168.") or hostname.startswith("10."):
        raise InvalidInputError("Access to internal networks not allowed")

    return url
