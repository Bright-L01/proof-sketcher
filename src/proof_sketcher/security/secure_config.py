"""
Secure configuration management for Proof Sketcher.
Implements security best practices for API key management and configuration.
"""

import os
import re
import secrets
from typing import Any, Dict, Optional
from urllib.parse import urlparse


class SecureConfig:
    """Secure configuration management following security best practices."""

    # Secure defaults
    DEFAULT_SESSION_TIMEOUT = 3600  # 1 hour
    MIN_API_KEY_LENGTH = 32
    ALLOWED_PROTOCOLS = {"https", "wss"}
    LOCAL_DEVELOPMENT_HOSTS = {"localhost", "127.0.0.1", "::1"}

    @staticmethod
    def get_api_key() -> Optional[str]:
        """
        Get API key from environment variables only.
        Never stores keys in code or configuration files.
        """
        key = os.getenv("ANTHROPIC_API_KEY")
        if not key:
            return None

        # Basic validation
        if not key.startswith("sk-"):
            return None

        if len(key) < SecureConfig.MIN_API_KEY_LENGTH:
            return None

        return key

    @staticmethod
    def generate_session_id() -> str:
        """Generate cryptographically secure session ID."""
        return secrets.token_urlsafe(32)

    @staticmethod
    def generate_nonce() -> str:
        """Generate cryptographically secure nonce for CSP."""
        return secrets.token_urlsafe(16)

    @staticmethod
    def validate_url(url: str, allow_local: bool = False) -> bool:
        """
        Validate URL for security.

        Args:
            url: URL to validate
            allow_local: Allow localhost/private IPs (for development)

        Returns:
            True if URL is safe
        """
        if not url:
            return False

        try:
            parsed = urlparse(url)
        except Exception:
            return False

        # Check protocol
        if parsed.scheme not in SecureConfig.ALLOWED_PROTOCOLS:
            # Allow http only for local development
            if not (
                allow_local
                and parsed.scheme == "http"
                and parsed.hostname in SecureConfig.LOCAL_DEVELOPMENT_HOSTS
            ):
                return False

        # Check for suspicious patterns
        suspicious_patterns = [
            r"\.\./",  # Path traversal
            r"javascript:",  # XSS
            r"data:",  # Data URLs
            r"ftp:",  # FTP
            r"file:",  # File protocol
        ]

        for pattern in suspicious_patterns:
            if re.search(pattern, url, re.IGNORECASE):
                return False

        return True

    @staticmethod
    def sanitize_filename(filename: str) -> str:
        """
        Sanitize filename to prevent path traversal attacks.

        Args:
            filename: Input filename

        Returns:
            Sanitized filename
        """
        if not filename:
            return "unknown"

        # Remove path components
        filename = os.path.basename(filename)

        # Remove dangerous characters
        filename = re.sub(r'[<>:"/\\|?*]', "", filename)

        # Remove leading/trailing dots and spaces
        filename = filename.strip(" .")

        # Ensure non-empty
        if not filename:
            return "unknown"

        # Limit length
        if len(filename) > 255:
            name, ext = os.path.splitext(filename)
            filename = name[:250] + ext

        return filename

    @staticmethod
    def get_secure_headers() -> Dict[str, str]:
        """
        Get security headers for HTTP responses.

        Returns:
            Dictionary of security headers
        """
        nonce = SecureConfig.generate_nonce()

        return {
            "X-Content-Type-Options": "nosniff",
            "X-Frame-Options": "DENY",
            "X-XSS-Protection": "1; mode=block",
            "Strict-Transport-Security": "max-age=31536000; includeSubDomains",
            "Content-Security-Policy": f"default-src 'self'; script-src 'self' 'nonce-{nonce}'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self'",
            "Referrer-Policy": "strict-origin-when-cross-origin",
            "Permissions-Policy": "geolocation=(), microphone=(), camera=()",
        }

    @staticmethod
    def validate_environment() -> Dict[str, bool]:
        """
        Validate environment for security issues.

        Returns:
            Dictionary of validation results
        """
        results = {}

        # Check for API key
        results["api_key_present"] = SecureConfig.get_api_key() is not None

        # Check for debug mode
        results["debug_disabled"] = os.getenv("DEBUG", "").lower() not in (
            "true",
            "1",
            "yes",
        )

        # Check for secure random
        try:
            secrets.randbits(32)
            results["secure_random_available"] = True
        except Exception:
            results["secure_random_available"] = False

        # Check for SSL verification
        results["ssl_verify_enabled"] = os.getenv("PYTHONHTTPSVERIFY", "1") != "0"

        return results


class InputValidator:
    """Validates and sanitizes user input."""

    @staticmethod
    def sanitize_lean_code(code: str) -> str:
        """
        Sanitize Lean code input.

        Args:
            code: Raw Lean code

        Returns:
            Sanitized code
        """
        if not code:
            return ""

        # Remove null bytes
        code = code.replace("\x00", "")

        # Limit size
        if len(code) > 1_000_000:  # 1MB limit
            code = code[:1_000_000]

        return code

    @staticmethod
    def validate_theorem_name(name: str) -> bool:
        """
        Validate theorem name for security.

        Args:
            name: Theorem name to validate

        Returns:
            True if valid
        """
        if not name:
            return False

        # Check length
        if len(name) > 200:
            return False

        # Check for valid characters (letters, numbers, underscore, dot)
        if not re.match(r"^[a-zA-Z_][a-zA-Z0-9_\.]*$", name):
            return False

        return True

    @staticmethod
    def sanitize_html_output(content: str) -> str:
        """
        Sanitize HTML content to prevent XSS.

        Args:
            content: HTML content

        Returns:
            Sanitized content
        """
        if not content:
            return ""

        # Basic HTML escaping
        content = content.replace("&", "&amp;")
        content = content.replace("<", "&lt;")
        content = content.replace(">", "&gt;")
        content = content.replace('"', "&quot;")
        content = content.replace("'", "&#x27;")

        return content

    @staticmethod
    def validate_file_path(path: str) -> bool:
        """
        Validate file path for security.

        Args:
            path: File path to validate

        Returns:
            True if safe
        """
        if not path:
            return False

        # Check for URL schemes
        if "://" in path:
            return False

        # Check for path traversal
        if ".." in path or path.startswith("/"):
            return False

        # Check for suspicious patterns
        suspicious = ["\\", "|", "&", ";", "`", "$", "(", ")", "{", "}"]
        for char in suspicious:
            if char in path:
                return False

        return True
