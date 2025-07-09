"""
Network security module for Proof Sketcher.
Implements secure network communication and SSL/TLS verification.
"""

import socket
import ssl
from typing import Any, Dict, Optional
from urllib.parse import urlparse

import requests
import urllib3

from .secure_config import SecureConfig


class SecureHTTPSession:
    """Secure HTTP session with proper SSL/TLS verification."""

    def __init__(self, verify_ssl: bool = True, timeout: int = 30):
        """
        Initialize secure HTTP session.

        Args:
            verify_ssl: Whether to verify SSL certificates
            timeout: Request timeout in seconds
        """
        self.session = requests.Session()
        self.verify_ssl = verify_ssl
        self.timeout = timeout

        # Configure SSL/TLS security
        self._configure_ssl()

        # Set secure headers
        self.session.headers.update(
            {
                "User-Agent": "ProofSketcher/1.0 (Security-Enhanced)",
                "Accept": "application/json",
                "Accept-Encoding": "gzip, deflate",
                "Connection": "keep-alive",
            }
        )

    def _configure_ssl(self):
        """Configure SSL/TLS security settings."""
        if self.verify_ssl:
            # Enable SSL verification
            self.session.verify = True

            # Create secure SSL context
            ssl_context = ssl.create_default_context()
            ssl_context.check_hostname = True
            ssl_context.verify_mode = ssl.CERT_REQUIRED

            # Disable weak protocols
            ssl_context.options |= ssl.OP_NO_SSLv2
            ssl_context.options |= ssl.OP_NO_SSLv3
            ssl_context.options |= ssl.OP_NO_TLSv1
            ssl_context.options |= ssl.OP_NO_TLSv1_1

            # Set minimum TLS version
            ssl_context.minimum_version = ssl.TLSVersion.TLSv1_2

            # Configure cipher suites (prefer strong ciphers)
            ssl_context.set_ciphers(
                "ECDHE+AESGCM:ECDHE+CHACHA20:DHE+AESGCM:DHE+CHACHA20:!aNULL:!MD5:!DSS"
            )

            # Mount HTTPSAdapter with SSL context
            adapter = requests.adapters.HTTPAdapter(
                max_retries=3, pool_connections=10, pool_maxsize=10
            )
            self.session.mount("https://", adapter)
        else:
            # Disable SSL verification (only for development)
            self.session.verify = False
            urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

    def get(self, url: str, **kwargs) -> requests.Response:
        """
        Secure GET request.

        Args:
            url: URL to request
            **kwargs: Additional request parameters

        Returns:
            Response object

        Raises:
            SecurityError: If URL is not secure
        """
        self._validate_url(url)

        kwargs.setdefault("timeout", self.timeout)
        kwargs.setdefault("verify", self.verify_ssl)

        return self.session.get(url, **kwargs)

    def post(self, url: str, **kwargs) -> requests.Response:
        """
        Secure POST request.

        Args:
            url: URL to request
            **kwargs: Additional request parameters

        Returns:
            Response object

        Raises:
            SecurityError: If URL is not secure
        """
        self._validate_url(url)

        kwargs.setdefault("timeout", self.timeout)
        kwargs.setdefault("verify", self.verify_ssl)

        return self.session.post(url, **kwargs)

    def _validate_url(self, url: str):
        """
        Validate URL for security.

        Args:
            url: URL to validate

        Raises:
            SecurityError: If URL is not secure
        """
        if not SecureConfig.validate_url(url):
            from ..core.exceptions import SecurityError

            raise SecurityError(f"URL is not secure: {url}")

    def close(self):
        """Close the session."""
        self.session.close()

    def __enter__(self):
        """Context manager entry."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.close()


class NetworkSecurityValidator:
    """Network security validation utilities."""

    @staticmethod
    def validate_certificate(hostname: str, port: int = 443) -> Dict[str, Any]:
        """
        Validate SSL certificate for a hostname.

        Args:
            hostname: Hostname to check
            port: Port to check (default 443)

        Returns:
            Certificate validation results
        """
        try:
            # Create SSL context
            context = ssl.create_default_context()

            # Connect and get certificate
            with socket.create_connection((hostname, port), timeout=10) as sock:
                with context.wrap_socket(sock, server_hostname=hostname) as ssock:
                    cert = ssock.getpeercert()

                    return {
                        "valid": True,
                        "subject": cert.get("subject", []),
                        "issuer": cert.get("issuer", []),
                        "not_after": cert.get("notAfter"),
                        "not_before": cert.get("notBefore"),
                        "serial_number": cert.get("serialNumber"),
                        "version": cert.get("version"),
                        "signature_algorithm": cert.get("signatureAlgorithm"),
                    }
        except Exception as e:
            return {"valid": False, "error": str(e)}

    @staticmethod
    def check_tls_version(hostname: str, port: int = 443) -> Dict[str, Any]:
        """
        Check TLS version support for a hostname.

        Args:
            hostname: Hostname to check
            port: Port to check (default 443)

        Returns:
            TLS version information
        """
        results = {}

        # Test different TLS versions
        versions_to_test = [
            ("TLSv1.2", ssl.TLSVersion.TLSv1_2),
            ("TLSv1.3", ssl.TLSVersion.TLSv1_3),
        ]

        for version_name, version_constant in versions_to_test:
            try:
                context = ssl.create_default_context()
                context.minimum_version = version_constant
                context.maximum_version = version_constant

                with socket.create_connection((hostname, port), timeout=10) as sock:
                    with context.wrap_socket(sock, server_hostname=hostname) as ssock:
                        results[version_name] = {
                            "supported": True,
                            "cipher": ssock.cipher(),
                            "version": ssock.version(),
                        }
            except Exception as e:
                results[version_name] = {"supported": False, "error": str(e)}

        return results

    @staticmethod
    def is_private_ip(ip: str) -> bool:
        """
        Check if IP address is private/internal.

        Args:
            ip: IP address to check

        Returns:
            True if private IP
        """
        try:
            import ipaddress

            ip_obj = ipaddress.ip_address(ip)
            return ip_obj.is_private
        except ValueError:
            return False

    @staticmethod
    def get_security_recommendations(url: str) -> Dict[str, Any]:
        """
        Get security recommendations for a URL.

        Args:
            url: URL to analyze

        Returns:
            Security recommendations
        """
        parsed = urlparse(url)
        recommendations = []

        # Check protocol
        if parsed.scheme != "https":
            recommendations.append(
                {
                    "type": "protocol",
                    "severity": "high",
                    "message": "Use HTTPS instead of HTTP",
                    "fix": f"Change {parsed.scheme}:// to https://",
                }
            )

        # Check for default ports
        if parsed.port == 80:
            recommendations.append(
                {
                    "type": "port",
                    "severity": "medium",
                    "message": "Using default HTTP port",
                    "fix": "Use HTTPS (port 443) instead",
                }
            )

        # Check hostname
        if parsed.hostname:
            if NetworkSecurityValidator.is_private_ip(parsed.hostname):
                recommendations.append(
                    {
                        "type": "hostname",
                        "severity": "low",
                        "message": "Using private IP address",
                        "fix": "Use public hostname with valid certificate",
                    }
                )

        return {
            "url": url,
            "recommendations": recommendations,
            "security_score": max(0, 100 - len(recommendations) * 20),
        }


# Global secure session instance
_secure_session = None


def get_secure_session(verify_ssl: bool = True) -> SecureHTTPSession:
    """
    Get global secure HTTP session.

    Args:
        verify_ssl: Whether to verify SSL certificates

    Returns:
        Secure HTTP session
    """
    global _secure_session
    if _secure_session is None:
        _secure_session = SecureHTTPSession(verify_ssl=verify_ssl)
    return _secure_session


def close_secure_session():
    """Close global secure session."""
    global _secure_session
    if _secure_session:
        _secure_session.close()
        _secure_session = None
