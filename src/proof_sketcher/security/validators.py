"""
Security validation utilities.
SECURITY: Central location for all security validation functions.
"""

import re
import shlex
import secrets
from pathlib import Path
from typing import Any, Dict, List, Union
from urllib.parse import urlparse
import hashlib

from ..core.exceptions import SecurityError


class SecurityValidator:
    """
    Central security validation class.
    
    SECURITY RATIONALE:
    - Centralized validation prevents security bugs from inconsistent validation
    - Input sanitization prevents injection attacks
    - Path validation prevents directory traversal
    - Command sanitization prevents command injection
    """
    
    # Safe characters for various contexts
    SAFE_FILENAME_PATTERN = re.compile(r'^[a-zA-Z0-9._-]+$')
    SAFE_THEOREM_NAME_PATTERN = re.compile(r'^[a-zA-Z_][a-zA-Z0-9_\.]*$')
    SAFE_IDENTIFIER_PATTERN = re.compile(r'^[a-zA-Z_][a-zA-Z0-9_]*$')
    
    # Maximum lengths to prevent DoS
    MAX_FILENAME_LENGTH = 255
    MAX_THEOREM_NAME_LENGTH = 200
    MAX_COMMAND_LENGTH = 1000
    MAX_PATH_DEPTH = 10
    
    @staticmethod
    def sanitize_command(cmd: str) -> str:
        """
        Prevent command injection by properly quoting shell commands.
        
        Args:
            cmd: Command string to sanitize
            
        Returns:
            Safely quoted command string
            
        Raises:
            SecurityError: If command is too long or contains suspicious content
        """
        if not isinstance(cmd, str):
            raise SecurityError(f"Command must be string, got {type(cmd)}")
            
        if len(cmd) > SecurityValidator.MAX_COMMAND_LENGTH:
            raise SecurityError(f"Command too long: {len(cmd)} > {SecurityValidator.MAX_COMMAND_LENGTH}")
            
        # Check for suspicious patterns
        suspicious_patterns = [
            r'&&', r'\|\|', r'[;&|]', r'\$\(', r'`',
            r'rm\s+', r'del\s+', r'format\s+', r'mkfs\s+',
            r'>\s*/dev/', r'>\s*/proc/', r'>\s*/sys/'
        ]
        
        for pattern in suspicious_patterns:
            if re.search(pattern, cmd, re.IGNORECASE):
                raise SecurityError(f"Suspicious command pattern detected: {pattern}")
        
        return shlex.quote(cmd)
    
    @staticmethod
    def validate_path(user_path: str, base_dir: str, allow_absolute: bool = False) -> Path:
        """
        Prevent path traversal attacks by validating file paths.
        
        Args:
            user_path: User-provided path
            base_dir: Base directory to constrain to
            allow_absolute: Whether to allow absolute paths
            
        Returns:
            Validated Path object
            
        Raises:
            SecurityError: If path is unsafe
        """
        if not isinstance(user_path, str):
            raise SecurityError(f"Path must be string, got {type(user_path)}")
            
        # Convert to Path objects
        try:
            user_path_obj = Path(user_path)
            base_dir_obj = Path(base_dir).resolve()
        except Exception as e:
            raise SecurityError(f"Invalid path format: {e}")
        
        # Check for absolute paths
        if user_path_obj.is_absolute() and not allow_absolute:
            raise SecurityError(f"Absolute paths not allowed: {user_path}")
        
        # Resolve the target path
        if user_path_obj.is_absolute():
            target_path = user_path_obj.resolve()
        else:
            target_path = (base_dir_obj / user_path).resolve()
        
        # Ensure target is within base directory
        try:
            target_path.relative_to(base_dir_obj)
        except ValueError:
            raise SecurityError(f"Path traversal attempt: {user_path} -> {target_path}")
        
        # Check path depth
        parts = target_path.relative_to(base_dir_obj).parts
        if len(parts) > SecurityValidator.MAX_PATH_DEPTH:
            raise SecurityError(f"Path too deep: {len(parts)} > {SecurityValidator.MAX_PATH_DEPTH}")
        
        # Validate filename components
        for part in parts:
            if not SecurityValidator.SAFE_FILENAME_PATTERN.match(part):
                raise SecurityError(f"Unsafe filename component: {part}")
            if len(part) > SecurityValidator.MAX_FILENAME_LENGTH:
                raise SecurityError(f"Filename too long: {len(part)} > {SecurityValidator.MAX_FILENAME_LENGTH}")
        
        return target_path
    
    @staticmethod
    def validate_theorem_name(name: str) -> str:
        """
        Validate theorem names to prevent injection attacks.
        
        Args:
            name: Theorem name to validate
            
        Returns:
            Validated theorem name
            
        Raises:
            SecurityError: If name is invalid
        """
        if not isinstance(name, str):
            raise SecurityError(f"Theorem name must be string, got {type(name)}")
            
        if not name:
            raise SecurityError("Theorem name cannot be empty")
            
        if len(name) > SecurityValidator.MAX_THEOREM_NAME_LENGTH:
            raise SecurityError(f"Theorem name too long: {len(name)} > {SecurityValidator.MAX_THEOREM_NAME_LENGTH}")
        
        if not SecurityValidator.SAFE_THEOREM_NAME_PATTERN.match(name):
            raise SecurityError(f"Invalid theorem name format: {name}")
        
        return name
    
    @staticmethod
    def validate_identifier(identifier: str) -> str:
        """
        Validate Python identifiers for safe dynamic access.
        
        Args:
            identifier: Identifier to validate
            
        Returns:
            Validated identifier
            
        Raises:
            SecurityError: If identifier is unsafe
        """
        if not isinstance(identifier, str):
            raise SecurityError(f"Identifier must be string, got {type(identifier)}")
            
        if not identifier:
            raise SecurityError("Identifier cannot be empty")
            
        if not SecurityValidator.SAFE_IDENTIFIER_PATTERN.match(identifier):
            raise SecurityError(f"Invalid identifier format: {identifier}")
        
        # Check against Python keywords
        import keyword
        if keyword.iskeyword(identifier):
            raise SecurityError(f"Identifier cannot be Python keyword: {identifier}")
        
        # Check against dangerous built-ins
        dangerous_builtins = {
            'eval', 'exec', 'compile', '__import__', 'open', 'input',
            'globals', 'locals', 'vars', 'dir', 'getattr', 'setattr',
            'hasattr', 'delattr', 'callable'
        }
        
        if identifier in dangerous_builtins:
            raise SecurityError(f"Identifier cannot be dangerous builtin: {identifier}")
        
        return identifier
    
    @staticmethod
    def validate_url(url: str, allowed_schemes: List[str] = None) -> str:
        """
        Validate URLs to prevent SSRF and other attacks.
        
        Args:
            url: URL to validate
            allowed_schemes: List of allowed URL schemes
            
        Returns:
            Validated URL
            
        Raises:
            SecurityError: If URL is unsafe
        """
        if not isinstance(url, str):
            raise SecurityError(f"URL must be string, got {type(url)}")
            
        if not url:
            raise SecurityError("URL cannot be empty")
        
        # Parse URL
        try:
            parsed = urlparse(url)
        except Exception as e:
            raise SecurityError(f"Invalid URL format: {e}")
        
        # Check scheme
        if allowed_schemes is None:
            allowed_schemes = ['http', 'https']
            
        if parsed.scheme.lower() not in allowed_schemes:
            raise SecurityError(f"URL scheme not allowed: {parsed.scheme}")
        
        # Check for localhost/private IPs
        if parsed.hostname:
            hostname = parsed.hostname.lower()
            private_patterns = [
                'localhost', '127.', '0.0.0.0', '::1',
                '10.', '192.168.', '172.'
            ]
            
            for pattern in private_patterns:
                if hostname.startswith(pattern):
                    raise SecurityError(f"Private/local URLs not allowed: {hostname}")
        
        return url
    
    @staticmethod
    def generate_secure_token(length: int = 32) -> str:
        """
        Generate cryptographically secure random token.
        
        Args:
            length: Token length in bytes
            
        Returns:
            Hex-encoded secure token
        """
        return secrets.token_hex(length)
    
    @staticmethod
    def hash_sensitive_data(data: str, salt: str = None) -> Dict[str, str]:
        """
        Securely hash sensitive data with salt.
        
        Args:
            data: Data to hash
            salt: Optional salt (generated if not provided)
            
        Returns:
            Dictionary with hash and salt
        """
        if salt is None:
            salt = secrets.token_hex(16)
            
        # Use SHA-256 for hashing
        hash_obj = hashlib.sha256()
        hash_obj.update(salt.encode('utf-8'))
        hash_obj.update(data.encode('utf-8'))
        
        return {
            'hash': hash_obj.hexdigest(),
            'salt': salt,
            'algorithm': 'sha256'
        }
    
    @staticmethod
    def verify_hash(data: str, hash_info: Dict[str, str]) -> bool:
        """
        Verify data against stored hash.
        
        Args:
            data: Data to verify
            hash_info: Hash information from hash_sensitive_data
            
        Returns:
            True if data matches hash
        """
        computed = SecurityValidator.hash_sensitive_data(
            data, hash_info['salt']
        )
        return computed['hash'] == hash_info['hash']