"""
Test security vulnerability fixes.
SECURITY: Comprehensive tests for all security fixes implemented.
"""

import json
import tempfile
import pytest
from pathlib import Path
from unittest.mock import patch

from proof_sketcher.utils.safe_serialization import SafeSerializer, SecurityError
from proof_sketcher.security.validators import SecurityValidator
from proof_sketcher.security.sanitizers import InputSanitizer


class TestSafeSerialization:
    """Test safe serialization replaces pickle vulnerabilities."""
    
    def test_safe_types_allowed(self, tmp_path):
        """Test that safe data types can be serialized."""
        safe_data = {
            'string': 'test',
            'number': 42,
            'float': 3.14,
            'boolean': True,
            'null': None,
            'list': [1, 2, 3],
            'nested': {'inner': 'value'}
        }
        
        file_path = tmp_path / "test.json"
        SafeSerializer.dump(safe_data, file_path)
        loaded_data = SafeSerializer.load(file_path)
        
        assert loaded_data == safe_data
    
    def test_unsafe_types_rejected(self, tmp_path):
        """Test that unsafe data types are rejected."""
        import os
        
        unsafe_data = {'function': os.system}
        file_path = tmp_path / "test.json"
        
        with pytest.raises(SecurityError, match="Cannot safely serialize"):
            SafeSerializer.dump(unsafe_data, file_path)
    
    def test_datetime_conversion(self, tmp_path):
        """Test that datetime objects are safely converted."""
        from datetime import datetime
        
        data = {'timestamp': datetime(2023, 1, 1, 12, 0)}
        file_path = tmp_path / "test.json"
        
        SafeSerializer.dump(data, file_path)
        loaded_data = SafeSerializer.load(file_path)
        
        # Should be converted back to datetime
        assert isinstance(loaded_data['timestamp'], datetime)
        assert loaded_data['timestamp'] == data['timestamp']
    
    def test_path_conversion(self, tmp_path):
        """Test that Path objects are safely converted."""
        data = {'path': Path('/test/path')}
        file_path = tmp_path / "test.json"
        
        SafeSerializer.dump(data, file_path)
        loaded_data = SafeSerializer.load(file_path)
        
        # Should be converted back to Path
        assert isinstance(loaded_data['path'], Path)
        assert loaded_data['path'] == data['path']
    
    def test_compression_support(self, tmp_path):
        """Test that compression works with safe serialization."""
        data = {'large_data': 'x' * 1000}
        file_path = tmp_path / "test.json.gz"
        
        SafeSerializer.dump(data, file_path, compress=True)
        loaded_data = SafeSerializer.load(file_path, compress=True)
        
        assert loaded_data == data
    
    def test_malicious_json_rejected(self, tmp_path):
        """Test that malicious JSON content is rejected."""
        # Create a file with malicious content
        malicious_json = '{"__class__": "os.system", "__module__": "os", "cmd": "rm -rf /"}'
        file_path = tmp_path / "malicious.json"
        file_path.write_text(malicious_json)
        
        # Should load safely without executing anything
        loaded_data = SafeSerializer.load(file_path)
        
        # Should be returned as safe dict, not executed
        assert isinstance(loaded_data, dict)
        assert '_class_name' in loaded_data  # Safe reconstruction
        assert loaded_data['_class_name'] == 'os.system'


class TestSecurityValidators:
    """Test security validation utilities."""
    
    def test_command_sanitization(self):
        """Test command injection prevention."""
        safe_cmd = "ls -la"
        sanitized = SecurityValidator.sanitize_command(safe_cmd)
        assert sanitized == "'ls -la'"
        
        # Test dangerous commands are rejected
        dangerous_cmds = [
            "ls; rm -rf /",
            "ls && rm file",
            "ls | tee /etc/passwd",
            "ls `whoami`",
            "ls $(id)"
        ]
        
        for cmd in dangerous_cmds:
            with pytest.raises(SecurityError, match="Suspicious command pattern"):
                SecurityValidator.sanitize_command(cmd)
    
    def test_path_validation(self, tmp_path):
        """Test path traversal prevention."""
        base_dir = str(tmp_path)
        
        # Safe paths should work
        safe_path = SecurityValidator.validate_path("subdir/file.txt", base_dir)
        assert safe_path.is_relative_to(tmp_path)
        
        # Path traversal attempts should be rejected
        dangerous_paths = [
            "../../../etc/passwd",
            "subdir/../../etc/passwd",
            "/etc/passwd",
            "..\\..\\windows\\system32"
        ]
        
        for path in dangerous_paths:
            with pytest.raises(SecurityError, match="Path traversal|Absolute paths"):
                SecurityValidator.validate_path(path, base_dir)
    
    def test_theorem_name_validation(self):
        """Test theorem name validation."""
        # Valid names should pass
        valid_names = [
            "Nat.add_comm",
            "List.length_append",
            "my_theorem",
            "Theorem_123"
        ]
        
        for name in valid_names:
            validated = SecurityValidator.validate_theorem_name(name)
            assert validated == name
        
        # Invalid names should be rejected
        invalid_names = [
            "",
            "123invalid",
            "name with spaces",
            "name;with;semicolons",
            "name<script>alert(1)</script>"
        ]
        
        for name in invalid_names:
            with pytest.raises(SecurityError):
                SecurityValidator.validate_theorem_name(name)
    
    def test_url_validation(self):
        """Test URL validation for SSRF prevention."""
        # Safe URLs should pass
        safe_urls = [
            "https://example.com/api",
            "http://public-api.com/data"
        ]
        
        for url in safe_urls:
            validated = SecurityValidator.validate_url(url)
            assert validated == url
        
        # Dangerous URLs should be rejected
        dangerous_urls = [
            "http://localhost:8080/admin",
            "http://127.0.0.1/secrets",
            "http://192.168.1.1/config",
            "ftp://example.com/file",
            "file:///etc/passwd"
        ]
        
        for url in dangerous_urls:
            with pytest.raises(SecurityError):
                SecurityValidator.validate_url(url)
    
    def test_secure_token_generation(self):
        """Test secure token generation."""
        token1 = SecurityValidator.generate_secure_token()
        token2 = SecurityValidator.generate_secure_token()
        
        # Tokens should be different
        assert token1 != token2
        
        # Should be hex-encoded
        assert all(c in '0123456789abcdef' for c in token1)
        
        # Should be correct length (32 bytes = 64 hex chars)
        assert len(token1) == 64
    
    def test_secure_hashing(self):
        """Test secure data hashing."""
        data = "sensitive_data"
        hash_info = SecurityValidator.hash_sensitive_data(data)
        
        # Should contain required fields
        assert 'hash' in hash_info
        assert 'salt' in hash_info
        assert 'algorithm' in hash_info
        assert hash_info['algorithm'] == 'sha256'
        
        # Should verify correctly
        assert SecurityValidator.verify_hash(data, hash_info)
        assert not SecurityValidator.verify_hash("wrong_data", hash_info)


class TestInputSanitizers:
    """Test input sanitization utilities."""
    
    def test_html_sanitization(self):
        """Test HTML XSS prevention."""
        # Basic text should be preserved
        safe_html = "This is safe text"
        sanitized = InputSanitizer.sanitize_html(safe_html)
        assert sanitized == safe_html
        
        # Dangerous HTML should be escaped
        dangerous_html = '<script>alert("XSS")</script>'
        sanitized = InputSanitizer.sanitize_html(dangerous_html)
        assert '<script>' not in sanitized
        assert '&lt;script&gt;' in sanitized
        
        # Event handlers should be removed
        dangerous_attrs = '<div onclick="alert(1)">Click me</div>'
        sanitized = InputSanitizer.sanitize_html(dangerous_attrs, allow_basic_tags=True)
        assert 'onclick' not in sanitized
    
    def test_filename_sanitization(self):
        """Test filename sanitization."""
        # Dangerous characters should be replaced
        dangerous_filename = "../../../etc/passwd<script>.txt"
        sanitized = InputSanitizer.sanitize_filename(dangerous_filename)
        assert '../' not in sanitized
        assert '<script>' not in sanitized
        assert sanitized.endswith('.txt')
        
        # Windows reserved names should be prefixed
        reserved_name = "CON.txt"
        sanitized = InputSanitizer.sanitize_filename(reserved_name)
        assert sanitized.startswith('safe_')
    
    def test_theorem_name_sanitization(self):
        """Test theorem name sanitization."""
        # Spaces should be replaced with underscores
        name_with_spaces = "My Theorem Name"
        sanitized = InputSanitizer.sanitize_theorem_name(name_with_spaces)
        assert ' ' not in sanitized
        assert '_' in sanitized
        
        # Should start with letter or underscore
        invalid_start = "123theorem"
        sanitized = InputSanitizer.sanitize_theorem_name(invalid_start)
        assert sanitized.startswith('theorem_')
    
    def test_latex_sanitization(self):
        """Test LaTeX command injection prevention."""
        # Safe LaTeX should be preserved
        safe_latex = r"$x + y = z$"
        sanitized = InputSanitizer.sanitize_latex(safe_latex)
        assert sanitized == safe_latex
        
        # Dangerous commands should be removed
        dangerous_latex = r"$x + y = z$ \input{/etc/passwd}"
        sanitized = InputSanitizer.sanitize_latex(dangerous_latex)
        assert r'\input' not in sanitized
    
    def test_json_input_sanitization(self):
        """Test JSON input sanitization."""
        # Nested data should be sanitized recursively
        nested_data = {
            'safe': 'value',
            'nested': {
                'deep': ['item1', 'item2'],
                'text': '<script>alert(1)</script>'
            }
        }
        
        sanitized = InputSanitizer.sanitize_json_input(nested_data)
        
        # Structure should be preserved
        assert 'safe' in sanitized
        assert 'nested' in sanitized
        assert 'deep' in sanitized['nested']
        
        # Dangerous content should be sanitized
        assert '<script>' not in str(sanitized)


class TestCacheManagerSecurityFixes:
    """Test that cache manager no longer uses pickle."""
    
    def test_cache_uses_json_serialization(self, tmp_path):
        """Test that cache files use .json extension instead of .pkl."""
        from proof_sketcher.batch.cache_manager import BatchCacheManager
        
        cache_manager = BatchCacheManager(
            cache_dir=tmp_path,
            ttl_hours=1,
            max_cache_size_gb=1
        )
        
        # Store some data
        test_data = {'test': 'data', 'number': 42}
        success = cache_manager.store('test_key', test_data)
        assert success
        
        # Check that .json files are created, not .pkl
        cache_files = list(tmp_path.rglob('*.json'))
        assert len(cache_files) > 0
        
        # Check that no .pkl files are created
        pkl_files = list(tmp_path.rglob('*.pkl'))
        assert len(pkl_files) == 0
        
        # Verify data can be retrieved
        retrieved = cache_manager.get('test_key')
        assert retrieved == test_data


class TestSmartCacheSecurityFixes:
    """Test that smart cache no longer uses pickle."""
    
    @patch('proof_sketcher.optimizations.smart_cache.REDIS_AVAILABLE', False)
    def test_smart_cache_safe_serialization(self):
        """Test that smart cache uses safe serialization."""
        from proof_sketcher.optimizations.smart_cache import SmartCache
        
        cache = SmartCache(namespace="test", redis_url=None)
        
        # Test data that would be dangerous with pickle
        test_data = {
            'safe_data': 'value',
            'numbers': [1, 2, 3],
            'nested': {'key': 'value'}
        }
        
        # This should work without using pickle
        success = cache.set('test_key', test_data)
        assert success
        
        retrieved = cache.get('test_key')
        assert retrieved == test_data


def test_no_pickle_imports():
    """Test that security-fixed modules don't import pickle."""
    # Check that safe_serialization doesn't import pickle in main module
    import proof_sketcher.utils.safe_serialization as safe_ser
    
    # Should not have pickle in namespace (except in LegacyPickleConverter)
    main_attrs = [attr for attr in dir(safe_ser.SafeSerializer) if not attr.startswith('_')]
    pickle_refs = [attr for attr in main_attrs if 'pickle' in attr.lower()]
    assert len(pickle_refs) == 0
    
    # Check batch cache manager
    import proof_sketcher.batch.cache_manager as cache_mgr
    source_file = Path(cache_mgr.__file__).read_text()
    
    # Should not contain pickle.load or pickle.dump calls
    assert 'pickle.load(' not in source_file
    assert 'pickle.dump(' not in source_file
    assert 'pickle.loads(' not in source_file
    assert 'pickle.dumps(' not in source_file


if __name__ == "__main__":
    pytest.main([__file__, "-v"])