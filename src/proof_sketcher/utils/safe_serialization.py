"""
Safe serialization utilities to replace insecure pickle usage.
SECURITY: This module provides JSON-based serialization to prevent
arbitrary code execution vulnerabilities from pickle deserialization.
"""

import json
import gzip
from pathlib import Path
from typing import Any, Dict, List, Union, Optional
from datetime import datetime
import base64

from ..core.exceptions import SecurityError

# Allowed data types for safe serialization
SAFE_TYPES = (str, int, float, bool, list, dict, type(None))


class SafeSerializer:
    """
    Secure serializer that uses JSON instead of pickle.
    
    SECURITY RATIONALE:
    - JSON cannot execute arbitrary code during deserialization
    - Explicit type checking prevents unsafe data
    - Base64 encoding for binary data when needed
    """
    
    @staticmethod
    def _validate_safe_data(data: Any, path: str = "root") -> None:
        """
        Recursively validate that data contains only safe types.
        
        Args:
            data: Data to validate
            path: Current path in data structure for error reporting
            
        Raises:
            SecurityError: If unsafe data types are found
        """
        if isinstance(data, SAFE_TYPES):
            if isinstance(data, dict):
                for key, value in data.items():
                    if not isinstance(key, (str, int)):
                        raise SecurityError(f"Unsafe dict key type at {path}.{key}: {type(key)}")
                    SafeSerializer._validate_safe_data(value, f"{path}.{key}")
            elif isinstance(data, list):
                for i, item in enumerate(data):
                    SafeSerializer._validate_safe_data(item, f"{path}[{i}]")
        else:
            raise SecurityError(f"Unsafe data type at {path}: {type(data)}")
    
    @staticmethod
    def _convert_to_safe(data: Any) -> Any:
        """
        Convert common Python objects to JSON-serializable format.
        
        Args:
            data: Data to convert
            
        Returns:
            JSON-serializable data
            
        Raises:
            SecurityError: If data cannot be safely converted
        """
        if isinstance(data, SAFE_TYPES):
            if isinstance(data, dict):
                return {str(k): SafeSerializer._convert_to_safe(v) for k, v in data.items()}
            elif isinstance(data, list):
                return [SafeSerializer._convert_to_safe(item) for item in data]
            else:
                return data
        elif isinstance(data, datetime):
            return {"__datetime__": data.isoformat()}
        elif isinstance(data, Path):
            return {"__path__": str(data)}
        elif isinstance(data, bytes):
            return {"__bytes__": base64.b64encode(data).decode('ascii')}
        elif hasattr(data, '__dict__') and hasattr(data, '__class__'):
            # Simple object with attributes - convert to dict
            obj_data = {
                "__class__": data.__class__.__name__,
                "__module__": data.__class__.__module__,
                "__data__": {k: SafeSerializer._convert_to_safe(v) 
                           for k, v in data.__dict__.items()}
            }
            return obj_data
        else:
            raise SecurityError(f"Cannot safely serialize type: {type(data)}")
    
    @staticmethod
    def _convert_from_safe(data: Any) -> Any:
        """
        Convert JSON data back to Python objects.
        
        Args:
            data: JSON data to convert
            
        Returns:
            Converted Python object
        """
        if isinstance(data, dict):
            # Handle special encoded types
            if "__datetime__" in data:
                return datetime.fromisoformat(data["__datetime__"])
            elif "__path__" in data:
                return Path(data["__path__"])
            elif "__bytes__" in data:
                return base64.b64decode(data["__bytes__"].encode('ascii'))
            elif "__class__" in data and "__module__" in data and "__data__" in data:
                # Simple object reconstruction - return as dict for safety
                # Do NOT reconstruct arbitrary classes for security
                return {
                    "_class_name": data["__class__"],
                    "_module": data["__module__"],
                    **SafeSerializer._convert_from_safe(data["__data__"])
                }
            else:
                return {k: SafeSerializer._convert_from_safe(v) for k, v in data.items()}
        elif isinstance(data, list):
            return [SafeSerializer._convert_from_safe(item) for item in data]
        else:
            return data
    
    @staticmethod
    def dump(data: Any, file_path: Path, compress: bool = False) -> None:
        """
        Safely serialize data to file.
        
        Args:
            data: Data to serialize
            file_path: Output file path
            compress: Whether to use gzip compression
            
        Raises:
            SecurityError: If data is not safe to serialize
        """
        # Convert to safe format
        safe_data = SafeSerializer._convert_to_safe(data)
        
        # Validate safety
        SafeSerializer._validate_safe_data(safe_data)
        
        # Serialize to JSON
        json_str = json.dumps(safe_data, indent=2, sort_keys=True)
        
        # Write to file
        if compress:
            with gzip.open(file_path, 'wt', encoding='utf-8') as f:
                f.write(json_str)
        else:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(json_str)
    
    @staticmethod
    def load(file_path: Path, compress: bool = False) -> Any:
        """
        Safely deserialize data from file.
        
        Args:
            file_path: Input file path
            compress: Whether file is gzip compressed
            
        Returns:
            Deserialized data
            
        Raises:
            SecurityError: If file contains unsafe data
        """
        # Read from file
        if compress:
            with gzip.open(file_path, 'rt', encoding='utf-8') as f:
                json_str = f.read()
        else:
            with open(file_path, 'r', encoding='utf-8') as f:
                json_str = f.read()
        
        # Parse JSON
        try:
            data = json.loads(json_str)
        except json.JSONDecodeError as e:
            raise SecurityError(f"Invalid JSON in cache file: {e}")
        
        # Validate safety
        SafeSerializer._validate_safe_data(data)
        
        # Convert back to Python objects
        return SafeSerializer._convert_from_safe(data)


class LegacyPickleConverter:
    """
    Utility to convert existing pickle files to safe JSON format.
    WARNING: Only use this on trusted pickle files during migration.
    """
    
    @staticmethod
    def convert_pickle_to_json(pickle_path: Path, json_path: Path, compress: bool = False) -> bool:
        """
        Convert a pickle file to safe JSON format.
        
        SECURITY WARNING: This function has been DISABLED for security reasons.
        Pickle deserialization is inherently unsafe and can lead to arbitrary code execution.
        
        Args:
            pickle_path: Path to pickle file
            json_path: Path for output JSON file
            compress: Whether to compress output
            
        Returns:
            False (always fails for security)
            
        Raises:
            SecurityError: Always raised to prevent pickle usage
        """
        raise SecurityError(
            "Pickle deserialization is disabled for security reasons. "
            "Pickle files can contain arbitrary code and are inherently unsafe. "
            "Please use JSON serialization instead with SafeSerializer.dump()"
        )
        
        # REMOVED: Dangerous pickle.load() code
        # This prevents arbitrary code execution vulnerabilities