"""Centralized configuration system for Proof Sketcher.

This module provides a unified configuration system that supports:
- Default configurations
- Configuration files (.proof-sketcher.yaml, pyproject.toml)
- Environment variable overrides
- Runtime configuration updates
"""

from __future__ import annotations

import os
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

import toml
import yaml
from pydantic import BaseModel, Field

from ..core.exceptions import ConfigError, ConfigNotFoundError, ConfigValidationError
from ..generator.models import GenerationConfig
from ..parser.config import ParserConfig


class ExportConfig(BaseModel):
    """Configuration for export system."""

    # Output directories
    output_dir: Path = Field(Path("output"), description="Base output directory")
    templates_dir: Path = Field(Path("templates"), description="Templates directory")
    assets_dir: Path = Field(Path("assets"), description="Static assets directory")

    # HTML export settings
    html_theme: str = Field(
        "doc-gen4", description="HTML theme (doc-gen4, modern, classic)"
    )
    html_syntax_style: str = Field(
        "monokai", description="Code syntax highlighting style"
    )
    html_embed_videos: bool = Field(True, description="Embed videos in HTML")
    html_video_formats: list[str] = Field(
        ["mp4", "webm"], description="Video formats to include"
    )

    # Markdown settings
    markdown_flavor: str = Field(
        "github", description="Markdown flavor (github, commonmark)"
    )
    markdown_math_style: str = Field(
        "katex", description="Math rendering (katex, mathjax)"
    )
    markdown_collapsible_proofs: bool = Field(
        True, description="Make proofs collapsible"
    )

    # PDF settings
    pdf_engine: str = Field(
        "pdflatex", description="LaTeX engine (pdflatex, xelatex, lualatex)"
    )
    pdf_document_class: str = Field("article", description="LaTeX document class")
    pdf_font_size: int = Field(11, ge=8, le=14, description="Base font size in points")
    pdf_paper_size: str = Field(
        "a4paper", description="Paper size (a4paper, letterpaper)"
    )

    # Jupyter settings
    jupyter_kernel: str = Field("python3", description="Jupyter kernel")
    jupyter_include_outputs: bool = Field(False, description="Include cell outputs")
    jupyter_interactive_widgets: bool = Field(
        True, description="Add interactive widgets"
    )

    # General settings
    parallel_exports: bool = Field(
        True, description="Enable parallel export processing"
    )
    max_workers: int = Field(4, ge=1, le=16, description="Maximum parallel workers")
    cache_exports: bool = Field(True, description="Cache generated exports")
    include_timestamps: bool = Field(True, description="Include generation timestamps")

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True


@dataclass
class ProofSketcherConfig:
    """Main configuration class for Proof Sketcher.

    This class consolidates all component configurations and provides
    methods for loading from various sources.
    """

    # Component configurations
    parser: ParserConfig = field(default_factory=ParserConfig)
    generator: GenerationConfig = field(default_factory=GenerationConfig)
    export: ExportConfig = field(default_factory=ExportConfig)

    # Global settings
    project_name: str = "Proof Sketcher"
    version: str = "0.1.0"
    debug: bool = False
    log_level: str = "INFO"

    # Paths
    cache_dir: Path = field(
        default_factory=lambda: Path.home() / ".proof_sketcher" / "cache"
    )
    data_dir: Path = field(
        default_factory=lambda: Path.home() / ".proof_sketcher" / "data"
    )

    @classmethod
    def load(cls, config_path: Path | None = None) -> "ProofSketcherConfig":
        """Load configuration from various sources.

        Priority order (highest to lowest):
        1. Environment variables (PROOF_SKETCHER_*)
        2. Config file specified in argument
        3. .proof-sketcher.yaml in current directory
        4. pyproject.toml [tool.proof-sketcher] section
        5. Default values

        Args:
            config_path: Optional path to configuration file

        Returns:
            Loaded configuration
        """
        config = cls()

        # Load from pyproject.toml if exists
        pyproject_path = Path("pyproject.toml")
        if pyproject_path.exists():
            config._load_from_pyproject(pyproject_path)

        # Load from .proof-sketcher.yaml if exists
        yaml_path = Path(".proof-sketcher.yaml")
        if yaml_path.exists():
            config._load_from_yaml(yaml_path)

        # Load from specified config file
        if config_path and config_path.exists():
            if config_path.suffix == ".yaml" or config_path.suffix == ".yml":
                config._load_from_yaml(config_path)
            elif config_path.suffix == ".toml":
                config._load_from_toml(config_path)

        # Apply environment variable overrides
        config._apply_env_overrides()

        # Validate configuration
        config._validate()

        return config

    def _load_from_yaml(self, path: Path) -> None:
        """Load configuration from YAML file."""
        try:
            with open(path) as f:
                data = yaml.safe_load(f)

            if data:
                self._apply_config_dict(data)
        except FileNotFoundError:
            raise ConfigNotFoundError(f"Config file not found: {path}") from None
        except yaml.YAMLError as e:
            raise ConfigValidationError(f"Invalid YAML in {path}: {e}") from e
        except (OSError, PermissionError) as e:
            raise ConfigError(f"Failed to read config file {path}: {e}") from e
        except Exception as e:
            raise ConfigError(
                f"Unexpected error loading config from {path}: {e}"
            ) from e

    def _load_from_pyproject(self, path: Path) -> None:
        """Load configuration from pyproject.toml."""
        try:
            with open(path) as f:
                data = toml.load(f)

            if "tool" in data and "proof-sketcher" in data["tool"]:
                self._apply_config_dict(data["tool"]["proof-sketcher"])
        except FileNotFoundError:
            raise ConfigNotFoundError(f"Config file not found: {path}") from None
        except toml.TomlDecodeError as e:
            raise ConfigValidationError(f"Invalid TOML in {path}: {e}") from e
        except (OSError, PermissionError) as e:
            raise ConfigError(f"Failed to read config file {path}: {e}") from e
        except Exception as e:
            raise ConfigError(
                f"Unexpected error loading config from {path}: {e}"
            ) from e

    def _load_from_toml(self, path: Path) -> None:
        """Load configuration from TOML file."""
        try:
            with open(path) as f:
                data = toml.load(f)

            if data:
                self._apply_config_dict(data)
        except FileNotFoundError:
            raise ConfigNotFoundError(f"Config file not found: {path}") from None
        except toml.TomlDecodeError as e:
            raise ConfigValidationError(f"Invalid TOML in {path}: {e}") from e
        except (OSError, PermissionError) as e:
            raise ConfigError(f"Failed to read config file {path}: {e}") from e
        except Exception as e:
            raise ConfigError(
                f"Unexpected error loading config from {path}: {e}"
            ) from e

    def _apply_config_dict(self, data: dict[str, Any]) -> None:
        """Apply configuration from dictionary."""
        # Global settings
        if "project_name" in data:
            self.project_name = data["project_name"]
        if "version" in data:
            self.version = data["version"]
        if "debug" in data:
            self.debug = data["debug"]
        if "log_level" in data:
            self.log_level = data["log_level"]

        # Paths
        if "cache_dir" in data:
            self.cache_dir = Path(data["cache_dir"])
        if "data_dir" in data:
            self.data_dir = Path(data["data_dir"])

        # Component configurations
        if "parser" in data:
            self.parser = ParserConfig(**data["parser"])
        if "generator" in data:
            self.generator = GenerationConfig(**data["generator"])
        if "export" in data:
            self.export = ExportConfig(**data["export"])

    def _apply_env_overrides(self) -> None:
        """Apply environment variable overrides.

        Environment variables follow the pattern:
        PROOF_SKETCHER_<COMPONENT>_<SETTING>

        Examples:
        - PROOF_SKETCHER_DEBUG=true
        - PROOF_SKETCHER_PARSER_LEAN_EXECUTABLE=/usr/bin/lean
        - PROOF_SKETCHER_GENERATOR_MODEL=claude-3-opus
        """
        prefix = "PROOF_SKETCHER_"

        for key, value in os.environ.items():
            if not key.startswith(prefix):
                continue

            # Parse the key
            parts = key[len(prefix) :].lower().split("_")

            try:
                # Handle special cases for global settings with underscores
                if len(parts) == 2 and parts[0] == "log" and parts[1] == "level":
                    self._set_value("log_level", value)
                elif len(parts) == 1:
                    # Global setting
                    self._set_value(parts[0], value)
                elif len(parts) >= 2:
                    # Component setting
                    component = parts[0]
                    setting = "_".join(parts[1:])
                    self._set_component_value(component, setting, value)
            except ConfigValidationError as e:
                print(f"Warning: Invalid env override {key}={value}: {e}")
            except Exception as e:
                print(
                    f"Warning: Failed to apply env override {key}={value}: {type(e).__name__}: {e}"
                )

    def _set_value(self, key: str, value: str) -> None:
        """Set a global configuration value."""
        if key == "debug":
            self.debug = value.lower() in ("true", "1", "yes")
        elif key == "log_level":
            self.log_level = value.upper()
        elif key == "cache_dir":
            self.cache_dir = Path(value)
        elif key == "data_dir":
            self.data_dir = Path(value)

    def _set_component_value(self, component: str, key: str, value: str) -> None:
        """Set a component configuration value."""
        # Convert string value to appropriate type
        if value.lower() in ("true", "false"):
            value = value.lower() == "true"
        elif value.isdigit():
            value = int(value)
        elif "." in value and value.replace(".", "").isdigit():
            value = float(value)

        # Apply to component
        if component == "parser" and hasattr(self.parser, key):
            setattr(self.parser, key, value)
        elif component == "generator" and hasattr(self.generator, key):
            setattr(self.generator, key, value)
        elif component == "export" and hasattr(self.export, key):
            setattr(self.export, key, value)

    def _validate(self) -> None:
        """Validate the configuration."""
        errors = []

        # Validate component configs
        # ParserConfig validates itself in __post_init__

        # Validate and create paths
        if not self.cache_dir.exists():
            try:
                self.cache_dir.mkdir(parents=True, exist_ok=True)
            except (OSError, PermissionError) as e:
                errors.append(f"Cannot create cache directory: {e}")

        if not self.data_dir.exists():
            try:
                self.data_dir.mkdir(parents=True, exist_ok=True)
            except (OSError, PermissionError) as e:
                errors.append(f"Cannot create data directory: {e}")

        if errors:
            raise ConfigValidationError(
                "Configuration validation failed", details={"errors": errors}
            )

    def save(self, path: Path) -> None:
        """Save configuration to file.

        Args:
            path: Path to save configuration
        """
        # Convert parser config (dataclass) to dict, handling Path objects
        parser_dict = asdict(self.parser)
        if parser_dict.get("working_dir") is not None:
            parser_dict["working_dir"] = str(parser_dict["working_dir"])

        config_dict = {
            "project_name": self.project_name,
            "version": self.version,
            "debug": self.debug,
            "log_level": self.log_level,
            "cache_dir": str(self.cache_dir),
            "data_dir": str(self.data_dir),
            "parser": parser_dict,
            "generator": self.generator.dict(),
            "export": self.export.dict(exclude_none=True),
        }

        # Convert enums and paths to strings in the config dict
        def convert_values(obj):
            """Recursively convert enums and Path objects to their string values."""
            if isinstance(obj, dict):
                return {k: convert_values(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_values(v) for v in obj]
            elif hasattr(obj, "value"):  # Enum
                return obj.value
            elif isinstance(obj, Path):  # Path object
                return str(obj)
            else:
                return obj

        config_dict = convert_values(config_dict)

        if path.suffix in (".yaml", ".yml"):
            with open(path, "w") as f:
                yaml.safe_dump(config_dict, f, default_flow_style=False)
        elif path.suffix == ".toml":
            with open(path, "w") as f:
                toml.dump(config_dict, f)
        else:
            raise ValueError(f"Unsupported config format: {path.suffix}")

    def to_dict(self) -> dict[str, Any]:
        """Convert configuration to dictionary."""
        return {
            "project_name": self.project_name,
            "version": self.version,
            "debug": self.debug,
            "log_level": self.log_level,
            "cache_dir": str(self.cache_dir),
            "data_dir": str(self.data_dir),
            "parser": self.parser.dict() if hasattr(self.parser, "dict") else {},
            "generator": (
                self.generator.dict() if hasattr(self.generator, "dict") else {}
            ),
            "export": self.export.dict() if hasattr(self.export, "dict") else {},
        }
    
    # Security methods for testing compatibility
    @staticmethod
    def sanitize_filename(filename: str) -> str:
        """Mock filename sanitization for security testing."""
        import re
        
        # Convert to string and strip whitespace
        filename = str(filename).strip()
        
        # Handle empty or whitespace-only filenames
        if not filename or filename in ['', '.', '..', '...']:
            return 'unknown'
            
        # Remove path traversal attempts first
        while '../' in filename or '..\\' in filename:
            filename = filename.replace('../', '').replace('..\\', '')
            
        # Remove leading dots and spaces
        filename = filename.lstrip('. ')
        
        # If nothing left after cleaning, return unknown
        if not filename:
            return 'unknown'
            
        # Remove dangerous characters
        safe_name = re.sub(r'[<>:"/\\|?*]', '', filename)
        
        # Ensure filename isn't too long (keep extension if possible)
        if len(safe_name) > 255:
            # Try to preserve extension
            parts = safe_name.rsplit('.', 1)
            if len(parts) == 2 and len(parts[1]) <= 10:
                # Keep extension, truncate name
                name_part = parts[0][:255 - len(parts[1]) - 1]
                safe_name = f"{name_part}.{parts[1]}"
            else:
                safe_name = safe_name[:255]
                
        return safe_name if safe_name else 'unknown'
    
    @staticmethod
    def validate_url(url: str, allow_local: bool = False) -> bool:
        """Mock URL validation for security testing."""
        import re
        from urllib.parse import urlparse
        
        url = str(url).strip()
        
        # Empty URL is invalid
        if not url:
            return False
            
        # Check for allowed protocols
        allowed_protocols = ['https', 'wss']  # WebSocket secure is also allowed
        if allow_local:
            allowed_protocols.extend(['http', 'ws'])
            
        try:
            parsed = urlparse(url)
            
            # Check protocol
            if parsed.scheme not in allowed_protocols:
                return False
                
            # Check for path traversal attempts
            if '../' in url:
                return False
                
            # Check hostname exists
            if not parsed.netloc:
                return False
                
            # Check for local and internal addresses
            hostname = parsed.hostname or ''
            
            # List of local addresses
            local_addresses = ['localhost', '127.0.0.1', '0.0.0.0']
            is_local = hostname in local_addresses or hostname.startswith('192.168.') or hostname.startswith('10.')
            
            # Check for internal/private domain names that should be blocked
            internal_domains = ['internal', 'local', 'private', 'intranet', 'corp']
            is_internal = any(domain in hostname.lower() for domain in internal_domains)
            
            if not allow_local:
                # Block both local and internal addresses
                if is_local or is_internal:
                    return False
                    
                # For non-local, require HTTPS or WSS
                if parsed.scheme in ['http', 'ws']:
                    return False
            else:
                # Even with allow_local, still block internal non-localhost addresses
                if is_internal and hostname not in local_addresses:
                    return False
                
            return True
            
        except Exception:
            return False
    
    @staticmethod
    def get_api_key() -> str | None:
        """Mock API key retrieval for security testing."""
        import os
        
        # Try different environment variable names
        key = os.environ.get('ANTHROPIC_API_KEY') or os.environ.get('PROOF_SKETCHER_API_KEY')
        
        if not key:
            return None
            
        # Validate key format (must start with 'sk-' and be at least 20 chars)
        if not key.startswith('sk-') or len(key) < 20:
            return None
            
        return key
    
    @staticmethod
    def generate_session_id() -> str:
        """Mock session ID generation for security testing."""
        import secrets
        # Generate URL-safe base64 encoded session ID
        return secrets.token_urlsafe(24)  # 24 bytes = 32 chars base64
    
    @staticmethod
    def generate_nonce() -> str:
        """Mock nonce generation for security testing."""
        import secrets
        # Generate URL-safe base64 encoded nonce
        return secrets.token_urlsafe(12)  # 12 bytes = 16 chars base64
    
    @staticmethod
    def get_secure_headers() -> dict[str, str]:
        """Mock secure headers generation for security testing."""
        import secrets
        # Generate nonce for CSP
        nonce = secrets.token_urlsafe(16)
        
        return {
            'X-Content-Type-Options': 'nosniff',
            'X-Frame-Options': 'DENY',
            'X-XSS-Protection': '1; mode=block',
            'Strict-Transport-Security': 'max-age=31536000; includeSubDomains',
            'Content-Security-Policy': f"default-src 'self'; script-src 'self' 'nonce-{nonce}'; style-src 'self' 'nonce-{nonce}'",
            'Referrer-Policy': 'strict-origin-when-cross-origin',
            'Permissions-Policy': 'geolocation=(), microphone=(), camera=()'
        }
    
    @staticmethod
    def validate_environment() -> dict[str, bool]:
        """Mock environment validation for security testing."""
        import os
        import secrets
        
        # Check for API key
        api_key = os.environ.get('ANTHROPIC_API_KEY') or os.environ.get('PROOF_SKETCHER_API_KEY')
        api_key_valid = bool(api_key and api_key.startswith('sk-') and len(api_key) >= 20)
        
        return {
            'api_key_present': api_key_valid,
            'debug_disabled': not os.environ.get('DEBUG', '').lower() in ('true', '1', 'yes'),
            'ssl_verify_enabled': os.environ.get('PYTHONHTTPSVERIFY', '1') != '0',
            'secure_random_available': True  # secrets module is always available in Python 3.6+
        }


# Global configuration instance
_config: ProofSketcherConfig | None = None


def get_config() -> ProofSketcherConfig:
    """Get the global configuration instance.

    Returns:
        Global configuration instance
    """
    global _config
    if _config is None:
        _config = ProofSketcherConfig.load()
    return _config


def set_config(config: ProofSketcherConfig) -> None:
    """Set the global configuration instance.

    Args:
        config: Configuration to set
    """
    global _config
    _config = config


def reset_config() -> None:
    """Reset configuration to defaults."""
    global _config
    _config = ProofSketcherConfig()


# Alias for convenience
Config = ProofSketcherConfig
