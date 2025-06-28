"""Tests for configuration system."""

import os
import tempfile
from pathlib import Path

import pytest
import yaml

from proof_sketcher.config.config import (ExportConfig, ProofSketcherConfig,
                                          get_config, reset_config)


class TestExportConfig:
    """Test ExportConfig model."""

    def test_default_values(self):
        """Test default configuration values."""
        config = ExportConfig()

        assert config.output_dir == Path("output")
        assert config.templates_dir == Path("templates")
        assert config.assets_dir == Path("assets")
        assert config.html_theme == "doc-gen4"
        assert config.html_embed_videos is True
        assert config.markdown_flavor == "github"
        assert config.pdf_engine == "pdflatex"
        assert config.jupyter_kernel == "python3"

    def test_validation(self):
        """Test configuration validation."""
        # Test invalid font size
        with pytest.raises(ValueError):
            ExportConfig(pdf_font_size=20)

        # Test invalid max workers
        with pytest.raises(ValueError):
            ExportConfig(max_workers=20)


class TestProofSketcherConfig:
    """Test main configuration class."""

    def test_default_initialization(self):
        """Test default configuration initialization."""
        config = ProofSketcherConfig()

        assert config.project_name == "Proof Sketcher"
        assert config.version == "0.1.0"
        assert config.debug is False
        assert config.log_level == "INFO"
        assert config.cache_dir == Path.home() / ".proof_sketcher" / "cache"
        assert config.data_dir == Path.home() / ".proof_sketcher" / "data"

    def test_load_from_yaml(self):
        """Test loading configuration from YAML file."""
        yaml_content = """
project_name: "Test Project"
version: "1.0.0"
debug: true
log_level: "DEBUG"

parser:
  lean_executable: "/custom/path/to/lean"
  auto_detect_lake: false

generator:
  model: "claude-3-opus-20240229"
  temperature: 0.8

export:
  output_dir: "/tmp/output"
  html_theme: "modern"
  pdf_font_size: 12
"""

        with tempfile.NamedTemporaryFile(mode="w", suffix=".yaml", delete=False) as f:
            f.write(yaml_content)
            temp_path = Path(f.name)

        try:
            config = ProofSketcherConfig.load(temp_path)

            assert config.project_name == "Test Project"
            assert config.version == "1.0.0"
            assert config.debug is True
            assert config.log_level == "DEBUG"
            assert config.parser.lean_executable == "/custom/path/to/lean"
            assert config.parser.auto_detect_lake is False
            assert config.generator.model == "claude-3-opus-20240229"
            assert config.generator.temperature == 0.8
            assert config.export.output_dir == Path("/tmp/output")
            assert config.export.html_theme == "modern"
            assert config.export.pdf_font_size == 12
        finally:
            temp_path.unlink()

    def test_environment_overrides(self):
        """Test environment variable overrides."""
        # Set environment variables
        os.environ["PROOF_SKETCHER_DEBUG"] = "true"
        os.environ["PROOF_SKETCHER_LOG_LEVEL"] = "DEBUG"
        os.environ["PROOF_SKETCHER_PARSER_LEAN_EXECUTABLE"] = "/env/path/to/lean"
        os.environ["PROOF_SKETCHER_GENERATOR_TEMPERATURE"] = "0.9"
        os.environ["PROOF_SKETCHER_EXPORT_MAX_WORKERS"] = "8"

        try:
            config = ProofSketcherConfig.load()

            assert config.debug is True
            assert config.log_level == "DEBUG"
            assert config.parser.lean_executable == "/env/path/to/lean"
            assert config.generator.temperature == 0.9
            assert config.export.max_workers == 8
        finally:
            # Clean up environment
            for key in list(os.environ.keys()):
                if key.startswith("PROOF_SKETCHER_"):
                    del os.environ[key]

    def test_save_to_yaml(self):
        """Test saving configuration to YAML."""
        config = ProofSketcherConfig()
        config.project_name = "Saved Project"
        config.debug = True

        with tempfile.NamedTemporaryFile(mode="w", suffix=".yaml", delete=False) as f:
            temp_path = Path(f.name)

        try:
            config.save(temp_path)

            # Load and verify
            with open(temp_path, "r") as f:
                data = yaml.safe_load(f)

            assert data["project_name"] == "Saved Project"
            assert data["debug"] is True
            assert "parser" in data
            assert "generator" in data
            assert "export" in data
        finally:
            temp_path.unlink()

    def test_save_to_toml(self):
        """Test saving configuration to TOML."""
        config = ProofSketcherConfig()
        config.version = "2.0.0"

        with tempfile.NamedTemporaryFile(mode="w", suffix=".toml", delete=False) as f:
            temp_path = Path(f.name)

        try:
            config.save(temp_path)

            # Verify file was created and is valid TOML
            import toml

            with open(temp_path, "r") as f:
                data = toml.load(f)

            assert data["version"] == "2.0.0"
        finally:
            temp_path.unlink()

    def test_to_dict(self):
        """Test converting configuration to dictionary."""
        config = ProofSketcherConfig()
        config_dict = config.to_dict()

        assert isinstance(config_dict, dict)
        assert config_dict["project_name"] == "Proof Sketcher"
        assert "parser" in config_dict
        assert "generator" in config_dict
        assert "animator" in config_dict
        assert "manim" in config_dict
        assert "export" in config_dict

    def test_validation_creates_directories(self):
        """Test that validation creates necessary directories."""
        config = ProofSketcherConfig()
        config.cache_dir = Path("/tmp/test_proof_sketcher_cache")
        config.data_dir = Path("/tmp/test_proof_sketcher_data")

        # Clean up if exists
        if config.cache_dir.exists():
            config.cache_dir.rmdir()
        if config.data_dir.exists():
            config.data_dir.rmdir()

        # Validation should create directories
        config._validate()

        assert config.cache_dir.exists()
        assert config.data_dir.exists()

        # Clean up
        config.cache_dir.rmdir()
        config.data_dir.rmdir()


class TestGlobalConfig:
    """Test global configuration management."""

    def test_get_config(self):
        """Test getting global configuration."""
        reset_config()
        config1 = get_config()
        config2 = get_config()

        # Should return same instance
        assert config1 is config2

    def test_reset_config(self):
        """Test resetting configuration."""
        config1 = get_config()
        config1.debug = True

        reset_config()
        config2 = get_config()

        assert config2.debug is False
        assert config1 is not config2
