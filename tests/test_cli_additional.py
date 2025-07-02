"""Additional CLI tests to improve coverage."""

import tempfile
import time
from pathlib import Path
from unittest.mock import Mock, patch, AsyncMock

import pytest
from click.testing import CliRunner

from proof_sketcher.cli import cli, setup_logging, main


class TestAdditionalCLICommands:
    """Test suite for CLI commands not fully covered."""

    @pytest.fixture
    def runner(self):
        """Create CLI test runner."""
        return CliRunner()

    def test_formats_command(self, runner):
        """Test formats command that shows supported export formats."""
        result = runner.invoke(cli, ["formats"])
        
        assert result.exit_code == 0
        assert "HTML" in result.output
        assert "Markdown" in result.output  
        assert "PDF" in result.output
        assert "Jupyter" in result.output
        assert ".html" in result.output
        assert ".md" in result.output
        assert ".pdf" in result.output
        assert ".ipynb" in result.output

    def test_version_command(self, runner):
        """Test version command that shows detailed version info."""
        result = runner.invoke(cli, ["version"])
        
        assert result.exit_code == 0
        assert "Proof Sketcher" in result.output
        assert "Components:" in result.output
        assert "Parser" in result.output
        assert "Generator" in result.output
        assert "Animator" in result.output
        assert "Exporters" in result.output

    def test_cache_list_command(self, runner):
        """Test cache list command."""
        # Mock the config loading
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.cache_dir = Path("/tmp/test-cache")
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            # Mock cache directory existence and contents
            with patch.object(Path, "exists") as mock_exists:
                mock_exists.return_value = True
                
                # Mock rglob to return some mock files
                with patch("pathlib.Path.rglob") as mock_rglob:
                    # Create mock files
                    mock_gen_file = Mock()
                    mock_gen_file.is_file.return_value = True
                    mock_gen_file.relative_to.return_value = Path("generator/sketch1.json")
                    mock_gen_file.stat.return_value.st_size = 1024
                    mock_gen_file.stat.return_value.st_mtime = time.time()
                    
                    mock_anim_file = Mock()
                    mock_anim_file.is_file.return_value = True  
                    mock_anim_file.relative_to.return_value = Path("animations/anim1.mp4")
                    mock_anim_file.stat.return_value.st_size = 2048
                    mock_anim_file.stat.return_value.st_mtime = time.time()
                    
                    mock_rglob.return_value = [mock_gen_file, mock_anim_file]
                    
                    result = runner.invoke(cli, ["cache", "list"])
                    
                    assert result.exit_code == 0
                    assert "Generator" in result.output or "Animation" in result.output

    def test_cache_list_with_pattern(self, runner):
        """Test cache list command with pattern filter."""
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.cache_dir = Path("/tmp/test-cache")
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            with patch.object(Path, "exists") as mock_exists:
                mock_exists.return_value = True
                
                with patch("pathlib.Path.rglob") as mock_rglob:
                    mock_rglob.return_value = []  # No matching files
                    
                    result = runner.invoke(cli, ["cache", "list", "pattern"])
                    
                    assert result.exit_code == 0
                    assert "No cached items found" in result.output

    def test_cache_list_no_directory(self, runner):
        """Test cache list when no cache directory exists."""
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.cache_dir = Path("/tmp/nonexistent-cache")
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            with patch.object(Path, "exists") as mock_exists:
                mock_exists.return_value = False
                
                result = runner.invoke(cli, ["cache", "list"])
                
                assert result.exit_code == 0
                assert "No cache directory found" in result.output


class TestCLIErrorHandling:
    """Test suite for CLI error handling scenarios."""

    @pytest.fixture
    def runner(self):
        return CliRunner()

    @pytest.fixture
    def sample_lean_file(self, tmp_path):
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial", encoding="utf-8")
        return lean_file

    def test_prove_export_errors(self, runner, sample_lean_file):
        """Test error handling during export in prove command."""
        with patch("proof_sketcher.cli.LeanParser") as mock_parser:
            # Mock successful parsing
            theorem_mock = Mock()
            theorem_mock.name = "test"
            theorem_mock.statement = "True"
            
            mock_result = Mock()
            mock_result.success = True
            mock_result.theorems = [theorem_mock]
            mock_result.errors = []
            mock_parser.return_value.parse_file.return_value = mock_result

            # Mock successful generation
            with patch("proof_sketcher.cli.ClaudeGenerator") as mock_generator:
                mock_instance = Mock()
                mock_generator.return_value = mock_instance
                mock_instance.generate_proof_sketch.return_value = Mock(
                    theorem_name="test"
                )

                # Mock export failure
                with patch("proof_sketcher.cli.HTMLExporter") as mock_exporter:
                    mock_exp_instance = Mock()
                    mock_exporter.return_value = mock_exp_instance
                    mock_exp_instance.export_multiple.side_effect = Exception("Export failed")

                    result = runner.invoke(cli, ["prove", str(sample_lean_file)])

                    assert result.exit_code == 0  # CLI doesn't exit on export errors
                    assert "Export error" in result.output

    def test_prove_generation_errors(self, runner, sample_lean_file):
        """Test error handling during generation in prove command."""
        with patch("proof_sketcher.cli.LeanParser") as mock_parser:
            # Mock successful parsing
            theorem_mock = Mock()
            theorem_mock.name = "test"
            theorem_mock.statement = "True"
            
            mock_result = Mock()
            mock_result.success = True
            mock_result.theorems = [theorem_mock]
            mock_result.errors = []
            mock_parser.return_value.parse_file.return_value = mock_result

            # Mock generation failure
            with patch("proof_sketcher.cli.ClaudeGenerator") as mock_generator:
                mock_instance = Mock()
                mock_generator.return_value = mock_instance
                mock_instance.generate_proof_sketch.side_effect = Exception("Generation failed")

                result = runner.invoke(cli, ["prove", str(sample_lean_file)])

                assert result.exit_code == 0  # Should continue and report error
                assert "Failed to process test" in result.output

    def test_prove_all_formats_with_errors(self, runner, sample_lean_file):
        """Test prove command with all formats when some fail."""
        with patch("proof_sketcher.cli.LeanParser") as mock_parser:
            theorem_mock = Mock()
            theorem_mock.name = "test"
            theorem_mock.statement = "True"
            
            mock_result = Mock()
            mock_result.success = True
            mock_result.theorems = [theorem_mock]
            mock_result.errors = []
            mock_parser.return_value.parse_file.return_value = mock_result

            with patch("proof_sketcher.cli.ClaudeGenerator") as mock_generator:
                mock_instance = Mock()
                mock_generator.return_value = mock_instance
                mock_instance.generate_proof_sketch.return_value = Mock(
                    theorem_name="test"
                )

                # Mock some exporters failing
                with patch("proof_sketcher.cli.HTMLExporter") as mock_html:
                    mock_html.return_value.export_multiple.return_value = Mock(success=True)
                    
                    with patch("proof_sketcher.cli.PDFExporter") as mock_pdf:
                        mock_pdf.return_value.export_multiple.side_effect = Exception("PDF failed")

                        result = runner.invoke(cli, ["prove", str(sample_lean_file), "--format", "all"])

                        assert result.exit_code == 0
                        assert "Export error (pdf)" in result.output

    def test_animation_generation_error(self, runner, sample_lean_file):
        """Test animation generation error handling.""" 
        with patch("proof_sketcher.cli.LeanParser") as mock_parser:
            theorem_mock = Mock()
            theorem_mock.name = "test"
            theorem_mock.statement = "True"
            
            mock_result = Mock()
            mock_result.success = True
            mock_result.theorems = [theorem_mock]
            mock_result.errors = []
            mock_parser.return_value.parse_file.return_value = mock_result

            with patch("proof_sketcher.cli.ClaudeGenerator") as mock_generator:
                mock_instance = Mock()
                mock_generator.return_value = mock_instance
                mock_sketch = Mock()
                mock_sketch.explanation = "Test explanation"
                mock_sketch.steps = []
                mock_instance.generate_proof_sketch.return_value = mock_sketch

                # Mock animation generation failure
                with patch("proof_sketcher.cli.ManimMCPClient") as mock_client:
                    mock_client_instance = AsyncMock()
                    mock_client.return_value = mock_client_instance
                    mock_client_instance.start_server = AsyncMock(side_effect=Exception("Animation failed"))

                    result = runner.invoke(cli, ["prove", str(sample_lean_file), "--animate"])

                    assert result.exit_code == 0
                    # Should continue processing even if animation fails

    def test_config_save_error(self, runner):
        """Test config save command error handling."""
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_config.save.side_effect = Exception("Save failed")
            mock_load.return_value = mock_config

            result = runner.invoke(cli, ["config", "save"])

            assert result.exit_code == 1  # Should exit with error code
            assert "Failed to save configuration" in result.output

    def test_cache_clear_no_confirmation(self, runner):
        """Test cache clear without force flag when user cancels."""
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.cache_dir = Path("/tmp/test-cache")
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            with patch.object(Path, "exists") as mock_exists:
                mock_exists.return_value = True
                
                # Mock user declining confirmation
                with patch("click.confirm") as mock_confirm:
                    mock_confirm.return_value = False

                    result = runner.invoke(cli, ["cache", "clear"])

                    assert result.exit_code == 0
                    assert "Cache clear cancelled" in result.output


class TestCLIConfiguration:
    """Test suite for CLI configuration and setup."""

    def test_setup_logging_debug(self):
        """Test setup_logging with debug configuration."""
        mock_config = Mock()
        mock_config.debug = True
        mock_config.log_level = "INFO"  # Should be overridden by debug=True

        with patch("logging.basicConfig") as mock_basic_config:
            setup_logging(mock_config)
            
            # Should have been called with DEBUG level
            mock_basic_config.assert_called_once()
            args, kwargs = mock_basic_config.call_args
            import logging
            assert kwargs["level"] == logging.DEBUG

    def test_setup_logging_custom_level(self):
        """Test setup_logging with custom log level."""
        mock_config = Mock()
        mock_config.debug = False
        mock_config.log_level = "WARNING"

        with patch("logging.basicConfig") as mock_basic_config:
            setup_logging(mock_config)
            
            mock_basic_config.assert_called_once()
            args, kwargs = mock_basic_config.call_args
            import logging
            assert kwargs["level"] == logging.WARNING

    def test_setup_logging_invalid_level(self):
        """Test setup_logging with invalid log level falls back to INFO."""
        mock_config = Mock()
        mock_config.debug = False
        mock_config.log_level = "INVALID_LEVEL"

        with patch("logging.basicConfig") as mock_basic_config:
            setup_logging(mock_config)
            
            mock_basic_config.assert_called_once()
            args, kwargs = mock_basic_config.call_args
            import logging
            assert kwargs["level"] == logging.INFO  # Default fallback

    def test_cli_with_custom_config_file(self):
        """Test CLI with custom configuration file."""
        runner = CliRunner()
        
        with tempfile.NamedTemporaryFile(suffix=".yaml") as config_file:
            # Mock config loading from custom file
            with patch("proof_sketcher.config.config.ProofSketcherConfig.load") as mock_load:
                mock_config = Mock()
                mock_config.debug = False
                mock_config.log_level = "INFO"
                mock_load.return_value = mock_config

                with patch("proof_sketcher.cli.setup_logging"):
                    # Use version command which should trigger config loading
                    result = runner.invoke(cli, ["--config", config_file.name, "version"])
                    
                    # Config loading should have been called with the custom path
                    mock_load.assert_called_once_with(Path(config_file.name))

    def test_main_entry_point(self):
        """Test main entry point function."""
        with patch("proof_sketcher.cli.cli") as mock_cli:
            main()
            mock_cli.assert_called_once()


class TestCLIEdgeCases:
    """Test suite for CLI edge cases and boundary conditions."""

    @pytest.fixture
    def runner(self):
        return CliRunner()

    def test_list_theorems_with_errors(self, runner, tmp_path):
        """Test list-theorems command when parsing has errors."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("invalid lean code", encoding="utf-8")

        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_config.parser = Mock()
            mock_load.return_value = mock_config

            with patch("proof_sketcher.cli.LeanParser") as mock_parser:
                mock_result = Mock()
                mock_result.success = False
                mock_result.errors = ["Syntax error on line 1", "Unknown identifier"]
                mock_result.theorems = []
                mock_parser.return_value.parse_file.return_value = mock_result

                result = runner.invoke(cli, ["list-theorems", str(lean_file)])

                assert result.exit_code == 0
                assert "Parsing errors" in result.output
                assert "Syntax error on line 1" in result.output
                assert "No theorems found" in result.output

    def test_list_theorems_invalid_extension(self, runner, tmp_path):
        """Test list-theorems with invalid file extension."""
        text_file = tmp_path / "test.txt"
        text_file.write_text("not a lean file")

        result = runner.invoke(cli, ["list-theorems", str(text_file)])

        assert result.exit_code != 0
        assert "Invalid file extension '.txt'" in result.output

    def test_prove_no_theorems_in_file(self, runner, tmp_path):
        """Test prove command when no theorems are found."""
        lean_file = tmp_path / "empty.lean"
        lean_file.write_text("-- Just a comment", encoding="utf-8")

        with patch("proof_sketcher.cli.LeanParser") as mock_parser:
            mock_result = Mock()
            mock_result.success = True
            mock_result.theorems = []  # No theorems found
            mock_result.errors = []
            mock_parser.return_value.parse_file.return_value = mock_result

            result = runner.invoke(cli, ["prove", str(lean_file)])

            assert result.exit_code == 0
            assert "No theorems found in file" in result.output

    def test_prove_nonexistent_theorem_filter(self, runner, tmp_path):
        """Test prove command with theorem filter that matches nothing."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem exists : True := trivial", encoding="utf-8")

        with patch("proof_sketcher.cli.LeanParser") as mock_parser:
            theorem_mock = Mock()
            theorem_mock.name = "exists"
            theorem_mock.statement = "True"
            
            mock_result = Mock()
            mock_result.success = True
            mock_result.theorems = [theorem_mock]
            mock_result.errors = []
            mock_parser.return_value.parse_file.return_value = mock_result

            result = runner.invoke(cli, ["prove", str(lean_file), "--theorem", "nonexistent"])

            assert result.exit_code == 0
            assert "None of the specified theorems found" in result.output

    def test_cache_status_no_cache_dir(self, runner):
        """Test cache status when cache directory doesn't exist."""
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.cache_dir = Path("/tmp/nonexistent-cache")
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            with patch.object(Path, "exists") as mock_exists:
                mock_exists.return_value = False

                result = runner.invoke(cli, ["cache", "status"])

                assert result.exit_code == 0
                assert "Directory exists: False" in result.output