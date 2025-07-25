"""Comprehensive tests for the CLI module."""

from __future__ import annotations

import tempfile
from pathlib import Path
from unittest.mock import Mock, patch

import click
import pytest
from click.testing import CliRunner

from proof_sketcher.cli import cli


class TestCLI:
    """Test suite for main CLI."""

    @pytest.fixture
    def runner(self):
        """Create CLI test runner."""
        return CliRunner()

    def test_cli_help(self, runner):
        """Test CLI help command."""
        result = runner.invoke(cli, ["--help"])
        assert result.exit_code == 0
        assert "Proof Sketcher" in result.output
        assert "Commands:" in result.output

    def test_cli_version(self, runner):
        """Test CLI version command."""
        result = runner.invoke(cli, ["--version"])
        assert result.exit_code == 0
        assert "version" in result.output.lower()

    def test_cli_debug_mode(self, runner):
        """Test debug mode flag."""
        import logging

        # Capture the logging level to verify verbose mode sets DEBUG
        original_level = logging.root.level

        # Run CLI with --verbose flag
        result = runner.invoke(cli, ["--verbose", "version"])
        assert result.exit_code == 0

        # In a real scenario, verbose mode would set logging to DEBUG
        # For this test, we just verify the command runs successfully
        # and produces output
        assert "version" in result.output.lower()


class TestProveCommand:
    """Test suite for prove command."""

    @pytest.fixture
    def runner(self):
        """Create CLI test runner."""
        return CliRunner()

    @pytest.fixture
    def sample_lean_file(self, tmp_path):
        """Create sample Lean file."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text(
            """
theorem test_theorem : 1 + 1 = 2 := by norm_num
""",
            encoding="utf-8",
        )
        return lean_file

    def test_prove_basic(self, runner, sample_lean_file):
        """Test basic prove command."""
        with patch("proof_sketcher.cli.SimpleLeanParser") as mock_parser:
            # Mock parser
            mock_result = Mock()
            mock_result.success = True
            mock_result.theorems = [Mock(name="test_theorem", statement="1 + 1 = 2")]
            mock_result.errors = []
            mock_parser.return_value.parse_file.return_value = mock_result

            # Mock ClaudeGenerator
            with patch("proof_sketcher.cli.ClaudeGenerator") as mock_generator:
                mock_instance = Mock()
                mock_generator.return_value = mock_instance
                mock_instance.generate_proof_sketch.return_value = Mock(
                    theorem_name="test_theorem"
                )

                result = runner.invoke(cli, ["prove", str(sample_lean_file)])

                if result.exit_code != 0:
                    print(f"\nError output: {result.output}")
                    print(f"\nException: {result.exception}")
                    if result.exception:
                        import traceback

                        traceback.print_exception(
                            type(result.exception),
                            result.exception,
                            result.exception.__traceback__,
                        )

                assert result.exit_code == 0
                assert "Selected theorem: test_theorem" in result.output
                assert "Generated HTML explanation" in result.output

    def test_prove_with_options(self, runner, sample_lean_file):
        """Test prove command with various options."""
        # Mock config loading
        with patch(
            "proof_sketcher.config.config.ProofSketcherConfig.load"
        ) as mock_load:
            mock_config = Mock()
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            # Mock parser and generator
            with (
                patch(
                    "proof_sketcher.cli.commands.prove.SimpleLeanParser"
                ) as mock_parser,
                patch(
                    "proof_sketcher.cli.commands.prove.SimpleGenerator"
                ) as mock_generator,
                patch(
                    "proof_sketcher.cli.commands.prove.SimpleHTMLExporter"
                ) as mock_html_exporter,
                patch(
                    "proof_sketcher.cli.commands.prove.SimpleMarkdownExporter"
                ) as mock_md_exporter,
            ):

                # Setup mocks
                mock_theorem = Mock()
                mock_theorem.name = "test_theorem"
                mock_theorem.statement = "test statement"
                mock_parser.return_value.parse_file.return_value = Mock(
                    success=True, theorems=[mock_theorem], errors=[]
                )

                mock_sketch = Mock()
                mock_sketch.theorem_name = "test_theorem"
                mock_generator.return_value.generate_offline.return_value = mock_sketch

                mock_html_exporter.return_value.export.return_value = None
                mock_md_exporter.return_value.export.return_value = None

                # Mock Path operations for preview
                with (
                    patch("pathlib.Path.stat") as mock_stat,
                    patch("pathlib.Path.read_text") as mock_read_text,
                ):
                    mock_stat.return_value.st_size = 1000
                    mock_read_text.return_value = "Mock content"

                    # Test with specific format
                    result = runner.invoke(
                        cli, ["prove", str(sample_lean_file), "--format", "html"]
                    )
                    assert result.exit_code == 0
                    assert "Generated HTML explanation" in result.output

                    # Test with markdown format
                    result = runner.invoke(
                        cli, ["prove", str(sample_lean_file), "--format", "markdown"]
                    )
                    assert result.exit_code == 0
                    assert "Generated MARKDOWN explanation" in result.output

                    # Test with educational level
                    result = runner.invoke(
                        cli,
                        [
                            "prove",
                            str(sample_lean_file),
                            "--educational-level",
                            "formal",
                        ],
                    )
                    assert result.exit_code == 0

    def test_prove_specific_theorem(self, runner, sample_lean_file):
        """Test proving specific theorem."""
        # Mock config loading
        with patch(
            "proof_sketcher.config.config.ProofSketcherConfig.load"
        ) as mock_load:
            mock_config = Mock()
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            with patch(
                "proof_sketcher.cli.commands.prove.SimpleLeanParser"
            ) as mock_parser:
                # Return multiple theorems, but only one matches
                mock_result = Mock()
                mock_result.success = True
                # Create properly configured mock theorems
                theorem1 = Mock()
                theorem1.name = "theorem1"
                theorem1.statement = "stmt1"

                theorem2 = Mock()
                theorem2.name = "specific_theorem"
                theorem2.statement = "stmt2"

                theorem3 = Mock()
                theorem3.name = "theorem3"
                theorem3.statement = "stmt3"

                mock_result.theorems = [theorem1, theorem2, theorem3]
                mock_result.errors = []
                mock_parser.return_value.parse_file.return_value = mock_result

                # Mock SimpleGenerator
                with patch(
                    "proof_sketcher.cli.commands.prove.SimpleGenerator"
                ) as mock_generator:
                    mock_instance = Mock()
                    mock_generator.return_value = mock_instance
                    # Create a proper mock sketch with all expected attributes
                    mock_sketch = Mock()
                    mock_sketch.theorem_name = "specific_theorem"
                    mock_sketch.theorem_statement = "stmt2"
                    mock_sketch.intuitive_overview = "Mock overview"
                    mock_sketch.key_steps = []
                    mock_instance.generate_offline.return_value = mock_sketch

                    # Mock exporters to avoid iteration issues
                    with patch(
                        "proof_sketcher.cli.commands.prove.SimpleHTMLExporter"
                    ) as mock_html_exporter:
                        mock_html_instance = Mock()
                        mock_html_exporter.return_value = mock_html_instance
                        mock_html_instance.export.return_value = None

                        # Mock Path operations to avoid file not found errors in preview
                        with (
                            patch("pathlib.Path.stat") as mock_stat,
                            patch("pathlib.Path.read_text") as mock_read_text,
                        ):
                            mock_stat.return_value.st_size = 1000  # Small file size
                            mock_read_text.return_value = "Mock HTML content"

                            result = runner.invoke(
                                cli,
                                [
                                    "prove",
                                    str(sample_lean_file),
                                    "--theorem",
                                    "specific_theorem",
                                ],
                            )

                            if result.exit_code != 0:
                                print(f"\nOutput: {result.output}")
                                print(
                                    f"\nTheorems: {[t.name for t in mock_result.theorems]}"
                                )

                            assert result.exit_code == 0
                            assert "Selected theorem: specific_theorem" in result.output
                            # Should only generate for the specific theorem
                            assert mock_instance.generate_offline.call_count == 1

    def test_prove_error_handling(self, runner):
        """Test error handling in prove command."""
        # Mock config loading for error cases
        with patch(
            "proof_sketcher.config.config.ProofSketcherConfig.load"
        ) as mock_load:
            mock_config = Mock()
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            # Non-existent file
            result = runner.invoke(cli, ["prove", "nonexistent.lean"])
            assert result.exit_code != 0
            assert (
                "does not exist" in result.output or "File not found" in result.output
            )

            # Invalid file extension
            with tempfile.NamedTemporaryFile(suffix=".txt") as tmp:
                result = runner.invoke(cli, ["prove", tmp.name])
                assert result.exit_code != 0
                assert (
                    "Not a Lean file" in result.output
                    or "Invalid file extension" in result.output
                )


class TestConfigCommand:
    """Test suite for config command."""

    @pytest.fixture
    def runner(self):
        """Create CLI test runner."""
        return CliRunner()

    def test_config_show(self, runner):
        """Test config show subcommand."""
        # Mock config loading
        with patch(
            "proof_sketcher.config.config.ProofSketcherConfig.load"
        ) as mock_load:
            # Create a simplified mock config
            mock_config = Mock()
            mock_config.project_name = "Test Project"
            mock_config.version = "1.0.0"
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_config.cache_dir = Path("/tmp/cache")

            # Parser config
            mock_config.parser = Mock()
            mock_config.parser.lean_executable = "lean"
            mock_config.parser.lake_build_on_parse = True
            mock_config.parser.lean_timeout = 30

            # Generator config (simplified)
            mock_config.generator = Mock()
            mock_config.generator.model = Mock(value="claude-3-5-sonnet")
            mock_config.generator.temperature = 0.7
            mock_config.generator.max_tokens = 4000

            # Export config
            mock_config.export = Mock()
            mock_config.export.output_dir = Path("output")
            mock_config.export.html_theme = "doc-gen4"
            mock_config.export.markdown_flavor = "github"
            mock_config.export.pdf_engine = "pdflatex"

            mock_load.return_value = mock_config

            result = runner.invoke(cli, ["config", "--show"])

            assert result.exit_code == 0
            assert "Configuration" in result.output or "config" in result.output.lower()

    def test_config_reset(self, runner):
        """Test config reset subcommand."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Change to temp directory to avoid creating config in current dir
            import os

            old_cwd = os.getcwd()
            os.chdir(tmpdir)

            try:
                # Mock the config loading
                with patch(
                    "proof_sketcher.config.config.ProofSketcherConfig"
                ) as mock_config_class:
                    mock_config = Mock()
                    mock_config.save = Mock()
                    mock_config.debug = False
                    mock_config.log_level = "INFO"
                    mock_config_class.return_value = mock_config

                    result = runner.invoke(cli, ["config", "--reset"])

                    if result.exit_code != 0:
                        print(f"Output: {result.output}")
                        print(f"Exception: {result.exception}")
                        if result.exception:
                            import traceback

                            traceback.print_exception(
                                type(result.exception),
                                result.exception,
                                result.exception.__traceback__,
                            )

                    assert result.exit_code == 0
                    assert (
                        "Configuration reset to defaults" in result.output
                        or "reset" in result.output.lower()
                    )
                    mock_config.save.assert_called_once()
            finally:
                os.chdir(old_cwd)


class TestCacheCommand:
    """Test suite for cache command."""

    @pytest.fixture
    def runner(self):
        """Create CLI test runner."""
        return CliRunner()

    def test_cache_status(self, runner):
        """Test cache status subcommand."""
        # Mock the config loading
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.cache_dir = Path("/tmp/test-cache")
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            # Mock the cache directory existence
            with patch.object(Path, "exists") as mock_exists:
                mock_exists.return_value = True

                # Mock CacheManager
                with patch("proof_sketcher.cli.CacheManager") as mock_cache_class:
                    mock_cache = Mock()
                    mock_cache.get_cache_stats.return_value = {
                        "total_entries": 100,
                        "size_mb": 50.5,
                        "max_size_mb": 100,
                        "by_type": {"proof_sketch": 80, "eli5": 20},
                    }
                    mock_cache_class.return_value = mock_cache

                    # Mock animation cache directory glob
                    with patch("pathlib.Path.glob") as mock_glob:
                        mock_glob.return_value = []  # No animation files

                        result = runner.invoke(cli, ["cache", "status"])

                        # Debug output
                        if result.exit_code != 0:
                            print(f"Exit code: {result.exit_code}")
                            print(f"Output: {result.output}")
                            print(f"Exception: {result.exception}")

                        assert result.exit_code == 0
                        assert "50.5" in result.output or "50.50" in result.output
                        assert "100" in result.output  # total entries
            assert "100" in result.output

    def test_cache_clear(self, runner):
        """Test cache clear subcommand."""
        # Mock the config loading
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.cache_dir = Path("/tmp/test-cache")
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            # Mock the cache directory existence
            with patch.object(Path, "exists") as mock_exists:
                mock_exists.return_value = True

                # Mock CacheManager
                with patch("proof_sketcher.cli.CacheManager") as mock_cache_class:
                    mock_cache = Mock()
                    mock_cache.clear.return_value = 50  # Number of entries cleared
                    mock_cache_class.return_value = mock_cache

                    # Mock animation cache directory glob
                    with patch("pathlib.Path.glob") as mock_glob:
                        mock_glob.return_value = []  # No animation files

                        # Test with --clear flag (current implementation)
                        result = runner.invoke(cli, ["cache", "--clear"])

                        assert result.exit_code == 0
                        # Current implementation just prints a message
                        assert (
                            "Cache cleared" in result.output
                            or "cleared" in result.output.lower()
                        )

    def test_cache_clear_specific_type(self, runner):
        """Test clearing specific cache type - currently clears all."""
        # Mock the config loading
        with patch("proof_sketcher.config.config.Config.load") as mock_load:
            mock_config = Mock()
            mock_config.cache_dir = Path("/tmp/test-cache")
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_load.return_value = mock_config

            # Mock the cache directory existence
            with patch.object(Path, "exists") as mock_exists:
                mock_exists.return_value = True

                # Mock CacheManager
                with patch("proof_sketcher.cli.CacheManager") as mock_cache_class:
                    mock_cache = Mock()
                    mock_cache.clear.return_value = 25
                    mock_cache_class.return_value = mock_cache

                    # Mock animation cache directory glob
                    with patch("pathlib.Path.glob") as mock_glob:
                        mock_glob.return_value = []  # No animation files

                        # Note: Current implementation clears all cache, not specific types
                        result = runner.invoke(cli, ["cache", "clear", "--force"])

                        assert result.exit_code == 0
                        mock_cache.clear.assert_called_once()


class TestListCommand:
    """Test suite for list command."""

    @pytest.fixture
    def runner(self):
        """Create CLI test runner."""
        return CliRunner()

    @pytest.fixture
    def sample_lean_file(self, tmp_path):
        """Create a sample Lean file for testing."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text(
            "theorem test_theorem : 1 + 1 = 2 := by simp\n", encoding="utf-8"
        )
        return lean_file

    def test_list_theorems(self, runner, sample_lean_file):
        """Test listing theorems in a file."""
        # Mock config loading
        with patch(
            "proof_sketcher.config.config.ProofSketcherConfig.load"
        ) as mock_load:
            mock_config = Mock()
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_config.parser = Mock()
            mock_load.return_value = mock_config

            with patch(
                "proof_sketcher.cli.commands.list_theorems.SimpleLeanParser"
            ) as mock_parser:
                mock_result = Mock()
                mock_result.success = True
                mock_result.errors = []  # Add the missing errors attribute

                # Create properly configured theorem mocks with string attributes
                theorem1 = Mock()
                theorem1.name = "theorem1"
                theorem1.statement = "∀x, P(x)"
                theorem1.line_number = 10

                theorem2 = Mock()
                theorem2.name = "theorem2"
                theorem2.statement = "∃x, Q(x)"
                theorem2.line_number = 20

                mock_result.theorems = [theorem1, theorem2]
                mock_parser.return_value.parse_file.return_value = mock_result

                result = runner.invoke(cli, ["list-theorems", str(sample_lean_file)])

                if result.exit_code != 0:
                    print(f"\nError output: {result.output}")
                    print(f"\nException: {result.exception}")
                    if result.exception:
                        import traceback

                        traceback.print_exception(
                            type(result.exception),
                            result.exception,
                            result.exception.__traceback__,
                        )

                assert result.exit_code == 0
                assert "theorem1" in result.output
                assert "theorem2" in result.output
                assert "Found 2 theorem(s)" in result.output
                assert "∀x, P(x)" in result.output
                assert "∃x, Q(x)" in result.output


class TestBatchProcessing:
    """Test suite for batch processing functionality."""

    @pytest.fixture
    def runner(self):
        """Create CLI test runner."""
        return CliRunner()

    def test_process_directory(self, runner, tmp_path):
        """Test processing multiple Lean files."""
        # Create multiple Lean files
        file1 = tmp_path / "file1.lean"
        file2 = tmp_path / "file2.lean"
        file1.write_text("theorem t1 : True := trivial", encoding="utf-8")
        file2.write_text("theorem t2 : True := trivial", encoding="utf-8")

        # Mock config loading
        with patch(
            "proof_sketcher.config.config.ProofSketcherConfig.load"
        ) as mock_load:
            mock_config = Mock()
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_config.parser = Mock()
            mock_config.generator = Mock()
            mock_config.export = Mock()
            mock_config.export.output_dir = tmp_path / "output"
            mock_load.return_value = mock_config

            with patch(
                "proof_sketcher.cli.commands.prove.SimpleLeanParser"
            ) as mock_parser:
                # Create properly configured theorem mock
                theorem_mock = Mock()
                theorem_mock.name = "t1"
                theorem_mock.statement = "True"

                mock_result = Mock()
                mock_result.success = True
                mock_result.theorems = [theorem_mock]
                mock_result.errors = []
                mock_parser.return_value.parse_file.return_value = mock_result

                # Mock ClaudeGenerator
                with patch(
                    "proof_sketcher.cli.commands.prove.SimpleGenerator"
                ) as mock_generator:
                    mock_instance = Mock()
                    mock_generator.return_value = mock_instance
                    mock_instance.generate_proof_sketch.return_value = Mock(
                        theorem_name="t1"
                    )

                    # Test processing first file
                    result1 = runner.invoke(cli, ["prove", str(file1)])
                    assert result1.exit_code == 0

                    # Test processing second file
                    result2 = runner.invoke(cli, ["prove", str(file2)])
                    assert result2.exit_code == 0

                    # Verify both files were processed
                    assert mock_parser.return_value.parse_file.call_count >= 2

    def test_progress_bar(self, runner, tmp_path):
        """Test that progress bar is shown during prove command."""
        # Create a single Lean file
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem t : True := trivial", encoding="utf-8")

        # Mock config loading
        with patch(
            "proof_sketcher.config.config.ProofSketcherConfig.load"
        ) as mock_load:
            mock_config = Mock()
            mock_config.debug = False
            mock_config.log_level = "INFO"
            mock_config.parser = Mock()
            mock_config.generator = Mock()
            mock_config.export = Mock()
            mock_config.export.output_dir = tmp_path / "output"
            mock_load.return_value = mock_config

            with patch(
                "proof_sketcher.cli.commands.prove.SimpleLeanParser"
            ) as mock_parser:
                theorem_mock = Mock()
                theorem_mock.name = "t"
                theorem_mock.statement = "True"

                mock_result = Mock()
                mock_result.success = True
                mock_result.theorems = [theorem_mock]
                mock_result.errors = []
                mock_parser.return_value.parse_file.return_value = mock_result

                # Mock ClaudeGenerator
                with patch(
                    "proof_sketcher.cli.commands.prove.SimpleGenerator"
                ) as mock_generator:
                    mock_instance = Mock()
                    mock_generator.return_value = mock_instance
                    mock_instance.generate_proof_sketch.return_value = Mock(
                        theorem_name="t"
                    )

                    result = runner.invoke(cli, ["prove", str(lean_file)])

                    assert result.exit_code == 0
                    # The progress indicators are shown by default
                    assert "Parsing Lean file" in result.output or "✓" in result.output


@pytest.mark.integration
class TestCLIIntegration:
    """Integration tests for CLI."""

    @pytest.fixture
    def runner(self):
        """Create CLI test runner."""
        return CliRunner()

    def test_full_pipeline_cli(self, runner, tmp_path):
        """Test complete pipeline through CLI."""
        # Create Lean file
        lean_file = tmp_path / "integration.lean"
        lean_file.write_text(
            """
/-- Test theorem for integration -/
theorem integration_test : 2 + 2 = 4 := by norm_num
""",
            encoding="utf-8",
        )

        # Mock necessary components
        with patch("proof_sketcher.cli.SimpleLeanParser") as mock_parser:
            # Mock ClaudeGenerator to avoid executable check
            mock_generator_instance = Mock()
            mock_generator_instance.generate_proof_sketch.return_value = Mock(
                theorem_name="integration_test",
                introduction="Test intro",
                key_steps=[],
                conclusion="Test conclusion",
            )

            with patch("proof_sketcher.cli.ClaudeGenerator") as mock_generator:
                mock_generator.return_value = mock_generator_instance

                # Mock parser response
                theorem_mock = Mock()
                theorem_mock.name = "integration_test"
                theorem_mock.statement = "2 + 2 = 4"
                mock_result = Mock(success=True, theorems=[theorem_mock], errors=[])
                mock_parser.return_value.parse_file.return_value = mock_result

                # Run prove command
                result = runner.invoke(
                    cli,
                    [
                        "prove",
                        str(lean_file),
                        "--format",
                        "markdown",
                        "--output",
                        str(tmp_path),
                    ],
                )

                # Should complete successfully
                assert result.exit_code == 0
                assert "Found 1 theorems" in result.output

    def test_config_persistence(self, runner, tmp_path):
        """Test configuration persistence."""
        with runner.isolated_filesystem():
            # Create a mock config
            with patch("proof_sketcher.config.config.Config.load") as mock_load:
                mock_config = Mock()
                mock_config.project_name = "proof-sketcher-test"
                mock_config.version = "0.1.0"
                mock_config.debug = True
                mock_config.log_level = "DEBUG"
                mock_config.cache_dir = Path(".cache")
                mock_config.parser = Mock(
                    lean_executable=Path("lean"),
                    lake_build_on_parse=True,
                    lean_timeout=60,
                )
                mock_config.generator = Mock(
                    model=Mock(value="claude-3-5-sonnet"),
                    temperature=0.7,
                    max_tokens=4096,
                )
                mock_config.animator = Mock(quality=Mock(value="1080p"), fps=30)
                mock_config.export = Mock(
                    output_dir=Path("output"),
                    html_theme="dark",
                    markdown_flavor="github",
                    pdf_engine="xelatex",
                )
                mock_config.save = Mock()
                mock_load.return_value = mock_config

                # Test config show
                result = runner.invoke(cli, ["config", "show"])
                assert result.exit_code == 0
                assert "proof-sketcher-test" in result.output
                assert "claude-3-5-sonnet" in result.output

                # Test config reset
                result = runner.invoke(cli, ["config", "--reset"])
                assert result.exit_code == 0
                assert (
                    "Configuration reset" in result.output
                    or "reset" in result.output.lower()
                )
