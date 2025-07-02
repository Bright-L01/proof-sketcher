"""Integration tests for the complete Proof Sketcher pipeline."""

import json
import tempfile
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.animator.manim_mcp import ManimMCPClient
from proof_sketcher.animator.models import (
    AnimationRequest,
    AnimationScene,
    AnimationSegment,
    TransformationType,
)
from proof_sketcher.config.config import ProofSketcherConfig
from proof_sketcher.generator import AIGenerator as ClaudeGenerator
from proof_sketcher.parser.lean_parser import LeanParser
from proof_sketcher.parser.models import TheoremInfo


class TestCompletePipeline:
    """Test the complete pipeline from parsing to output generation."""

    @pytest.fixture
    def config(self):
        """Create test configuration."""
        config = ProofSketcherConfig()
        config.cache_dir = Path(tempfile.mkdtemp()) / "cache"
        config.data_dir = Path(tempfile.mkdtemp()) / "data"
        return config

    @pytest.fixture
    def sample_lean_file(self, tmp_path):
        """Create a sample Lean file for testing."""
        lean_content = """
-- Test theorem for integration testing
theorem test_theorem (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]
"""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text(lean_content, encoding="utf-8")
        return lean_file

    def test_parse_lean_file(self, config, sample_lean_file):
        """Test parsing a Lean file."""
        parser = LeanParser(config.parser)
        result = parser.parse_file(sample_lean_file)

        assert len(result.theorems) == 1
        assert result.theorems[0].name == "test_theorem"
        assert "n + 0 = n" in result.theorems[0].statement
        assert result.errors == []

    @patch("subprocess.run")
    @patch("proof_sketcher.generator.ai_generator.AIGenerator.check_claude_available")
    def test_generate_proof_sketch(self, mock_check, mock_run, config):
        """Test generating natural language explanation."""
        # Mock executable check to pass
        mock_check.return_value = True

        # Mock Claude response with proper ProofSketch format
        mock_json = {
            "theorem_name": "test_theorem",
            "introduction": "This theorem proves that adding zero to any natural number gives the same number.",
            "key_steps": [
                {
                    "step_number": 1,
                    "description": "Base case: 0 + 0 = 0",
                    "mathematical_content": "0 + 0 = 0",
                    "tactics": ["rfl"],
                },
                {
                    "step_number": 2,
                    "description": "Inductive step: assume true for n, prove for n+1",
                    "mathematical_content": "(n + 1) + 0 = n + 1",
                    "tactics": ["induction", "rw"],
                },
            ],
            "conclusion": "Therefore, adding zero to any natural number leaves it unchanged.",
            "difficulty_level": "beginner",
        }

        mock_run.return_value = Mock(
            stdout=json.dumps(mock_json),
            stderr="",
            returncode=0,
        )

        theorem = TheoremInfo(
            name="test_theorem", statement="∀ n : Nat, n + 0 = n", proof="by induction"
        )

        with patch('subprocess.run') as mock_run_gen:
            mock_run_gen.return_value = Mock(returncode=0)  # Mock successful executable check
            generator = ClaudeGenerator(default_config=config.generator)
        sketch = generator.generate_proof_sketch(theorem)

        assert sketch.theorem_name == "test_theorem"
        assert "adding zero" in sketch.introduction.lower()
        assert len(sketch.key_steps) == 2

    @pytest.mark.asyncio
    async def test_animation_generation(self, config):
        """Test animation generation with mocked MCP server."""
        # Note: AnimationConfig doesn't have 'enabled' field, animation is always available

        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            # Mock successful animation response
            mock_render.return_value = Mock(
                video_path="/tmp/animation.mp4", duration=45.0, success=True, error=None
            )

            client = ManimMCPClient(config.manim)

            # Create proper animation request with required fields
            scene1 = AnimationScene(
                scene_id="scene1",
                title="Step 1",
                duration=10.0,
                initial_formula="n + 0",
                final_formula="n",
                transformation_type=TransformationType.SIMPLIFICATION,
            )
            scene2 = AnimationScene(
                scene_id="scene2",
                title="Step 2",
                duration=10.0,
                initial_formula="n",
                final_formula="n",
                transformation_type=TransformationType.EQUALITY_CHAIN,
            )

            segment = AnimationSegment(
                segment_id="main", title="Test Theorem Proof", scenes=[scene1, scene2]
            )

            request = AnimationRequest(
                theorem_name="test_theorem",
                request_id="test-request-id",
                segments=[segment],
                config=config.animator,
            )

            response = await client.render_animation(request)

            assert response.success
            assert response.video_path == "/tmp/animation.mp4"
            assert response.duration == 45.0

    def test_full_pipeline_without_animation(self, config, sample_lean_file, tmp_path):
        """Test complete pipeline without animation."""
        # Animation is controlled by whether --animate flag is passed, not config
        tmp_path / "output"

        # Parse
        parser = LeanParser(config.parser)
        parse_result = parser.parse_file(sample_lean_file)
        assert len(parse_result.theorems) > 0

        # Generate explanation (mocked)
        with patch("subprocess.run") as mock_run:
            with patch(
                "proof_sketcher.generator.ai_generator.AIGenerator.check_claude_available"
            ) as mock_check:
                mock_check.return_value = True

                # Mock proper ProofSketch JSON
                mock_json = {
                    "theorem_name": "test_theorem",
                    "introduction": "Test explanation",
                    "key_steps": [
                        {
                            "step_number": 1,
                            "description": "Step 1",
                            "mathematical_content": "n + 0 = n",
                            "tactics": [],
                        }
                    ],
                    "conclusion": "Proven.",
                    "difficulty_level": "beginner",
                }

                mock_run.return_value = Mock(
                    stdout=json.dumps(mock_json),
                    stderr="",
                    returncode=0,
                )

                with patch('subprocess.run') as mock_run_gen:
                    mock_run_gen.return_value = Mock(returncode=0)  # Mock successful executable check
                    generator = ClaudeGenerator(default_config=config.generator)
                sketch = generator.generate_proof_sketch(parse_result.theorems[0])
                assert sketch.introduction == "Test explanation"

        # TODO: Test export when exporters are implemented
        # exporter = HTMLExporter(config.export)
        # exporter.export(sketch, output_dir)
        # assert (output_dir / "test_theorem.html").exists()

    @pytest.mark.asyncio
    async def test_full_pipeline_with_animation(
        self, config, sample_lean_file, tmp_path
    ):
        """Test complete pipeline with animation."""
        # Animation will be rendered when requested
        output_dir = tmp_path / "output"

        # Parse
        parser = LeanParser(config.parser)
        parse_result = parser.parse_file(sample_lean_file)
        theorem = parse_result.theorems[0]

        # Generate explanation
        with patch("subprocess.run") as mock_run:
            with patch(
                "proof_sketcher.generator.ai_generator.AIGenerator.check_claude_available"
            ) as mock_check:
                mock_check.return_value = True

                # Mock proper ProofSketch JSON
                mock_json = {
                    "theorem_name": theorem.name,
                    "introduction": "Test explanation",
                    "key_steps": [
                        {
                            "step_number": 1,
                            "description": "Step 1",
                            "mathematical_content": "n + 0 = n",
                            "tactics": [],
                        },
                        {
                            "step_number": 2,
                            "description": "Step 2",
                            "mathematical_content": "n = n",
                            "tactics": [],
                        },
                    ],
                    "conclusion": "Proven.",
                    "difficulty_level": "beginner",
                }

                mock_run.return_value = Mock(
                    stdout=json.dumps(mock_json),
                    stderr="",
                    returncode=0,
                )

                with patch('subprocess.run') as mock_run_gen:
                    mock_run_gen.return_value = Mock(returncode=0)  # Mock successful executable check
                    generator = ClaudeGenerator(default_config=config.generator)
                sketch = generator.generate_proof_sketch(theorem)

        # Generate animation
        with patch.object(ManimMCPClient, "start_server"):
            with patch.object(ManimMCPClient, "render_animation") as mock_render:
                mock_render.return_value = Mock(
                    video_path=str(output_dir / "animation.mp4"),
                    duration=45.0,
                    success=True,
                )

                client = ManimMCPClient(config.manim)
                await client.start_server()

                # Create proper animation request similar to above
                scene = AnimationScene(
                    scene_id="main_scene",
                    title="Main Proof",
                    duration=60.0,
                    initial_formula="n + 0",
                    final_formula="n",
                    transformation_type=TransformationType.SIMPLIFICATION,
                )

                segment = AnimationSegment(
                    segment_id="main", title=sketch.theorem_name, scenes=[scene]
                )

                request = AnimationRequest(
                    theorem_name=theorem.name,
                    request_id="test-request-id",
                    segments=[segment],
                    config=config.animator,
                )
                response = await client.render_animation(request)

                assert response.success
                assert "animation.mp4" in response.video_path

    def test_error_handling_parse_failure(self, config, tmp_path):
        """Test handling of parse failures."""
        # Create file with no theorems (just plain text)
        bad_lean = tmp_path / "bad.lean"
        bad_lean.write_text(
            "This is not a Lean file, just plain text", encoding="utf-8"
        )

        parser = LeanParser(config.parser)
        result = parser.parse_file(bad_lean)

        # Should handle gracefully - parser returns success with empty theorem list
        assert result.success  # Parser doesn't fail on non-Lean content
        assert len(result.theorems) == 0  # No theorems are extracted from plain text

    @patch("subprocess.run")
    @patch("proof_sketcher.generator.ai_generator.AIGenerator.check_claude_available")
    def test_error_handling_generation_failure(self, mock_check, mock_run, config):
        """Test handling of generation failures."""
        # Mock executable check to pass
        mock_check.return_value = True

        # Mock Claude failure
        mock_run.return_value = Mock(
            stdout="", stderr="Error: API limit exceeded", returncode=1
        )

        theorem = TheoremInfo(name="test", statement="test")

        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)  # Mock successful executable check
            generator = ClaudeGenerator(default_config=config.generator)
        
        # Since claude returns non-zero exit code, this should raise an exception
        with pytest.raises(Exception):
            generator.generate_proof_sketch(theorem)

    @pytest.mark.asyncio
    async def test_error_handling_animation_failure(self, config):
        """Test handling of animation failures."""
        with patch.object(ManimMCPClient, "render_animation") as mock_render:
            mock_render.return_value = Mock(
                video_path=None,
                duration=0,
                success=False,
                error="Animation rendering failed",
            )

            client = ManimMCPClient(config.manim)

            # Create minimal valid animation request
            scene = AnimationScene(
                scene_id="test_scene",
                title="Test",
                duration=30.0,
                initial_formula="1",
                final_formula="1",
                transformation_type=TransformationType.EQUALITY_CHAIN,
            )

            segment = AnimationSegment(
                segment_id="test_segment", title="Test", scenes=[scene]
            )

            request = AnimationRequest(
                theorem_name="test",
                request_id="test-id",
                segments=[segment],
                config=config.animator,
            )

            response = await client.render_animation(request)
            assert not response.success
            assert response.error == "Animation rendering failed"


class TestCLIIntegration:
    """Test CLI command integration."""

    @patch("proof_sketcher.cli.LeanParser")
    @patch("proof_sketcher.cli.ClaudeGenerator")
    def test_cli_prove_command(self, mock_generator_class, mock_parser_class, tmp_path):
        """Test the prove command through CLI."""
        from click.testing import CliRunner

        from proof_sketcher.cli import cli

        # Create test Lean file
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : 1 = 1 := rfl", encoding="utf-8")

        # Mock parser to return a successful result
        mock_parser = Mock()
        mock_result = Mock()
        mock_result.success = True
        mock_result.errors = []
        mock_theorem = Mock()
        mock_theorem.name = "test"
        mock_theorem.statement = "1 = 1"
        mock_result.theorems = [mock_theorem]
        mock_parser.parse_file.return_value = mock_result
        mock_parser_class.return_value = mock_parser

        # Mock generator to return a proof sketch
        mock_generator = Mock()
        mock_sketch = Mock()
        mock_sketch.theorem_name = "test"
        mock_sketch.introduction = "This is a simple equality."
        mock_sketch.key_steps = []
        mock_sketch.conclusion = "Proven by reflexivity."
        mock_generator.generate_proof_sketch.return_value = mock_sketch
        mock_generator_class.return_value = mock_generator

        runner = CliRunner()
        result = runner.invoke(cli, ["prove", str(lean_file)])

        assert result.exit_code == 0
        assert "Found 1 theorems" in result.output

    def test_cli_config_show(self):
        """Test config show command."""
        from click.testing import CliRunner

        from proof_sketcher.cli import cli

        runner = CliRunner()
        result = runner.invoke(cli, ["config", "show"])

        assert result.exit_code == 0
        assert "Current Configuration" in result.output

    def test_cli_config_save(self, tmp_path):
        """Test config save command."""
        from click.testing import CliRunner

        from proof_sketcher.cli import cli

        config_file = tmp_path / "test-config.yaml"

        runner = CliRunner()
        result = runner.invoke(cli, ["config", "save", "-o", str(config_file)])

        # Print output for debugging
        if result.exit_code != 0:
            print(f"Exit code: {result.exit_code}")
            print(f"Output: {result.output}")
            if result.exception:
                import traceback

                traceback.print_exception(
                    type(result.exception),
                    result.exception,
                    result.exception.__traceback__,
                )

        assert result.exit_code == 0
        assert config_file.exists()
        assert "Configuration saved" in result.output

    def test_cli_cache_status(self):
        """Test cache status command."""
        from click.testing import CliRunner

        from proof_sketcher.cli import cli

        runner = CliRunner()
        result = runner.invoke(cli, ["cache", "status"])

        assert result.exit_code == 0
        assert "Cache Status" in result.output


class TestConfigurationIntegration:
    """Test configuration loading and usage."""

    def test_load_from_yaml_file(self, tmp_path):
        """Test loading configuration from YAML file."""
        config_content = """
project_name: "Test Project"
debug: true
parser:
  lean_timeout: 60
generator:
  model: "claude-3-opus-20240229"
"""
        config_file = tmp_path / ".proof-sketcher.yaml"
        config_file.write_text(config_content, encoding="utf-8")

        config = ProofSketcherConfig.load(config_file)

        assert config.project_name == "Test Project"
        assert config.debug is True
        assert config.parser.lean_timeout == 60
        # Model is stored as an enum, check its value
        assert config.generator.model.value == "claude-3-opus-20240229"

    def test_environment_override(self, monkeypatch):
        """Test environment variable overrides."""
        monkeypatch.setenv("PROOF_SKETCHER_DEBUG", "true")
        monkeypatch.setenv("PROOF_SKETCHER_PARSER_LEAN_TIMEOUT", "120")

        config = ProofSketcherConfig.load()

        assert config.debug is True
        assert config.parser.lean_timeout == 120

    def test_config_validation(self):
        """Test configuration validation."""
        config = ProofSketcherConfig()
        config.cache_dir = Path("/invalid/path/that/cannot/exist")

        # Validation should create directories or fail gracefully
        try:
            config._validate()
        except ValueError as e:
            assert "Cannot create cache directory" in str(e)
