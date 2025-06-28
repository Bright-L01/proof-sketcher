"""Tests for ClaudeGenerator with mocked subprocess calls."""

import json
import subprocess
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.generator.claude import (ClaudeAPIError,
                                             ClaudeExecutableError,
                                             ClaudeGenerator,
                                             ClaudeTimeoutError)
from proof_sketcher.generator.models import (GenerationConfig, GenerationType,
                                             ProofSketch)
from proof_sketcher.parser.models import TheoremInfo


class TestClaudeGenerator:
    """Tests for ClaudeGenerator class."""

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generator_initialization_success(self, mock_run):
        """Test successful generator initialization."""
        mock_run.return_value = Mock(returncode=0, stdout="Claude CLI v1.0.0")

        generator = ClaudeGenerator()
        assert generator.claude_executable == "claude"
        assert isinstance(generator.default_config, GenerationConfig)

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generator_initialization_claude_not_found(self, mock_run):
        """Test generator initialization when Claude is not found."""
        mock_run.side_effect = FileNotFoundError()

        with pytest.raises(ClaudeExecutableError):
            ClaudeGenerator()

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generate_proof_sketch_success(self, mock_run):
        """Test successful proof sketch generation."""

        # Mock version check
        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                # Mock successful generation
                sketch_json = {
                    "theorem_name": "add_zero",
                    "introduction": "This theorem states the additive identity for natural numbers.",
                    "key_steps": [
                        {
                            "step_number": 1,
                            "description": "Apply the definition of addition",
                            "mathematical_content": "n + 0 = n by definition",
                            "tactics": ["simp"],
                            "intuition": "Addition of zero doesn't change the number",
                        }
                    ],
                    "conclusion": "Therefore, n + 0 = n for all natural numbers n.",
                    "difficulty_level": "beginner",
                    "mathematical_areas": ["arithmetic"],
                    "prerequisites": ["natural_numbers"],
                }
                return Mock(returncode=0, stdout=json.dumps(sketch_json))

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()

        theorem = TheoremInfo(
            name="add_zero",
            statement="∀ n : Nat, n + 0 = n",
            dependencies=["Nat.add_zero"],
        )

        sketch = generator.generate_proof_sketch(theorem)

        assert isinstance(sketch, ProofSketch)
        assert sketch.theorem_name == "add_zero"
        assert (
            sketch.introduction
            == "This theorem states the additive identity for natural numbers."
        )
        assert len(sketch.key_steps) == 1
        assert sketch.key_steps[0].step_number == 1
        assert sketch.difficulty_level == "beginner"
        assert sketch.mathematical_areas == ["arithmetic"]

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generate_proof_sketch_with_wrapped_json(self, mock_run):
        """Test proof sketch generation with JSON wrapped in markdown."""

        # Mock version check and generation
        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                sketch_json = {
                    "theorem_name": "test",
                    "introduction": "Test intro",
                    "key_steps": [],
                    "conclusion": "Test conclusion",
                }
                wrapped_response = f"```json\n{json.dumps(sketch_json)}\n```"
                return Mock(returncode=0, stdout=wrapped_response)

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        theorem = TheoremInfo(name="test", statement="P")

        sketch = generator.generate_proof_sketch(theorem)

        assert isinstance(sketch, ProofSketch)
        assert sketch.theorem_name == "test"

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generate_proof_sketch_invalid_json(self, mock_run):
        """Test proof sketch generation with invalid JSON response."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                return Mock(returncode=0, stdout="Invalid JSON response")

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        theorem = TheoremInfo(name="test", statement="P")

        # Should fallback to simple proof sketch
        sketch = generator.generate_proof_sketch(theorem)

        assert isinstance(sketch, ProofSketch)
        assert sketch.theorem_name == "test"
        assert "Invalid JSON response" in sketch.introduction

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generate_eli5_explanation_success(self, mock_run):
        """Test successful ELI5 explanation generation."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                return Mock(
                    returncode=0, stdout="This is a simple explanation for beginners."
                )

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        theorem = TheoremInfo(name="add_zero", statement="∀ n : Nat, n + 0 = n")

        explanation = generator.generate_eli5_explanation(theorem)

        assert explanation == "This is a simple explanation for beginners."

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generate_tactic_explanation_success(self, mock_run):
        """Test successful tactic explanation generation."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                return Mock(
                    returncode=0,
                    stdout="The 'simp' tactic simplifies the expression using known simplification rules.",
                )

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        theorem = TheoremInfo(
            name="add_zero", statement="∀ n : Nat, n + 0 = n", proof="by simp"
        )

        explanation = generator.generate_tactic_explanation(theorem)

        assert "simp" in explanation
        assert "simplifies" in explanation

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generate_step_by_step_success(self, mock_run):
        """Test successful step-by-step explanation generation."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                return Mock(
                    returncode=0,
                    stdout="Step 1: Start with the theorem statement.\nStep 2: Apply the definition.\nStep 3: Conclude the proof.",
                )

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        theorem = TheoremInfo(name="add_zero", statement="∀ n : Nat, n + 0 = n")

        explanation = generator.generate_step_by_step(theorem)

        assert "Step 1" in explanation
        assert "Step 2" in explanation
        assert "Step 3" in explanation

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_generate_with_custom_config(self, mock_run):
        """Test generation with custom configuration."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                # Verify the command includes our custom settings
                cmd = args[0]
                assert "-m" in cmd
                assert "claude-3-5-haiku-20241022" in cmd
                assert "-t" in cmd
                assert "0.3" in cmd
                assert "--max-tokens" in cmd
                assert "2000" in cmd

                return Mock(returncode=0, stdout="Custom config response")

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        config = GenerationConfig.fast()  # Uses Haiku model with specific settings

        theorem = TheoremInfo(name="test", statement="P")

        explanation = generator.generate_eli5_explanation(theorem, config)
        assert explanation == "Custom config response"

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_claude_api_error(self, mock_run):
        """Test handling of Claude API errors."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                return Mock(returncode=1, stderr="API rate limit exceeded")

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        theorem = TheoremInfo(name="test", statement="P")

        with pytest.raises(ClaudeAPIError, match="API rate limit exceeded"):
            generator.generate_eli5_explanation(theorem)

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_claude_timeout_error(self, mock_run):
        """Test handling of Claude timeout errors."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                raise subprocess.TimeoutExpired("claude", 120)

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        theorem = TheoremInfo(name="test", statement="P")

        with pytest.raises(ClaudeTimeoutError):
            generator.generate_eli5_explanation(theorem)

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_streaming_generation(self, mock_run):
        """Test streaming generation functionality."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        theorem = TheoremInfo(name="test", statement="P")

        # Mock Popen for streaming
        mock_process = Mock()
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stderr = Mock()
        mock_process.wait.return_value = 0

        # Mock streaming output
        mock_process.stdout.readline.side_effect = [
            "First chunk of response\n",
            "Second chunk of response\n",
            "Final chunk of response\n",
            "",  # End of stream
        ]

        with patch(
            "proof_sketcher.generator.claude.subprocess.Popen",
            return_value=mock_process,
        ):
            chunks = list(
                generator.generate_streaming(theorem, GenerationType.ELI5_EXPLANATION)
            )

        assert len(chunks) == 3
        assert chunks[0] == "First chunk of response"
        assert chunks[1] == "Second chunk of response"
        assert chunks[2] == "Final chunk of response"

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_build_claude_command(self, mock_run):
        """Test Claude command building."""
        mock_run.return_value = Mock(returncode=0, stdout="Claude CLI v1.0.0")

        generator = ClaudeGenerator()

        config = GenerationConfig(
            model="claude-3-5-sonnet-20241022",
            temperature=0.8,
            max_tokens=3000,
            system_message="You are a math tutor",
            stop_sequences=["END", "STOP"],
        )

        cmd = generator._build_claude_command(config)

        expected_elements = [
            "claude",
            "-m",
            "claude-3-5-sonnet-20241022",
            "-t",
            "0.8",
            "--max-tokens",
            "3000",
            "-s",
            "You are a math tutor",
            "--stop",
            "END",
            "--stop",
            "STOP",
            "-p",
        ]

        for element in expected_elements:
            assert element in cmd

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_check_claude_available(self, mock_run):
        """Test checking Claude availability."""
        # Test successful check
        mock_run.return_value = Mock(returncode=0, stdout="Claude CLI v1.0.0")
        generator = ClaudeGenerator()
        assert generator.check_claude_available() is True

        # Test failed check
        mock_run.return_value = Mock(returncode=1)
        assert generator.check_claude_available() is False

        # Test FileNotFoundError
        mock_run.side_effect = FileNotFoundError()
        assert generator.check_claude_available() is False

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_get_claude_version(self, mock_run):
        """Test getting Claude version."""
        mock_run.side_effect = [
            Mock(returncode=0, stdout="Claude CLI v1.0.0"),  # For initialization
            Mock(returncode=0, stdout="Claude CLI version 1.2.3"),  # For version check
        ]

        generator = ClaudeGenerator()
        version = generator.get_claude_version()

        assert version == "Claude CLI version 1.2.3"

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_validate_setup_success(self, mock_run):
        """Test successful setup validation."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                # Mock successful test call
                return Mock(returncode=0, stdout="Claude is working")

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        assert generator.validate_setup() is True

    @patch("proof_sketcher.generator.claude.subprocess.run")
    def test_validate_setup_test_failure(self, mock_run):
        """Test setup validation with test call failure."""

        def mock_subprocess(*args, **kwargs):
            if "--version" in args[0]:
                return Mock(returncode=0, stdout="Claude CLI v1.0.0")
            else:
                # Mock failed test call
                return Mock(returncode=1, stderr="API key not found")

        mock_run.side_effect = mock_subprocess

        generator = ClaudeGenerator()
        assert generator.validate_setup() is False
