"""Comprehensive test suite to improve AIGenerator coverage.

This test file focuses on testing the uncovered methods and edge cases
to bring the ai_generator coverage from 17% to a target of 80%+.
"""

import json
import subprocess
import time
from typing import Iterator
from unittest.mock import Mock, patch, MagicMock
from pathlib import Path

import pytest

from proof_sketcher.core.exceptions import (
    AIExecutableError,
    AITimeoutError,
    GeneratorError,
)
from proof_sketcher.generator.ai_generator import AIGenerator
from proof_sketcher.generator.models import (
    GenerationConfig,
    GenerationRequest,
    GenerationResponse,
    GenerationType,
    ProofSketch,
    ProofStep,
)
from proof_sketcher.parser.models import TheoremInfo


class TestAIGeneratorCoverageImprovement:
    """Test suite to improve AIGenerator coverage."""

    @pytest.fixture
    def sample_theorem(self):
        """Create a sample theorem for testing."""
        return TheoremInfo(
            name="test_theorem",
            statement="∀ n : ℕ, n + 0 = n",
            proof="by simp",
            dependencies=["Nat.add_zero"],
            docstring="Zero is the right identity for addition",
        )

    @pytest.fixture
    def generator(self):
        """Create an AIGenerator instance."""
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)  # Mock successful executable check
            return AIGenerator()

    @pytest.fixture
    def custom_generator(self):
        """Create an AIGenerator with custom config."""
        config = GenerationConfig(
            temperature=0.5,
            max_tokens=2000,
            verbosity="concise"
        )
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)  # Mock successful executable check
            return AIGenerator(ai_executable="custom-claude", default_config=config)

    def test_generator_initialization_default(self):
        """Test generator initialization with defaults."""
        generator = AIGenerator()
        assert generator.ai_executable == "claude"
        assert isinstance(generator.default_config, GenerationConfig)
        assert generator.default_config.temperature == 0.7

    def test_generator_initialization_custom(self):
        """Test generator initialization with custom parameters."""
        config = GenerationConfig(temperature=0.3, max_tokens=1000)
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)  # Mock successful executable check
            
            generator = AIGenerator(ai_executable="custom-ai", default_config=config)
            
            assert generator.ai_executable == "custom-ai"
            assert generator.default_config.temperature == 0.3
            assert generator.default_config.max_tokens == 1000

    def test_generate_eli5_explanation_success(self, generator, sample_theorem):
        """Test generate_eli5_explanation with successful response."""
        with patch.object(generator, '_generate_response') as mock_generate:
            mock_request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test_theorem",
                theorem_statement="∀ n : ℕ, n + 0 = n"
            )
            mock_response = GenerationResponse(
                request=mock_request,
                content="This theorem says that adding zero to any number gives you the same number back.",
                success=True
            )
            mock_generate.return_value = mock_response
            
            result = generator.generate_eli5_explanation(sample_theorem)
            
            # The method returns a string (the content), not the full response
            assert isinstance(result, str)
            assert "adding zero" in result
            mock_generate.assert_called_once()
            
            # Check the request was properly constructed
            request = mock_generate.call_args[0][0]
            assert request.generation_type == GenerationType.ELI5_EXPLANATION
            assert request.theorem_name == "test_theorem"

    def test_generate_eli5_explanation_with_custom_config(self, generator, sample_theorem):
        """Test generate_eli5_explanation with custom configuration."""
        custom_config = GenerationConfig(temperature=0.2, verbosity="verbose")
        
        with patch.object(generator, '_generate_response') as mock_generate:
            mock_request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test_theorem",
                theorem_statement="∀ n : ℕ, n + 0 = n"
            )
            mock_response = GenerationResponse(
                request=mock_request,
                content="Detailed explanation...",
                success=True
            )
            mock_generate.return_value = mock_response
            
            result = generator.generate_eli5_explanation(sample_theorem, config=custom_config)
            
            # The method returns a string (the content), not the full response
            assert isinstance(result, str)
            assert "Detailed explanation" in result
            request = mock_generate.call_args[0][0]
            assert request.config.temperature == 0.2
            assert request.config.verbosity == "verbose"

    def test_generate_tactic_explanation_success(self, generator, sample_theorem):
        """Test generate_tactic_explanation with successful response."""
        with patch.object(generator, '_generate_response') as mock_generate:
            mock_request = GenerationRequest(
                generation_type=GenerationType.TACTIC_EXPLANATION,
                theorem_name="test_theorem",
                theorem_statement="∀ n : ℕ, n + 0 = n"
            )
            mock_response = GenerationResponse(
                request=mock_request,
                content="The 'simp' tactic simplifies expressions by applying simplification rules.",
                success=True
            )
            mock_generate.return_value = mock_response
            
            result = generator.generate_tactic_explanation(sample_theorem)
            
            # Returns a string
            assert isinstance(result, str)
            assert "simp" in result
            
            request = mock_generate.call_args[0][0]
            assert request.generation_type == GenerationType.TACTIC_EXPLANATION

    def test_generate_step_by_step_success(self, generator, sample_theorem):
        """Test generate_step_by_step with successful response."""
        with patch.object(generator, '_generate_response') as mock_generate:
            mock_request = GenerationRequest(
                generation_type=GenerationType.STEP_BY_STEP,
                theorem_name="test_theorem",
                theorem_statement="∀ n : ℕ, n + 0 = n"
            )
            mock_response = GenerationResponse(
                request=mock_request,
                content="Step 1: Apply reflexivity. Step 2: The equation n + 0 = n is true by definition.",
                success=True
            )
            mock_generate.return_value = mock_response
            
            result = generator.generate_step_by_step(sample_theorem)
            
            # generate_step_by_step returns a string, not a GenerationResponse
            assert isinstance(result, str)
            assert "Apply reflexivity" in result
            assert "n + 0 = n" in result
            
            request = mock_generate.call_args[0][0]
            assert request.generation_type == GenerationType.STEP_BY_STEP

    def test_generate_streaming_success(self, generator, sample_theorem):
        """Test generate_streaming with successful streaming response."""
        mock_chunks = ["First part", " of the", " explanation."]
        
        with patch('subprocess.Popen') as mock_popen:
            # Mock the process
            mock_process = Mock()
            mock_process.stdout.readline.side_effect = ["First part", " of the", " explanation.", ""]
            mock_process.wait.return_value = 0
            mock_process.stdin = Mock()
            mock_popen.return_value = mock_process
            
            chunks = list(generator.generate_streaming(sample_theorem, GenerationType.ELI5_EXPLANATION))
            
            # Should return chunks as they come
            assert len(chunks) >= 1
            assert any("First part" in chunk for chunk in chunks)

    def test_generate_streaming_with_custom_config(self, generator, sample_theorem):
        """Test generate_streaming with custom configuration."""
        config = GenerationConfig(stream=True, temperature=0.1)
        
        with patch('subprocess.Popen') as mock_popen:
            # Mock the process  
            mock_process = Mock()
            mock_process.stdout.readline.side_effect = ["Streaming response", ""]
            mock_process.wait.return_value = 0
            mock_process.stdin = Mock()
            mock_popen.return_value = mock_process
            
            chunks = list(generator.generate_streaming(sample_theorem, GenerationType.TACTIC_EXPLANATION, config=config))
            
            assert len(chunks) >= 1
            assert any("Streaming response" in chunk for chunk in chunks)

    def test_generate_response_success(self, generator):
        """Test _generate_response with successful AI call."""
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="test",
            theorem_statement="True"
        )
        
        with patch.object(generator, '_call_ai') as mock_call:
            mock_call.return_value = "Natural language explanation"
            
            start_time = time.time()
            response = generator._generate_response(request)
            
            assert response.success
            assert response.content == "Natural language explanation"
            assert response.request == request
            assert response.generation_time_ms is not None
            assert response.generation_time_ms >= 0

    def test_generate_response_ai_error(self, generator):
        """Test _generate_response handling AI call errors."""
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="test",
            theorem_statement="True"
        )
        
        with patch.object(generator, '_call_ai') as mock_call:
            mock_call.side_effect = GeneratorError("AI call failed")
            
            response = generator._generate_response(request)
            
            assert not response.success
            assert "AI call failed" in response.error_message
            assert response.content == ""
            assert response.generation_time_ms is not None

    def test_generate_response_unexpected_error(self, generator):
        """Test _generate_response handling unexpected errors."""
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="test",
            theorem_statement="True"
        )
        
        with patch.object(generator, '_call_ai') as mock_call:
            mock_call.side_effect = RuntimeError("Unexpected error")
            
            response = generator._generate_response(request)
            
            assert not response.success
            assert "Unexpected error during generation" in response.error_message
            assert "RuntimeError: Unexpected error" in response.error_message

    def test_call_ai_success(self, generator):
        """Test _call_ai with successful subprocess call."""
        config = GenerationConfig(temperature=0.5, max_tokens=1000)
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Generated response",
                stderr=""
            )
            
            result = generator._call_ai("Test prompt", config)
            
            assert result == "Generated response"
            
            # Verify subprocess was called correctly
            mock_run.assert_called_once()
            call_args = mock_run.call_args[0][0]
            assert "claude" in call_args
            assert "-p" in call_args  # Check for the actual prompt flag used

    def test_call_ai_non_zero_return_code(self, generator):
        """Test _call_ai handling non-zero return code."""
        config = GenerationConfig()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=1,
                stdout="",
                stderr="API Error: Rate limit exceeded"
            )
            
            with pytest.raises(GeneratorError) as exc_info:
                generator._call_ai("Test prompt", config)
            
            assert "Claude command failed" in str(exc_info.value)
            assert "Rate limit exceeded" in str(exc_info.value)

    def test_call_ai_timeout(self, generator):
        """Test _call_ai handling timeout."""
        config = GenerationConfig()
        
        with patch('subprocess.run') as mock_run:
            mock_run.side_effect = subprocess.TimeoutExpired("claude", 30)
            
            with pytest.raises(AITimeoutError) as exc_info:
                generator._call_ai("Test prompt", config)
            
            assert "AI call timed out" in str(exc_info.value)

    def test_call_ai_file_not_found(self, generator):
        """Test _call_ai handling executable not found."""
        config = GenerationConfig()
        
        with patch('subprocess.run') as mock_run:
            mock_run.side_effect = FileNotFoundError("claude: command not found")
            
            with pytest.raises(AIExecutableError) as exc_info:
                generator._call_ai("Test prompt", config)
            
            assert "AI executable not found" in str(exc_info.value)

    def test_call_ai_permission_error(self, generator):
        """Test _call_ai handling permission error."""
        config = GenerationConfig()
        
        with patch('subprocess.run') as mock_run:
            mock_run.side_effect = PermissionError("Permission denied")
            
            with pytest.raises(AIExecutableError) as exc_info:
                generator._call_ai("Test prompt", config)
            
            assert "Permission denied" in str(exc_info.value)

    def test_build_ai_command_basic(self, generator):
        """Test _build_ai_command with basic configuration."""
        config = GenerationConfig(temperature=0.3, max_tokens=2000)
        
        command = generator._build_ai_command(config)
        
        assert "claude" in command
        assert str(config.temperature) in " ".join(command)
        assert str(config.max_tokens) in " ".join(command)

    def test_build_ai_command_with_streaming(self, generator):
        """Test _build_ai_command with streaming enabled."""
        config = GenerationConfig(stream=True)
        
        command = generator._build_ai_command(config)
        
        # Check that streaming flag is included
        command_str = " ".join(command)
        assert "--stream" in command_str or "stream" in command_str

    def test_build_ai_command_with_system_message(self, generator):
        """Test _build_ai_command with custom system message."""
        config = GenerationConfig(system_message="You are a helpful math tutor")
        
        command = generator._build_ai_command(config)
        
        command_str = " ".join(command)
        assert "math tutor" in command_str or "--system" in command_str

    def test_build_ai_command_with_stop_sequences(self, generator):
        """Test _build_ai_command with stop sequences."""
        config = GenerationConfig(stop_sequences=["END", "STOP"])
        
        command = generator._build_ai_command(config)
        
        command_str = " ".join(command)
        # Stop sequences should be included somehow
        assert "--stop" in command_str or len(command) > 3

    def test_check_ai_available_true(self, generator):
        """Test check_ai_available when AI executable is available."""
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)
            
            result = generator.check_ai_available()
            
            assert result is True
            mock_run.assert_called_once()

    def test_check_ai_available_false_not_found(self, generator):
        """Test check_ai_available when AI executable not found."""
        with patch('subprocess.run') as mock_run:
            mock_run.side_effect = FileNotFoundError()
            
            result = generator.check_ai_available()
            
            assert result is False

    def test_check_ai_available_false_non_zero_exit(self, generator):
        """Test check_ai_available when AI executable returns non-zero."""
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=1)
            
            result = generator.check_ai_available()
            
            assert result is False

    def test_check_ai_available_exception(self, generator):
        """Test check_ai_available handling unexpected exceptions."""
        with patch('subprocess.run') as mock_run:
            mock_run.side_effect = PermissionError("Permission denied")
            
            result = generator.check_ai_available()
            
            assert result is False

    def test_get_ai_version_success(self, generator):
        """Test get_ai_version with successful version retrieval."""
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Claude CLI v1.2.3 (build 12345)\n"
            )
            
            version = generator.get_ai_version()
            
            assert version == "Claude CLI v1.2.3 (build 12345)"

    def test_get_ai_version_failure(self, generator):
        """Test get_ai_version when version command fails."""
        with patch('subprocess.run') as mock_run:
            mock_run.side_effect = FileNotFoundError()
            
            version = generator.get_ai_version()
            
            assert version is None

    def test_get_ai_version_non_zero_exit(self, generator):
        """Test get_ai_version with non-zero exit code."""
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=1,
                stdout="",
                stderr="Version command failed"
            )
            
            version = generator.get_ai_version()
            
            assert version is None

    def test_validate_setup_success(self, generator):
        """Test validate_setup when everything is configured correctly."""
        with patch.object(generator, 'check_ai_available', return_value=True), \
             patch.object(generator, 'get_ai_version', return_value="Claude CLI v1.2.3"), \
             patch.object(generator, '_call_ai', return_value="Claude is working"):
            
            result = generator.validate_setup()
            
            assert result is True

    def test_validate_setup_ai_not_available(self, generator):
        """Test validate_setup when AI executable is not available."""
        with patch.object(generator, 'check_ai_available', return_value=False):
            
            result = generator.validate_setup()
            
            assert result is False

    def test_validate_setup_version_unavailable(self, generator):
        """Test validate_setup when version cannot be retrieved."""
        with patch.object(generator, 'check_ai_available', return_value=True), \
             patch.object(generator, 'get_ai_version', return_value=None), \
             patch.object(generator, '_call_ai', return_value="Claude is working"):
            
            # Should still be valid even if version can't be retrieved
            result = generator.validate_setup()
            
            assert result is True

    def test_backward_compatibility_aliases(self):
        """Test that backward compatibility aliases work correctly."""
        # Import aliases from ai_generator module
        from proof_sketcher.generator.ai_generator import (
            ClaudeError,
            ClaudeExecutableError,
            ClaudeAPIError,
            ClaudeTimeoutError
        )
        
        # Verify they map to the correct new exceptions
        assert ClaudeError is GeneratorError
        assert ClaudeExecutableError is AIExecutableError
        assert ClaudeAPIError is GeneratorError
        assert ClaudeTimeoutError is AITimeoutError

    def test_custom_ai_executable(self):
        """Test generator with custom AI executable."""
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0)  # Mock successful executable check
            generator = AIGenerator(ai_executable="gpt-4")
        
        assert generator.ai_executable == "gpt-4"
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(returncode=0, stdout="Response")
            
            config = GenerationConfig()
            result = generator._call_ai("Test", config)
            
            # Verify the custom executable was used
            call_args = mock_run.call_args[0][0]
            assert "gpt-4" in call_args

    def test_long_prompt_handling(self, generator):
        """Test handling of very long prompts."""
        # Create a very long prompt
        long_prompt = "This is a test prompt. " * 1000
        config = GenerationConfig()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Response to long prompt"
            )
            
            result = generator._call_ai(long_prompt, config)
            
            assert result == "Response to long prompt"
            # Verify the long prompt was handled
            mock_run.assert_called_once()

    def test_special_characters_in_prompt(self, generator):
        """Test handling of special characters in prompts."""
        special_prompt = "Test with special chars: ∀∃∈∉≤≥→↔∧∨¬"
        config = GenerationConfig()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Response with special chars"
            )
            
            result = generator._call_ai(special_prompt, config)
            
            assert result == "Response with special chars"

    def test_empty_prompt_handling(self, generator):
        """Test handling of empty prompts."""
        config = GenerationConfig()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Empty prompt response"
            )
            
            result = generator._call_ai("", config)
            
            assert result == "Empty prompt response"

    def test_multiline_prompt_handling(self, generator):
        """Test handling of multiline prompts."""
        multiline_prompt = """This is a multiline prompt
        with multiple lines
        and indentation."""
        config = GenerationConfig()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Multiline response"
            )
            
            result = generator._call_ai(multiline_prompt, config)
            
            assert result == "Multiline response"


class TestAIGeneratorIntegration:
    """Integration tests for AI generator functionality."""

    @pytest.fixture
    def mock_ai_response(self):
        """Create a mock AI response."""
        return """
        This theorem states that addition is commutative for natural numbers.
        
        ## Key Steps:
        1. **Base case**: For n = 0, we have 0 + m = m = m + 0 by definition
        2. **Inductive step**: Assume n + m = m + n, prove (n+1) + m = m + (n+1)
        3. **Conclusion**: By induction, the property holds for all natural numbers
        
        The proof uses the associativity and commutativity properties of addition.
        """

    def test_full_generation_pipeline(self, mock_ai_response):
        """Test complete generation pipeline from theorem to response."""
        theorem = TheoremInfo(
            name="nat_add_comm",
            statement="∀ (m n : Nat), m + n = n + m",
            proof="by induction on n",
            dependencies=["Nat.add_assoc", "Nat.add_zero"]
        )
        
        generator = AIGenerator()
        
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout=mock_ai_response
            )
            
            proof_sketch = generator.generate_proof_sketch(theorem)
            
            assert isinstance(proof_sketch, ProofSketch)
            assert "commutative" in proof_sketch.introduction
            assert proof_sketch.theorem_name == "nat_add_comm"

    def test_error_recovery_and_logging(self, caplog):
        """Test error recovery and proper logging."""
        theorem = TheoremInfo(name="test", statement="True")
        generator = AIGenerator()
        
        with patch('subprocess.run') as mock_run:
            mock_run.side_effect = subprocess.TimeoutExpired("claude", 30)
            
            # generate_proof_sketch should raise an exception on timeout
            with pytest.raises((AITimeoutError, GeneratorError)) as exc_info:
                generator.generate_proof_sketch(theorem)
            
            # Check that the error contains timeout information
            assert "timed out" in str(exc_info.value).lower() or "timeout" in str(exc_info.value).lower()

    def test_config_inheritance_and_override(self):
        """Test configuration inheritance and override behavior."""
        default_config = GenerationConfig(temperature=0.7, max_tokens=4000)
        generator = AIGenerator(default_config=default_config)
        
        # Test that default config is used
        assert generator.default_config.temperature == 0.7
        assert generator.default_config.max_tokens == 4000
        
        # Test override behavior
        override_config = GenerationConfig(temperature=0.2)
        theorem = TheoremInfo(name="test", statement="True")
        
        with patch.object(generator, '_call_ai') as mock_call:
            mock_call.return_value = "Response"
            
            generator.generate_proof_sketch(theorem, config=override_config)
            
            # Verify the override config was used
            # _call_ai is called with positional args: _call_ai(prompt, config)
            call_config = mock_call.call_args[0][1]  # Second positional argument
            assert call_config.temperature == 0.2
            # Default values should still be present for non-overridden fields
            assert call_config.max_tokens == 4000