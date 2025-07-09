"""
Test the new AI integration to ensure it works properly.
This replaces the broken subprocess-based Claude CLI tests.
"""

import os
import pytest
from unittest.mock import patch, MagicMock

from proof_sketcher.ai import AIClient, AnthropicClient, OfflineClient
from proof_sketcher.generator.ai_generator_fixed import FixedAIGenerator
from proof_sketcher.parser.models import TheoremInfo
from proof_sketcher.generator.models import GenerationConfig, ProofSketch


class TestOfflineClient:
    """Test the offline fallback client."""
    
    def test_offline_client_always_available(self):
        """Offline client should always be available."""
        client = OfflineClient()
        assert client.is_available() is True
    
    def test_offline_client_generates_response(self):
        """Offline client should generate template responses."""
        client = OfflineClient()
        
        # Test theorem explanation
        response = client.generate("Explain theorem Nat.add_comm")
        assert isinstance(response, str)
        assert len(response) > 0
        assert "theorem" in response.lower()
    
    def test_offline_client_proof_sketch(self):
        """Test proof sketch generation."""
        client = OfflineClient()
        response = client.generate("Generate a proof sketch for theorem add_assoc")
        
        # Should return JSON-like structure
        assert isinstance(response, str)
        assert "theorem_name" in response
        assert "introduction" in response
        assert "key_steps" in response
    
    def test_offline_client_eli5(self):
        """Test ELI5 explanation."""
        client = OfflineClient()
        response = client.generate("Explain theorem List.append like I'm five")
        
        assert isinstance(response, str)
        assert "simple" in response.lower() or "imagine" in response.lower()
    
    def test_offline_client_tactics(self):
        """Test tactic explanation."""
        client = OfflineClient()
        response = client.generate("Explain the tactics used in this proof")
        
        assert isinstance(response, str)
        assert "tactic" in response.lower()
    
    def test_offline_client_info(self):
        """Test client info."""
        client = OfflineClient()
        info = client.get_info()
        
        assert info["client_type"] == "OfflineClient"
        assert info["is_available"] is True
        assert info["provider"] == "Offline Templates"


class TestAnthropicClient:
    """Test the Anthropic client."""
    
    def test_anthropic_client_without_api_key(self):
        """Client should handle missing API key gracefully."""
        with patch.dict(os.environ, {}, clear=True):
            client = AnthropicClient()
            assert client.is_available() is False
    
    @patch('proof_sketcher.ai.anthropic_client.ANTHROPIC_AVAILABLE', False)
    def test_anthropic_client_without_sdk(self):
        """Client should handle missing SDK gracefully."""
        client = AnthropicClient()
        assert client.is_available() is False
    
    @patch('proof_sketcher.ai.anthropic_client.Anthropic')
    def test_anthropic_client_with_mock(self, mock_anthropic_class):
        """Test with mocked Anthropic SDK."""
        # Mock the API response
        mock_client = MagicMock()
        mock_response = MagicMock()
        mock_response.content = [MagicMock(text="This is a test response")]
        mock_client.messages.create.return_value = mock_response
        mock_anthropic_class.return_value = mock_client
        
        # Set fake API key
        with patch.dict(os.environ, {'ANTHROPIC_API_KEY': 'test-key'}):
            client = AnthropicClient()
            assert client.is_available() is True
            
            response = client.generate("Test prompt")
            assert response == "This is a test response"
            
            # Verify API was called correctly
            mock_client.messages.create.assert_called_once()
            call_args = mock_client.messages.create.call_args
            assert call_args.kwargs['messages'][0]['content'] == "Test prompt"
    
    @patch('proof_sketcher.ai.anthropic_client.Anthropic')
    def test_anthropic_client_fallback_on_error(self, mock_anthropic_class):
        """Test fallback when API fails."""
        mock_client = MagicMock()
        mock_client.messages.create.side_effect = Exception("API Error")
        mock_anthropic_class.return_value = mock_client
        
        with patch.dict(os.environ, {'ANTHROPIC_API_KEY': 'test-key'}):
            client = AnthropicClient()
            response = client.generate("Explain theorem")
            
            # Should return fallback response
            assert isinstance(response, str)
            assert "theorem" in response.lower()
            assert "unavailable" in response
    
    def test_anthropic_client_info(self):
        """Test client info."""
        with patch.dict(os.environ, {}, clear=True):
            client = AnthropicClient()
            info = client.get_info()
            
            assert info["client_type"] == "AnthropicClient"
            assert info["provider"] == "Anthropic"
            assert info["api_key_set"] is False


class TestFixedAIGenerator:
    """Test the fixed AI generator."""
    
    def test_generator_with_offline_fallback(self):
        """Generator should work with offline fallback."""
        generator = FixedAIGenerator(use_offline_fallback=True)
        
        # Create test theorem
        theorem = TheoremInfo(
            name="test_theorem",
            statement="∀ a b : Nat, a + b = b + a",
            proof="by simp [add_comm]",
            dependencies=[],
            docstring="Test theorem"
        )
        
        # Should generate without errors
        sketch = generator.generate_proof_sketch(theorem)
        assert isinstance(sketch, ProofSketch)
        assert sketch.theorem_name == "test_theorem"
        assert len(sketch.introduction) > 0
        assert len(sketch.key_steps) > 0
    
    def test_generator_eli5(self):
        """Test ELI5 generation."""
        generator = FixedAIGenerator(ai_client=OfflineClient())
        
        theorem = TheoremInfo(
            name="add_comm",
            statement="a + b = b + a",
            proof="",
            dependencies=[],
            docstring=""
        )
        
        explanation = generator.generate_eli5_explanation(theorem)
        assert isinstance(explanation, str)
        assert len(explanation) > 0
    
    def test_generator_tactics(self):
        """Test tactic explanation generation."""
        generator = FixedAIGenerator(ai_client=OfflineClient())
        
        theorem = TheoremInfo(
            name="test",
            statement="true",
            proof="intro h; exact h",
            dependencies=[],
            docstring=""
        )
        
        explanation = generator.generate_tactic_explanation(theorem)
        assert isinstance(explanation, str)
        assert "tactic" in explanation.lower()
    
    def test_generator_step_by_step(self):
        """Test step-by-step generation."""
        generator = FixedAIGenerator(ai_client=OfflineClient())
        
        theorem = TheoremInfo(
            name="test",
            statement="P → P",
            proof="intro h; exact h",
            dependencies=[],
            docstring=""
        )
        
        explanation = generator.generate_step_by_step(theorem)
        assert isinstance(explanation, str)
        assert "step" in explanation.lower()
    
    @patch('proof_sketcher.ai.anthropic_client.Anthropic')
    def test_generator_with_anthropic(self, mock_anthropic_class):
        """Test generator with mocked Anthropic client."""
        # Mock successful API response
        mock_client = MagicMock()
        mock_response = MagicMock()
        mock_response.content = [MagicMock(text="""{
            "theorem_name": "test_theorem",
            "introduction": "This theorem shows commutativity",
            "key_steps": [
                {
                    "step_number": 1,
                    "description": "Apply commutativity",
                    "mathematical_content": "a + b = b + a",
                    "tactics": ["simp", "add_comm"]
                }
            ],
            "conclusion": "Commutativity is established",
            "difficulty_level": "beginner",
            "mathematical_areas": ["algebra"],
            "prerequisites": ["basic arithmetic"]
        }""")]
        mock_client.messages.create.return_value = mock_response
        mock_anthropic_class.return_value = mock_client
        
        with patch.dict(os.environ, {'ANTHROPIC_API_KEY': 'test-key'}):
            generator = FixedAIGenerator()
            
            theorem = TheoremInfo(
                name="add_comm",
                statement="∀ a b : Nat, a + b = b + a",
                proof="",
                dependencies=[],
                docstring=""
            )
            
            sketch = generator.generate_proof_sketch(theorem)
            assert sketch.theorem_name == "test_theorem"
            assert sketch.introduction == "This theorem shows commutativity"
            assert len(sketch.key_steps) == 1
            assert sketch.key_steps[0].description == "Apply commutativity"


def test_ai_integration_end_to_end():
    """Test complete AI integration flow."""
    # This test verifies the integration works without crashing
    generator = FixedAIGenerator(use_offline_fallback=True)
    
    theorem = TheoremInfo(
        name="example",
        statement="1 + 1 = 2",
        proof="rfl",
        dependencies=[],
        docstring="Simple arithmetic"
    )
    
    # Test all generation methods
    proof_sketch = generator.generate_proof_sketch(theorem)
    assert proof_sketch is not None
    
    eli5 = generator.generate_eli5_explanation(theorem)
    assert isinstance(eli5, str) and len(eli5) > 0
    
    tactics = generator.generate_tactic_explanation(theorem)
    assert isinstance(tactics, str) and len(tactics) > 0
    
    steps = generator.generate_step_by_step(theorem)
    assert isinstance(steps, str) and len(steps) > 0
    
    # Test streaming (should work even if not truly streaming)
    stream = list(generator.generate_streaming(
        theorem,
        generation_type="proof_sketch"
    ))
    assert len(stream) > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])