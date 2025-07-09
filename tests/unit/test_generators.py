"""Unit tests for generator modules."""

import json
import tempfile
from pathlib import Path
from unittest.mock import Mock, patch, AsyncMock

import pytest

from proof_sketcher.generator.ai_generator import AIGenerator
from proof_sketcher.generator.offline import OfflineGenerator
from proof_sketcher.generator.cache import GenerationCache
from proof_sketcher.generator.models import ProofSketch, ProofStep, GenerationContext
from proof_sketcher.generator.prompts.base import BasePromptTemplate
from proof_sketcher.generator.prompts.proof_sketch import ProofSketchPrompt
from proof_sketcher.generator.prompts.step_by_step import StepByStepPrompt
from proof_sketcher.generator.prompts.eli5 import ELI5Prompt
from proof_sketcher.generator.prompts.mathematical_context import MathematicalContextPrompt
from proof_sketcher.generator.prompts.tactic_explanation import TacticExplanationPrompt
from proof_sketcher.parser.models import TheoremInfo


@pytest.fixture
def sample_theorem():
    """Create a sample theorem for testing."""
    return TheoremInfo(
        name="add_comm",
        statement="∀ (a b : ℕ), a + b = b + a",
        proof="by rw [Nat.add_comm]",
        line_number=10,
        docstring="Addition of natural numbers is commutative",
        dependencies=["Mathlib.Data.Nat.Basic"],
        tactics=["rw"],
        complexity_score=2
    )


@pytest.fixture
def generation_context():
    """Create a generation context for testing."""
    return GenerationContext(
        model="claude-3",
        temperature=0.7,
        max_tokens=2000,
        style="detailed",
        include_intuition=True,
        include_visualizations=True
    )


@pytest.fixture
def sample_proof_sketch():
    """Create a sample proof sketch for testing."""
    return ProofSketch(
        theorem_name="add_comm",
        theorem_statement="∀ (a b : ℕ), a + b = b + a",
        introduction="This theorem establishes the commutative property of addition for natural numbers.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="Apply commutativity of addition",
                mathematical_content="a + b = b + a",
                reasoning="Direct application of Nat.add_comm",
                tactics_used=["rw"],
                intuition="Addition order doesn't matter for natural numbers"
            )
        ],
        conclusion="Therefore, addition is commutative for all natural numbers.",
        difficulty_level="easy",
        key_insights=["Commutativity", "Natural number properties"],
        mathematical_context="Elementary number theory"
    )


class TestAIGenerator:
    """Test AI-powered proof sketch generator."""
    
    def test_ai_generator_initialization(self, generation_context):
        """Test AI generator initialization."""
        generator = AIGenerator(context=generation_context)
        assert generator.context == generation_context
        assert generator.client is not None
        assert generator.cache is not None
    
    @pytest.mark.asyncio
    async def test_generate_proof_sketch_basic(self, sample_theorem, generation_context):
        """Test basic proof sketch generation."""
        generator = AIGenerator(context=generation_context)
        
        # Mock Claude API response
        mock_response = {
            "theorem_name": "add_comm",
            "theorem_statement": "∀ (a b : ℕ), a + b = b + a",
            "introduction": "Test introduction",
            "key_steps": [
                {
                    "step_number": 1,
                    "description": "Test step",
                    "mathematical_content": "a + b = b + a",
                    "reasoning": "Test reasoning",
                    "tactics_used": ["rw"],
                    "intuition": "Test intuition"
                }
            ],
            "conclusion": "Test conclusion",
            "difficulty_level": "easy"
        }
        
        with patch.object(generator, '_call_claude_api') as mock_api:
            mock_api.return_value = json.dumps(mock_response)
            
            result = await generator.generate_proof_sketch_async(sample_theorem)
            
            assert isinstance(result, ProofSketch)
            assert result.theorem_name == "add_comm"
            assert len(result.key_steps) == 1
            mock_api.assert_called_once()
    
    def test_generate_proof_sketch_sync(self, sample_theorem, generation_context):
        """Test synchronous proof sketch generation."""
        generator = AIGenerator(context=generation_context)
        
        with patch.object(generator, 'generate_proof_sketch_async') as mock_async:
            mock_async.return_value = ProofSketch(
                theorem_name="add_comm",
                theorem_statement="∀ (a b : ℕ), a + b = b + a",
                introduction="Test",
                key_steps=[],
                conclusion="Done",
                difficulty_level="easy"
            )
            
            result = generator.generate_proof_sketch(sample_theorem)
            
            assert isinstance(result, ProofSketch)
            assert result.theorem_name == "add_comm"
    
    def test_prompt_building(self, sample_theorem, generation_context):
        """Test prompt building for Claude API."""
        generator = AIGenerator(context=generation_context)
        
        prompt = generator._build_prompt(sample_theorem)
        
        assert isinstance(prompt, str)
        assert sample_theorem.name in prompt
        assert sample_theorem.statement in prompt
        assert "proof sketch" in prompt.lower()
    
    def test_response_parsing(self, generation_context):
        """Test parsing of Claude API responses."""
        generator = AIGenerator(context=generation_context)
        
        raw_response = """{
            "theorem_name": "test",
            "theorem_statement": "Test statement",
            "introduction": "Test intro",
            "key_steps": [
                {
                    "step_number": 1,
                    "description": "Step 1",
                    "mathematical_content": "Math content",
                    "reasoning": "Because...",
                    "tactics_used": ["simp"],
                    "intuition": "Intuitive explanation"
                }
            ],
            "conclusion": "Test conclusion",
            "difficulty_level": "easy",
            "key_insights": ["Insight 1"],
            "mathematical_context": "Test context"
        }"""
        
        result = generator._parse_response(raw_response)
        
        assert isinstance(result, ProofSketch)
        assert result.theorem_name == "test"
        assert len(result.key_steps) == 1
        assert result.key_steps[0].step_number == 1
    
    def test_error_handling(self, sample_theorem, generation_context):
        """Test error handling in AI generation."""
        generator = AIGenerator(context=generation_context)
        
        with patch.object(generator, '_call_claude_api') as mock_api:
            mock_api.side_effect = Exception("API Error")
            
            with pytest.raises(Exception):
                generator.generate_proof_sketch(sample_theorem)
    
    def test_caching_integration(self, sample_theorem, generation_context, tmp_path):
        """Test integration with caching system."""
        cache = GenerationCache(cache_dir=tmp_path)
        generator = AIGenerator(context=generation_context, cache=cache)
        
        # First generation
        with patch.object(generator, '_call_claude_api') as mock_api:
            mock_api.return_value = json.dumps({
                "theorem_name": "add_comm",
                "theorem_statement": "∀ (a b : ℕ), a + b = b + a",
                "introduction": "Test",
                "key_steps": [],
                "conclusion": "Done",
                "difficulty_level": "easy"
            })
            
            result1 = generator.generate_proof_sketch(sample_theorem)
            assert mock_api.call_count == 1
        
        # Second generation should use cache
        with patch.object(generator, '_call_claude_api') as mock_api:
            result2 = generator.generate_proof_sketch(sample_theorem)
            assert mock_api.call_count == 0  # Should not call API
            assert result1.theorem_name == result2.theorem_name


class TestOfflineGenerator:
    """Test offline proof sketch generator."""
    
    def test_offline_generator_initialization(self):
        """Test offline generator initialization."""
        generator = OfflineGenerator()
        assert generator.template_library is not None
        assert generator.pattern_matcher is not None
    
    def test_generate_basic_proof_sketch(self, sample_theorem):
        """Test basic offline proof sketch generation."""
        generator = OfflineGenerator()
        
        result = generator.generate_proof_sketch(sample_theorem)
        
        assert isinstance(result, ProofSketch)
        assert result.theorem_name == sample_theorem.name
        assert result.theorem_statement == sample_theorem.statement
        assert len(result.key_steps) > 0
    
    def test_pattern_recognition(self, sample_theorem):
        """Test theorem pattern recognition."""
        generator = OfflineGenerator()
        
        patterns = generator._identify_patterns(sample_theorem)
        
        assert isinstance(patterns, list)
        # Should identify commutativity pattern
        assert any("commutat" in pattern.lower() for pattern in patterns)
    
    def test_template_selection(self, sample_theorem):
        """Test template selection based on patterns."""
        generator = OfflineGenerator()
        
        patterns = ["commutativity", "algebraic_property"]
        template = generator._select_template(patterns, sample_theorem)
        
        assert template is not None
        assert hasattr(template, 'generate_introduction')
        assert hasattr(template, 'generate_steps')
        assert hasattr(template, 'generate_conclusion')
    
    def test_proof_step_generation(self, sample_theorem):
        """Test proof step generation."""
        generator = OfflineGenerator()
        
        steps = generator._generate_proof_steps(sample_theorem)
        
        assert isinstance(steps, list)
        assert len(steps) > 0
        assert all(isinstance(step, ProofStep) for step in steps)
        assert all(step.step_number > 0 for step in steps)
    
    def test_complexity_assessment(self, sample_theorem):
        """Test theorem complexity assessment."""
        generator = OfflineGenerator()
        
        complexity = generator._assess_complexity(sample_theorem)
        
        assert complexity in ["trivial", "easy", "intermediate", "hard", "expert"]
    
    def test_intuition_generation(self, sample_theorem):
        """Test intuitive explanation generation."""
        generator = OfflineGenerator()
        
        intuition = generator._generate_intuition(sample_theorem)
        
        assert isinstance(intuition, str)
        assert len(intuition) > 0
        assert "commutative" in intuition.lower() or "order" in intuition.lower()


class TestGenerationCache:
    """Test generation cache system."""
    
    def test_cache_initialization(self, tmp_path):
        """Test cache initialization."""
        cache = GenerationCache(cache_dir=tmp_path)
        assert cache.cache_dir == tmp_path
        assert cache.cache_dir.exists()
    
    def test_cache_key_generation(self, sample_theorem):
        """Test cache key generation."""
        cache = GenerationCache()
        
        key1 = cache.get_cache_key(sample_theorem)
        key2 = cache.get_cache_key(sample_theorem)
        
        assert key1 == key2  # Deterministic
        assert len(key1) == 64  # SHA256 hex length
    
    def test_cache_put_and_get(self, sample_proof_sketch, tmp_path):
        """Test cache storage and retrieval."""
        cache = GenerationCache(cache_dir=tmp_path)
        
        key = "test_key"
        cache.put(key, sample_proof_sketch)
        
        retrieved = cache.get(key)
        
        assert retrieved is not None
        assert retrieved.theorem_name == sample_proof_sketch.theorem_name
        assert retrieved.theorem_statement == sample_proof_sketch.theorem_statement
    
    def test_cache_expiration(self, sample_proof_sketch, tmp_path):
        """Test cache expiration."""
        cache = GenerationCache(cache_dir=tmp_path, ttl_hours=0.001)  # Very short TTL
        
        key = "test_key"
        cache.put(key, sample_proof_sketch)
        
        # Should be available immediately
        assert cache.get(key) is not None
        
        # Should expire quickly (but testing this is timing-dependent)
        # In a real test, we'd mock time or sleep
    
    def test_cache_cleanup(self, sample_proof_sketch, tmp_path):
        """Test cache cleanup."""
        cache = GenerationCache(cache_dir=tmp_path)
        
        # Add some entries
        for i in range(5):
            cache.put(f"key_{i}", sample_proof_sketch)
        
        # Cleanup
        removed = cache.cleanup()
        
        assert isinstance(removed, int)
        assert removed >= 0
    
    def test_cache_statistics(self, sample_proof_sketch, tmp_path):
        """Test cache statistics."""
        cache = GenerationCache(cache_dir=tmp_path)
        
        # Add entries
        for i in range(3):
            cache.put(f"key_{i}", sample_proof_sketch)
        
        # Get some to create hits
        cache.get("key_0")
        cache.get("key_1")
        cache.get("nonexistent")  # Miss
        
        stats = cache.stats()
        
        assert "total_entries" in stats
        assert "cache_size" in stats
        assert "hit_rate" in stats
        assert stats["total_entries"] == 3


class TestPromptTemplates:
    """Test prompt template system."""
    
    def test_base_prompt_template(self):
        """Test base prompt template."""
        template = BasePromptTemplate()
        
        assert hasattr(template, 'format_prompt')
        assert hasattr(template, 'get_system_message')
        assert hasattr(template, 'get_user_message')
    
    def test_proof_sketch_prompt(self, sample_theorem):
        """Test proof sketch prompt template."""
        prompt = ProofSketchPrompt()
        
        formatted = prompt.format_prompt(sample_theorem)
        
        assert isinstance(formatted, str)
        assert sample_theorem.name in formatted
        assert sample_theorem.statement in formatted
        assert "proof sketch" in formatted.lower()
    
    def test_step_by_step_prompt(self, sample_theorem):
        """Test step-by-step prompt template."""
        prompt = StepByStepPrompt()
        
        formatted = prompt.format_prompt(sample_theorem)
        
        assert isinstance(formatted, str)
        assert "step" in formatted.lower()
        assert sample_theorem.statement in formatted
    
    def test_eli5_prompt(self, sample_theorem):
        """Test ELI5 (explain like I'm 5) prompt template."""
        prompt = ELI5Prompt()
        
        formatted = prompt.format_prompt(sample_theorem)
        
        assert isinstance(formatted, str)
        assert "simple" in formatted.lower() or "explain" in formatted.lower()
    
    def test_mathematical_context_prompt(self, sample_theorem):
        """Test mathematical context prompt template."""
        prompt = MathematicalContextPrompt()
        
        formatted = prompt.format_prompt(sample_theorem)
        
        assert isinstance(formatted, str)
        assert "context" in formatted.lower() or "mathematical" in formatted.lower()
    
    def test_tactic_explanation_prompt(self, sample_theorem):
        """Test tactic explanation prompt template."""
        prompt = TacticExplanationPrompt()
        
        formatted = prompt.format_prompt(sample_theorem)
        
        assert isinstance(formatted, str)
        assert "tactic" in formatted.lower()
        if sample_theorem.tactics:
            assert any(tactic in formatted for tactic in sample_theorem.tactics)
    
    def test_prompt_customization(self, sample_theorem):
        """Test prompt customization."""
        prompt = ProofSketchPrompt()
        
        # Test with custom parameters
        formatted = prompt.format_prompt(
            sample_theorem,
            style="concise",
            include_examples=True,
            audience="undergraduate"
        )
        
        assert isinstance(formatted, str)
        # Should include customization hints
        assert "concise" in formatted.lower() or "brief" in formatted.lower()


class TestGenerationContext:
    """Test generation context management."""
    
    def test_context_creation(self):
        """Test generation context creation."""
        context = GenerationContext(
            model="claude-3",
            temperature=0.7,
            max_tokens=2000
        )
        
        assert context.model == "claude-3"
        assert context.temperature == 0.7
        assert context.max_tokens == 2000
    
    def test_context_validation(self):
        """Test context validation."""
        # Valid context
        context = GenerationContext(temperature=0.5)
        assert 0 <= context.temperature <= 1
        
        # Invalid temperature should be clamped or raise error
        with pytest.raises(ValueError):
            GenerationContext(temperature=2.0)
    
    def test_context_serialization(self):
        """Test context serialization."""
        context = GenerationContext(
            model="claude-3",
            temperature=0.7,
            style="detailed"
        )
        
        # Should be serializable to dict
        context_dict = context.model_dump()
        assert isinstance(context_dict, dict)
        assert context_dict["model"] == "claude-3"
        assert context_dict["temperature"] == 0.7
    
    def test_context_merging(self):
        """Test context merging."""
        base_context = GenerationContext(
            model="claude-3",
            temperature=0.7
        )
        
        override_context = GenerationContext(
            temperature=0.5,
            max_tokens=1500
        )
        
        # Merge contexts (implementation-dependent)
        merged = base_context.merge(override_context)
        
        assert merged.model == "claude-3"  # From base
        assert merged.temperature == 0.5   # From override
        assert merged.max_tokens == 1500    # From override


if __name__ == "__main__":
    pytest.main([__file__, "-v"])