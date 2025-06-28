"""Comprehensive tests for the natural language generator module."""

import json
import subprocess
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.generator import ClaudeGenerator, GenerationConfig
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.parser.models import TheoremInfo


class TestClaudeGenerator:
    """Test suite for ClaudeGenerator."""

    @pytest.fixture
    def generator(self):
        """Create generator instance with test config."""
        config = GenerationConfig(
            model="claude-3-sonnet", temperature=0.3, max_retries=2
        )
        return ClaudeGenerator(config)

    @pytest.fixture
    def sample_theorem(self):
        """Create sample theorem for testing."""
        return TheoremInfo(
            name="nat_add_comm",
            statement="∀ (m n : Nat), m + n = n + m",
            proof="by induction m with | zero => simp | succ m ih => simp [add_succ, ih]",
            dependencies=["Nat.add", "Nat.add_succ"],
            docstring="Addition is commutative for natural numbers",
        )

    def test_generator_initialization(self):
        """Test generator initialization."""
        # Default config
        gen = ClaudeGenerator()
        assert gen.config.model == "claude-3-opus"
        assert gen.prompt_manager is not None

        # Custom config
        config = GenerationConfig(
            model="claude-3-sonnet", temperature=0.5, explanation_type="tutorial"
        )
        gen = ClaudeGenerator(config)
        assert gen.config.model == "claude-3-sonnet"
        assert gen.config.explanation_type == "tutorial"

    @patch("subprocess.run")
    def test_generate_proof_sketch_success(self, mock_run, generator, sample_theorem):
        """Test successful proof sketch generation."""
        # Mock Claude response
        mock_response = {
            "explanation": "Addition is commutative...",
            "key_insight": "Order doesn't matter",
            "steps": [
                {
                    "description": "Base case",
                    "formula": "0 + n = n + 0",
                    "step_type": "assertion",
                }
            ],
            "prerequisites": ["Natural numbers", "Addition"],
            "applications": ["Arithmetic", "Algebra"],
        }

        mock_result = Mock()
        mock_result.returncode = 0
        mock_result.stdout = json.dumps(mock_response)
        mock_run.return_value = mock_result

        # Generate sketch
        sketch = generator.generate_proof_sketch(sample_theorem)

        assert sketch is not None
        assert sketch.theorem_name == "nat_add_comm"
        assert "commutative" in sketch.explanation
        assert len(sketch.steps) > 0
        assert sketch.key_insight == "Order doesn't matter"

    @patch("subprocess.run")
    def test_generate_with_streaming(self, mock_run, generator, sample_theorem):
        """Test proof generation with streaming."""

        # Mock streaming response
        def mock_stream(*args, **kwargs):
            yield '{"explanation": "Part 1..."}'
            yield '{"explanation": "Part 1... Part 2..."}'
            yield '{"explanation": "Part 1... Part 2... Complete.", "steps": []}'

        generator._stream_claude_response = mock_stream

        chunks = []
        sketch = generator.generate_proof_sketch(
            sample_theorem, stream_callback=lambda c: chunks.append(c)
        )

        assert len(chunks) > 0
        assert sketch is not None

    def test_prompt_generation(self, generator, sample_theorem):
        """Test prompt template generation."""
        prompt = generator.prompt_manager.get_prompt(
            "proof_explanation", theorem=sample_theorem, config=generator.config
        )

        assert sample_theorem.name in prompt
        assert sample_theorem.statement in prompt
        assert "natural language" in prompt.lower()

    @patch("subprocess.run")
    def test_error_handling(self, mock_run, generator, sample_theorem):
        """Test error handling in generation."""
        # Test subprocess error
        mock_run.side_effect = subprocess.TimeoutExpired(cmd="claude", timeout=30)

        with pytest.raises(Exception):
            generator.generate_proof_sketch(sample_theorem)

        # Test invalid JSON response
        mock_result = Mock()
        mock_result.returncode = 0
        mock_result.stdout = "Invalid JSON"
        mock_run.side_effect = None
        mock_run.return_value = mock_result

        sketch = generator.generate_proof_sketch(sample_theorem)
        # Should return a basic sketch even with parse error
        assert sketch is not None
        assert sketch.theorem_name == sample_theorem.name

    def test_explanation_types(self, generator):
        """Test different explanation types."""
        config_concise = GenerationConfig(explanation_type="concise")
        config_detailed = GenerationConfig(explanation_type="detailed")
        config_tutorial = GenerationConfig(explanation_type="tutorial")

        gen_concise = ClaudeGenerator(config_concise)
        gen_detailed = ClaudeGenerator(config_detailed)
        gen_tutorial = ClaudeGenerator(config_tutorial)

        # Each should have different prompts
        assert gen_concise.config.explanation_type == "concise"
        assert gen_detailed.config.explanation_type == "detailed"
        assert gen_tutorial.config.explanation_type == "tutorial"

    @patch("subprocess.run")
    def test_retry_logic(self, mock_run, generator, sample_theorem):
        """Test retry logic on failures."""
        # First call fails, second succeeds
        mock_result_fail = Mock()
        mock_result_fail.returncode = 1

        mock_result_success = Mock()
        mock_result_success.returncode = 0
        mock_result_success.stdout = json.dumps({"explanation": "Success", "steps": []})

        mock_run.side_effect = [mock_result_fail, mock_result_success]

        sketch = generator.generate_proof_sketch(sample_theorem)
        assert sketch is not None
        assert mock_run.call_count == 2


class TestGenerationModels:
    """Test suite for generation data models."""

    def test_proof_step_model(self):
        """Test ProofStep model."""
        step = ProofStep(
            step_number=1,
            description="Apply induction",
            mathematical_content="∀n, P(n)",
            tactics=["induction", "simp"],
            intuition="We prove this by induction on n",
        )

        assert step.step_number == 1
        assert step.description == "Apply induction"
        assert step.mathematical_content == "∀n, P(n)"
        assert len(step.tactics) == 2

    def test_proof_sketch_model(self):
        """Test ProofSketch model."""
        steps = [
            ProofStep(
                step_number=1, description="Base case", mathematical_content="P(0)"
            ),
            ProofStep(
                step_number=2,
                description="Inductive step",
                mathematical_content="P(n) → P(n+1)",
            ),
        ]

        sketch = ProofSketch(
            theorem_name="induction_principle",
            explanation="Mathematical induction...",
            steps=steps,
            key_insight="Build from base",
            prerequisites=["Logic", "Natural numbers"],
            complexity_score=3,
        )

        assert sketch.theorem_name == "induction_principle"
        assert len(sketch.steps) == 2
        assert sketch.total_duration == 30.0  # Default durations
        assert sketch.complexity_score == 3

    def test_generation_config(self):
        """Test GenerationConfig model."""
        config = GenerationConfig(
            model="claude-3-opus",
            temperature=0.7,
            max_tokens=2000,
            explanation_type="detailed",
            include_prerequisites=True,
        )

        assert config.model == "claude-3-opus"
        assert config.temperature == 0.7
        assert config.include_prerequisites is True

        # Test validation
        assert 0 <= config.temperature <= 1
        assert config.max_tokens > 0


class TestPromptManager:
    """Test suite for prompt template management."""

    def test_prompt_loading(self):
        """Test loading prompt templates."""
        from proof_sketcher.generator.prompts import PromptManager

        manager = PromptManager()

        # Test getting a prompt
        prompt = manager.get_prompt(
            "proof_explanation",
            theorem=Mock(name="test", statement="True"),
            config=GenerationConfig(),
        )

        assert isinstance(prompt, str)
        assert len(prompt) > 0

    def test_custom_prompts(self):
        """Test custom prompt templates."""
        from proof_sketcher.generator.prompts import PromptManager

        manager = PromptManager()

        # Register custom prompt
        custom_template = "Explain {{theorem.name}} simply"
        manager.register_template("custom", custom_template)

        prompt = manager.get_prompt("custom", theorem=Mock(name="my_theorem"))

        assert "Explain my_theorem simply" in prompt


class TestCacheManager:
    """Test suite for caching functionality."""

    @pytest.fixture
    def cache_manager(self, tmp_path):
        """Create cache manager with temp directory."""
        from proof_sketcher.generator.cache import CacheManager

        return CacheManager(cache_dir=tmp_path / "cache")

    def test_cache_operations(self, cache_manager):
        """Test basic cache operations."""
        # Create test data
        key = "test_theorem_v1"
        data = {"explanation": "Test explanation", "steps": []}

        # Store in cache
        cache_manager.store(key, data)

        # Retrieve from cache
        cached_data = cache_manager.get(key)
        assert cached_data is not None
        assert cached_data["explanation"] == "Test explanation"

        # Test cache miss
        miss = cache_manager.get("nonexistent")
        assert miss is None

    def test_cache_expiration(self, cache_manager):
        """Test cache expiration logic."""
        import time

        # Store with short TTL
        cache_manager.store("temp", {"data": "test"}, ttl_hours=0.0001)

        # Should exist immediately
        assert cache_manager.get("temp") is not None

        # Wait and check expiration
        time.sleep(0.5)
        assert cache_manager.get("temp") is None

    def test_cache_size_management(self, cache_manager):
        """Test cache size limits."""
        # Fill cache
        for i in range(100):
            cache_manager.store(f"key_{i}", {"data": f"value_{i}" * 1000})

        # Check size is managed
        cache_size = cache_manager.get_cache_size_mb()
        assert cache_size < cache_manager.max_cache_size_mb

    def test_cache_persistence(self, tmp_path):
        """Test cache persistence across instances."""
        from proof_sketcher.generator.cache import CacheManager

        # First instance
        cache1 = CacheManager(cache_dir=tmp_path / "persist")
        cache1.store("persistent", {"value": 42})

        # Second instance
        cache2 = CacheManager(cache_dir=tmp_path / "persist")
        data = cache2.get("persistent")
        assert data is not None
        assert data["value"] == 42


@pytest.mark.integration
class TestGeneratorIntegration:
    """Integration tests for the generator."""

    def test_end_to_end_generation(self):
        """Test complete generation pipeline."""
        from proof_sketcher.generator import ClaudeGenerator
        from proof_sketcher.parser import LeanParser

        # Parse a theorem
        LeanParser()
        theorem = TheoremInfo(
            name="simple_proof", statement="1 + 1 = 2", proof="by norm_num"
        )

        # Generate explanation (will use mock if no Claude)
        generator = ClaudeGenerator()

        with patch("subprocess.run") as mock_run:
            mock_result = Mock()
            mock_result.returncode = 0
            mock_result.stdout = json.dumps(
                {
                    "explanation": "One plus one equals two",
                    "steps": [{"description": "By arithmetic", "formula": "1+1=2"}],
                }
            )
            mock_run.return_value = mock_result

            sketch = generator.generate_proof_sketch(theorem)

        assert sketch is not None
        assert sketch.theorem_name == "simple_proof"
        assert len(sketch.steps) > 0
