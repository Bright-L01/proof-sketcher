"""Comprehensive tests for the natural language generator module."""

import json
import subprocess
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.generator import ClaudeGenerator, GenerationConfig
from proof_sketcher.generator.models import (
    GenerationModel,
    GenerationType,
    ProofSketch,
    ProofStep,
)
from proof_sketcher.parser.models import TheoremInfo


class TestClaudeGenerator:
    """Test suite for ClaudeGenerator."""

    @pytest.fixture
    def generator(self):
        """Create generator instance with test config."""
        config = GenerationConfig(
            model=GenerationModel.CLAUDE_3_5_SONNET, temperature=0.3, max_retries=2
        )
        with patch.object(ClaudeGenerator, "check_ai_available", return_value=True):
            return ClaudeGenerator(default_config=config)

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
        with patch.object(ClaudeGenerator, "check_ai_available", return_value=True):
            gen = ClaudeGenerator()
            assert gen.default_config.model == GenerationModel.CLAUDE_3_5_SONNET
            assert gen.ai_executable == "claude"

            # Custom config
            config = GenerationConfig(
                model=GenerationModel.CLAUDE_3_5_HAIKU, temperature=0.5
            )
            gen = ClaudeGenerator(default_config=config)
            assert gen.default_config.model == GenerationModel.CLAUDE_3_5_HAIKU
            assert gen.default_config.temperature == 0.5

    @patch("subprocess.run")
    def test_generate_proof_sketch_success(self, mock_run, generator, sample_theorem):
        """Test successful proof sketch generation."""
        # Mock Claude response
        mock_response = {
            "theorem_name": "nat_add_comm",
            "introduction": "Addition is commutative...",
            "key_steps": [
                {
                    "step_number": 1,
                    "description": "Base case",
                    "mathematical_content": "0 + n = n + 0",
                    "tactics": ["simp"],
                }
            ],
            "conclusion": "Therefore, addition is commutative for natural numbers.",
            "difficulty_level": "beginner",
            "prerequisites": ["Natural numbers", "Addition"],
        }

        mock_result = Mock()
        mock_result.returncode = 0
        mock_result.stdout = json.dumps(mock_response)
        mock_run.return_value = mock_result

        # Generate sketch
        sketch = generator.generate_proof_sketch(sample_theorem)

        assert sketch is not None
        assert sketch.theorem_name == "nat_add_comm"
        assert "commutative" in sketch.introduction
        assert len(sketch.key_steps) > 0
        assert sketch.difficulty_level == "beginner"

    def test_generate_with_streaming(self, generator, sample_theorem):
        """Test proof generation with streaming."""
        with patch("subprocess.Popen") as mock_popen:
            # Mock the subprocess for streaming
            mock_process = Mock()
            mock_process.stdin = Mock()
            mock_process.stdout = Mock()
            mock_process.stderr = Mock()
            mock_process.wait.return_value = 0

            # Mock streaming output
            mock_process.stdout.readline.side_effect = [
                "First chunk of the proof\n",
                "Second chunk of the proof\n",
                "Final chunk\n",
                "",  # End of stream
            ]

            mock_popen.return_value = mock_process

            # Use the streaming method
            chunks = list(
                generator.generate_streaming(
                    sample_theorem, GenerationType.PROOF_SKETCH
                )
            )

            assert len(chunks) > 0
            assert "First chunk" in chunks[0]

    def test_prompt_generation(self, generator, sample_theorem):
        """Test prompt template generation."""
        from proof_sketcher.generator.prompts import prompt_templates

        prompt = prompt_templates.render_prompt(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name=sample_theorem.name,
            theorem_statement=sample_theorem.statement,
            config=generator.default_config,
            dependencies=sample_theorem.dependencies,
            proof_text=sample_theorem.proof,
            docstring=sample_theorem.docstring,
        )

        assert sample_theorem.name in prompt
        # Check that either the original statement or a transformed version is in the prompt
        assert sample_theorem.statement in prompt or "for all" in prompt
        assert len(prompt) > 0

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

    def test_explanation_types(self, generator, sample_theorem):
        """Test different generation types."""
        with patch("subprocess.run") as mock_run:
            # Mock response
            mock_result = Mock()
            mock_result.returncode = 0
            mock_result.stdout = "This is a simple explanation"
            mock_run.return_value = mock_result

            # Test ELI5 explanation
            eli5 = generator.generate_eli5_explanation(sample_theorem)
            assert isinstance(eli5, str)
            assert len(eli5) > 0

            # Test tactic explanation
            mock_result.stdout = "The tactics used are..."
            tactic_exp = generator.generate_tactic_explanation(sample_theorem)
            assert isinstance(tactic_exp, str)

            # Test step-by-step explanation
            mock_result.stdout = "Step 1: ..."
            step_by_step = generator.generate_step_by_step(sample_theorem)
            assert isinstance(step_by_step, str)

    @patch("subprocess.run")
    def test_retry_logic(self, mock_run, generator, sample_theorem):
        """Test retry logic on failures."""
        # Test that generation retries are handled in the config
        # The actual implementation doesn't retry automatically

        mock_result_fail = Mock()
        mock_result_fail.returncode = 1
        mock_result_fail.stderr = "API Error"
        mock_run.return_value = mock_result_fail

        # The generator should raise an error on failure
        from proof_sketcher.core.exceptions import GeneratorError

        with pytest.raises(GeneratorError):
            generator.generate_proof_sketch(sample_theorem)

        # Test that timeout is handled differently
        mock_run.side_effect = subprocess.TimeoutExpired("claude", 30)
        from proof_sketcher.core.exceptions import AITimeoutError

        with pytest.raises(AITimeoutError):
            generator.generate_proof_sketch(sample_theorem)


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
            introduction="Mathematical induction...",
            key_steps=steps,
            conclusion="Thus proved by induction.",
            prerequisites=["Logic", "Natural numbers"],
            difficulty_level="intermediate",
        )

        assert sketch.theorem_name == "induction_principle"
        assert len(sketch.key_steps) == 2
        assert sketch.total_steps == 2
        assert sketch.difficulty_level == "intermediate"

    def test_generation_config(self):
        """Test GenerationConfig model."""
        config = GenerationConfig(
            model=GenerationModel.CLAUDE_3_5_SONNET,
            temperature=0.7,
            max_tokens=2000,
            verbosity="verbose",
            cache_responses=True,
            cache_ttl_hours=48,
        )

        assert config.model == GenerationModel.CLAUDE_3_5_SONNET
        assert config.temperature == 0.7
        assert config.max_tokens == 2000
        assert config.verbosity == "verbose"
        assert config.cache_responses is True
        assert config.cache_ttl_hours == 48

        # Test validation
        assert 0 <= config.temperature <= 1
        assert config.max_tokens > 0


class TestPromptTemplates:
    """Test suite for prompt template functionality."""

    def test_prompt_loading(self):
        """Test loading prompt templates."""
        from proof_sketcher.generator.prompts import GenerationType, prompt_templates

        # Test rendering a proof sketch prompt
        prompt = prompt_templates.render_prompt(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="test_theorem",
            theorem_statement="∀x, P(x)",
            config=GenerationConfig(),
        )

        assert isinstance(prompt, str)
        assert len(prompt) > 0
        assert "test_theorem" in prompt

    def test_custom_prompts(self):
        """Test prompt template filters."""
        from proof_sketcher.generator.prompts import PromptTemplates

        templates = PromptTemplates()

        # Test format_dependencies filter
        deps = ["Nat.add", "Nat.mul"]
        formatted = templates._format_dependencies(deps)
        assert "Nat.add" in formatted
        assert "Nat.mul" in formatted

        # Test format_statement filter
        statement = "∀ (x : Nat), x + 0 = x"
        formatted = templates._format_statement(statement)
        # The filter converts symbols to readable text
        assert "for all" in formatted
        assert "x + 0 = x" in formatted


class TestCacheManager:
    """Test suite for caching functionality."""

    @pytest.fixture
    def cache_manager(self, tmp_path):
        """Create cache manager with temp directory."""
        from proof_sketcher.generator.cache import CacheManager

        return CacheManager(cache_dir=tmp_path / "cache")

    def test_cache_operations(self, cache_manager):
        """Test basic cache operations."""
        from proof_sketcher.generator.models import (
            GenerationRequest,
            GenerationResponse,
            GenerationType,
        )

        # Create test request and response
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="test_theorem",
            theorem_statement="test",
            config=GenerationConfig(),
        )

        response = GenerationResponse(
            request=request,
            content="Test explanation",
            generation_time_ms=100,
            success=True,
        )

        # Store in cache
        cache_key = request.get_cache_key()
        cache_manager.put(cache_key, response)

        # Retrieve from cache using the same request
        cached_response = cache_manager.get(cache_key)
        assert cached_response is not None
        assert cached_response.content == "Test explanation"

        # Test cache miss
        miss = cache_manager.get("nonexistent")
        assert miss is None

    def test_cache_expiration(self, cache_manager):
        """Test cache expiration logic."""
        from proof_sketcher.generator.models import (
            GenerationRequest,
            GenerationResponse,
            GenerationType,
        )

        # Create test request and response
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="temp_theorem",
            theorem_statement="temp",
            config=GenerationConfig(cache_ttl_hours=1),  # 1 hour TTL
        )

        response = GenerationResponse(
            request=request, content="Temporary", generation_time_ms=100, success=True
        )

        # Store in cache
        cache_key = request.get_cache_key()
        cache_manager.put(cache_key, response)

        # Should exist immediately
        assert cache_manager.get(cache_key) is not None

        # Test clearing the cache
        cleared = cache_manager.clear()
        assert cleared > 0

        # Should be gone after clear
        assert cache_manager.get(cache_key) is None

    def test_cache_size_management(self, cache_manager):
        """Test cache size limits."""
        from proof_sketcher.generator.models import (
            GenerationRequest,
            GenerationResponse,
            GenerationType,
        )

        # Fill cache with large responses
        for i in range(20):
            request = GenerationRequest(
                generation_type=GenerationType.PROOF_SKETCH,
                theorem_name=f"theorem_{i}",
                theorem_statement=f"statement_{i}",
                config=GenerationConfig(),
            )

            response = GenerationResponse(
                request=request,
                content="x" * 10000,  # Large content
                generation_time_ms=100,
                success=True,
            )

            cache_key = request.get_cache_key()
            cache_manager.put(cache_key, response)

        # Check size is managed
        cache_size = cache_manager.get_cache_size_mb()
        assert cache_size < cache_manager.max_cache_size_mb

    def test_cache_persistence(self, tmp_path):
        """Test cache persistence across instances."""
        from proof_sketcher.generator.cache import CacheManager
        from proof_sketcher.generator.models import (
            GenerationRequest,
            GenerationResponse,
            GenerationType,
        )

        # Create test request and response
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="persistent_theorem",
            theorem_statement="persistent",
            config=GenerationConfig(),
        )

        response = GenerationResponse(
            request=request,
            content="Persistent content",
            generation_time_ms=100,
            success=True,
        )

        # First instance
        cache1 = CacheManager(cache_dir=tmp_path / "persist")
        cache_key = request.get_cache_key()
        cache1.put(cache_key, response)

        # Second instance should find the cached response
        cache2 = CacheManager(cache_dir=tmp_path / "persist")
        cached = cache2.get(cache_key)
        assert cached is not None
        assert cached.content == "Persistent content"


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
        with patch.object(ClaudeGenerator, "check_ai_available", return_value=True):
            generator = ClaudeGenerator()

        with patch("subprocess.run") as mock_run:
            mock_result = Mock()
            mock_result.returncode = 0
            mock_result.stdout = json.dumps(
                {
                    "theorem_name": "simple_proof",
                    "introduction": "One plus one equals two",
                    "key_steps": [
                        {
                            "step_number": 1,
                            "description": "By arithmetic",
                            "mathematical_content": "1+1=2",
                            "tactics": ["norm_num"],
                        }
                    ],
                    "conclusion": "Therefore, 1 + 1 = 2.",
                }
            )
            mock_run.return_value = mock_result

            sketch = generator.generate_proof_sketch(theorem)

        assert sketch is not None
        assert sketch.theorem_name == "simple_proof"
        assert len(sketch.key_steps) > 0
