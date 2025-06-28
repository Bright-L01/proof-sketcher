"""Tests for generator models."""

from datetime import datetime, timedelta

import pytest

from proof_sketcher.generator.models import (CacheEntry, GenerationConfig,
                                             GenerationModel,
                                             GenerationRequest,
                                             GenerationResponse,
                                             GenerationType, ProofSketch,
                                             ProofStep)


class TestProofStep:
    """Tests for ProofStep model."""

    def test_proof_step_creation(self):
        """Test basic proof step creation."""
        step = ProofStep(
            step_number=1,
            description="Apply induction hypothesis",
            mathematical_content="P(n) → P(n+1)",
            tactics=["induction", "simp"],
            intuition="We assume P(n) and prove P(n+1)",
        )

        assert step.step_number == 1
        assert step.description == "Apply induction hypothesis"
        assert step.mathematical_content == "P(n) → P(n+1)"
        assert step.tactics == ["induction", "simp"]
        assert step.intuition == "We assume P(n) and prove P(n+1)"

    def test_proof_step_defaults(self):
        """Test proof step with default values."""
        step = ProofStep(
            step_number=2, description="Base case", mathematical_content="P(0)"
        )

        assert step.tactics == []
        assert step.intuition is None


class TestProofSketch:
    """Tests for ProofSketch model."""

    def test_proof_sketch_creation(self):
        """Test proof sketch creation."""
        steps = [
            ProofStep(
                step_number=1,
                description="Base case",
                mathematical_content="P(0)",
                tactics=["trivial"],
            ),
            ProofStep(
                step_number=2,
                description="Inductive step",
                mathematical_content="P(n) → P(n+1)",
                tactics=["induction", "simp"],
            ),
        ]

        sketch = ProofSketch(
            theorem_name="nat_induction",
            introduction="We prove by mathematical induction",
            key_steps=steps,
            conclusion="By induction, P(n) holds for all n",
            difficulty_level="beginner",
            mathematical_areas=["number_theory"],
            prerequisites=["natural_numbers"],
        )

        assert sketch.theorem_name == "nat_induction"
        assert sketch.total_steps == 2
        assert sketch.difficulty_level == "beginner"
        assert sketch.mathematical_areas == ["number_theory"]
        assert sketch.prerequisites == ["natural_numbers"]

    def test_proof_sketch_validation(self):
        """Test proof sketch validation."""
        steps = [
            ProofStep(step_number=1, description="test", mathematical_content="test")
        ]

        # Invalid difficulty level
        with pytest.raises(ValueError, match="Difficulty must be one of"):
            ProofSketch(
                theorem_name="test",
                introduction="test",
                key_steps=steps,
                conclusion="test",
                difficulty_level="invalid",
            )

    def test_get_step(self):
        """Test getting specific proof steps."""
        steps = [
            ProofStep(step_number=1, description="first", mathematical_content="P(0)"),
            ProofStep(step_number=3, description="third", mathematical_content="P(2)"),
        ]

        sketch = ProofSketch(
            theorem_name="test", introduction="test", key_steps=steps, conclusion="test"
        )

        step1 = sketch.get_step(1)
        assert step1 is not None
        assert step1.description == "first"

        step2 = sketch.get_step(2)
        assert step2 is None

        step3 = sketch.get_step(3)
        assert step3 is not None
        assert step3.description == "third"


class TestGenerationConfig:
    """Tests for GenerationConfig model."""

    def test_default_config(self):
        """Test default configuration."""
        config = GenerationConfig()

        assert config.model == GenerationModel.CLAUDE_3_5_SONNET
        assert config.temperature == 0.7
        assert config.max_tokens == 4000
        assert config.stream is False
        assert config.include_reasoning is True
        assert config.verbosity == "detailed"
        assert config.cache_responses is True
        assert config.cache_ttl_hours == 24

    def test_config_presets(self):
        """Test configuration presets."""
        fast = GenerationConfig.fast()
        assert fast.model == GenerationModel.CLAUDE_3_5_HAIKU
        assert fast.temperature == 0.3
        assert fast.max_tokens == 2000
        assert fast.verbosity == "concise"

        detailed = GenerationConfig.detailed()
        assert detailed.model == GenerationModel.CLAUDE_3_5_SONNET
        assert detailed.max_tokens == 6000
        assert detailed.verbosity == "detailed"

        creative = GenerationConfig.creative()
        assert creative.model == GenerationModel.CLAUDE_3_OPUS
        assert creative.temperature == 0.9
        assert creative.verbosity == "verbose"

    def test_config_validation(self):
        """Test configuration validation."""
        # Invalid temperature
        with pytest.raises(ValueError):
            GenerationConfig(temperature=1.5)

        with pytest.raises(ValueError):
            GenerationConfig(temperature=-0.1)

        # Invalid max_tokens
        with pytest.raises(ValueError):
            GenerationConfig(max_tokens=0)

        # Invalid verbosity
        with pytest.raises(ValueError):
            GenerationConfig(verbosity="invalid")


class TestGenerationRequest:
    """Tests for GenerationRequest model."""

    def test_generation_request_creation(self):
        """Test generation request creation."""
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="add_zero",
            theorem_statement="∀ n : Nat, n + 0 = n",
            theorem_dependencies=["Nat.add_zero"],
            proof_text="by simp",
            docstring="Addition identity",
        )

        assert request.generation_type == GenerationType.PROOF_SKETCH
        assert request.theorem_name == "add_zero"
        assert request.theorem_statement == "∀ n : Nat, n + 0 = n"
        assert request.theorem_dependencies == ["Nat.add_zero"]
        assert request.proof_text == "by simp"
        assert request.docstring == "Addition identity"

    def test_cache_key_generation(self):
        """Test cache key generation."""
        config = GenerationConfig(temperature=0.5, verbosity="concise")

        request1 = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="test_theorem",
            theorem_statement="P → Q",
            config=config,
        )

        request2 = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="test_theorem",
            theorem_statement="P → Q",
            config=config,
        )

        # Same requests should have same cache key
        assert request1.get_cache_key() == request2.get_cache_key()

        # Different theorem names should have different cache keys
        request3 = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="different_theorem",
            theorem_statement="P → Q",
            config=config,
        )

        assert request1.get_cache_key() != request3.get_cache_key()

        # Different generation types should have different cache keys
        request4 = GenerationRequest(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name="test_theorem",
            theorem_statement="P → Q",
            config=config,
        )

        assert request1.get_cache_key() != request4.get_cache_key()


class TestGenerationResponse:
    """Tests for GenerationResponse model."""

    def test_generation_response_creation(self):
        """Test generation response creation."""
        request = GenerationRequest(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name="test",
            theorem_statement="P",
        )

        response = GenerationResponse(
            request=request,
            content="This theorem says that P is true.",
            generation_time_ms=1500.0,
            token_count=20,
            success=True,
        )

        assert response.request == request
        assert response.content == "This theorem says that P is true."
        assert response.generation_time_ms == 1500.0
        assert response.token_count == 20
        assert response.success is True
        assert response.error_message is None

    def test_content_type_properties(self):
        """Test content type checking properties."""
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name="test",
            theorem_statement="P",
        )

        # Text response
        text_response = GenerationResponse(
            request=request, content="Some explanation text"
        )

        assert text_response.is_text_response is True
        assert text_response.is_proof_sketch is False

        # ProofSketch response
        sketch = ProofSketch(
            theorem_name="test",
            introduction="intro",
            key_steps=[],
            conclusion="conclusion",
        )

        sketch_response = GenerationResponse(request=request, content=sketch)

        assert sketch_response.is_text_response is False
        assert sketch_response.is_proof_sketch is True

    def test_to_dict_serialization(self):
        """Test dictionary serialization."""
        request = GenerationRequest(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name="test",
            theorem_statement="P",
        )

        response = GenerationResponse(
            request=request, content="Test content", success=True
        )

        response_dict = response.to_dict()

        assert isinstance(response_dict, dict)
        assert "request" in response_dict
        assert "content" in response_dict
        assert "generated_at" in response_dict
        assert "success" in response_dict

        # Check datetime serialization
        assert isinstance(response_dict["generated_at"], str)


class TestCacheEntry:
    """Tests for CacheEntry model."""

    def test_cache_entry_creation(self):
        """Test cache entry creation."""
        request = GenerationRequest(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name="test",
            theorem_statement="P",
        )

        response = GenerationResponse(request=request, content="Test content")

        entry = CacheEntry(cache_key="test_key", response=response, ttl_hours=12)

        assert entry.cache_key == "test_key"
        assert entry.response == response
        assert entry.ttl_hours == 12
        assert isinstance(entry.cached_at, datetime)

    def test_expiry_checking(self):
        """Test cache entry expiry checking."""
        request = GenerationRequest(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name="test",
            theorem_statement="P",
        )

        response = GenerationResponse(request=request, content="Test content")

        # Recent entry (not expired)
        recent_entry = CacheEntry(cache_key="recent", response=response, ttl_hours=24)

        assert recent_entry.is_expired is False

        # Old entry (expired)
        old_time = datetime.now() - timedelta(hours=48)
        old_entry = CacheEntry(
            cache_key="old", response=response, cached_at=old_time, ttl_hours=24
        )

        assert old_entry.is_expired is True
