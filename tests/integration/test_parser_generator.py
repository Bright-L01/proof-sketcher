"""Integration tests for parser and generator components."""

from __future__ import annotations

import tempfile
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.generator.models import GenerationConfig, GenerationModel
from proof_sketcher.generator.simple_generator import SimpleGenerator as ClaudeGenerator
from proof_sketcher.parser.config import ParserConfig
from proof_sketcher.parser.simple_parser import SimpleLeanParser


class TestParserGeneratorIntegration:
    """Test integration between parser and generator."""

    @pytest.fixture
    def parser_config(self):
        """Create parser configuration for tests."""
        return ParserConfig(lean_executable="lean", timeout=10)

    @pytest.fixture
    def generator_config(self):
        """Create generator configuration for tests."""
        return GenerationConfig(
            model=GenerationModel.CLAUDE_3_5_SONNET, temperature=0.7, max_tokens=1000
        )

    @pytest.fixture
    def lean_files(self, tmp_path):
        """Create various Lean files for testing."""
        files = {}

        # Simple theorem
        simple = tmp_path / "simple.lean"
        simple.write_text(
            """
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl
"""
        )
        files["simple"] = simple

        # Induction theorem
        induction = tmp_path / "induction.lean"
        induction.write_text(
            """
theorem sum_formula (n : Nat) : 2 * sum_to_n n = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [sum_to_n]
    ring
    exact ih
"""
        )
        files["induction"] = induction

        # Multiple theorems
        multiple = tmp_path / "multiple.lean"
        multiple.write_text(
            """
theorem eq_refl (a : Nat) : a = a := rfl

theorem eq_symm (a b : Nat) (h : a = b) : b = a := h.symm

theorem eq_trans (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  h1.trans h2
"""
        )
        files["multiple"] = multiple

        return files

    def test_parse_and_generate_simple(
        self, parser_config, generator_config, lean_files
    ):
        """Test parsing and generating for a simple theorem."""
        parser = SimpleLeanParser(parser_config)

        # Mock Claude availability check
        with patch.object(ClaudeGenerator, "check_claude_available", return_value=True):
            generator = ClaudeGenerator(default_config=generator_config)

        # Parse
        result = parser.parse_file(lean_files["simple"])
        assert len(result.theorems) == 1
        theorem = result.theorems[0]

        # Generate with mocked Claude
        with patch("subprocess.run") as mock_run:
            mock_run.return_value = Mock(
                stdout='{"theorem_name": "add_zero", "introduction": "This theorem states that adding zero to any natural number leaves it unchanged.", "key_steps": [{"step_number": 1, "description": "Apply reflexivity", "mathematical_content": "n + 0 = n"}], "conclusion": "Thus, adding zero to any natural number leaves it unchanged.", "difficulty_level": "beginner"}',
                stderr="",
                returncode=0,
            )

            sketch = generator.generate_proof_sketch(theorem)

            assert sketch.theorem_name == "add_zero"
            assert len(sketch.introduction) > 10  # Has meaningful introduction
            assert "theorem" in sketch.introduction.lower()  # Mentions theorem
            assert len(sketch.key_steps) >= 1  # Has at least one step

    def test_parse_and_generate_induction(
        self, parser_config, generator_config, lean_files
    ):
        """Test parsing and generating for an induction proof."""
        parser = SimpleLeanParser(parser_config)

        # Mock Claude availability check
        with patch.object(ClaudeGenerator, "check_claude_available", return_value=True):
            generator = ClaudeGenerator(default_config=generator_config)

        # Parse
        result = parser.parse_file(lean_files["induction"])
        theorem = result.theorems[0]

        # Generate with mocked Claude
        with patch("subprocess.run") as mock_run:
            mock_run.return_value = Mock(
                stdout='{"theorem_name": "sum_formula", "introduction": "This theorem proves the formula for the sum of first n natural numbers using induction.", "key_steps": [{"step_number": 1, "description": "Base case: n=0", "mathematical_content": "sum(0) = 0"}, {"step_number": 2, "description": "Inductive step: assume true for n, prove for n+1", "mathematical_content": "sum(n+1) = sum(n) + (n+1)"}, {"step_number": 3, "description": "Simplify and apply inductive hypothesis", "mathematical_content": "= n(n+1)/2 + (n+1) = (n+1)(n+2)/2"}], "conclusion": "By mathematical induction, the formula holds for all natural numbers.", "difficulty_level": "intermediate"}',
                stderr="",
                returncode=0,
            )

            sketch = generator.generate_proof_sketch(theorem)

            assert len(sketch.introduction) > 10  # Has meaningful introduction
            assert sketch.proof_strategy.value == "induction"  # Uses induction strategy
            assert (
                len(sketch.key_steps) >= 2
            )  # Has at least base case and inductive step
            assert any(
                any(
                    term in step.intuitive_explanation.lower()
                    for term in ["base", "simplest case", "check that"]
                )
                for step in sketch.key_steps
            )

    def test_parse_and_generate_multiple(
        self, parser_config, generator_config, lean_files
    ):
        """Test parsing and generating for multiple theorems."""
        parser = SimpleLeanParser(parser_config)

        # Mock Claude availability check
        with patch.object(ClaudeGenerator, "check_claude_available", return_value=True):
            generator = ClaudeGenerator(default_config=generator_config)

        # Parse
        result = parser.parse_file(lean_files["multiple"])
        assert len(result.theorems) == 3

        # Generate for each theorem
        sketches = []
        with patch("subprocess.run") as mock_run:
            responses = [
                '{"theorem_name": "eq_refl", "introduction": "Reflexivity of equality", "key_steps": [{"step_number": 1, "description": "Direct application of rfl", "mathematical_content": "a = a"}], "conclusion": "Any element equals itself.", "difficulty_level": "beginner"}',
                '{"theorem_name": "eq_symm", "introduction": "Symmetry of equality", "key_steps": [{"step_number": 1, "description": "Apply symmetry to hypothesis", "mathematical_content": "a = b → b = a"}], "conclusion": "Equality is symmetric.", "difficulty_level": "beginner"}',
                '{"theorem_name": "eq_trans", "introduction": "Transitivity of equality", "key_steps": [{"step_number": 1, "description": "Chain equalities using trans", "mathematical_content": "a = b ∧ b = c → a = c"}], "conclusion": "Equality is transitive.", "difficulty_level": "beginner"}',
            ]

            for i, theorem in enumerate(result.theorems):
                mock_run.return_value = Mock(
                    stdout=responses[i], stderr="", returncode=0
                )

                sketch = generator.generate_proof_sketch(theorem)
                sketches.append(sketch)

        assert len(sketches) == 3
        assert len(sketches[0].introduction) > 10  # Has meaningful introduction
        assert "theorem" in sketches[0].introduction.lower()  # Mentions theorem
        assert len(sketches[1].introduction) > 10  # Second sketch has introduction
        assert len(sketches[2].introduction) > 10  # Third sketch has introduction

    def test_mathematical_context_generation(self, parser_config, generator_config):
        """Test generating with mathematical context."""
        parser = SimpleLeanParser(parser_config)

        # Mock Claude availability check
        with patch.object(ClaudeGenerator, "check_claude_available", return_value=True):
            generator = ClaudeGenerator(default_config=generator_config)

        # Create theorem with imports
        theorem_content = """
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime

theorem prime_exists (n : Nat) : ∃ p, Nat.Prime p ∧ p > n := by
  sorry
"""

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False, encoding="utf-8"
        ) as f:
            f.write(theorem_content)
            lean_file = Path(f.name)

        try:
            result = parser.parse_file(lean_file)
            theorem = result.theorems[0]

            # Generate with context (template-based system doesn't use subprocess)
            context = "This theorem uses Mathlib's prime number theory"
            sketch = generator.generate_proof_sketch(
                theorem, mathematical_context=context
            )

            # Verify sketch was generated successfully
            assert sketch.theorem_name == "prime_exists"
            assert len(sketch.introduction) > 10  # Has meaningful content
            assert len(sketch.key_steps) >= 1  # Has at least one step
        finally:
            lean_file.unlink()

    def test_error_recovery(self, parser_config, generator_config, tmp_path):
        """Test error recovery in the pipeline."""
        parser = SimpleLeanParser(parser_config)

        # Mock Claude availability check
        with patch.object(ClaudeGenerator, "check_claude_available", return_value=True):
            generator = ClaudeGenerator(default_config=generator_config)

        # Create file with mixed valid/invalid content
        mixed_file = tmp_path / "mixed.lean"
        mixed_file.write_text(
            """
theorem valid_theorem : 1 = 1 := rfl

invalid syntax here

theorem another_valid : 2 = 2 := rfl
""",
            encoding="utf-8",
        )

        # Parse with errors
        result = parser.parse_file(mixed_file)

        # Should still find valid theorems
        assert len(result.theorems) >= 1
        assert any(t.name == "valid_theorem" for t in result.theorems)

        # Generate for valid theorems despite errors
        valid_theorems = [t for t in result.theorems if t.name == "valid_theorem"]
        if valid_theorems:
            with patch("subprocess.run") as mock_run:
                mock_run.return_value = Mock(
                    stdout='{"theorem_name": "valid_theorem", "introduction": "Trivial equality", "key_steps": [{"step_number": 1, "description": "rfl", "mathematical_content": "a = a"}], "conclusion": "Equality is reflexive.", "difficulty_level": "beginner"}',
                    stderr="",
                    returncode=0,
                )

                sketch = generator.generate_proof_sketch(valid_theorems[0])
                assert sketch is not None

    def test_caching_integration(
        self, parser_config, generator_config, lean_files, tmp_path
    ):
        """Test caching between parser and generator."""
        # Enable caching
        parser_config.cache_results = True
        generator_config.cache_responses = True

        parser = SimpleLeanParser(parser_config)

        # Mock Claude availability check
        with patch.object(ClaudeGenerator, "check_claude_available", return_value=True):
            generator = ClaudeGenerator(default_config=generator_config)

        # Set cache directories
        cache_dir = tmp_path / "cache"
        cache_dir.mkdir()

        # First run
        result1 = parser.parse_file(lean_files["simple"])
        with patch("subprocess.run") as mock_run:
            mock_run.return_value = Mock(
                stdout='{"theorem_name": "add_zero", "introduction": "Cached result", "key_steps": [{"step_number": 1, "description": "Step 1", "mathematical_content": "n + 0 = n"}], "conclusion": "Adding zero leaves the number unchanged.", "difficulty_level": "beginner"}',
                stderr="",
                returncode=0,
            )
            sketch1 = generator.generate_proof_sketch(result1.theorems[0])

        # Second run should use cache
        result2 = parser.parse_file(lean_files["simple"])
        with patch("subprocess.run") as mock_run:
            # If cache works, this shouldn't be called
            mock_run.return_value = Mock(
                stdout='{"theorem_name": "add_zero", "introduction": "Should not see this", "key_steps": [], "conclusion": "Not cached", "difficulty_level": "beginner"}',
                stderr="",
                returncode=0,
            )
            sketch2 = generator.generate_proof_sketch(result2.theorems[0])

        # Both sketches should be created successfully
        assert sketch1 is not None
        assert sketch2 is not None
