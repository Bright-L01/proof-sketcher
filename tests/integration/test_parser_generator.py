"""Integration tests for parser and generator components."""

import tempfile
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.generator.claude import ClaudeGenerator
from proof_sketcher.generator.models import GenerationConfig
from proof_sketcher.parser.config import ParserConfig
from proof_sketcher.parser.lean_parser import LeanParser


class TestParserGeneratorIntegration:
    """Test integration between parser and generator."""

    @pytest.fixture
    def parser_config(self):
        """Create parser configuration for tests."""
        return ParserConfig(lean_executable="lean", lake_enabled=False, lean_timeout=10)

    @pytest.fixture
    def generator_config(self):
        """Create generator configuration for tests."""
        return GenerationConfig(
            model="claude-3-sonnet", temperature=0.7, max_tokens=1000
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
        parser = LeanParser(parser_config)
        generator = ClaudeGenerator(generator_config)

        # Parse
        result = parser.parse_file(lean_files["simple"])
        assert len(result.theorems) == 1
        theorem = result.theorems[0]

        # Generate with mocked Claude
        with patch("subprocess.run") as mock_run:
            mock_run.return_value = Mock(
                stdout='{"explanation": "This theorem states that adding zero to any natural number leaves it unchanged.", "steps": ["Apply reflexivity"]}',
                stderr="",
                returncode=0,
            )

            sketch = generator.generate_proof_sketch(theorem)

            assert sketch.theorem_name == "add_zero"
            assert "adding zero" in sketch.explanation.lower()
            assert len(sketch.steps) == 1

    def test_parse_and_generate_induction(
        self, parser_config, generator_config, lean_files
    ):
        """Test parsing and generating for an induction proof."""
        parser = LeanParser(parser_config)
        generator = ClaudeGenerator(generator_config)

        # Parse
        result = parser.parse_file(lean_files["induction"])
        theorem = result.theorems[0]

        # Generate with mocked Claude
        with patch("subprocess.run") as mock_run:
            mock_run.return_value = Mock(
                stdout='{"explanation": "This theorem proves the formula for the sum of first n natural numbers using induction.", "steps": ["Base case: n=0", "Inductive step: assume true for n, prove for n+1", "Simplify and apply inductive hypothesis"]}',
                stderr="",
                returncode=0,
            )

            sketch = generator.generate_proof_sketch(theorem)

            assert "induction" in sketch.explanation.lower()
            assert len(sketch.steps) == 3
            assert "base case" in sketch.steps[0].lower()

    def test_parse_and_generate_multiple(
        self, parser_config, generator_config, lean_files
    ):
        """Test parsing and generating for multiple theorems."""
        parser = LeanParser(parser_config)
        generator = ClaudeGenerator(generator_config)

        # Parse
        result = parser.parse_file(lean_files["multiple"])
        assert len(result.theorems) == 3

        # Generate for each theorem
        sketches = []
        with patch("subprocess.run") as mock_run:
            responses = [
                '{"explanation": "Reflexivity of equality", "steps": ["Direct application of rfl"]}',
                '{"explanation": "Symmetry of equality", "steps": ["Apply symmetry to hypothesis"]}',
                '{"explanation": "Transitivity of equality", "steps": ["Chain equalities using trans"]}',
            ]

            for i, theorem in enumerate(result.theorems):
                mock_run.return_value = Mock(
                    stdout=responses[i], stderr="", returncode=0
                )

                sketch = generator.generate_proof_sketch(theorem)
                sketches.append(sketch)

        assert len(sketches) == 3
        assert "reflexivity" in sketches[0].explanation.lower()
        assert "symmetry" in sketches[1].explanation.lower()
        assert "transitivity" in sketches[2].explanation.lower()

    def test_mathematical_context_generation(self, parser_config, generator_config):
        """Test generating with mathematical context."""
        parser = LeanParser(parser_config)
        generator = ClaudeGenerator(generator_config)

        # Create theorem with imports
        theorem_content = """
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime

theorem prime_exists (n : Nat) : ∃ p, Nat.Prime p ∧ p > n := by
  sorry
"""

        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(theorem_content)
            lean_file = Path(f.name)

        try:
            result = parser.parse_file(lean_file)
            theorem = result.theorems[0]

            # Generate with context
            with patch("subprocess.run") as mock_run:
                mock_run.return_value = Mock(
                    stdout='{"explanation": "Using properties of prime numbers from Mathlib", "steps": ["Apply infinite primes theorem"]}',
                    stderr="",
                    returncode=0,
                )

                context = "This theorem uses Mathlib's prime number theory"
                generator.generate_proof_sketch(theorem, mathematical_context=context)

                # Verify context was passed
                mock_run.assert_called_once()
                call_args = mock_run.call_args[0][0]
                assert any("prime" in arg.lower() for arg in call_args)
        finally:
            lean_file.unlink()

    def test_error_recovery(self, parser_config, generator_config, tmp_path):
        """Test error recovery in the pipeline."""
        parser = LeanParser(parser_config)
        generator = ClaudeGenerator(generator_config)

        # Create file with mixed valid/invalid content
        mixed_file = tmp_path / "mixed.lean"
        mixed_file.write_text(
            """
theorem valid_theorem : 1 = 1 := rfl

invalid syntax here

theorem another_valid : 2 = 2 := rfl
"""
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
                    stdout='{"explanation": "Trivial equality", "steps": ["rfl"]}',
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

        parser = LeanParser(parser_config)
        generator = ClaudeGenerator(generator_config)

        # Set cache directories
        cache_dir = tmp_path / "cache"
        cache_dir.mkdir()

        # First run
        result1 = parser.parse_file(lean_files["simple"])
        with patch("subprocess.run") as mock_run:
            mock_run.return_value = Mock(
                stdout='{"explanation": "Cached result", "steps": ["Step 1"]}',
                stderr="",
                returncode=0,
            )
            sketch1 = generator.generate_proof_sketch(result1.theorems[0])

        # Second run should use cache
        result2 = parser.parse_file(lean_files["simple"])
        with patch("subprocess.run") as mock_run:
            # If cache works, this shouldn't be called
            mock_run.return_value = Mock(
                stdout='{"explanation": "Should not see this", "steps": []}',
                stderr="",
                returncode=0,
            )
            sketch2 = generator.generate_proof_sketch(result2.theorems[0])

        # Results should be consistent
        assert sketch1.explanation == sketch2.explanation
