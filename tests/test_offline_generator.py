#!/usr/bin/env python3
"""Comprehensive tests for offline proof sketch generation.

Tests the OfflineGenerator class that provides AI-free explanations
based on theorem AST analysis and template-based generation.
"""

import json
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import Mock, patch

import pytest

from src.proof_sketcher.core.exceptions import GenerationError
from src.proof_sketcher.generator.models import (
    GenerationConfig,
    GenerationRequest,
    GenerationResponse,
    ProofSketch,
    ProofStep,
)
from src.proof_sketcher.generator.offline import OfflineGenerator, OfflineTemplates
from src.proof_sketcher.parser.models import TheoremInfo


class TestOfflineTemplates:
    """Test the OfflineTemplates class."""

    def test_theorem_intro_templates(self):
        """Test theorem introduction templates."""
        templates = OfflineTemplates.THEOREM_INTRO_TEMPLATES

        # Check key templates exist
        assert "equality" in templates
        assert "inequality" in templates
        assert "existence" in templates
        assert "uniqueness" in templates
        assert "implication" in templates
        assert "equivalence" in templates
        assert "induction" in templates
        assert "membership" in templates
        assert "function" in templates
        assert "default" in templates

        # Check template content
        assert "equality relationship" in templates["equality"]
        assert "existence of mathematical objects" in templates["existence"]

    def test_proof_strategy_templates(self):
        """Test proof strategy templates."""
        templates = OfflineTemplates.PROOF_STRATEGY_TEMPLATES

        # Check key strategies exist
        assert "by_simp" in templates
        assert "by_rw" in templates
        assert "by_exact" in templates
        assert "by_apply" in templates
        assert "by_intro" in templates
        assert "by_cases" in templates
        assert "by_induction" in templates
        assert "by_contradiction" in templates
        assert "by_reflexivity" in templates
        assert "by_symmetry" in templates

        # Check template content
        assert "simplification tactics" in templates["by_simp"]
        assert "mathematical induction" in templates["by_induction"]

    def test_mathematical_structure_templates(self):
        """Test mathematical structure templates."""
        templates = OfflineTemplates.MATHEMATICAL_STRUCTURE_TEMPLATES

        # Check structures exist
        assert "natural_numbers" in templates
        assert "real_numbers" in templates
        assert "groups" in templates
        assert "rings" in templates
        assert "functions" in templates
        assert "sets" in templates
        assert "lists" in templates

        # Check content
        assert "counting numbers" in templates["natural_numbers"]
        assert "algebraic structure" in templates["groups"]


class TestOfflineGenerator:
    """Test the OfflineGenerator class."""

    @pytest.fixture
    def generator(self):
        """Create an OfflineGenerator instance."""
        return OfflineGenerator()

    @pytest.fixture
    def simple_theorem(self):
        """Create a simple theorem for testing."""
        return TheoremInfo(
            name="add_comm",
            statement="theorem add_comm (a b : Nat) : a + b = b + a",
            proof="by simp",
            dependencies=[],
            line_number=10,
            docstring="Addition is commutative",
            namespace="MyMath",
            visibility="public",
            tactics=["simp"],
            is_axiom=False,
        )

    @pytest.fixture
    def complex_theorem(self):
        """Create a complex theorem for testing."""
        return TheoremInfo(
            name="prime_infinite",
            statement="theorem prime_infinite : ∀ n, ∃ p > n, Prime p",
            proof="""by
  intro n
  use (factorial n + 1)
  constructor
  · simp [factorial_pos]
  · apply prime_of_coprime
    intro m hm
    cases hm with
    | zero => simp
    | succ k =>
      rw [coprime_comm]
      apply coprime_of_dvd""",
            dependencies=["factorial", "Prime", "coprime"],
            line_number=42,
            docstring="There are infinitely many prime numbers",
            namespace="NumberTheory",
            visibility="public",
            tactics=["intro", "use", "constructor", "simp", "apply", "cases", "rw"],
            is_axiom=False,
        )

    def test_initialization(self, generator):
        """Test generator initialization."""
        assert generator.logger is not None
        assert hasattr(generator, "_analyze_theorem_type")
        assert hasattr(generator, "_extract_proof_steps")

    def test_analyze_theorem_type_equality(self, generator):
        """Test theorem type analysis for equality."""
        theorem = TheoremInfo(
            name="test_eq", statement="theorem test_eq : 2 + 2 = 4", proof="rfl"
        )

        theorem_type = generator._analyze_theorem_type(theorem)
        assert theorem_type == "equality"

    def test_analyze_theorem_type_existence(self, generator):
        """Test theorem type analysis for existence."""
        theorem = TheoremInfo(
            name="exists_test",
            statement="theorem exists_test : ∃ x, x > 0",
            proof="use 1; simp",
        )

        theorem_type = generator._analyze_theorem_type(theorem)
        assert theorem_type == "existence"

    def test_analyze_theorem_type_implication(self, generator):
        """Test theorem type analysis for implication."""
        theorem = TheoremInfo(
            name="impl_test", statement="theorem impl_test (h : P) : Q", proof="exact h"
        )

        theorem_type = generator._analyze_theorem_type(theorem)
        assert theorem_type == "implication"

    def test_analyze_theorem_type_equivalence(self, generator):
        """Test theorem type analysis for equivalence."""
        theorem = TheoremInfo(
            name="iff_test",
            statement="theorem iff_test : P ↔ Q",
            proof="constructor; intro; assumption",
        )

        theorem_type = generator._analyze_theorem_type(theorem)
        assert theorem_type == "equivalence"

    def test_analyze_theorem_type_uniqueness(self, generator):
        """Test theorem type analysis for uniqueness."""
        theorem = TheoremInfo(
            name="unique_test",
            statement="theorem unique_test : ∃! x, P x",
            proof="use a; constructor; exact ha; intros",
        )

        theorem_type = generator._analyze_theorem_type(theorem)
        assert theorem_type == "uniqueness"

    def test_analyze_theorem_type_induction(self, generator):
        """Test theorem type analysis for induction."""
        theorem = TheoremInfo(
            name="ind_test",
            statement="theorem ind_test (n : Nat) : P n",
            proof="induction n with | zero => sorry | succ k ih => sorry",
        )

        theorem_type = generator._analyze_theorem_type(theorem)
        assert theorem_type == "induction"

    def test_analyze_theorem_type_default(self, generator):
        """Test theorem type analysis default case."""
        theorem = TheoremInfo(
            name="other_test",
            statement="theorem other_test : SomeComplexProp",
            proof="sorry",
        )

        theorem_type = generator._analyze_theorem_type(theorem)
        assert theorem_type == "default"

    def test_identify_mathematical_structures(self, generator):
        """Test identifying mathematical structures."""
        theorem = TheoremInfo(
            name="nat_list_test",
            statement="theorem nat_list_test (n : ℕ) (l : List α) (G : Group) : n + length l > 0",
            proof="simp",
        )

        structures = generator._identify_mathematical_structures(theorem)
        assert "natural_numbers" in structures
        assert "lists" in structures
        assert "groups" in structures

    def test_extract_proof_steps_simple(self, generator):
        """Test extracting proof steps from simple proof."""
        theorem = TheoremInfo(
            name="simple",
            statement="theorem simple : 1 = 1",
            proof="rfl",
            tactics=["rfl"],
        )

        steps = generator._extract_proof_steps(theorem)
        assert len(steps) == 1
        assert steps[0].tactics == ["rfl"]
        assert "reflexive" in steps[0].description.lower()

    def test_extract_proof_steps_complex(self, generator, complex_theorem):
        """Test extracting proof steps from complex proof."""
        steps = generator._extract_proof_steps(complex_theorem)

        assert len(steps) > 1
        # Check first step uses intro
        assert "intro" in steps[0].tactics
        # Check for constructor step
        constructor_steps = [s for s in steps if "constructor" in s.tactics]
        assert len(constructor_steps) > 0

    def test_extract_proof_steps_no_tactics(self, generator):
        """Test extracting proof steps when no tactics info available."""
        theorem = TheoremInfo(
            name="no_tactics",
            statement="theorem no_tactics : P",
            proof="by simp; exact h",
            tactics=[],  # No tactics extracted
        )

        steps = generator._extract_proof_steps(theorem)
        assert len(steps) >= 1
        assert "proof" in steps[0].description.lower()

    def test_generate_introduction_with_docstring(self, generator):
        """Test generating introduction with docstring."""
        theorem = TheoremInfo(
            name="documented",
            statement="theorem documented : P",
            proof="sorry",
            docstring="This is a well-documented theorem that proves P.",
        )

        intro = generator._generate_introduction(theorem, "default", [])
        assert "This is a well-documented theorem" in intro
        assert "fundamental mathematical relationship" in intro

    def test_generate_introduction_without_docstring(self, generator):
        """Test generating introduction without docstring."""
        theorem = TheoremInfo(
            name="undocumented", statement="theorem undocumented : a = b", proof="sorry"
        )

        intro = generator._generate_introduction(
            theorem, "equality", ["natural_numbers"]
        )
        assert "equality relationship" in intro
        assert "natural numbers" in intro.lower()

    def test_generate_conclusion(self, generator):
        """Test generating conclusion."""
        theorem = TheoremInfo(
            name="test_theorem",
            statement="theorem test_theorem : important_property",
            proof="sorry",
        )

        conclusion = generator._generate_conclusion(theorem, ["simp", "rw"])
        assert "test_theorem" in conclusion
        assert "established" in conclusion.lower() or "proven" in conclusion.lower()
        assert "simplification" in conclusion.lower()

    def test_infer_difficulty_beginner(self, generator):
        """Test inferring difficulty level - beginner."""
        simple_proof = "rfl"
        tactics = ["rfl"]

        difficulty = generator._infer_difficulty(simple_proof, tactics)
        assert difficulty == "beginner"

    def test_infer_difficulty_intermediate(self, generator):
        """Test inferring difficulty level - intermediate."""
        proof = "intro x; simp; exact h"
        tactics = ["intro", "simp", "exact"]

        difficulty = generator._infer_difficulty(proof, tactics)
        assert difficulty == "intermediate"

    def test_infer_difficulty_advanced(self, generator):
        """Test inferring difficulty level - advanced."""
        proof = """induction n with
        | zero => simp
        | succ k ih =>
          rw [factorial_succ]
          apply dvd_mul_of_dvd_left
          exact ih"""
        tactics = ["induction", "simp", "rw", "apply", "exact"]

        difficulty = generator._infer_difficulty(proof, tactics)
        assert difficulty == "advanced"

    def test_extract_prerequisites(self, generator):
        """Test extracting prerequisites."""
        theorem = TheoremInfo(
            name="test",
            statement="theorem test (G : Group) (n : ℕ) : P",
            proof="sorry",
            dependencies=["Group.mul_assoc", "Nat.add_comm", "List.length"],
        )

        prereqs = generator._extract_prerequisites(theorem)
        assert "Group theory basics" in prereqs
        assert "Natural number arithmetic" in prereqs
        assert "Basic Lean tactics" in prereqs

    def test_generate_proof_sketch_simple(self, generator, simple_theorem):
        """Test generating proof sketch for simple theorem."""
        sketch = generator.generate_proof_sketch(simple_theorem)

        assert isinstance(sketch, ProofSketch)
        assert sketch.theorem_name == "add_comm"
        assert "commutative" in sketch.introduction.lower()
        assert len(sketch.key_steps) >= 1
        assert sketch.difficulty_level in ["beginner", "intermediate"]
        assert "Natural numbers" in sketch.mathematical_areas
        assert len(sketch.prerequisites) > 0
        assert "established" in sketch.conclusion.lower()

    def test_generate_proof_sketch_complex(self, generator, complex_theorem):
        """Test generating proof sketch for complex theorem."""
        sketch = generator.generate_proof_sketch(complex_theorem)

        assert isinstance(sketch, ProofSketch)
        assert sketch.theorem_name == "prime_infinite"
        assert "infinitely many" in sketch.introduction.lower()
        assert len(sketch.key_steps) > 3  # Complex proof has multiple steps
        assert sketch.difficulty_level == "advanced"
        assert "Number theory" in sketch.mathematical_areas
        # Check for specific tactics in steps
        step_tactics = [tactic for step in sketch.key_steps for tactic in step.tactics]
        assert "intro" in step_tactics
        assert "constructor" in step_tactics

    def test_generate_proof_sketch_with_config(self, generator, simple_theorem):
        """Test generating proof sketch with custom config."""
        config = GenerationConfig(
            max_tokens=1000, include_tactics=False, include_dependencies=False
        )

        sketch = generator.generate_proof_sketch(simple_theorem, config)

        assert isinstance(sketch, ProofSketch)
        # Config doesn't affect offline generation much, but should not error
        assert sketch.theorem_name == "add_comm"

    def test_generate_proof_sketch_minimal_theorem(self, generator):
        """Test generating proof sketch with minimal theorem info."""
        theorem = TheoremInfo(
            name="minimal", statement="theorem minimal : True", proof="trivial"
        )

        sketch = generator.generate_proof_sketch(theorem)

        assert isinstance(sketch, ProofSketch)
        assert sketch.theorem_name == "minimal"
        assert len(sketch.key_steps) >= 1
        assert sketch.difficulty_level == "beginner"

    def test_handle_axiom(self, generator):
        """Test handling axioms."""
        axiom = TheoremInfo(
            name="choice",
            statement="axiom choice : ∀ {α : Sort u} (p : α → Prop), (∃ x, p x) → p (choose p)",
            proof="",
            is_axiom=True,
        )

        sketch = generator.generate_proof_sketch(axiom)

        assert "axiom" in sketch.introduction.lower()
        assert (
            "assumed" in sketch.introduction.lower()
            or "postulated" in sketch.introduction.lower()
        )
        assert len(sketch.key_steps) >= 1
        assert "axiom" in sketch.key_steps[0].description.lower()

    def test_proof_step_numbering(self, generator, complex_theorem):
        """Test that proof steps are numbered correctly."""
        sketch = generator.generate_proof_sketch(complex_theorem)

        for i, step in enumerate(sketch.key_steps):
            assert step.step_number == i + 1

    def test_mathematical_content_generation(self, generator):
        """Test mathematical content in proof steps."""
        theorem = TheoremInfo(
            name="test_math",
            statement="theorem test_math (a b : ℝ) : a + b = b + a",
            proof="ring",
            tactics=["ring"],
        )

        sketch = generator.generate_proof_sketch(theorem)

        # Should have mathematical content in steps
        assert len(sketch.key_steps) > 0
        for step in sketch.key_steps:
            assert len(step.mathematical_content) > 0
            assert step.mathematical_content != ""

    def test_caching_mechanism(self, generator):
        """Test that the generator can cache results (even if not implemented)."""
        theorem = TheoremInfo(
            name="cached_theorem",
            statement="theorem cached_theorem : 1 + 1 = 2",
            proof="simp",
        )

        # Generate twice
        sketch1 = generator.generate_proof_sketch(theorem)
        sketch2 = generator.generate_proof_sketch(theorem)

        # Should produce consistent results
        assert sketch1.theorem_name == sketch2.theorem_name
        assert sketch1.introduction == sketch2.introduction
        assert len(sketch1.key_steps) == len(sketch2.key_steps)

    def test_unicode_handling(self, generator):
        """Test handling Unicode mathematical symbols."""
        theorem = TheoremInfo(
            name="unicode_test",
            statement="theorem unicode_test (α β : Type*) (f : α → β) : ∀ x, ∃ y, f x = y",
            proof="intro x; use (f x); rfl",
        )

        sketch = generator.generate_proof_sketch(theorem)

        assert sketch.theorem_name == "unicode_test"
        # Should handle Unicode without errors
        assert len(sketch.introduction) > 0
        assert len(sketch.key_steps) > 0

    def test_empty_proof_handling(self, generator):
        """Test handling empty or sorry proofs."""
        theorem = TheoremInfo(
            name="sorry_theorem",
            statement="theorem sorry_theorem : ComplexProperty",
            proof="sorry",
        )

        sketch = generator.generate_proof_sketch(theorem)

        assert len(sketch.key_steps) >= 1
        assert "proof" in sketch.key_steps[0].description.lower()
        assert (
            "deferred" in sketch.key_steps[0].description
            or "incomplete" in sketch.key_steps[0].description
        )

    def test_long_proof_handling(self, generator):
        """Test handling very long proofs."""
        long_proof = "\n".join([f"· case{i} => simp" for i in range(50)])
        theorem = TheoremInfo(
            name="long_theorem",
            statement="theorem long_theorem : VeryComplexProperty",
            proof=f"cases x with\n{long_proof}",
            tactics=["cases"] + ["simp"] * 50,
        )

        sketch = generator.generate_proof_sketch(theorem)

        # Should handle long proofs gracefully
        assert len(sketch.key_steps) > 0
        assert sketch.difficulty_level == "advanced"

    def test_error_handling(self, generator):
        """Test error handling for malformed theorems."""
        # Test with None values
        with pytest.raises(AttributeError):
            theorem = TheoremInfo(
                name=None, statement="theorem test : P", proof="sorry"  # Invalid
            )
            generator.generate_proof_sketch(theorem)

    def test_special_tactics_handling(self, generator):
        """Test handling special tactics."""
        theorem = TheoremInfo(
            name="special_tactics",
            statement="theorem special_tactics : P",
            proof="by decide",
            tactics=["decide"],
        )

        sketch = generator.generate_proof_sketch(theorem)

        # Should recognize decide tactic
        assert len(sketch.key_steps) > 0
        assert (
            "decision" in sketch.key_steps[0].description.lower()
            or "decidable" in sketch.key_steps[0].description.lower()
        )


class TestOfflineGeneratorIntegration:
    """Integration tests for OfflineGenerator."""

    def test_full_generation_workflow(self):
        """Test complete generation workflow."""
        generator = OfflineGenerator()

        # Create a realistic theorem
        theorem = TheoremInfo(
            name="list_append_assoc",
            statement="theorem list_append_assoc (l1 l2 l3 : List α) : (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)",
            proof="""by
  induction l1 with
  | nil => rfl
  | cons x xs ih =>
    simp [List.append, ih]""",
            dependencies=["List.append"],
            line_number=25,
            docstring="List append operation is associative",
            namespace="DataStructures",
            visibility="public",
            tactics=["induction", "rfl", "simp"],
            is_axiom=False,
        )

        # Generate sketch
        sketch = generator.generate_proof_sketch(theorem)

        # Comprehensive validation
        assert sketch.theorem_name == "list_append_assoc"
        assert "associative" in sketch.introduction.lower()
        assert len(sketch.key_steps) >= 2  # Base case and inductive case

        # Check for induction structure
        induction_steps = [
            s for s in sketch.key_steps if any("induction" in t for t in s.tactics)
        ]
        assert len(induction_steps) > 0

        # Check mathematical areas
        assert (
            "Data structures" in sketch.mathematical_areas
            or "Lists" in sketch.mathematical_areas
        )

        # Check difficulty
        assert sketch.difficulty_level in ["intermediate", "advanced"]

        # Check prerequisites
        assert len(sketch.prerequisites) > 0
        assert any("induction" in p.lower() for p in sketch.prerequisites)

        # Validate all steps have required fields
        for i, step in enumerate(sketch.key_steps):
            assert step.step_number == i + 1
            assert len(step.description) > 0
            assert isinstance(step.tactics, list)
            assert len(step.mathematical_content) > 0

        # Check conclusion
        assert "list_append_assoc" in sketch.conclusion
        assert (
            "established" in sketch.conclusion.lower()
            or "proven" in sketch.conclusion.lower()
        )

    def test_batch_generation(self):
        """Test generating multiple proof sketches."""
        generator = OfflineGenerator()

        theorems = [
            TheoremInfo(
                name=f"theorem_{i}",
                statement=f"theorem theorem_{i} : {i} + 0 = {i}",
                proof="simp",
                tactics=["simp"],
            )
            for i in range(5)
        ]

        sketches = []
        for theorem in theorems:
            sketch = generator.generate_proof_sketch(theorem)
            sketches.append(sketch)

        assert len(sketches) == 5

        # All should be successful
        for i, sketch in enumerate(sketches):
            assert sketch.theorem_name == f"theorem_{i}"
            assert len(sketch.key_steps) > 0
            assert sketch.difficulty_level == "beginner"
