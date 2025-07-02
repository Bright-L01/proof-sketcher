"""Tests for prompt templates."""

import pytest
from jinja2 import Template

from proof_sketcher.generator.models import GenerationConfig, GenerationType
from proof_sketcher.generator.prompts import (
    PromptTemplates,
    prompt_templates,
    render_eli5_prompt,
    render_proof_sketch_prompt,
    render_step_by_step_prompt,
    render_tactic_explanation_prompt,
)
from proof_sketcher.parser.models import TheoremInfo


class TestPromptTemplates:
    """Tests for PromptTemplates class."""

    def test_prompt_templates_initialization(self):
        """Test prompt templates initialization."""
        templates = PromptTemplates()

        assert templates.env is not None
        assert "format_dependencies" in templates.env.filters
        assert "format_statement" in templates.env.filters

    def test_format_dependencies_filter(self):
        """Test the format_dependencies filter."""
        templates = PromptTemplates()

        # Empty dependencies
        assert templates._format_dependencies([]) == "None"

        # Few dependencies
        deps_short = ["Nat.add", "Eq.refl"]
        result_short = templates._format_dependencies(deps_short)
        assert result_short == "Nat.add, Eq.refl"

        # Many dependencies
        deps_long = ["Nat.add", "Eq.refl", "List.length", "Vector.cons", "Fin.val"]
        result_long = templates._format_dependencies(deps_long)
        assert "Nat.add, Eq.refl, List.length, and 2 others" == result_long

    def test_format_statement_filter(self):
        """Test the format_statement filter."""
        templates = PromptTemplates()

        # Test mathematical symbol replacement
        statement = "∀ n : Nat, n + 0 = n → ∃ m : Nat, m ≠ 0 ∧ (¬(m = 1) ∨ m > 0)"
        formatted = templates._format_statement(statement)

        assert "for all" in formatted
        assert "there exists" in formatted
        assert "implies" in formatted
        assert "not" in formatted
        assert "and" in formatted
        assert "or" in formatted
        assert "∀" not in formatted
        assert "∃" not in formatted
        assert "→" not in formatted
        assert "¬" not in formatted
        assert "∧" not in formatted
        assert "∨" not in formatted

    def test_get_template_for_each_type(self):
        """Test getting templates for each generation type."""
        templates = PromptTemplates()

        # Test all generation types have templates
        for gen_type in GenerationType:
            template = templates.get_template(gen_type)
            assert isinstance(template, Template)

    def test_get_template_invalid_type(self):
        """Test getting template for invalid type."""
        templates = PromptTemplates()

        with pytest.raises(ValueError, match="No template found"):
            templates.get_template("invalid_type")

    def test_proof_sketch_template_rendering(self):
        """Test proof sketch template rendering."""
        templates = PromptTemplates()
        template = templates.proof_sketch_template

        config = GenerationConfig(verbosity="detailed", include_reasoning=True)

        rendered = template.render(
            theorem_name="add_zero",
            theorem_statement="∀ n : Nat, n + 0 = n",
            config=config,
            dependencies=["Nat.add_zero"],
            proof_text="by simp",
            docstring="Addition identity theorem",
        )

        assert "add_zero" in rendered
        assert "for all n : Nat, n + 0 = n" in rendered  # Formatted statement
        assert "Nat.add_zero" in rendered
        assert "by simp" in rendered
        assert "Addition identity theorem" in rendered
        assert "detailed" in rendered
        assert "```json" in rendered

    def test_eli5_template_rendering(self):
        """Test ELI5 template rendering."""
        templates = PromptTemplates()
        template = templates.eli5_template

        config = GenerationConfig(verbosity="concise")

        rendered = template.render(
            theorem_name="commutativity",
            theorem_statement="a + b = b + a",
            config=config,
            dependencies=["addition"],
            docstring="Addition is commutative",
        )

        assert "commutativity" in rendered
        assert "a + b = b + a" in rendered
        assert "addition" in rendered
        assert "Addition is commutative" in rendered
        assert "ANALOGY BANK" in rendered
        assert "real-world comparison" in rendered
        assert "150-250 words" in rendered  # Concise verbosity

    def test_tactic_explanation_template_rendering(self):
        """Test tactic explanation template rendering."""
        templates = PromptTemplates()
        template = templates.tactic_explanation_template

        config = GenerationConfig(include_reasoning=True)

        rendered = template.render(
            theorem_name="induction_example",
            theorem_statement="P(n) for all n",
            config=config,
            proof_text="by induction on n; simp; exact h",
            dependencies=["Nat.induction"],
        )

        assert "induction_example" in rendered
        assert "P(n) for all n" in rendered
        assert "by induction on n; simp; exact h" in rendered
        assert "Nat.induction" in rendered
        assert "TACTICAL ANALYSIS" in rendered
        assert "Reasoning-heavy" in rendered  # include_reasoning=True

    def test_step_by_step_template_rendering(self):
        """Test step-by-step template rendering."""
        templates = PromptTemplates()
        template = templates.step_by_step_template

        config = GenerationConfig(verbosity="verbose")

        rendered = template.render(
            theorem_name="transitivity",
            theorem_statement="a = b ∧ b = c → a = c",
            config=config,
            dependencies=["Eq.trans"],
            docstring="Transitivity of equality",
        )

        assert "transitivity" in rendered
        assert "a = b and b = c implies a = c" in rendered  # Formatted
        assert "Eq.trans" in rendered
        assert "Transitivity of equality" in rendered
        assert "STEP-BY-STEP" in rendered
        assert "verbose" in rendered

    def test_render_prompt_method(self):
        """Test the render_prompt method."""
        templates = PromptTemplates()

        config = GenerationConfig()

        rendered = templates.render_prompt(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name="test_theorem",
            theorem_statement="P → Q",
            config=config,
            dependencies=["Logic.impl"],
            proof_text="by assumption",
            docstring="Implication example",
        )

        assert "test_theorem" in rendered
        assert "P implies Q" in rendered  # Formatted statement
        assert "Logic.impl" in rendered
        assert "Implication example" in rendered
        # ELI5 template doesn't include proof text, only proof sketch does


class TestConvenienceFunctions:
    """Tests for convenience prompt rendering functions."""

    def setup_method(self):
        """Set up test fixtures."""
        self.theorem = TheoremInfo(
            name="add_comm",
            statement="∀ a b : Nat, a + b = b + a",
            dependencies=["Nat.add_comm"],
            proof="by ring",
            docstring="Commutativity of addition",
        )
        self.config = GenerationConfig(verbosity="detailed")

    def test_render_proof_sketch_prompt(self):
        """Test proof sketch prompt rendering."""
        prompt = render_proof_sketch_prompt(
            self.theorem,
            self.config,
            mathematical_context="Basic arithmetic properties",
        )

        assert "add_comm" in prompt
        assert "for all a b : Nat, a + b = b + a" in prompt
        assert "Nat.add_comm" in prompt
        assert "by ring" in prompt
        assert "Commutativity of addition" in prompt
        assert "Basic arithmetic properties" in prompt
        assert "```json" in prompt

    def test_render_eli5_prompt(self):
        """Test ELI5 prompt rendering."""
        prompt = render_eli5_prompt(
            self.theorem, self.config, mathematical_context="Elementary arithmetic"
        )

        assert "add_comm" in prompt
        assert "for all a b : Nat, a + b = b + a" in prompt
        assert "Nat.add_comm" in prompt
        assert "Commutativity of addition" in prompt
        assert "Elementary arithmetic" in prompt
        assert "ANALOGY BANK" in prompt
        assert "science communicator" in prompt

    def test_render_tactic_explanation_prompt(self):
        """Test tactic explanation prompt rendering."""
        prompt = render_tactic_explanation_prompt(
            self.theorem, self.config, mathematical_context="Ring theory context"
        )

        assert "add_comm" in prompt
        assert "for all a b : Nat, a + b = b + a" in prompt
        assert "by ring" in prompt
        assert "Nat.add_comm" in prompt
        assert "Ring theory context" in prompt
        assert "tactics" in prompt
        assert "Lean 4" in prompt

    def test_render_step_by_step_prompt(self):
        """Test step-by-step prompt rendering."""
        prompt = render_step_by_step_prompt(
            self.theorem, self.config, mathematical_context="Proof techniques"
        )

        assert "add_comm" in prompt
        assert "for all a b : Nat, a + b = b + a" in prompt
        assert "Nat.add_comm" in prompt
        assert "Commutativity of addition" in prompt
        assert "Proof techniques" in prompt
        assert "Step-by-Step" in prompt
        assert "walkthrough" in prompt

    def test_prompt_rendering_with_minimal_theorem(self):
        """Test prompt rendering with minimal theorem info."""
        minimal_theorem = TheoremInfo(name="simple_theorem", statement="P")

        config = GenerationConfig()

        # Should not crash with minimal info
        prompt = render_eli5_prompt(minimal_theorem, config)

        assert "simple_theorem" in prompt
        assert "P" in prompt
        # Should handle missing fields gracefully

    def test_prompt_rendering_with_empty_dependencies(self):
        """Test prompt rendering with empty dependencies."""
        theorem = TheoremInfo(
            name="independent_theorem", statement="True", dependencies=[]
        )

        config = GenerationConfig()

        prompt = render_proof_sketch_prompt(theorem, config)

        assert "independent_theorem" in prompt
        assert "True" in prompt
        # Should handle empty dependencies gracefully


class TestGlobalPromptTemplatesInstance:
    """Tests for the global prompt_templates instance."""

    def test_global_instance_exists(self):
        """Test that global prompt_templates instance exists."""
        assert prompt_templates is not None
        assert isinstance(prompt_templates, PromptTemplates)

    def test_global_instance_functionality(self):
        """Test that global instance works correctly."""
        template = prompt_templates.get_template(GenerationType.ELI5_EXPLANATION)
        assert isinstance(template, Template)

        config = GenerationConfig()
        rendered = prompt_templates.render_prompt(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name="test",
            theorem_statement="P",
            config=config,
        )

        assert "test" in rendered
        assert "P" in rendered
