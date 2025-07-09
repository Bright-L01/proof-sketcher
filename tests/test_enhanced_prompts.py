"""Test enhanced prompt engineering improvements."""

import pytest

from proof_sketcher.generator.models import GenerationConfig, GenerationType
from proof_sketcher.generator.prompts import prompt_templates
from proof_sketcher.parser.models import TheoremInfo


class TestEnhancedPrompts:
    """Test the enhanced prompt templates."""

    @pytest.fixture
    def sample_theorem(self):
        """Create a sample theorem for testing."""
        return TheoremInfo(
            name="add_comm",
            statement="∀ (a b : ℕ), a + b = b + a",
            proof="by simp [add_comm]",
            line_number=42,
            dependencies=["Nat.add_comm"],
            docstring="Commutativity of natural number addition",
        )

    @pytest.fixture
    def sample_config(self):
        """Create a sample generation config."""
        return GenerationConfig(verbosity="detailed", include_reasoning=True)

    def test_enhanced_proof_sketch_template(self, sample_theorem, sample_config):
        """Test the enhanced proof sketch template includes new sections."""
        prompt = prompt_templates.render_prompt(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name=sample_theorem.name,
            theorem_statement=sample_theorem.statement,
            config=sample_config,
            dependencies=sample_theorem.dependencies,
            proof_text=sample_theorem.proof,
            docstring=sample_theorem.docstring,
            mathematical_context="algebra",
        )

        # Check for enhanced prompt features
        assert "🎯 OBJECTIVE" in prompt
        assert "💡 EXAMPLE OF EXCELLENT EXPLANATION" in prompt
        assert "mathematical_significance" in prompt
        assert "proof_strategy" in prompt
        assert "pedagogical_notes" in prompt
        assert "lean_tactics" in prompt
        assert "landscape of interconnected ideas" in prompt

    def test_enhanced_eli5_template(self, sample_theorem, sample_config):
        """Test the enhanced ELI5 template includes storytelling elements."""
        prompt = prompt_templates.render_prompt(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name=sample_theorem.name,
            theorem_statement=sample_theorem.statement,
            config=sample_config,
            mathematical_context="basic arithmetic",
        )

        # Check for storytelling features
        assert "🎪 THE MATHEMATICAL DISCOVERY" in prompt
        assert "Bill Nye" in prompt or "Neil deGrasse Tyson" in prompt
        assert "🌟 MASTER CLASS EXAMPLE" in prompt
        assert "STORYTELLING FRAMEWORK" in prompt
        assert "ANALOGY BANK" in prompt
        assert "mathematical wonder" in prompt

    def test_enhanced_tactic_template(self, sample_theorem, sample_config):
        """Test the enhanced tactic explanation template includes pedagogical insight."""
        prompt = prompt_templates.render_prompt(
            generation_type=GenerationType.TACTIC_EXPLANATION,
            theorem_name=sample_theorem.name,
            theorem_statement=sample_theorem.statement,
            config=sample_config,
            proof_text=sample_theorem.proof,
        )

        # Check for tactical analysis features
        assert "🧠 TACTICAL THINKING FRAMEWORK" in prompt
        assert "PHASE 1: TACTICAL INVENTORY" in prompt
        assert "PHASE 2: STRATEGIC REASONING" in prompt
        assert "PHASE 3: LEARNING PATTERNS" in prompt
        assert "simp [one_mul, mul_one]" in prompt  # Example
        assert "tactical intuition" in prompt

    def test_enhanced_step_by_step_template(self, sample_theorem, sample_config):
        """Test the enhanced step-by-step template includes guided learning."""
        prompt = prompt_templates.render_prompt(
            generation_type=GenerationType.STEP_BY_STEP,
            theorem_name=sample_theorem.name,
            theorem_statement=sample_theorem.statement,
            config=sample_config,
            proof_text=sample_theorem.proof,
        )

        # Check for guided tutorial features
        assert "🔍 THE MATHEMATICAL INVESTIGATION" in prompt
        assert "mathematical detectives" in prompt
        assert "🎪 MASTERFUL TUTORING EXAMPLE" in prompt
        assert "GUIDED DISCOVERY STRUCTURE" in prompt
        assert "🎬 THE SETUP" in prompt
        assert "🧠 THE THINKING" in prompt
        assert "🔧 THE EXECUTION" in prompt
        assert "🎉 THE PAYOFF" in prompt

    def test_mathematical_context_template(self, sample_theorem, sample_config):
        """Test the new mathematical context template."""
        prompt = prompt_templates.render_prompt(
            generation_type=GenerationType.MATHEMATICAL_CONTEXT,
            theorem_name=sample_theorem.name,
            theorem_statement=sample_theorem.statement,
            config=sample_config,
        )

        # Check for context analysis features
        assert "🔬 THE MATHEMATICAL SPECIMEN" in prompt
        assert "MATHEMATICAL CARTOGRAPHY" in prompt
        assert "HISTORICAL PERSPECTIVE" in prompt
        assert "MATHEMATICAL ECOLOGY" in prompt
        assert "CONNECTION WEB" in prompt
        assert "CONCEPTUAL LANDSCAPE" in prompt
        assert "mathematical_context" in prompt
        assert "historical_context" in prompt
        assert "pedagogical_insights" in prompt

    def test_all_templates_contain_emoji_structure(self, sample_theorem, sample_config):
        """Test that all enhanced templates use consistent emoji-based structure."""
        for gen_type in [
            GenerationType.PROOF_SKETCH,
            GenerationType.ELI5_EXPLANATION,
            GenerationType.TACTIC_EXPLANATION,
            GenerationType.STEP_BY_STEP,
            GenerationType.MATHEMATICAL_CONTEXT,
        ]:
            prompt = prompt_templates.render_prompt(
                generation_type=gen_type,
                theorem_name=sample_theorem.name,
                theorem_statement=sample_theorem.statement,
                config=sample_config,
            )

            # Each template should have emoji-structured sections
            emoji_indicators = ["🎯", "📚", "💡", "🔧", "🌟", "🎪", "🔍", "🧠", "🎓"]
            assert any(
                emoji in prompt for emoji in emoji_indicators
            ), f"Template {gen_type} should have emoji structure"

    def test_verbosity_handling(self, sample_theorem):
        """Test that different verbosity levels generate different content."""
        for verbosity in ["concise", "detailed", "verbose"]:
            config = GenerationConfig(verbosity=verbosity)

            prompt = prompt_templates.render_prompt(
                generation_type=GenerationType.PROOF_SKETCH,
                theorem_name=sample_theorem.name,
                theorem_statement=sample_theorem.statement,
                config=config,
            )

            # Should contain verbosity-specific content or references
            verbosity_found = verbosity in prompt.lower()
            audience_level_found = f"Audience Level**: {verbosity}" in prompt
            assert (
                verbosity_found or audience_level_found
            ), f"Template should reference verbosity level {verbosity}"

    def test_mathematical_context_integration(self, sample_theorem, sample_config):
        """Test that mathematical context is properly integrated."""
        math_context = "abstract algebra"

        prompt = prompt_templates.render_prompt(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name=sample_theorem.name,
            theorem_statement=sample_theorem.statement,
            config=sample_config,
            mathematical_context=math_context,
        )

        assert math_context in prompt

    def test_template_consistency(self, sample_theorem, sample_config):
        """Test that all templates maintain consistent structure and quality."""
        for gen_type in GenerationType:
            prompt = prompt_templates.render_prompt(
                generation_type=gen_type,
                theorem_name=sample_theorem.name,
                theorem_statement=sample_theorem.statement,
                config=sample_config,
            )

            # Basic quality checks
            assert len(prompt) > 500, f"Template {gen_type} should be substantial"
            # Allow "theorem_name" in JSON examples, but not as unrendered variable
            unrendered_vars = ["{{ theorem_name }}", "{{theorem_name}}"]
            assert not any(
                var in prompt for var in unrendered_vars
            ), "Template variables should be rendered"
            assert sample_theorem.name in prompt, "Theorem name should appear in prompt"

    def test_example_inclusion(self, sample_theorem, sample_config):
        """Test that enhanced templates include helpful examples."""
        examples_templates = [
            GenerationType.PROOF_SKETCH,
            GenerationType.ELI5_EXPLANATION,
            GenerationType.TACTIC_EXPLANATION,
            GenerationType.STEP_BY_STEP,
        ]

        for gen_type in examples_templates:
            prompt = prompt_templates.render_prompt(
                generation_type=gen_type,
                theorem_name=sample_theorem.name,
                theorem_statement=sample_theorem.statement,
                config=sample_config,
            )

            # Should contain example or demonstration
            example_indicators = ["example", "masterful", "master class", "watch how"]
            assert any(
                indicator in prompt.lower() for indicator in example_indicators
            ), f"Template {gen_type} should include examples"
