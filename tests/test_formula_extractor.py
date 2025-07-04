"""Comprehensive tests for formula_extractor.py to improve coverage."""

import re
from unittest.mock import Mock, patch

import pytest

from src.proof_sketcher.animator.formula_extractor import (
    FormulaExtractor,
    LeanToLatexConverter,
    ProofStepAnalyzer,
    FormulaTransformation,
    ExtractedFormula,
    ProcessedContent
)
from src.proof_sketcher.animator.models import TransformationType
from src.proof_sketcher.core.exceptions import FormulaExtractionError


class TestLeanToLatexConverter:
    """Tests for LeanToLatexConverter class."""
    
    @pytest.fixture
    def converter(self):
        """Create a converter instance."""
        return LeanToLatexConverter()
    
    def test_convert_simple_expression(self, converter):
        """Test conversion of simple expressions."""
        # Basic arithmetic
        assert converter.convert("a + b") == "a + b"
        assert converter.convert("a - b") == "a - b"
        assert converter.convert("a * b") == "a * b"
        assert converter.convert("a / b") == "a / b"
    
    def test_convert_unicode_symbols(self, converter):
        """Test conversion of Unicode symbols."""
        # Quantifiers
        assert converter.convert("∀ x, P(x)") == "\\forall x, P(x)"
        assert converter.convert("∃ x, P(x)") == "\\exists x, P(x)"
        
        # Logic operators
        assert converter.convert("a → b") == "a \\to b"
        assert converter.convert("a ↔ b") == "a \\leftrightarrow b"
        assert converter.convert("¬a") == "\\neg a"
        assert converter.convert("a ∧ b") == "a \\land b"
        assert converter.convert("a ∨ b") == "a \\lor b"
        
        # Set operations
        assert converter.convert("x ∈ A") == "x \\in A"
        assert converter.convert("A ⊆ B") == "A \\subseteq B"
        assert converter.convert("A ∪ B") == "A \\cup B"
        assert converter.convert("A ∩ B") == "A \\cap B"
        assert converter.convert("∅") == "\\emptyset"
        
        # Arithmetic symbols
        assert converter.convert("a ≤ b") == "a \\leq b"
        assert converter.convert("a ≥ b") == "a \\geq b"
        assert converter.convert("a ≠ b") == "a \\neq b"
        assert converter.convert("a ≈ b") == "a \\approx b"
        
        # Number sets
        assert converter.convert("n ∈ ℕ") == "n \\in \\mathbb{N}"
        assert converter.convert("x ∈ ℝ") == "x \\in \\mathbb{R}"
        
        # Greek letters
        assert converter.convert("α + β") == "\\alpha + \\beta"
        assert converter.convert("λ x, x + 1") == "\\lambda x. x + 1"
        assert converter.convert("Σ i") == "\\Sigma i"
    
    def test_convert_function_applications(self, converter):
        """Test conversion of function applications."""
        # Arithmetic functions
        assert converter.convert("Nat.add a b") == "a + b"
        assert converter.convert("Real.mul x y") == "x \\cdot y"
        assert converter.convert("Real.pow x 2") == "x^{2}"
        assert converter.convert("Nat.factorial n") == "n!"
        
        # Mathematical functions
        assert converter.convert("Real.sqrt x") == "\\sqrt{x}"
        assert converter.convert("Real.sin θ") == "\\sin(\\theta)"
        assert converter.convert("Real.cos θ") == "\\cos(\\theta)"
        assert converter.convert("Real.log x") == "\\log(x)"
        
        # Set operations
        assert converter.convert("Set.union A B") == "A \\cup B"
        assert converter.convert("Set.inter A B") == "A \\cap B"
    
    def test_clean_type_annotations(self, converter):
        """Test removal of type annotations."""
        # Simple type annotations
        assert converter.convert("(n : Nat)") == "n"
        assert converter.convert("(x : Real)") == "x"
        assert converter.convert("(f : Nat → Nat)") == "f"
        
        # Standalone type declarations
        assert converter.convert("x : Real") == "x"
        assert converter.convert("f : Nat → Nat") == "f"
        
        # Complex expressions with types
        result = converter.convert("∀ (n : Nat), n + 0 = n")
        assert "Nat" not in result
        assert "\\forall n, n + 0 = n" == result
    
    def test_convert_quantifiers(self, converter):
        """Test quantifier conversion."""
        # Universal quantifier
        assert converter.convert("∀ x, P x") == "\\forall x, P(x)"
        assert converter.convert("∀ x : T, P x") == "\\forall x, P(x)"
        
        # Existential quantifier
        assert converter.convert("∃ x, P x") == "\\exists x, P(x)"
        assert converter.convert("∃ x : T, P x") == "\\exists x, P(x)"
        
        # Lambda expressions
        assert converter.convert("λ x, x + 1") == "\\lambda x. x + 1"
        assert converter.convert("λ x, f x") == "\\lambda x. f(x)"
    
    def test_convert_infix_operators(self, converter):
        """Test infix operator conversion."""
        # Equality chains
        assert converter.convert("a = b = c") == "a = b = c"
        
        # Implications
        assert converter.convert("a → b") == "a \\to b"
        
        # Biconditionals
        assert converter.convert("a ↔ b") == "a \\leftrightarrow b"
    
    def test_improve_formatting(self, converter):
        """Test formatting improvements."""
        # Spacing around operators
        assert converter.convert("a+b") == "a + b"
        assert converter.convert("x-y") == "x - y"
        
        # Subscripts
        assert converter.convert("x_n") == "x_{n}"
        assert converter.convert("a_i") == "a_{i}"
        
        # Function calls
        assert converter.convert("f( x )") == "f(x)"
        assert converter.convert("g(a, b)") == "g(a, b)"
    
    def test_error_handling(self, converter):
        """Test error handling in conversion."""
        # Test with invalid input that causes an exception
        with patch.object(converter, '_convert_unicode_symbols', side_effect=Exception("Test error")):
            with pytest.raises(FormulaExtractionError) as exc_info:
                converter.convert("test")
            assert "Failed to convert Lean expression" in str(exc_info.value)
    
    def test_complex_expressions(self, converter):
        """Test conversion of complex expressions."""
        # Complex formula with multiple elements
        expr = "∀ n : ℕ, n ≥ 0 → (∃ m : ℕ, m = n + 1)"
        result = converter.convert(expr)
        assert "\\forall" in result
        assert "\\exists" in result
        assert "\\geq" in result
        assert "\\to" in result
        assert "\\mathbb{N}" in result
        
        # Expression with multiple function applications
        expr = "Real.sin x + Real.cos y = Real.sqrt (Real.pow x 2 + Real.pow y 2)"
        result = converter.convert(expr)
        assert "\\sin(x)" in result
        assert "\\cos(y)" in result
        assert "\\sqrt{" in result
        assert "x^{2}" in result
        assert "y^{2}" in result


class TestProofStepAnalyzer:
    """Tests for ProofStepAnalyzer class."""
    
    @pytest.fixture
    def analyzer(self):
        """Create an analyzer instance."""
        return ProofStepAnalyzer()
    
    def test_analyze_transformation(self, analyzer):
        """Test transformation analysis."""
        source = "a + 0"
        target = "a"
        proof_step = "simp"
        
        transformation = analyzer.analyze_transformation(source, target, proof_step)
        
        assert isinstance(transformation, FormulaTransformation)
        assert transformation.source == "a + 0"
        assert transformation.target == "a"
        assert transformation.transformation_type == TransformationType.SIMPLIFICATION
        assert transformation.explanation == "Simplify using simp"
        assert isinstance(transformation.highlighted_parts, list)
        assert isinstance(transformation.intermediate_steps, list)
    
    def test_identify_transformation_type(self, analyzer):
        """Test transformation type identification."""
        # Simplification patterns
        assert analyzer._identify_transformation_type("simp") == TransformationType.SIMPLIFICATION
        assert analyzer._identify_transformation_type("norm_num") == TransformationType.SIMPLIFICATION
        assert analyzer._identify_transformation_type("ring") == TransformationType.SIMPLIFICATION
        assert analyzer._identify_transformation_type("abel") == TransformationType.SIMPLIFICATION
        
        # Rewriting patterns
        assert analyzer._identify_transformation_type("rw [h]") == TransformationType.REWRITE
        assert analyzer._identify_transformation_type("rewrite h") == TransformationType.REWRITE
        
        # Substitution patterns
        assert analyzer._identify_transformation_type("subst h") == TransformationType.SUBSTITUTION
        assert analyzer._identify_transformation_type("apply h") == TransformationType.SUBSTITUTION
        
        # Induction
        assert analyzer._identify_transformation_type("induction n") == TransformationType.INDUCTION_STEP
        
        # Case analysis
        assert analyzer._identify_transformation_type("cases h") == TransformationType.CASE_SPLIT
        assert analyzer._identify_transformation_type("by_cases h") == TransformationType.CASE_SPLIT
        
        # Default
        assert analyzer._identify_transformation_type("unknown") == TransformationType.SIMPLIFICATION
    
    def test_extract_formula_components(self, analyzer):
        """Test formula component extraction."""
        formula = "a + b = c"
        components = analyzer.extract_formula_components(formula)
        
        assert "a" in components
        assert "b" in components
        assert "c" in components
        
        # Test with functions
        formula = "\\sin{x} + \\cos{y}"
        components = analyzer.extract_formula_components(formula)
        
        assert "\\sin{x}" in components or "x" in components
        assert "\\cos{y}" in components or "y" in components
    
    def test_find_changes(self, analyzer):
        """Test finding changes between formulas."""
        source = "a + 0"
        target = "a"
        
        changes = analyzer._find_changes(source, target)
        
        # "0" was removed
        assert any("0" in change for change in changes)
    
    def test_generate_explanation(self, analyzer):
        """Test explanation generation."""
        explanations = {
            TransformationType.SIMPLIFICATION: "simp",
            TransformationType.REWRITE: "rw [h]",
            TransformationType.SUBSTITUTION: "subst",
            TransformationType.INDUCTION_STEP: "induction",
            TransformationType.CASE_SPLIT: "cases",
            TransformationType.EXPANSION: "expand",
            TransformationType.FACTORIZATION: "factor",
            TransformationType.EQUALITY_CHAIN: "calc",
        }
        
        for trans_type, step in explanations.items():
            explanation = analyzer._generate_explanation("a", "b", step, trans_type)
            assert step in explanation
            assert isinstance(explanation, str)
    
    def test_generate_intermediate_steps(self, analyzer):
        """Test intermediate step generation."""
        # Currently returns empty list, but test the interface
        steps = analyzer._generate_intermediate_steps("a + b", "b + a", TransformationType.REWRITE)
        assert isinstance(steps, list)


class TestFormulaExtractor:
    """Tests for FormulaExtractor class."""
    
    @pytest.fixture
    def extractor(self):
        """Create an extractor instance."""
        return FormulaExtractor()
    
    def test_extract_from_proof_step(self, extractor):
        """Test formula extraction from proof steps."""
        # Test with two formulas
        text = "Transform a + b into b + a"
        before, after = extractor.extract_from_proof_step(text)
        assert before is not None
        assert after is not None
        
        # Test with one formula
        text = "Consider the expression x + y"
        before, after = extractor.extract_from_proof_step(text)
        assert before is not None
        assert after is None or before != after
        
        # Test with no formulas
        text = "Apply the theorem"
        before, after = extractor.extract_from_proof_step(text)
        assert before == text  # Falls back to whole text
        assert after is None
    
    def test_convert_lean_to_latex(self, extractor):
        """Test Lean to LaTeX conversion wrapper."""
        result = extractor.convert_lean_to_latex("∀ x, x ∈ ℕ")
        assert "\\forall" in result
        assert "\\mathbb{N}" in result
    
    def test_analyze_proof_transformation(self, extractor):
        """Test proof transformation analysis wrapper."""
        transformation = extractor.analyze_proof_transformation(
            "a + 0", "a", "simp"
        )
        assert isinstance(transformation, FormulaTransformation)
        assert transformation.transformation_type == TransformationType.SIMPLIFICATION
    
    def test_extract_key_formulas_from_theorem(self, extractor):
        """Test extracting key formulas from theorem."""
        theorem = "∀ n : ℕ, n + 0 = n"
        proof = "By induction on n. Base case: 0 + 0 = 0. Inductive step: (n+1) + 0 = n+1."
        
        formulas = extractor.extract_key_formulas_from_theorem(theorem, proof)
        
        assert len(formulas) > 0
        assert any("\\forall" in f for f in formulas)
        
        # Should extract formulas from proof too
        assert any("0 + 0" in f or "0" in f for f in formulas)
    
    def test_extract_formulas(self, extractor):
        """Test LaTeX formula extraction from text."""
        text = "Consider the formula $a + b = c$ and also $$x^2 + y^2 = z^2$$"
        
        formulas = extractor.extract_formulas(text)
        
        assert len(formulas) == 2
        
        # Check inline formula
        inline = [f for f in formulas if not f.display_mode][0]
        assert inline.latex == "a + b = c"
        assert inline.display_mode is False
        
        # Check display formula
        display = [f for f in formulas if f.display_mode][0]
        assert display.latex == "x^2 + y^2 = z^2"
        assert display.display_mode is True
        
        # Check ordering
        assert formulas[0].position < formulas[1].position
    
    def test_extract_lean_notation(self, extractor):
        """Test Lean notation extraction."""
        text = "The tactic `simp` simplifies expressions like `a + 0` to `a`."
        
        lean_code = extractor.extract_lean_notation(text)
        
        assert len(lean_code) == 3
        assert "simp" in lean_code
        assert "a + 0" in lean_code
        assert "a" in lean_code
    
    def test_process_proof_content(self, extractor):
        """Test processing mixed content."""
        content = """
        We prove $a + 0 = a$ using the tactic `simp`.
        This gives us:
        $$a + 0 = a$$
        The code `rfl` finishes the proof.
        """
        
        processed = extractor.process_proof_content(content)
        
        assert isinstance(processed, ProcessedContent)
        assert len(processed.formulas) == 2  # One inline, one display
        assert len(processed.lean_code) == 2  # simp and rfl
        assert "[FORMULA]" in processed.text  # Formulas replaced
        assert processed.text.count("[FORMULA]") == 2
    
    def test_extract_formulas_edge_cases(self, extractor):
        """Test formula extraction edge cases."""
        # Adjacent dollar signs
        text = "Cost is $50 and price is $100"
        formulas = extractor.extract_formulas(text)
        assert len(formulas) == 0  # Should not match currency
        
        # Escaped dollars
        text = r"The formula \$a + b\$ is simple"
        formulas = extractor.extract_formulas(text)
        assert len(formulas) == 0  # Escaped dollars don't count
        
        # Empty formulas
        text = "Empty $$ $$ formula"
        formulas = extractor.extract_formulas(text)
        if formulas:
            assert all(f.latex.strip() != "" for f in formulas)
        
        # Nested dollars
        text = "Formula $$a + $b$ + c$$"
        formulas = extractor.extract_formulas(text)
        # Should handle this gracefully
    
    def test_extract_formulas_complex(self, extractor):
        """Test extraction of complex formulas."""
        text = """
        The quadratic formula is $x = \\frac{-b \\pm \\sqrt{b^2 - 4ac}}{2a}$.
        
        For matrices, we have:
        $$
        \\begin{pmatrix}
        a & b \\\\
        c & d
        \\end{pmatrix}
        $$
        """
        
        formulas = extractor.extract_formulas(text)
        
        assert len(formulas) == 2
        assert "\\frac" in formulas[0].latex
        assert "\\begin{pmatrix}" in formulas[1].latex
    
    def test_process_proof_content_preserves_order(self, extractor):
        """Test that processed content preserves formula order."""
        content = "First $a$, then $b$, finally $c$"
        
        processed = extractor.process_proof_content(content)
        
        assert len(processed.formulas) == 3
        assert processed.formulas[0].latex == "a"
        assert processed.formulas[1].latex == "b" 
        assert processed.formulas[2].latex == "c"
        assert processed.formulas[0].position < processed.formulas[1].position < processed.formulas[2].position


class TestExtractedFormula:
    """Test ExtractedFormula dataclass."""
    
    def test_extracted_formula_creation(self):
        """Test creating ExtractedFormula instances."""
        formula = ExtractedFormula(
            latex="x^2 + y^2 = z^2",
            display_mode=True,
            position=42
        )
        
        assert formula.latex == "x^2 + y^2 = z^2"
        assert formula.display_mode is True
        assert formula.position == 42


class TestProcessedContent:
    """Test ProcessedContent dataclass."""
    
    def test_processed_content_creation(self):
        """Test creating ProcessedContent instances."""
        formulas = [
            ExtractedFormula("a + b", False, 10),
            ExtractedFormula("x^2", True, 20)
        ]
        lean_code = ["simp", "rfl"]
        text = "Some text with [FORMULA] and more [FORMULA]"
        
        content = ProcessedContent(
            formulas=formulas,
            lean_code=lean_code,
            text=text
        )
        
        assert len(content.formulas) == 2
        assert len(content.lean_code) == 2
        assert content.text == text


class TestFormulaTransformation:
    """Test FormulaTransformation dataclass."""
    
    def test_formula_transformation_creation(self):
        """Test creating FormulaTransformation instances."""
        transformation = FormulaTransformation(
            source="a + 0",
            target="a",
            transformation_type=TransformationType.SIMPLIFICATION,
            highlighted_parts=["0", "+"],
            explanation="Remove additive identity",
            intermediate_steps=[]
        )
        
        assert transformation.source == "a + 0"
        assert transformation.target == "a"
        assert transformation.transformation_type == TransformationType.SIMPLIFICATION
        assert "0" in transformation.highlighted_parts
        assert "Remove" in transformation.explanation
        assert len(transformation.intermediate_steps) == 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])