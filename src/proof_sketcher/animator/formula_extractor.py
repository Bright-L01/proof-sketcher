"""Formula extraction and conversion from Lean to LaTeX."""

import re
from dataclasses import dataclass
from typing import List, Optional, Tuple

from ..core.exceptions import FormulaExtractionError
from .models import TransformationType


@dataclass
class FormulaTransformation:
    """Represents a transformation between two formulas."""

    source: str
    target: str
    transformation_type: TransformationType
    highlighted_parts: List[str]
    explanation: str
    intermediate_steps: List[str]


class LeanToLatexConverter:
    """Converts Lean mathematical expressions to LaTeX."""

    def __init__(self):
        """Initialize the converter with symbol mappings."""
        # Unicode to LaTeX mappings
        self.symbol_map = {
            # Quantifiers
            "∀": r"\forall",
            "∃": r"\exists",
            "∄": r"\nexists",
            # Logic operators
            "→": r"\to",
            "↔": r"\leftrightarrow",
            "¬": r"\neg",
            "∧": r"\land",
            "∨": r"\lor",
            "⊤": r"\top",
            "⊥": r"\bot",
            # Set operations
            "∈": r"\in",
            "∉": r"\notin",
            "⊆": r"\subseteq",
            "⊇": r"\supseteq",
            "⊂": r"\subset",
            "⊃": r"\supset",
            "∪": r"\cup",
            "∩": r"\cap",
            "∅": r"\emptyset",
            # Arithmetic
            "≤": r"\leq",
            "≥": r"\geq",
            "≠": r"\neq",
            "≈": r"\approx",
            "≡": r"\equiv",
            "±": r"\pm",
            "∞": r"\infty",
            # Number sets
            "ℕ": r"\mathbb{N}",
            "ℤ": r"\mathbb{Z}",
            "ℚ": r"\mathbb{Q}",
            "ℝ": r"\mathbb{R}",
            "ℂ": r"\mathbb{C}",
            # Greek letters (common ones)
            "α": r"\alpha",
            "β": r"\beta",
            "γ": r"\gamma",
            "δ": r"\delta",
            "ε": r"\epsilon",
            "θ": r"\theta",
            "λ": r"\lambda",
            "μ": r"\mu",
            "π": r"\pi",
            "σ": r"\sigma",
            "τ": r"\tau",
            "φ": r"\phi",
            "ψ": r"\psi",
            "ω": r"\omega",
            "Γ": r"\Gamma",
            "Δ": r"\Delta",
            "Θ": r"\Theta",
            "Λ": r"\Lambda",
            "Π": r"\Pi",
            "Σ": r"\Sigma",
            "Φ": r"\Phi",
            "Ψ": r"\Psi",
            "Ω": r"\Omega",
            # Other mathematical symbols
            "∑": r"\sum",
            "∏": r"\prod",
            "∫": r"\int",
            "∂": r"\partial",
            "∇": r"\nabla",
            "√": r"\sqrt",
        }

        # Function name mappings
        self.function_map = {
            "Nat.add": "+",
            "Nat.mul": r"\cdot",
            "Nat.sub": "-",
            "Nat.div": r"\div",
            "Nat.mod": r"\bmod",
            "Nat.pow": "^",
            "Nat.factorial": "!",
            "Int.add": "+",
            "Int.mul": r"\cdot",
            "Int.sub": "-",
            "Int.div": r"\div",
            "Real.add": "+",
            "Real.mul": r"\cdot",
            "Real.sub": "-",
            "Real.div": r"\div",
            "Real.pow": "^",
            "Real.sqrt": r"\sqrt",
            "Real.sin": r"\sin",
            "Real.cos": r"\cos",
            "Real.tan": r"\tan",
            "Real.log": r"\log",
            "Real.exp": r"\exp",
            "List.length": r"\text{length}",
            "List.append": r"\text{++}",
            "Set.union": r"\cup",
            "Set.inter": r"\cap",
            "Set.diff": r"\setminus",
        }

    def convert(self, lean_expr: str) -> str:
        """Convert a Lean expression to LaTeX.

        Args:
            lean_expr: Lean mathematical expression

        Returns:
            LaTeX representation of the expression
        """
        try:
            # Start with the original expression
            latex = lean_expr.strip()

            # Handle type annotations (this now includes Unicode conversion)
            latex = self._clean_type_annotations(latex)

            # Convert function applications
            latex = self._convert_function_applications(latex)

            # Convert quantifiers
            latex = self._convert_quantifiers(latex)

            # Convert infix operators
            latex = self._convert_infix_operators(latex)

            # Handle parentheses and spacing
            latex = self._improve_formatting(latex)

            return latex

        except Exception as e:
            raise FormulaExtractionError(
                f"Failed to convert Lean expression '{lean_expr}': {e}"
            ) from e

    def _clean_type_annotations(self, expr: str) -> str:
        """Remove or simplify type annotations while preserving mathematical symbols."""
        # Remove simple type annotations like (n : Nat) BEFORE Unicode conversion
        expr = re.sub(r"\(([a-zA-Z_][a-zA-Z0-9_]*)\s*:\s*[^)]+\)", r"\1", expr)

        # Remove standalone type declarations like "x : Real" or "f : Nat → Nat"
        # But preserve mathematical symbols that appear in types
        def remove_type_annotation(match):
            var = match.group(1)
            type_part = match.group(2)
            # Keep mathematical symbols from the type, but exclude arrows in type declarations
            math_symbols = re.findall(r"[ℕℤℚℝℂ∀∃¬∧∨⊤⊥∈∉⊆⊇⊂⊃∪∩∅≤≥≠≈≡±∞]", type_part)
            if math_symbols:
                return var + " " + "".join(math_symbols)
            else:
                return var

        expr = re.sub(
            r"([a-zA-Z_][a-zA-Z0-9_]*)\s*:\s*([^,]+?)(?=\s*,|\s*$)",
            remove_type_annotation,
            expr,
        )

        # Now convert Unicode symbols
        expr = self._convert_unicode_symbols(expr)

        # Clean up extra spaces
        expr = re.sub(r"\s+", " ", expr).strip()

        return expr

    def _convert_function_applications(self, expr: str) -> str:
        """Convert function applications to mathematical notation."""
        # Convert known functions
        for lean_func, latex_func in self.function_map.items():
            if lean_func in expr:
                if latex_func in [
                    "+",
                    "-",
                    r"\cdot",
                    r"\div",
                    r"\cup",
                    r"\cap",
                    r"\setminus",
                ]:
                    # Infix operators
                    pattern = rf"{re.escape(lean_func)}\s+([^\s]+)\s+([^\s]+)"

                    # Use lambda to avoid escape issues
                    def make_replacement(latex_func):
                        return lambda m: f"{m.group(1)} {latex_func} {m.group(2)}"

                    expr = re.sub(pattern, make_replacement(latex_func), expr)
                elif latex_func == "^":
                    # Exponentiation - be careful about parentheses in the exponent
                    pattern = rf"{re.escape(lean_func)}\s+([^\s]+)\s+([^\s)]+)"
                    expr = re.sub(pattern, r"\1^{\2}", expr)
                elif latex_func == "!":
                    # Factorial (postfix)
                    pattern = rf"{re.escape(lean_func)}\s+([^\s]+)"
                    expr = re.sub(pattern, r"\1!", expr)
                elif latex_func.startswith(r"\sqrt"):
                    # Square root - handle parenthesized expressions properly
                    pattern = rf"{re.escape(lean_func)}\s+(\([^)]*\)|[^\s]+)"
                    expr = re.sub(pattern, lambda m: f"\\sqrt{{{m.group(1)}}}", expr)
                else:
                    # Function notation - use lambda to avoid escape issues
                    pattern = rf"{re.escape(lean_func)}\s+([^\s]+)"

                    def make_func_replacement(latex_func):
                        return lambda m: f"{latex_func}({m.group(1)})"

                    expr = re.sub(pattern, make_func_replacement(latex_func), expr)

        return expr

    def _convert_quantifiers(self, expr: str) -> str:
        """Convert quantifier expressions."""

        # Universal quantifier: ∀ x : T, P(x)
        def convert_universal(match):
            var = match.group(1)
            rest = match.group(2)
            # Add parentheses to function applications like P x -> P(x)
            rest = re.sub(
                r"\b([A-Z][a-zA-Z0-9_]*)\s+([a-z][a-zA-Z0-9_]*)\b", r"\1(\2)", rest
            )
            return f"\\forall {var}, {rest}"

        expr = re.sub(
            r"(?:∀|\\forall)\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*(?::\s*[^,]+)?,\s*(.+)",
            convert_universal,
            expr,
        )

        # Existential quantifier: ∃ x : T, P(x)
        def convert_existential(match):
            var = match.group(1)
            rest = match.group(2)
            # Add parentheses to function applications like P x -> P(x)
            rest = re.sub(
                r"\b([A-Z][a-zA-Z0-9_]*)\s+([a-z][a-zA-Z0-9_]*)\b", r"\1(\2)", rest
            )
            return f"\\exists {var}, {rest}"

        expr = re.sub(
            r"(?:∃|\\exists)\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*(?::\s*[^,]+)?,\s*(.+)",
            convert_existential,
            expr,
        )

        # Lambda expressions: λ x, expr or \lambda x, expr
        def convert_lambda(match):
            var = match.group(1)
            body = match.group(2)
            # Add parentheses to function applications like f x -> f(x)
            body = re.sub(
                r"(?<!\\)\b([a-z][a-zA-Z0-9_]*)\s+([a-z][a-zA-Z0-9_]*)\b",
                r"\1(\2)",
                body,
            )
            return f"\\lambda {var}. {body}"

        expr = re.sub(
            r"(?:λ|\\lambda)\s*([a-zA-Z_][a-zA-Z0-9_]*),\s*(.+)",
            convert_lambda,
            expr,
        )

        # Handle standalone function applications outside quantifiers
        # But avoid LaTeX commands (starting with \) and single letters
        expr = re.sub(
            r"(?<!\\)\b([A-Z][a-z][a-zA-Z0-9_]*)\s+([a-z][a-zA-Z0-9_]*)\b",
            r"\1(\2)",
            expr,
        )

        return expr

    def _convert_infix_operators(self, expr: str) -> str:
        """Convert infix operators."""
        # Handle equality chains
        expr = re.sub(r"(\w+)\s*=\s*(\w+)\s*=\s*(\w+)", r"\1 = \2 = \3", expr)

        # Handle implications
        expr = re.sub(r"(\w+)\s*→\s*(\w+)", r"\1 \\to \2", expr)

        # Handle biconditionals
        expr = re.sub(r"(\w+)\s*↔\s*(\w+)", r"\1 \\leftrightarrow \2", expr)

        return expr

    def _convert_unicode_symbols(self, expr: str) -> str:
        """Convert Unicode symbols to LaTeX."""
        for unicode_char, latex_cmd in self.symbol_map.items():
            expr = expr.replace(unicode_char, latex_cmd)

        return expr

    def _improve_formatting(self, expr: str) -> str:
        """Improve LaTeX formatting."""
        # Add proper spacing around operators (but not LaTeX commands)
        expr = re.sub(r"(?<!\\)(\w)(\+|\-|\*|/)(\w)", r"\1 \2 \3", expr)

        # Add space after LaTeX commands when followed by variables (but only if no space exists)
        expr = re.sub(r"(\\(?:neg|land|lor|in))(?=[a-zA-Z])", r"\1 ", expr)

        # Handle subscripts (convert _ to LaTeX subscript)
        expr = re.sub(r"(\w+)_(\w+)", r"\1_{\2}", expr)

        # Handle function calls with proper parentheses (clean up extra spaces)
        expr = re.sub(r"(\w+)\s*\(\s*([^)]+?)\s*\)", r"\1(\2)", expr)

        return expr


class ProofStepAnalyzer:
    """Analyzes proof steps to identify transformations."""

    def __init__(self):
        """Initialize the analyzer."""
        self.converter = LeanToLatexConverter()
        self.transformation_patterns = {
            # Simplification patterns
            r"simp": TransformationType.SIMPLIFICATION,
            r"norm_num": TransformationType.SIMPLIFICATION,
            r"ring": TransformationType.SIMPLIFICATION,
            r"abel": TransformationType.SIMPLIFICATION,
            # Rewriting patterns
            r"rw\s*\[": TransformationType.REWRITE,
            r"rewrite": TransformationType.REWRITE,
            # Substitution patterns
            r"subst": TransformationType.SUBSTITUTION,
            r"apply": TransformationType.SUBSTITUTION,
            # Induction patterns
            r"induction": TransformationType.INDUCTION_STEP,
            # Case analysis
            r"cases": TransformationType.CASE_SPLIT,
            r"by_cases": TransformationType.CASE_SPLIT,
        }

    def analyze_transformation(
        self, source_formula: str, target_formula: str, proof_step: str
    ) -> FormulaTransformation:
        """Analyze the transformation between two formulas.

        Args:
            source_formula: Starting formula
            target_formula: Ending formula
            proof_step: Proof step/tactic that caused the transformation

        Returns:
            FormulaTransformation describing the change
        """
        # Convert formulas to LaTeX
        source_latex = self.converter.convert(source_formula)
        target_latex = self.converter.convert(target_formula)

        # Identify transformation type
        transformation_type = self._identify_transformation_type(proof_step)

        # Find highlighted parts (what changed)
        highlighted_parts = self._find_changes(source_formula, target_formula)

        # Generate explanation
        explanation = self._generate_explanation(
            source_formula, target_formula, proof_step, transformation_type
        )

        # Generate intermediate steps if needed
        intermediate_steps = self._generate_intermediate_steps(
            source_latex, target_latex, transformation_type
        )

        return FormulaTransformation(
            source=source_latex,
            target=target_latex,
            transformation_type=transformation_type,
            highlighted_parts=highlighted_parts,
            explanation=explanation,
            intermediate_steps=intermediate_steps,
        )

    def extract_formula_components(self, formula: str) -> List[str]:
        """Extract meaningful components from a formula for highlighting.

        Args:
            formula: Mathematical formula

        Returns:
            List of formula components
        """
        # Convert to LaTeX first
        latex_formula = self.converter.convert(formula)

        components = []

        # Extract terms separated by operators
        terms = re.split(r"[+\-=<>≤≥≠]", latex_formula)
        components.extend([term.strip() for term in terms if term.strip()])

        # Extract function calls
        function_calls = re.findall(r"\\[a-z]+\{[^}]+\}", latex_formula)
        components.extend(function_calls)

        # Extract variables
        variables = re.findall(r"\b[a-zA-Z]\b", latex_formula)
        components.extend(variables)

        return list(set(components))  # Remove duplicates

    def _identify_transformation_type(self, proof_step: str) -> TransformationType:
        """Identify the type of transformation from proof step."""
        for pattern, trans_type in self.transformation_patterns.items():
            if re.search(pattern, proof_step, re.IGNORECASE):
                return trans_type

        # Default to simplification if no specific pattern found
        return TransformationType.SIMPLIFICATION

    def _find_changes(self, source: str, target: str) -> List[str]:
        """Find what changed between source and target formulas."""
        source_components = set(self.extract_formula_components(source))
        target_components = set(self.extract_formula_components(target))

        # Components that changed (removed or added)
        changed_components = source_components.symmetric_difference(target_components)

        return list(changed_components)

    def _generate_explanation(
        self, source: str, target: str, proof_step: str, trans_type: TransformationType
    ) -> str:
        """Generate human-readable explanation of the transformation."""
        explanations = {
            TransformationType.SIMPLIFICATION: f"Simplify using {proof_step}",
            TransformationType.REWRITE: f"Rewrite using the rule in {proof_step}",
            TransformationType.SUBSTITUTION: f"Substitute using {proof_step}",
            TransformationType.INDUCTION_STEP: f"Apply induction step: {proof_step}",
            TransformationType.CASE_SPLIT: f"Split into cases: {proof_step}",
            TransformationType.EXPANSION: f"Expand the expression: {proof_step}",
            TransformationType.FACTORIZATION: f"Factor the expression: {proof_step}",
            TransformationType.EQUALITY_CHAIN: f"Chain equalities: {proof_step}",
        }

        return explanations.get(trans_type, f"Transform using {proof_step}")

    def _generate_intermediate_steps(
        self, source: str, target: str, trans_type: TransformationType
    ) -> List[str]:
        """Generate intermediate steps for smooth animation."""
        # For now, return empty list - could be enhanced to show step-by-step
        intermediates = []

        # For complex transformations, we might want to generate intermediate states
        if trans_type in [TransformationType.REWRITE, TransformationType.SUBSTITUTION]:
            # Could analyze the difference and create intermediate steps
            pass

        return intermediates


@dataclass
class ExtractedFormula:
    """Represents an extracted mathematical formula."""

    latex: str
    display_mode: bool
    position: int


@dataclass
class ProcessedContent:
    """Represents processed mathematical content."""

    formulas: List[ExtractedFormula]
    lean_code: List[str]
    text: str


class FormulaExtractor:
    """High-level interface for formula extraction and conversion."""

    def __init__(self):
        """Initialize the extractor."""
        self.converter = LeanToLatexConverter()
        self.analyzer = ProofStepAnalyzer()

    def extract_from_proof_step(
        self, proof_step_text: str
    ) -> Tuple[str, Optional[str]]:
        """Extract before/after formulas from a proof step description.

        Args:
            proof_step_text: Natural language description of proof step

        Returns:
            Tuple of (before_formula, after_formula). after_formula may be None.
        """
        # This would need to be enhanced with NLP to extract formulas from text
        # For now, return basic parsing

        # Look for mathematical expressions in the text - more targeted approach
        # First try to find expressions with operators
        math_expressions = re.findall(
            r"\b[A-Za-z0-9_]+(?:\s*[+\-*/=<>≤≥≠]\s*[A-Za-z0-9_]+)+\b", proof_step_text
        )

        # If none found, look for simpler patterns
        if not math_expressions:
            math_expressions = re.findall(
                r"\b[A-Za-z0-9_]+\s*[+\-*/=<>≤≥≠∀∃→↔¬∧∨]\s*[A-Za-z0-9_]+\b",
                proof_step_text,
            )

        # If still none, look for variable-like patterns
        if not math_expressions:
            # Look for single variables or simple expressions
            math_expressions = re.findall(
                r"\b[a-zA-Z]\s*[+\-*/=]\s*[a-zA-Z]\b", proof_step_text
            )

        # Clean up and filter
        math_expressions = [expr.strip() for expr in math_expressions if expr.strip()]

        if len(math_expressions) >= 2:
            return math_expressions[0], math_expressions[1]
        elif len(math_expressions) == 1:
            return math_expressions[0], None
        else:
            return proof_step_text, None

    def convert_lean_to_latex(self, lean_expr: str) -> str:
        """Convert Lean expression to LaTeX."""
        return self.converter.convert(lean_expr)

    def analyze_proof_transformation(
        self, source_formula: str, target_formula: str, proof_step: str
    ) -> FormulaTransformation:
        """Analyze transformation between formulas."""
        return self.analyzer.analyze_transformation(
            source_formula, target_formula, proof_step
        )

    def extract_key_formulas_from_theorem(
        self, theorem_statement: str, proof_text: str
    ) -> List[str]:
        """Extract key formulas from theorem statement and proof.

        Args:
            theorem_statement: The theorem statement
            proof_text: The proof text

        Returns:
            List of key formulas in LaTeX format
        """
        formulas = []

        # Extract main theorem statement
        main_formula = self.converter.convert(theorem_statement)
        formulas.append(main_formula)

        # Extract formulas from proof steps
        # Look for expressions that look like mathematical formulas
        proof_formulas = re.findall(
            r"[A-Za-z0-9_]+(?:\s*[+\-*/=<>≤≥≠]\s*[A-Za-z0-9_]+)+", proof_text
        )

        for formula in proof_formulas:
            latex_formula = self.converter.convert(formula.strip())
            if latex_formula not in formulas:
                formulas.append(latex_formula)

        return formulas

    def extract_formulas(self, text: str) -> List[ExtractedFormula]:
        """Extract LaTeX formulas from text.

        Args:
            text: Text containing LaTeX formulas

        Returns:
            List of extracted formulas
        """
        formulas = []

        # Extract display math ($$...$$) - handle multiline
        display_pattern = r"\$\$(.*?)\$\$"
        for match in re.finditer(display_pattern, text, re.DOTALL):
            content = match.group(1).strip()
            if content:  # Don't include empty formulas
                formulas.append(
                    ExtractedFormula(
                        latex=content,
                        display_mode=True,
                        position=match.start(),
                    )
                )

        # Extract inline math ($...$) - avoid matching currency and escaped dollars
        # Don't match escaped dollars (\$) or currency patterns ($50)
        inline_pattern = r"(?<!\\)\$(?!\$|\d+\.?\d*)([^$\n]+?)(?<!\d)\$(?!\$)"
        for match in re.finditer(inline_pattern, text):
            content = match.group(1).strip()
            # Additional filter: must contain mathematical content or be a single variable
            if content and (
                any(c in content for c in r"\{}^_=+-<>≤≥≠∀∃→↔¬∧∨")
                or re.search(r"[a-zA-Z]\s*[+\-*/=]\s*[a-zA-Z]", content)
                or (len(content.split()) == 1 and content.isalpha())
            ):
                formulas.append(
                    ExtractedFormula(
                        latex=content,
                        display_mode=False,
                        position=match.start(),
                    )
                )

        return sorted(formulas, key=lambda f: f.position)

    def extract_lean_notation(self, text: str) -> List[str]:
        """Extract Lean notation from text (backtick delimited).

        Args:
            text: Text containing Lean notation

        Returns:
            List of Lean expressions
        """
        pattern = r"`([^`]+)`"
        return re.findall(pattern, text)

    def process_proof_content(self, content: str) -> ProcessedContent:
        """Process mixed mathematical content.

        Args:
            content: Mixed content with LaTeX and Lean notation

        Returns:
            Processed content with extracted formulas and code
        """
        # Extract LaTeX formulas
        formulas = self.extract_formulas(content)

        # Extract Lean code
        lean_code = self.extract_lean_notation(content)

        # Clean text by removing formulas
        clean_text = content
        for formula in formulas:
            if formula.display_mode:
                clean_text = re.sub(r"\$\$.*?\$\$", "[FORMULA]", clean_text, count=1)
            else:
                clean_text = re.sub(r"\$.*?\$", "[FORMULA]", clean_text, count=1)

        return ProcessedContent(formulas=formulas, lean_code=lean_code, text=clean_text)
