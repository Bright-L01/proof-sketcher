"""Mathlib4 notation handler for converting Lean notation to LaTeX and HTML.

This module handles the complex notation system used in Mathlib4, including:
- Unicode mathematical symbols
- Type class notation
- Category theory symbols
- Analysis and topology notation
- Set theory and logic symbols
"""

import logging
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple


@dataclass
class NotationMapping:
    """A notation mapping with context information."""

    lean_symbol: str
    latex_symbol: str
    html_entity: str
    description: str
    category: str


class MathlibNotationHandler:
    """Handle mathlib-specific notation and convert to appropriate formats."""

    def __init__(self):
        """Initialize the notation handler with comprehensive mappings."""
        self.logger = logging.getLogger(__name__)
        self._build_notation_mappings()
        self._compile_patterns()

    def _build_notation_mappings(self) -> None:
        """Build comprehensive notation mappings organized by category."""

        # Core mathematical symbols
        self.core_symbols = [
            NotationMapping("∈", r"\in", "&isin;", "element of", "set_theory"),
            NotationMapping("∉", r"\notin", "&notin;", "not element of", "set_theory"),
            NotationMapping(
                "⊆", r"\subseteq", "&sube;", "subset or equal", "set_theory"
            ),
            NotationMapping("⊂", r"\subset", "&sub;", "proper subset", "set_theory"),
            NotationMapping(
                "⊇", r"\supseteq", "&supe;", "superset or equal", "set_theory"
            ),
            NotationMapping("⊃", r"\supset", "&sup;", "proper superset", "set_theory"),
            NotationMapping("∪", r"\cup", "&cup;", "union", "set_theory"),
            NotationMapping("∩", r"\cap", "&cap;", "intersection", "set_theory"),
            NotationMapping("∅", r"\emptyset", "&empty;", "empty set", "set_theory"),
        ]

        # Logic symbols
        self.logic_symbols = [
            NotationMapping("→", r"\to", "&rarr;", "implies", "logic"),
            NotationMapping("↔", r"\iff", "&harr;", "if and only if", "logic"),
            NotationMapping("∀", r"\forall", "&forall;", "for all", "logic"),
            NotationMapping("∃", r"\exists", "&exist;", "there exists", "logic"),
            NotationMapping("¬", r"\neg", "&not;", "not", "logic"),
            NotationMapping("∧", r"\land", "&and;", "and", "logic"),
            NotationMapping("∨", r"\lor", "&or;", "or", "logic"),
            NotationMapping("⊤", r"\top", "&top;", "top/true", "logic"),
            NotationMapping("⊥", r"\bot", "&bot;", "bottom/false", "logic"),
        ]

        # Algebra and arithmetic
        self.algebra_symbols = [
            NotationMapping("×", r"\times", "&times;", "cartesian product", "algebra"),
            NotationMapping("·", r"\cdot", "&middot;", "multiplication", "algebra"),
            NotationMapping("∘", r"\circ", "&cir;", "composition", "algebra"),
            NotationMapping("⊕", r"\oplus", "&oplus;", "direct sum", "algebra"),
            NotationMapping("⊗", r"\otimes", "&otimes;", "tensor product", "algebra"),
            NotationMapping("⊔", r"\sqcup", "&#8852;", "join/supremum", "algebra"),
            NotationMapping("⊓", r"\sqcap", "&#8851;", "meet/infimum", "algebra"),
        ]

        # Order relations
        self.order_symbols = [
            NotationMapping("≤", r"\le", "&le;", "less than or equal", "order"),
            NotationMapping("≥", r"\ge", "&ge;", "greater than or equal", "order"),
            NotationMapping("≠", r"\ne", "&ne;", "not equal", "order"),
            NotationMapping("≈", r"\approx", "&asymp;", "approximately equal", "order"),
            NotationMapping("≡", r"\equiv", "&equiv;", "equivalent", "order"),
            NotationMapping("∼", r"\sim", "&sim;", "similar", "order"),
            NotationMapping("≃", r"\simeq", "&#8771;", "asymptotically equal", "order"),
            NotationMapping("≅", r"\cong", "&cong;", "congruent", "order"),
        ]

        # Brackets and delimiters
        self.delimiter_symbols = [
            NotationMapping(
                "⟨", r"\langle", "&lang;", "left angle bracket", "delimiters"
            ),
            NotationMapping(
                "⟩", r"\rangle", "&rang;", "right angle bracket", "delimiters"
            ),
            NotationMapping(
                "⟦", r"\llbracket", "&#10214;", "left semantic bracket", "delimiters"
            ),
            NotationMapping(
                "⟧", r"\rrbracket", "&#10215;", "right semantic bracket", "delimiters"
            ),
            NotationMapping("⌊", r"\lfloor", "&lfloor;", "left floor", "delimiters"),
            NotationMapping("⌋", r"\rfloor", "&rfloor;", "right floor", "delimiters"),
            NotationMapping("⌈", r"\lceil", "&lceil;", "left ceiling", "delimiters"),
            NotationMapping("⌉", r"\rceil", "&rceil;", "right ceiling", "delimiters"),
        ]

        # Number systems
        self.number_systems = [
            NotationMapping(
                "ℕ", r"\mathbb{N}", "&#8469;", "natural numbers", "numbers"
            ),
            NotationMapping("ℤ", r"\mathbb{Z}", "&#8484;", "integers", "numbers"),
            NotationMapping("ℚ", r"\mathbb{Q}", "&#8474;", "rationals", "numbers"),
            NotationMapping("ℝ", r"\mathbb{R}", "&#8477;", "real numbers", "numbers"),
            NotationMapping(
                "ℂ", r"\mathbb{C}", "&#8450;", "complex numbers", "numbers"
            ),
            NotationMapping("𝔽", r"\mathbb{F}", "&#120125;", "field", "numbers"),
            NotationMapping("𝔾", r"\mathbb{G}", "&#120126;", "group", "numbers"),
        ]

        # Analysis symbols
        self.analysis_symbols = [
            NotationMapping("∑", r"\sum", "&sum;", "summation", "analysis"),
            NotationMapping("∏", r"\prod", "&prod;", "product", "analysis"),
            NotationMapping("∫", r"\int", "&int;", "integral", "analysis"),
            NotationMapping(
                "∂", r"\partial", "&part;", "partial derivative", "analysis"
            ),
            NotationMapping("∇", r"\nabla", "&nabla;", "gradient", "analysis"),
            NotationMapping(
                "△", r"\triangle", "&#9651;", "triangle/Laplacian", "analysis"
            ),
            NotationMapping("∆", r"\Delta", "&Delta;", "change/Laplacian", "analysis"),
            NotationMapping("∞", r"\infty", "&infin;", "infinity", "analysis"),
            NotationMapping("⨆", r"\bigsqcup", "&#10758;", "supremum", "analysis"),
            NotationMapping("⨅", r"\bigsqcap", "&#10757;", "infimum", "analysis"),
        ]

        # Category theory symbols
        self.category_symbols = [
            NotationMapping(
                "⟶", r"\longrightarrow", "&#10230;", "morphism", "category"
            ),
            NotationMapping(
                "⇒", r"\Rightarrow", "&rArr;", "natural transformation", "category"
            ),
            NotationMapping(
                "⇔", r"\Leftrightarrow", "&hArr;", "equivalence", "category"
            ),
            NotationMapping("≈", r"\approx", "&asymp;", "isomorphism", "category"),
            NotationMapping("⊣", r"\dashv", "&#8867;", "adjunction", "category"),
            NotationMapping("◦", r"\circ", "&#9702;", "composition", "category"),
        ]

        # Combine all mappings
        self.all_mappings = (
            self.core_symbols
            + self.logic_symbols
            + self.algebra_symbols
            + self.order_symbols
            + self.delimiter_symbols
            + self.number_systems
            + self.analysis_symbols
            + self.category_symbols
        )

        # Create lookup dictionaries
        self.lean_to_latex = {m.lean_symbol: m.latex_symbol for m in self.all_mappings}
        self.lean_to_html = {m.lean_symbol: m.html_entity for m in self.all_mappings}
        self.symbol_descriptions = {
            m.lean_symbol: m.description for m in self.all_mappings
        }

    def _compile_patterns(self) -> None:
        """Compile regex patterns for efficient notation processing."""
        # Sort symbols by length (longest first) to avoid partial matches
        sorted_symbols = sorted(self.lean_to_latex.keys(), key=len, reverse=True)

        # Create pattern for all symbols
        escaped_symbols = [re.escape(symbol) for symbol in sorted_symbols]
        self.symbol_pattern = re.compile("|".join(escaped_symbols))

        # Pattern for function types (α → β → γ)
        self.function_type_pattern = re.compile(r"([α-ωΑ-Ω])\s*→\s*([α-ωΑ-Ω])")

        # Pattern for type class constraints [TypeClass Instance]
        self.typeclass_pattern = re.compile(
            r"\[([A-Z][A-Za-z0-9]*)\s+([a-zA-Z][a-zA-Z0-9]*)\]"
        )

        # Pattern for dependent types (x : α) → β
        self.dependent_type_pattern = re.compile(
            r"\(([a-zA-Z][a-zA-Z0-9]*)\s*:\s*([α-ωΑ-Ω][a-zA-Z0-9]*)\)\s*→"
        )

        # Pattern for namespace qualification
        self.namespace_pattern = re.compile(
            r"([A-Z][a-zA-Z0-9]*\.)+([a-zA-Z][a-zA-Z0-9_]*)"
        )

    def convert_to_latex(self, lean_notation: str) -> str:
        """Convert Lean notation to LaTeX with proper handling of complex structures.

        Args:
            lean_notation: Lean mathematical notation string

        Returns:
            LaTeX-formatted string
        """
        if not lean_notation:
            return ""

        result = lean_notation

        # Handle type class constraints first (before symbol replacement)
        result = self._handle_type_classes_latex(result)

        # Handle dependent types
        result = self._handle_dependent_types_latex(result)

        # Replace mathematical symbols
        result = self.symbol_pattern.sub(
            lambda m: self.lean_to_latex.get(m.group(0), m.group(0)), result
        )

        # Handle function types
        result = self._handle_function_types_latex(result)

        # Handle Greek letters
        result = self._handle_greek_letters_latex(result)

        # Handle namespace qualification
        result = self._handle_namespaces_latex(result)

        # Clean up spacing
        result = self._clean_latex_spacing(result)

        return result

    def convert_to_html(self, lean_notation: str) -> str:
        """Convert Lean notation to HTML with proper entities.

        Args:
            lean_notation: Lean mathematical notation string

        Returns:
            HTML-formatted string with proper entities
        """
        if not lean_notation:
            return ""

        result = lean_notation

        # Replace mathematical symbols with HTML entities
        result = self.symbol_pattern.sub(
            lambda m: self.lean_to_html.get(m.group(0), m.group(0)), result
        )

        # Handle type classes for HTML
        result = self._handle_type_classes_html(result)

        # Handle Greek letters for HTML
        result = self._handle_greek_letters_html(result)

        # Escape remaining special characters
        result = result.replace("<", "&lt;").replace(">", "&gt;")

        return result

    def _handle_type_classes_latex(self, text: str) -> str:
        """Handle type class constraints for LaTeX."""

        def replace_typeclass(match):
            typeclass = match.group(1)
            instance = match.group(2)
            return rf"\text{{[{typeclass} {instance}]}}"

        return self.typeclass_pattern.sub(replace_typeclass, text)

    def _handle_type_classes_html(self, text: str) -> str:
        """Handle type class constraints for HTML."""

        def replace_typeclass(match):
            typeclass = match.group(1)
            instance = match.group(2)
            return f'<span class="typeclass">[{typeclass} {instance}]</span>'

        return self.typeclass_pattern.sub(replace_typeclass, text)

    def _handle_dependent_types_latex(self, text: str) -> str:
        """Handle dependent type notation."""

        def replace_dependent(match):
            var = match.group(1)
            type_name = match.group(2)
            return rf"({var} : {type_name}) \to "

        return self.dependent_type_pattern.sub(replace_dependent, text)

    def _handle_function_types_latex(self, text: str) -> str:
        """Handle function type arrows."""
        # Replace → with proper LaTeX arrow in function contexts
        return text.replace("→", r" \to ")

    def _handle_greek_letters_latex(self, text: str) -> str:
        """Convert Greek letters to LaTeX commands."""
        greek_map = {
            "α": r"\alpha",
            "β": r"\beta",
            "γ": r"\gamma",
            "δ": r"\delta",
            "ε": r"\varepsilon",
            "ζ": r"\zeta",
            "η": r"\eta",
            "θ": r"\theta",
            "ι": r"\iota",
            "κ": r"\kappa",
            "λ": r"\lambda",
            "μ": r"\mu",
            "ν": r"\nu",
            "ξ": r"\xi",
            "ο": r"o",
            "π": r"\pi",
            "ρ": r"\rho",
            "σ": r"\sigma",
            "τ": r"\tau",
            "υ": r"\upsilon",
            "φ": r"\varphi",
            "χ": r"\chi",
            "ψ": r"\psi",
            "ω": r"\omega",
            "Α": r"A",
            "Β": r"B",
            "Γ": r"\Gamma",
            "Δ": r"\Delta",
            "Ε": r"E",
            "Ζ": r"Z",
            "Η": r"H",
            "Θ": r"\Theta",
            "Ι": r"I",
            "Κ": r"K",
            "Λ": r"\Lambda",
            "Μ": r"M",
            "Ν": r"N",
            "Ξ": r"\Xi",
            "Ο": r"O",
            "Π": r"\Pi",
            "Ρ": r"P",
            "Σ": r"\Sigma",
            "Τ": r"T",
            "Υ": r"\Upsilon",
            "Φ": r"\Phi",
            "Χ": r"X",
            "Ψ": r"\Psi",
            "Ω": r"\Omega",
        }

        result = text
        for greek, latex in greek_map.items():
            result = result.replace(greek, latex)

        return result

    def _handle_greek_letters_html(self, text: str) -> str:
        """Convert Greek letters to HTML entities."""
        greek_html_map = {
            "α": "&alpha;",
            "β": "&beta;",
            "γ": "&gamma;",
            "δ": "&delta;",
            "ε": "&epsilon;",
            "ζ": "&zeta;",
            "η": "&eta;",
            "θ": "&theta;",
            "ι": "&iota;",
            "κ": "&kappa;",
            "λ": "&lambda;",
            "μ": "&mu;",
            "ν": "&nu;",
            "ξ": "&xi;",
            "π": "&pi;",
            "ρ": "&rho;",
            "σ": "&sigma;",
            "τ": "&tau;",
            "υ": "&upsilon;",
            "φ": "&phi;",
            "χ": "&chi;",
            "ψ": "&psi;",
            "ω": "&omega;",
            "Γ": "&Gamma;",
            "Δ": "&Delta;",
            "Θ": "&Theta;",
            "Λ": "&Lambda;",
            "Ξ": "&Xi;",
            "Π": "&Pi;",
            "Σ": "&Sigma;",
            "Υ": "&Upsilon;",
            "Φ": "&Phi;",
            "Ψ": "&Psi;",
            "Ω": "&Omega;",
        }

        result = text
        for greek, html in greek_html_map.items():
            result = result.replace(greek, html)

        return result

    def _handle_namespaces_latex(self, text: str) -> str:
        """Handle namespace qualification."""

        def replace_namespace(match):
            full_match = match.group(0)
            # Use text mode for namespace qualification
            return rf"\text{{{full_match}}}"

        return self.namespace_pattern.sub(replace_namespace, text)

    def _clean_latex_spacing(self, text: str) -> str:
        """Clean up LaTeX spacing issues."""
        # Remove extra spaces around commands
        text = re.sub(r"\s+", " ", text)
        text = re.sub(r"\s*\\\s*", r"\\", text)

        # Fix spacing around operators (but not commands followed by braces)
        # Only add spaces around operators like \to, \in, etc., not \mathbb{...}
        text = re.sub(
            r"\s*(\\(?:to|in|notin|subseteq|subset|supseteq|supset|cup|cap|emptyset|iff|forall|exists|neg|land|lor|top|bot|times|cdot|circ|oplus|otimes|sqcup|sqcap|le|ge|ne|approx|equiv|sim|simeq|cong|sum|prod|int|partial|nabla|triangle|Delta|infty|bigsqcup|bigsqcap|longrightarrow|Rightarrow|Leftrightarrow|dashv))\s*",
            r" \1 ",
            text,
        )

        # Remove spaces between commands and their arguments (e.g., \mathbb {N} -> \mathbb{N})
        text = re.sub(r"(\\[a-zA-Z]+)\s+\{", r"\1{", text)

        return text.strip()

    def get_notation_table(self, text: str) -> List[Dict[str, str]]:
        """Generate a notation table for symbols used in the text.

        Args:
            text: Text to analyze for symbols

        Returns:
            List of notation entries with symbol, LaTeX, and description
        """
        used_symbols = []

        for symbol in self.lean_to_latex.keys():
            if symbol in text:
                used_symbols.append(
                    {
                        "symbol": symbol,
                        "latex": self.lean_to_latex[symbol],
                        "html": self.lean_to_html[symbol],
                        "description": self.symbol_descriptions[symbol],
                    }
                )

        # Sort by symbol for consistent output
        return sorted(used_symbols, key=lambda x: x["symbol"])

    def detect_mathematical_areas(self, text: str) -> List[str]:
        """Detect mathematical areas based on notation used.

        Args:
            text: Text to analyze

        Returns:
            List of mathematical areas detected
        """
        areas = set()

        for mapping in self.all_mappings:
            if mapping.lean_symbol in text:
                areas.add(mapping.category)

        # Map categories to mathematical areas
        area_map = {
            "set_theory": "Set Theory",
            "logic": "Mathematical Logic",
            "algebra": "Abstract Algebra",
            "order": "Order Theory",
            "numbers": "Number Theory",
            "analysis": "Mathematical Analysis",
            "category": "Category Theory",
        }

        return [area_map.get(area, area.title()) for area in areas]

    def validate_notation(self, text: str) -> Tuple[bool, List[str]]:
        """Validate that all notation in text is supported.

        Args:
            text: Text to validate

        Returns:
            Tuple of (is_valid, list_of_unsupported_symbols)
        """
        # Find all Unicode symbols that might be mathematical notation
        unicode_symbols = re.findall(r"[^\x00-\x7F]", text)

        unsupported = []
        for symbol in set(unicode_symbols):
            if symbol not in self.lean_to_latex:
                unsupported.append(symbol)

        return len(unsupported) == 0, unsupported
