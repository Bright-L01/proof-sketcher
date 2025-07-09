"""Mathlib-specific exporter with enhanced mathematical notation support.

This exporter extends the base HTML exporter with features specifically designed
for Mathlib4 content, including:
- Advanced notation handling
- Links to Mathlib documentation
- Mathematical area detection
- Enhanced theorem cross-referencing
"""

import logging
import re
from pathlib import Path
from typing import Any, Dict, List, Optional
from urllib.parse import quote

from ..generator.models import ProofSketch
from ..parser.mathlib_notation import MathlibNotationHandler
from .html import HTMLExporter
from .models import ExportContext, ExportFormat, ExportOptions, TemplateType


class MathlibExporter(HTMLExporter):
    """Enhanced HTML exporter for Mathlib4 theorems with mathematical notation support."""

    def __init__(
        self,
        options: Optional[ExportOptions] = None,
        mathlib_base_url: str = "https://leanprover-community.github.io/mathlib4_docs/",
    ):
        """Initialize Mathlib exporter.

        Args:
            options: Export options
            mathlib_base_url: Base URL for Mathlib documentation
        """
        super().__init__(options)
        self.notation_handler = MathlibNotationHandler()
        self.mathlib_base_url = mathlib_base_url
        self.logger = logging.getLogger(__name__)

    def _export_sketch(self, sketch: ProofSketch, context: ExportContext) -> List[Path]:
        """Export a Mathlib theorem with enhanced formatting.

        Args:
            sketch: Proof sketch to export
            context: Export context

        Returns:
            List of created files
        """
        # Preprocess sketch for Mathlib-specific content
        enhanced_sketch = self._enhance_mathlib_sketch(sketch)

        # Create enhanced template context
        template_context = self._create_mathlib_template_context(
            enhanced_sketch, context
        )

        # Export using parent method with enhanced context
        return self._export_with_enhanced_context(
            enhanced_sketch, context, template_context
        )

    def _enhance_mathlib_sketch(self, sketch: ProofSketch) -> ProofSketch:
        """Enhance sketch with Mathlib-specific processing.

        Args:
            sketch: Original proof sketch

        Returns:
            Enhanced proof sketch with Mathlib features
        """
        # Create a copy to avoid modifying the original
        enhanced_sketch = ProofSketch(
            theorem_name=sketch.theorem_name,
            introduction=sketch.introduction,
            key_steps=sketch.key_steps,
            conclusion=sketch.conclusion,
            difficulty_level=sketch.difficulty_level,
            mathematical_areas=sketch.mathematical_areas,
            prerequisites=sketch.prerequisites,
        )

        # Enhance introduction with notation processing
        if enhanced_sketch.introduction:
            enhanced_sketch.introduction = self._process_mathematical_text(
                enhanced_sketch.introduction
            )

        # Enhance proof steps
        for step in enhanced_sketch.key_steps:
            if step.description:
                step.description = self._process_mathematical_text(step.description)
            if step.mathematical_content:
                step.mathematical_content = self._process_mathematical_content(
                    step.mathematical_content
                )

        # Enhance conclusion
        if enhanced_sketch.conclusion:
            enhanced_sketch.conclusion = self._process_mathematical_text(
                enhanced_sketch.conclusion
            )

        # Detect and add mathematical areas
        if not enhanced_sketch.mathematical_areas:
            enhanced_sketch.mathematical_areas = self._detect_mathematical_areas(
                enhanced_sketch
            )

        return enhanced_sketch

    def _process_mathematical_text(self, text: str) -> str:
        """Process mathematical text with notation enhancement.

        Args:
            text: Raw mathematical text

        Returns:
            Enhanced text with proper notation handling
        """
        if not text:
            return text

        # Convert notation for display
        processed_text = text

        # Handle inline mathematical expressions (marked with `)
        def enhance_inline_math(match):
            math_content = match.group(1)
            latex_content = self.notation_handler.convert_to_latex(math_content)
            return f"$${latex_content}$$"

        processed_text = re.sub(r"`([^`]+)`", enhance_inline_math, processed_text)

        # Add links to Mathlib theorems mentioned in text
        processed_text = self._add_mathlib_links(processed_text)

        return processed_text

    def _process_mathematical_content(self, content: str) -> str:
        """Process mathematical content (formulas, expressions).

        Args:
            content: Mathematical content

        Returns:
            LaTeX-formatted mathematical content
        """
        if not content:
            return content

        # Convert Lean notation to LaTeX
        latex_content = self.notation_handler.convert_to_latex(content)

        # Ensure proper math delimiters
        if not latex_content.startswith("$") and not latex_content.startswith("\\["):
            latex_content = f"$${latex_content}$$"

        return latex_content

    def _add_mathlib_links(self, text: str) -> str:
        """Add links to Mathlib theorems mentioned in text.

        Args:
            text: Text that may contain theorem references

        Returns:
            Text with added links to Mathlib documentation
        """
        # Pattern for Mathlib theorem names (namespace.theorem_name)
        theorem_pattern = re.compile(
            r"\b([A-Z][a-zA-Z0-9]*(?:\.[A-Z][a-zA-Z0-9]*)*\.[a-z][a-zA-Z0-9_]*)\b"
        )

        def add_link(match):
            theorem_name = match.group(1)
            encoded_name = quote(theorem_name)
            link_url = f"{self.mathlib_base_url}find/?pattern={encoded_name}#doc"
            return f'<a href="{link_url}" class="mathlib-link" target="_blank">{theorem_name}</a>'

        return theorem_pattern.sub(add_link, text)

    def _detect_mathematical_areas(self, sketch: ProofSketch) -> List[str]:
        """Detect mathematical areas based on theorem content.

        Args:
            sketch: Proof sketch to analyze

        Returns:
            List of detected mathematical areas
        """
        # Collect all text content
        all_text = " ".join(
            [
                sketch.theorem_name,
                sketch.introduction or "",
                sketch.conclusion or "",
                " ".join(step.description or "" for step in sketch.key_steps),
                " ".join(step.mathematical_content or "" for step in sketch.key_steps),
            ]
        )

        # Use notation handler to detect areas
        detected_areas = self.notation_handler.detect_mathematical_areas(all_text)

        # Add areas based on theorem name patterns
        name_based_areas = self._detect_areas_from_name(sketch.theorem_name)
        detected_areas.extend(name_based_areas)

        # Remove duplicates and return
        return list(set(detected_areas))

    def _detect_areas_from_name(self, theorem_name: str) -> List[str]:
        """Detect mathematical areas from theorem name patterns.

        Args:
            theorem_name: Name of the theorem

        Returns:
            List of mathematical areas based on naming patterns
        """
        areas = []
        name_lower = theorem_name.lower()

        # Common Mathlib namespace patterns
        area_patterns = {
            "topology": ["Topology", "topological"],
            "algebra": ["Algebra", "Ring", "Group", "Field"],
            "analysis": ["Analysis", "Calculus", "Deriv", "Continuous"],
            "geometry": ["Geometry", "Euclidean", "Metric"],
            "category": ["CategoryTheory", "Functor", "Monad"],
            "logic": ["Logic", "Set", "Prop"],
            "number_theory": ["NumberTheory", "Prime", "Nat", "Int"],
            "linear_algebra": ["LinearAlgebra", "Module", "Vector"],
            "measure_theory": ["MeasureTheory", "Measure", "Integral"],
            "probability": ["Probability", "Random", "Distribution"],
        }

        for area, keywords in area_patterns.items():
            if any(keyword.lower() in name_lower for keyword in keywords):
                areas.append(area.replace("_", " ").title())

        return areas

    def _create_mathlib_template_context(
        self, sketch: ProofSketch, context: ExportContext
    ) -> Dict[str, Any]:
        """Create enhanced template context for Mathlib theorems.

        Args:
            sketch: Enhanced proof sketch
            context: Export context

        Returns:
            Enhanced template context dictionary
        """
        # Get base context
        base_context = super()._create_template_context(sketch, context)

        # Add Mathlib-specific enhancements
        mathlib_context = {
            # Notation support
            "notation_table": self._generate_notation_table(sketch),
            "mathematical_areas": sketch.mathematical_areas or [],
            # Mathlib integration
            "is_mathlib": True,
            "mathlib_base_url": self.mathlib_base_url,
            "mathlib_search_url": f"{self.mathlib_base_url}find/",
            # Enhanced theorem information
            "theorem_complexity": self._assess_complexity(sketch),
            "prerequisites_with_links": self._enhance_prerequisites(sketch),
            # Mathematical formatting
            "math_renderer": "katex",  # KaTeX for better math rendering
            "katex_config": self._get_katex_config(),
            # Enhanced navigation
            "related_theorems": self._find_related_theorems(sketch, context),
            # Mathematical areas for styling
            "primary_area": (
                sketch.mathematical_areas[0] if sketch.mathematical_areas else "General"
            ),
            "area_color_scheme": self._get_area_color_scheme(sketch.mathematical_areas),
        }

        # Merge with base context
        base_context.update(mathlib_context)

        return base_context

    def _generate_notation_table(self, sketch: ProofSketch) -> List[Dict[str, str]]:
        """Generate notation table for symbols used in the theorem.

        Args:
            sketch: Proof sketch

        Returns:
            List of notation entries
        """
        # Collect all mathematical content
        all_content = " ".join(
            [
                sketch.introduction or "",
                " ".join(step.mathematical_content or "" for step in sketch.key_steps),
                sketch.conclusion or "",
            ]
        )

        return self.notation_handler.get_notation_table(all_content)

    def _assess_complexity(self, sketch: ProofSketch) -> Dict[str, Any]:
        """Assess the complexity of the theorem.

        Args:
            sketch: Proof sketch

        Returns:
            Complexity assessment dictionary
        """
        # Count various complexity indicators
        proof_steps = len(sketch.key_steps)
        prerequisites = len(sketch.prerequisites) if sketch.prerequisites else 0
        mathematical_areas = (
            len(sketch.mathematical_areas) if sketch.mathematical_areas else 0
        )

        # Analyze text complexity
        intro_length = len(sketch.introduction.split()) if sketch.introduction else 0

        # Simple complexity scoring
        complexity_score = (
            proof_steps * 2 + prerequisites + mathematical_areas + intro_length // 20
        )

        if complexity_score < 5:
            level = "Beginner"
        elif complexity_score < 15:
            level = "Intermediate"
        elif complexity_score < 25:
            level = "Advanced"
        else:
            level = "Expert"

        return {
            "level": level,
            "score": complexity_score,
            "proof_steps": proof_steps,
            "prerequisites": prerequisites,
            "areas": mathematical_areas,
        }

    def _enhance_prerequisites(self, sketch: ProofSketch) -> List[Dict[str, str]]:
        """Enhance prerequisites with links and descriptions.

        Args:
            sketch: Proof sketch

        Returns:
            List of enhanced prerequisite entries
        """
        if not sketch.prerequisites:
            return []

        enhanced_prereqs = []
        for prereq in sketch.prerequisites:
            enhanced_prereqs.append(
                {
                    "name": prereq,
                    "link": f"{self.mathlib_base_url}find/?pattern={quote(prereq)}#doc",
                    "description": self._get_prerequisite_description(prereq),
                }
            )

        return enhanced_prereqs

    def _get_prerequisite_description(self, prereq: str) -> str:
        """Get description for a prerequisite.

        Args:
            prereq: Prerequisite name

        Returns:
            Description of the prerequisite
        """
        # Simple pattern-based descriptions
        descriptions = {
            "add_comm": "Addition is commutative",
            "mul_comm": "Multiplication is commutative",
            "add_assoc": "Addition is associative",
            "mul_assoc": "Multiplication is associative",
            "zero_add": "Zero is the left identity for addition",
            "add_zero": "Zero is the right identity for addition",
            "one_mul": "One is the left identity for multiplication",
            "mul_one": "One is the right identity for multiplication",
        }

        return descriptions.get(prereq, f"Mathematical concept: {prereq}")

    def _get_katex_config(self) -> Dict[str, Any]:
        """Get KaTeX configuration for mathematical rendering.

        Returns:
            KaTeX configuration dictionary
        """
        return {
            "delimiters": [
                {"left": "$$", "right": "$$", "display": True},
                {"left": "$", "right": "$", "display": False},
                {"left": "\\[", "right": "\\]", "display": True},
                {"left": "\\(", "right": "\\)", "display": False},
            ],
            "macros": {
                "\\N": "\\mathbb{N}",
                "\\Z": "\\mathbb{Z}",
                "\\Q": "\\mathbb{Q}",
                "\\R": "\\mathbb{R}",
                "\\C": "\\mathbb{C}",
                "\\F": "\\mathbb{F}",
                "\\to": "\\rightarrow",
                "\\iff": "\\leftrightarrow",
                "\\implies": "\\rightarrow",
            },
            "trust": False,  # Security setting
            "strict": False,  # Allow some LaTeX extensions
        }

    def _find_related_theorems(
        self, sketch: ProofSketch, context: ExportContext
    ) -> List[Dict[str, str]]:
        """Find related theorems based on content similarity.

        Args:
            sketch: Current proof sketch
            context: Export context

        Returns:
            List of related theorem entries
        """
        related = []

        # Simple relatedness based on shared mathematical areas
        if sketch.mathematical_areas:
            for other_sketch in context.sketches:
                if other_sketch.theorem_name != sketch.theorem_name:
                    if other_sketch.mathematical_areas and set(
                        sketch.mathematical_areas
                    ) & set(other_sketch.mathematical_areas):
                        related.append(
                            {
                                "name": other_sketch.theorem_name,
                                "url": context.theorem_links.get(
                                    other_sketch.theorem_name, "#"
                                ),
                                "areas": other_sketch.mathematical_areas,
                            }
                        )

        return related[:5]  # Limit to 5 related theorems

    def _get_area_color_scheme(self, areas: Optional[List[str]]) -> Dict[str, str]:
        """Get color scheme based on mathematical areas.

        Args:
            areas: List of mathematical areas

        Returns:
            Color scheme dictionary
        """
        # Default color scheme
        default_colors = {
            "primary": "#2563eb",  # Blue
            "secondary": "#e5e7eb",  # Gray
            "accent": "#10b981",  # Green
        }

        if not areas:
            return default_colors

        # Area-specific color schemes
        area_colors = {
            "Topology": {
                "primary": "#8b5cf6",
                "secondary": "#ede9fe",
                "accent": "#a78bfa",
            },
            "Algebra": {
                "primary": "#ef4444",
                "secondary": "#fee2e2",
                "accent": "#f87171",
            },
            "Analysis": {
                "primary": "#059669",
                "secondary": "#d1fae5",
                "accent": "#34d399",
            },
            "Geometry": {
                "primary": "#dc2626",
                "secondary": "#fef2f2",
                "accent": "#f87171",
            },
            "Category Theory": {
                "primary": "#7c3aed",
                "secondary": "#f3e8ff",
                "accent": "#a78bfa",
            },
            "Number Theory": {
                "primary": "#d97706",
                "secondary": "#fef3c7",
                "accent": "#fbbf24",
            },
            "Logic": {
                "primary": "#374151",
                "secondary": "#f9fafb",
                "accent": "#6b7280",
            },
        }

        # Use color scheme for the first area
        primary_area = areas[0]
        return area_colors.get(primary_area, default_colors)

    def _export_with_enhanced_context(
        self,
        sketch: ProofSketch,
        context: ExportContext,
        template_context: Dict[str, Any],
    ) -> List[Path]:
        """Export with enhanced mathlib template context.

        Args:
            sketch: Enhanced proof sketch
            context: Export context
            template_context: Enhanced template context

        Returns:
            List of created files
        """
        created_files = []

        # Generate output filename
        output_file = self._generate_filename(sketch.theorem_name, "html")

        # Render with enhanced template
        try:
            html_content = self.template_manager.render_template(
                ExportFormat.HTML,
                TemplateType.THEOREM,  # Use standard theorem template
                template_context,
            )
        except Exception:
            # Fallback to regular theorem template
            html_content = self.template_manager.render_template(
                ExportFormat.HTML, TemplateType.THEOREM, template_context
            )

        # Write output file
        output_file.write_text(html_content, encoding="utf-8")
        created_files.append(output_file)

        # Copy enhanced assets if needed
        if self.options.create_subdirs:
            asset_files = self._copy_mathlib_assets()
            created_files.extend(asset_files)

        self.logger.info(
            f"Exported Mathlib theorem {sketch.theorem_name} to {output_file}"
        )

        return created_files

    def _copy_mathlib_assets(self) -> List[Path]:
        """Copy Mathlib-specific assets.

        Returns:
            List of copied asset files
        """
        copied_files = []

        # Copy standard assets first
        copied_files.extend(super()._copy_assets())

        # Copy additional Mathlib assets (CSS, JS for enhanced math rendering)
        mathlib_assets = [
            "css/mathlib.css",
            "js/mathlib-enhanced.js",
            "js/katex-auto-render.min.js",
        ]

        for asset_rel_path in mathlib_assets:
            src_path = (
                self.template_manager.template_dir / "html" / "assets" / asset_rel_path
            )
            if src_path.exists():
                dst_path = self.options.output_dir / asset_rel_path
                dst_path.parent.mkdir(parents=True, exist_ok=True)

                try:
                    dst_path.write_bytes(src_path.read_bytes())
                    copied_files.append(dst_path)
                except Exception as e:
                    self.logger.warning(f"Failed to copy {asset_rel_path}: {e}")

        return copied_files
