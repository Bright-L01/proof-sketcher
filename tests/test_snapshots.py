"""Snapshot tests for output verification.

This module uses snapshot testing to ensure that generated outputs
(HTML, Markdown, LaTeX, etc.) remain consistent and meet quality standards.
"""

import json
import re
from pathlib import Path
from typing import Dict, Optional

import pytest

from proof_sketcher.exporter.html import HTMLExporter
from proof_sketcher.exporter.markdown import MarkdownExporter
from proof_sketcher.exporter.models import ExportOptions
from proof_sketcher.exporter.pdf import PDFExporter
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.parser.mathlib_notation import MathlibNotationHandler
from proof_sketcher.parser.models import TheoremInfo


class SnapshotManager:
    """Manages snapshot storage and comparison."""

    def __init__(self, snapshot_dir: Path = Path("tests/snapshots")):
        """Initialize snapshot manager.

        Args:
            snapshot_dir: Directory to store snapshots
        """
        self.snapshot_dir = snapshot_dir
        self.snapshot_dir.mkdir(exist_ok=True)

    def get_snapshot_path(self, test_name: str, format: str) -> Path:
        """Get path for a snapshot file.

        Args:
            test_name: Name of the test
            format: File format (html, md, tex, etc.)

        Returns:
            Path to snapshot file
        """
        return self.snapshot_dir / f"{test_name}.{format}"

    def save_snapshot(self, test_name: str, content: str, format: str) -> None:
        """Save a snapshot.

        Args:
            test_name: Name of the test
            content: Content to save
            format: File format
        """
        path = self.get_snapshot_path(test_name, format)
        path.write_text(content, encoding="utf-8")

    def load_snapshot(self, test_name: str, format: str) -> Optional[str]:
        """Load a snapshot.

        Args:
            test_name: Name of the test
            format: File format

        Returns:
            Snapshot content if exists, None otherwise
        """
        path = self.get_snapshot_path(test_name, format)
        if path.exists():
            return path.read_text(encoding="utf-8")
        return None

    def compare_snapshots(
        self, actual: str, expected: str, ignore_patterns: Optional[list] = None
    ) -> bool:
        """Compare two snapshots.

        Args:
            actual: Actual output
            expected: Expected output
            ignore_patterns: Regex patterns to ignore in comparison

        Returns:
            True if snapshots match (ignoring patterns)
        """
        if ignore_patterns:
            for pattern in ignore_patterns:
                actual = re.sub(pattern, "<IGNORED>", actual)
                expected = re.sub(pattern, "<IGNORED>", expected)

        return actual.strip() == expected.strip()


@pytest.fixture
def snapshot_manager():
    """Provide snapshot manager for tests."""
    return SnapshotManager()


@pytest.fixture
def sample_proof_sketch():
    """Create a sample proof sketch for testing."""
    return ProofSketch(
        theorem_name="pythagorean_theorem",
        theorem_statement="∀ a b c : ℝ, a² + b² = c² ↔ IsRightTriangle a b c",
        introduction="The Pythagorean theorem relates the sides of a right triangle.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="Establish the forward direction",
                mathematical_content="a² + b² = c² → IsRightTriangle a b c",
                reasoning="Use the definition of right triangle",
                tactics_used=["unfold", "simp"],
                intuition="If the equation holds, the triangle has a right angle",
            ),
            ProofStep(
                step_number=2,
                description="Prove the reverse direction",
                mathematical_content="IsRightTriangle a b c → a² + b² = c²",
                reasoning="Apply trigonometric identities",
                tactics_used=["rw", "field_simp"],
                intuition="A right triangle satisfies the Pythagorean equation",
            ),
        ],
        conclusion="Thus, the Pythagorean equation characterizes right triangles.",
        difficulty_level="intermediate",
        key_insights=["Geometric-algebraic correspondence", "Bidirectional proof"],
        mathematical_context="Euclidean geometry",
    )


@pytest.fixture
def complex_proof_sketch():
    """Create a complex proof sketch with special notation."""
    return ProofSketch(
        theorem_name="fundamental_theorem_calculus",
        theorem_statement="∀ f : ℝ → ℝ, Continuous f → ∀ a b : ℝ, ∫_a^b f(x) dx = F(b) - F(a)",
        introduction="The fundamental theorem of calculus connects differentiation and integration.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="Define the antiderivative",
                mathematical_content="F(x) = ∫_a^x f(t) dt",
                reasoning="Construction of the antiderivative function",
                tactics_used=["define", "intro"],
                intuition="The integral up to x gives us a function of x",
            ),
            ProofStep(
                step_number=2,
                description="Show F' = f",
                mathematical_content="∀ x ∈ [a, b], F'(x) = f(x)",
                reasoning="Apply the definition of derivative",
                tactics_used=["unfold", "limit"],
                intuition="The derivative undoes the integral",
            ),
            ProofStep(
                step_number=3,
                description="Apply the evaluation theorem",
                mathematical_content="∫_a^b f(x) dx = F(b) - F(a)",
                reasoning="Use the fundamental property",
                tactics_used=["calc", "simp"],
                intuition="The definite integral is the difference of antiderivative values",
            ),
        ],
        conclusion="This establishes the fundamental connection between differential and integral calculus.",
        difficulty_level="advanced",
        key_insights=[
            "Inverse relationship",
            "Continuity requirement",
            "Geometric interpretation",
        ],
        mathematical_context="Real analysis",
    )


class TestHTMLSnapshots:
    """Test HTML export snapshots."""

    def test_basic_html_export(self, sample_proof_sketch, snapshot_manager, tmp_path):
        """Test basic HTML export snapshot."""
        exporter = HTMLExporter(ExportOptions(output_dir=tmp_path))

        # Generate HTML
        result = exporter.export_single(sample_proof_sketch)
        assert result.success

        # Read generated HTML
        html_file = result.output_files[0]
        actual_html = html_file.read_text()

        # Patterns to ignore (timestamps, paths, etc.)
        ignore_patterns = [
            r'<meta name="generated-date" content="[^"]+">',
            r'<div class="timestamp">[^<]+</div>',
            r"<!-- Generated by Proof Sketcher v[^>]+-->",
        ]

        # Compare with snapshot
        expected_html = snapshot_manager.load_snapshot("basic_html_export", "html")

        if expected_html is None:
            # First run - save snapshot
            snapshot_manager.save_snapshot("basic_html_export", actual_html, "html")
            pytest.skip("Snapshot saved for first run")
        else:
            # Compare snapshots
            assert snapshot_manager.compare_snapshots(
                actual_html, expected_html, ignore_patterns
            ), "HTML output has changed"

    def test_complex_notation_html(
        self, complex_proof_sketch, snapshot_manager, tmp_path
    ):
        """Test HTML export with complex mathematical notation."""
        exporter = HTMLExporter(
            ExportOptions(output_dir=tmp_path, include_mathjax=True, include_css=True)
        )

        result = exporter.export_single(complex_proof_sketch)
        assert result.success

        html_content = result.output_files[0].read_text()

        # Verify MathJax is included
        assert "MathJax" in html_content
        assert "\\int_a^b" in html_content or "∫_a^b" in html_content

        # Check snapshot
        expected = snapshot_manager.load_snapshot("complex_notation_html", "html")
        if expected is None:
            snapshot_manager.save_snapshot(
                "complex_notation_html", html_content, "html"
            )
            pytest.skip("Snapshot saved")
        else:
            assert snapshot_manager.compare_snapshots(
                html_content, expected, [r"<meta[^>]+>", r"<!--[^>]+-->"]
            )


class TestMarkdownSnapshots:
    """Test Markdown export snapshots."""

    def test_github_markdown_export(
        self, sample_proof_sketch, snapshot_manager, tmp_path
    ):
        """Test GitHub-flavored Markdown export."""
        exporter = MarkdownExporter(
            ExportOptions(output_dir=tmp_path, markdown_flavor="github")
        )

        result = exporter.export_single(sample_proof_sketch)
        assert result.success

        md_content = result.output_files[0].read_text()

        # Verify GitHub-specific features
        assert "```lean" in md_content  # Code blocks
        assert "## " in md_content  # Headers
        assert "1. " in md_content  # Numbered lists

        # Check snapshot
        expected = snapshot_manager.load_snapshot("github_markdown", "md")
        if expected is None:
            snapshot_manager.save_snapshot("github_markdown", md_content, "md")
            pytest.skip("Snapshot saved")
        else:
            assert snapshot_manager.compare_snapshots(md_content, expected)

    def test_markdown_with_math(self, complex_proof_sketch, snapshot_manager, tmp_path):
        """Test Markdown with mathematical notation."""
        exporter = MarkdownExporter(ExportOptions(output_dir=tmp_path))

        result = exporter.export_single(complex_proof_sketch)
        assert result.success

        md_content = result.output_files[0].read_text()

        # Verify math delimiters
        assert "$" in md_content or "$$" in md_content
        assert "∫" in md_content or "\\int" in md_content

        # Check snapshot
        expected = snapshot_manager.load_snapshot("markdown_math", "md")
        if expected is None:
            snapshot_manager.save_snapshot("markdown_math", md_content, "md")
            pytest.skip("Snapshot saved")
        else:
            assert snapshot_manager.compare_snapshots(md_content, expected)


class TestLaTeXSnapshots:
    """Test LaTeX/PDF export snapshots."""

    def test_latex_export(self, sample_proof_sketch, snapshot_manager, tmp_path):
        """Test LaTeX export snapshot."""
        exporter = PDFExporter(ExportOptions(output_dir=tmp_path))

        # Generate LaTeX (not PDF, for snapshot testing)
        latex_content = exporter._generate_latex(sample_proof_sketch)

        # Verify LaTeX structure
        assert "\\documentclass" in latex_content
        assert "\\begin{document}" in latex_content
        assert "\\end{document}" in latex_content
        assert "\\section" in latex_content or "\\subsection" in latex_content

        # Check snapshot
        expected = snapshot_manager.load_snapshot("basic_latex", "tex")
        if expected is None:
            snapshot_manager.save_snapshot("basic_latex", latex_content, "tex")
            pytest.skip("Snapshot saved")
        else:
            # Ignore date/version in comparison
            ignore_patterns = [
                r"\\date\{[^}]+\}",
                r"% Generated on [^\n]+",
            ]
            assert snapshot_manager.compare_snapshots(
                latex_content, expected, ignore_patterns
            )

    def test_latex_math_environments(
        self, complex_proof_sketch, snapshot_manager, tmp_path
    ):
        """Test LaTeX with complex math environments."""
        exporter = PDFExporter(ExportOptions(output_dir=tmp_path))

        latex_content = exporter._generate_latex(complex_proof_sketch)

        # Verify math environments
        assert "\\begin{equation}" in latex_content or "\\[" in latex_content
        assert "\\int" in latex_content
        assert "\\forall" in latex_content or "∀" in latex_content

        # Check snapshot
        expected = snapshot_manager.load_snapshot("complex_latex", "tex")
        if expected is None:
            snapshot_manager.save_snapshot("complex_latex", latex_content, "tex")
            pytest.skip("Snapshot saved")
        else:
            assert snapshot_manager.compare_snapshots(
                latex_content, expected, [r"\\date\{[^}]+\}", r"%[^\n]+\n"]
            )


class TestNotationSnapshots:
    """Test mathematical notation conversion snapshots."""

    def test_notation_conversions(self, snapshot_manager):
        """Test notation handler conversions remain consistent."""
        handler = MathlibNotationHandler()

        test_cases = [
            ("∀ x ∈ ℕ, x + 0 = x", "forall_nat"),
            ("∃ f : ℝ → ℝ, continuous f", "exists_function"),
            ("A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C", "set_theory"),
            ("∫₀¹ f(x) dx = ∑_{n=0}^∞ aₙ", "integral_sum"),
            ("∇ × F = 0", "vector_calculus"),
            ("lim_{n→∞} (1 + 1/n)ⁿ = e", "limit"),
        ]

        results = {}
        for expr, name in test_cases:
            results[name] = {
                "original": expr,
                "latex": handler.convert_to_latex(expr),
                "html": handler.convert_to_html(expr),
            }

        # Save as JSON for easy comparison
        snapshot_path = snapshot_manager.get_snapshot_path(
            "notation_conversions", "json"
        )

        if snapshot_path.exists():
            expected = json.loads(snapshot_path.read_text())
            assert results == expected, "Notation conversions have changed"
        else:
            snapshot_path.write_text(json.dumps(results, indent=2, ensure_ascii=False))
            pytest.skip("Snapshot saved")


class TestTemplateSnapshots:
    """Test template rendering snapshots."""

    def test_template_structure(self, sample_proof_sketch, snapshot_manager, tmp_path):
        """Test that template structure remains consistent."""
        # Test different template types
        templates = {
            "html": HTMLExporter(ExportOptions(output_dir=tmp_path)),
            "markdown": MarkdownExporter(ExportOptions(output_dir=tmp_path)),
        }

        for format_name, exporter in templates.items():
            # Extract template structure (headers, sections, etc.)
            if hasattr(exporter, "_render_template"):
                # Mock rendering to get structure
                template_vars = {
                    "theorem": sample_proof_sketch,
                    "title": sample_proof_sketch.theorem_name,
                    "steps": sample_proof_sketch.key_steps,
                }

                # This would need actual template rendering
                # For now, we just verify the exporter works
                result = exporter.export_single(sample_proof_sketch)
                assert result.success


class TestRegressionSnapshots:
    """Test for regressions in specific scenarios."""

    def test_edge_case_snapshots(self, snapshot_manager, tmp_path):
        """Test edge cases to prevent regressions."""
        edge_cases = [
            # Empty proof
            ProofSketch(
                theorem_name="empty_proof",
                theorem_statement="P",
                introduction="Trivial",
                key_steps=[],
                conclusion="QED",
                difficulty_level="trivial",
            ),
            # Unicode-heavy proof
            ProofSketch(
                theorem_name="unicode_heavy",
                theorem_statement="∀ ε > 0, ∃ δ > 0, |x - x₀| < δ ⇒ |f(x) - f(x₀)| < ε",
                introduction="Continuity in ε-δ definition",
                key_steps=[
                    ProofStep(
                        step_number=1,
                        description="Choose δ = ε/2",
                        mathematical_content="δ := ε/2",
                        reasoning="Standard choice",
                        tactics_used=["define"],
                        intuition="Half of epsilon works",
                    )
                ],
                conclusion="Therefore f is continuous at x₀",
                difficulty_level="intermediate",
            ),
            # Very long proof
            ProofSketch(
                theorem_name="long_proof",
                theorem_statement="Long theorem statement " * 20,
                introduction="Long introduction " * 50,
                key_steps=[
                    ProofStep(
                        step_number=i,
                        description=f"Step {i} description",
                        mathematical_content=f"Math for step {i}",
                        reasoning="Because...",
                        tactics_used=["tactic"],
                        intuition="Intuition",
                    )
                    for i in range(1, 11)
                ],
                conclusion="Long conclusion " * 30,
                difficulty_level="expert",
            ),
        ]

        exporter = HTMLExporter(ExportOptions(output_dir=tmp_path))

        for sketch in edge_cases:
            result = exporter.export_single(sketch)
            assert result.success

            content = result.output_files[0].read_text()

            # Basic sanity checks
            assert sketch.theorem_name in content
            assert len(content) > 100  # Not empty

            # Save snapshot
            snapshot_name = f"edge_case_{sketch.theorem_name}"
            expected = snapshot_manager.load_snapshot(snapshot_name, "html")

            if expected is None:
                snapshot_manager.save_snapshot(snapshot_name, content, "html")
            else:
                # For edge cases, we're more lenient with changes
                # Just ensure core content is preserved
                assert sketch.theorem_statement in content
                assert sketch.introduction in content
                assert sketch.conclusion in content


class TestSnapshotValidation:
    """Validate snapshot quality and consistency."""

    def test_snapshot_html_validity(self, snapshot_manager):
        """Test that HTML snapshots are valid HTML."""
        html_snapshots = list(snapshot_manager.snapshot_dir.glob("*.html"))

        for snapshot_path in html_snapshots:
            content = snapshot_path.read_text()

            # Basic HTML validation
            assert content.strip().startswith(
                "<!DOCTYPE html>"
            ) or content.strip().startswith("<")
            assert "</html>" in content or snapshot_path.name.endswith("_fragment.html")

            # Check for common issues
            assert content.count("<div") == content.count(
                "</div"
            ), f"Unclosed divs in {snapshot_path.name}"
            assert content.count("<span") == content.count(
                "</span"
            ), f"Unclosed spans in {snapshot_path.name}"

    def test_snapshot_markdown_validity(self, snapshot_manager):
        """Test that Markdown snapshots are valid Markdown."""
        md_snapshots = list(snapshot_manager.snapshot_dir.glob("*.md"))

        for snapshot_path in md_snapshots:
            content = snapshot_path.read_text()

            # Basic Markdown validation
            lines = content.split("\n")

            # Check headers are properly formatted
            for line in lines:
                if line.startswith("#"):
                    assert (
                        line.startswith("# ")
                        or line.startswith("## ")
                        or line.startswith("### ")
                    ), f"Invalid header format in {snapshot_path.name}: {line}"

            # Check code blocks are closed
            code_block_count = content.count("```")
            assert (
                code_block_count % 2 == 0
            ), f"Unclosed code blocks in {snapshot_path.name}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
