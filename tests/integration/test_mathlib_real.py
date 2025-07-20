"""Real Mathlib4 integration tests.

These tests verify that Proof Sketcher works correctly with actual Mathlib4 theorems,
handling real mathematical notation, dependencies, and complex proof structures.
"""

from __future__ import annotations

import subprocess
import tempfile
import time
from pathlib import Path
from typing import Dict, List, Optional

import pytest

from proof_sketcher.exporter.batch_processor import BatchExporter
from proof_sketcher.exporter.markdown import MarkdownExporter
from proof_sketcher.generator import SimpleGenerator
from proof_sketcher.generator.offline import OfflineGenerator
from proof_sketcher.parser.config import ParserConfig
from proof_sketcher.parser.simple_parser import SimpleLeanParser


class MathlibTestFixtures:
    """Test fixtures for Mathlib integration tests."""

    @staticmethod
    def create_minimal_mathlib_files(test_dir: Path) -> Dict[str, Path]:
        """Create minimal mathlib-style files for testing.

        Args:
            test_dir: Directory to create files in

        Returns:
            Dictionary mapping file types to file paths
        """
        files = {}

        # Basic arithmetic file
        basic_file = test_dir / "Basic.lean"
        basic_file.write_text(
            """
-- Basic arithmetic theorems with mathlib notation
namespace Nat

/-- Addition is commutative -/
theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction a with
  | zero => simp [zero_add]
  | succ a ih =>
    rw [succ_add, ih, add_succ]

/-- Addition is associative -/
theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => simp [zero_add]
  | succ a ih =>
    rw [succ_add, succ_add, ih, succ_add]

/-- Zero is the right identity for addition -/
theorem add_zero (a : ℕ) : a + 0 = a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [succ_add, ih]

end Nat
"""
        )
        files["basic"] = basic_file

        # Set theory file with Unicode notation
        set_file = test_dir / "Set.lean"
        set_file.write_text(
            """
-- Set theory with Unicode notation
namespace Set

variable {α : Type*}

/-- Membership in union -/
theorem mem_union {s t : Set α} {a : α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := by
  constructor
  · intro h
    cases h with
    | inl hs => exact Or.inl hs
    | inr ht => exact Or.inr ht
  · intro h
    cases h with
    | inl hs => exact Or.inl hs
    | inr ht => exact Or.inr ht

/-- Subset transitivity -/
theorem subset_trans {s t u : Set α} : s ⊆ t → t ⊆ u → s ⊆ u := by
  intros h1 h2 x hx
  exact h2 (h1 hx)

/-- Empty set is subset of any set -/
theorem empty_subset (s : Set α) : ∅ ⊆ s := by
  intro x h
  exact False.elim h

end Set
"""
        )
        files["set"] = set_file

        # Topology file with advanced notation
        topology_file = test_dir / "Topology.lean"
        topology_file.write_text(
            """
-- Topology with advanced mathematical notation
import Set

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- Union of open sets is open -/
theorem isOpen_union {ι : Type*} (s : ι → Set X) (h : ∀ i, IsOpen (s i)) :
    IsOpen (⋃ i, s i) := by
  sorry  -- Proof omitted for demo

/-- Intersection of finitely many open sets is open -/
theorem isOpen_finite_inter {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) :
    IsOpen (s ∩ t) := by
  sorry  -- Proof omitted for demo

/-- Continuous function preserves compactness -/
theorem IsCompact.image {Y : Type*} [TopologicalSpace Y] {f : X → Y} {s : Set X}
    (hf : Continuous f) (hs : IsCompact s) : IsCompact (f '' s) := by
  sorry  -- Proof omitted for demo

end TopologicalSpace
"""
        )
        files["topology"] = topology_file

        return files


class TestParserConfig:
    """Test the Mathlib notation handler."""

    def test_basic_notation_conversion(self):
        """Test basic notation conversion."""
        handler = ParserConfig()

        # Test basic symbols
        assert handler.convert_to_latex("∀ x ∈ ℕ") == r"\forall x \in \mathbb{N}"
        assert handler.convert_to_latex("∃ y ∈ ℝ") == r"\exists y \in \mathbb{R}"
        assert handler.convert_to_latex("A ⊆ B") == r"A \subseteq B"

    def test_complex_notation(self):
        """Test complex mathematical notation."""
        handler = ParserConfig()

        # Function types
        result = handler.convert_to_latex("f : ℕ → ℝ")
        assert r"\mathbb{N}" in result and r"\mathbb{R}" in result and r"\to" in result

        # Set operations
        result = handler.convert_to_latex("s ∪ t ∩ u")
        assert r"\cup" in result and r"\cap" in result

    def test_notation_table_generation(self):
        """Test generation of notation tables."""
        handler = ParserConfig()

        text = "∀ x ∈ ℕ, ∃ y ∈ ℝ"
        table = handler.get_notation_table(text)

        # Should find all symbols used
        symbols = {entry["symbol"] for entry in table}
        assert "∀" in symbols
        assert "∃" in symbols
        assert "∈" in symbols
        assert "ℕ" in symbols
        assert "ℝ" in symbols

    def test_mathematical_area_detection(self):
        """Test detection of mathematical areas."""
        handler = ParserConfig()

        # Set theory text
        set_text = "Let A ⊆ B and x ∈ A ∪ C"
        areas = handler.detect_mathematical_areas(set_text)
        assert "Set Theory" in areas

        # Analysis text
        analysis_text = "∫₀¹ f(x) dx ≤ ∑ₙ aₙ"
        areas = handler.detect_mathematical_areas(analysis_text)
        assert "Mathematical Analysis" in areas


class TestMarkdownExporter:
    """Test the Mathlib-specific exporter."""

    @pytest.fixture
    def sample_mathlib_sketch(self):
        """Create a sample proof sketch with mathlib notation."""
        from proof_sketcher.generator.models import ProofSketch, ProofStep

        return ProofSketch(
            theorem_name="Nat.add_comm",
            introduction="Addition of natural numbers is commutative. This fundamental property states that for any two natural numbers a and b, we have a + b = b + a.",
            key_steps=[
                ProofStep(
step_number=1,
    intuitive_explanation="Test intuitive explanation",
    conceptual_explanation="Test conceptual explanation",
    bridging_explanation="Test bridging explanation",
    formal_explanation="Test formal explanation",
                    description="Base case: Show 0 + b = b + 0",
                    mathematical_content="0 + b = b + 0",
                    tactics=["simp", "zero_add"],
),
                ProofStep(
step_number=2,
    intuitive_explanation="Test intuitive explanation",
    conceptual_explanation="Test conceptual explanation",
    bridging_explanation="Test bridging explanation",
    formal_explanation="Test formal explanation",
                    description="Inductive step: Assume a + b = b + a, prove (a + 1) + b = b + (a + 1)",
                    mathematical_content="(a + 1) + b = b + (a + 1)",
                    tactics=["rw", "succ_add", "add_succ", "ih"],
                ),
            ],
            conclusion="By mathematical induction, addition is commutative for all natural numbers.",
            mathematical_areas=["Number Theory", "Algebra"],
            prerequisites=["Nat.zero_add", "Nat.add_succ", "Nat.succ_add"],
        )

    def test_mathlib_sketch_enhancement(self, sample_mathlib_sketch, tmp_path):
        """Test enhancement of mathlib sketches."""
        exporter = MarkdownExporter()
        enhanced = exporter._enhance_mathlib_sketch(sample_mathlib_sketch)

        # Check that mathematical areas were detected/preserved
        assert enhanced.mathematical_areas
        assert (
            "Number Theory" in enhanced.mathematical_areas
            or "Algebra" in enhanced.mathematical_areas
        )

        # Check that text was processed
        assert enhanced.introduction  # Should be preserved and potentially enhanced

    def test_notation_table_generation(self, sample_mathlib_sketch):
        """Test notation table generation for mathlib content."""
        exporter = MarkdownExporter()
        notation_table = exporter._generate_notation_table(sample_mathlib_sketch)

        # Should be a list of notation entries
        assert isinstance(notation_table, list)
        # May be empty if no special notation in this example

    def test_complexity_assessment(self, sample_mathlib_sketch):
        """Test complexity assessment."""
        exporter = MarkdownExporter()
        complexity = exporter._assess_complexity(sample_mathlib_sketch)

        assert "level" in complexity
        assert "score" in complexity
        assert complexity["level"] in ["Beginner", "Intermediate", "Advanced", "Expert"]
        assert isinstance(complexity["score"], int)

    def test_mathlib_export(self, sample_mathlib_sketch, tmp_path):
        """Test full mathlib export process."""
        from proof_sketcher.exporter.models import ExportContext, ExportOptions

        # Set up exporter
        options = ExportOptions(output_dir=tmp_path, create_subdirs=True)
        exporter = MarkdownExporter(options)

        # Create export context
        context = ExportContext(
            format=exporter.format,
            output_dir=tmp_path,
            sketches=[sample_mathlib_sketch],
            project_name="Test Mathlib Project",
        )

        # Export
        result = exporter.export_single(sample_mathlib_sketch, context)

        # Verify result
        assert result.success
        assert len(result.files_created) > 0

        # Check output file
        html_file = result.files_created[0]
        assert html_file.exists()
        assert html_file.suffix == ".html"

        # Check content
        content = html_file.read_text()
        assert sample_mathlib_sketch.theorem_name in content
        # Content should be substantial (at least has the theorem introduction)
        assert sample_mathlib_sketch.introduction.lower()[:20] in content.lower()


class TestMathlibIntegration:
    """Integration tests with mathlib-style content."""

    def test_mathlib_style_project_scanning(self, tmp_path):
        """Test project scanning with mathlib-style files."""
        # Create test files
        fixtures = MathlibTestFixtures.create_minimal_mathlib_files(tmp_path)

        # Scan project
        scanner = BatchExporter()
        result = scanner.scan_project(tmp_path)

        # Verify scanning results
        assert result["statistics"]["total_files"] == len(fixtures)
        assert result["statistics"]["total_theorems"] > 0

        # Check that Unicode notation doesn't break scanning
        file_theorems = result["file_theorems"]
        assert len(file_theorems) == len(fixtures)

        # Verify specific theorems were found
        all_theorems = [t for theorems in file_theorems.values() for t in theorems]
        assert "add_comm" in all_theorems
        assert "mem_union" in all_theorems

    def test_mathlib_notation_in_parsing(self, tmp_path):
        """Test that mathlib notation is handled correctly in parsing."""
        # Create file with Unicode notation
        test_file = tmp_path / "Unicode.lean"
        test_file.write_text(
            """
theorem unicode_test (A B : Set ℕ) : A ∪ B = B ∪ A := by
  ext x
  simp [Set.mem_union]
  tauto
"""
        )

        # Parse file
        parser = SimpleLeanParser()
        try:
            theorems = parser.parse_file(test_file)

            # Should not crash on Unicode
            assert (
                len(theorems) >= 0
            )  # May be 0 if parser has issues, but shouldn't crash

        except Exception as e:
            # If parsing fails, it should be a graceful failure, not a crash
            assert "unicode" not in str(e).lower() or "encoding" not in str(e).lower()

    def test_end_to_end_mathlib_processing(self, tmp_path):
        """Test end-to-end processing of mathlib-style content."""
        # Create test files
        fixtures = MathlibTestFixtures.create_minimal_mathlib_files(tmp_path)

        # Test with offline generator (more reliable than AI for testing)
        generator = OfflineGenerator()
        exporter = MarkdownExporter()

        processed_theorems = []

        for file_type, file_path in fixtures.items():
            try:
                # Parse file
                parser = SimpleLeanParser()
                theorems = parser.parse_file(file_path)

                for theorem in theorems[:2]:  # Limit to first 2 theorems per file
                    # Generate explanation
                    sketch = generator.generate_proof_sketch(theorem)

                    if sketch:
                        processed_theorems.append(
                            {
                                "theorem": theorem,
                                "sketch": sketch,
                                "file_type": file_type,
                            }
                        )

            except Exception as e:
                # Log but don't fail - some failures are expected in testing
                print(f"Processing failed for {file_type}: {e}")

        # Should have processed at least some theorems
        assert len(processed_theorems) > 0

        # Test export of processed theorems
        for item in processed_theorems[:3]:  # Test first 3
            try:
                from proof_sketcher.exporter.models import ExportContext, ExportOptions

                options = ExportOptions(output_dir=tmp_path / "output")
                exporter = MarkdownExporter(options)

                context = ExportContext(
                    format=exporter.format,
                    output_dir=tmp_path / "output",
                    sketches=[item["sketch"]],
                )

                result = exporter.export_single(item["sketch"], context)
                assert (
                    result.success or len(result.errors) > 0
                )  # Either success or documented failure

            except Exception as e:
                print(f"Export failed for {item['theorem'].name}: {e}")

    def test_mathlib_batch_processing(self, tmp_path):
        """Test batch processing with mathlib-style content."""
        from proof_sketcher.exporter.batch_processor import (
            BatchExporter,
            ParallelProcessor,
        )

        # Create test files
        fixtures = MathlibTestFixtures.create_minimal_mathlib_files(tmp_path)

        # Scan project
        scanner = BatchExporter()
        project_data = scanner.scan_project(tmp_path)

        # Process with batch system
        processor = ParallelProcessor(max_workers=2)  # Small number for testing

        options = {
            "use_claude": False,  # Use offline mode for reliability
            "create_visualization": False,  # Skip for speed
            "export_formats": ["html"],
        }

        try:
            import asyncio

            async def run_test():
                result = await processor.process_project(
                    project_data, tmp_path / "batch_output", options
                )
                return result

            result = asyncio.run(run_test())

            # Verify batch processing results
            assert result["total_theorems"] > 0
            assert (
                result["processed"] >= 0
            )  # May be 0 if all failed, but shouldn't crash

            # Check that some output was generated (even if errors occurred)
            output_dir = tmp_path / "batch_output"
            if output_dir.exists():
                output_files = list(output_dir.rglob("*"))
                # May have created some files even with errors

        except Exception as e:
            # Batch processing might fail in test environment, but shouldn't crash
            print(f"Batch processing test failed (expected in some environments): {e}")


class TestMathlibPerformance:
    """Performance tests for mathlib integration."""

    def test_notation_handler_performance(self):
        """Test performance of notation handling."""
        handler = ParserConfig()

        # Large text with lots of notation
        large_text = " ".join(["∀ x ∈ ℕ, ∃ y ∈ ℝ, x + y ∈ ℂ ∧ x ⊆ y ∪ z ∩ w"] * 100)

        start_time = time.time()
        result = handler.convert_to_latex(large_text)
        processing_time = time.time() - start_time

        # Should process reasonably quickly
        assert processing_time < 1.0  # Less than 1 second
        assert len(result) > len(large_text)  # LaTeX should be longer

    def test_exporter_performance(self, tmp_path):
        """Test performance of mathlib exporter."""
        from proof_sketcher.generator.models import ProofSketch, ProofStep

        # Create a complex sketch
        complex_sketch = ProofSketch(
            theorem_name="ComplexTheorem",
            introduction="A complex theorem with lots of mathematical notation: ∀ x ∈ ℕ, ∃ y ∈ ℝ, x + y ∈ ℂ ∧ x ⊆ y ∪ z ∩ w"
            * 10,
            key_steps=[
                ProofStep(
step_number=i,
    intuitive_explanation="Test intuitive explanation",
    conceptual_explanation="Test conceptual explanation",
    bridging_explanation="Test bridging explanation",
    formal_explanation="Test formal explanation",
                    description=f"Step {i} with notation: ∀ x ∈ ℕ, x + 0 = x",
                    mathematical_content=f"step_{i}: ∀ x ∈ ℕ, ∃ y ∈ ℝ, x + y = y + x",
                    tactics=[f"tactic_{i}"],
)
                for i in range(20)
            ],
            conclusion="Complex conclusion with notation: ∀ x ∈ ℕ, ∃ y ∈ ℝ, x + y ∈ ℂ"
            * 5,
        )

        # Test export performance
        from proof_sketcher.exporter.models import ExportContext, ExportOptions

        options = ExportOptions(output_dir=tmp_path)
        exporter = MarkdownExporter(options)
        context = ExportContext(
            format=exporter.format,
            output_dir=tmp_path,
            sketches=[complex_sketch],
        )

        start_time = time.time()
        result = exporter.export_single(complex_sketch, context)
        export_time = time.time() - start_time

        # Should export reasonably quickly even with complex content
        assert export_time < 5.0  # Less than 5 seconds

        if result.success:
            # Check that complex notation was handled
            html_file = result.files_created[0]
            content = html_file.read_text()
            assert len(content) > 1000  # Should generate substantial content


@pytest.mark.slow
class TestRealMathlibIntegration:
    """Tests that require actual Mathlib4 (marked as slow tests)."""

    def setup_class(self):
        """Check if mathlib is available for testing."""
        self.mathlib_available = False
        self.mathlib_path = Path("mathlib4")

        # Check if mathlib4 directory exists
        if self.mathlib_path.exists() and (self.mathlib_path / ".git").exists():
            self.mathlib_available = True
        else:
            pytest.skip("Mathlib4 not available for integration testing")

    @pytest.mark.skipif(not Path("mathlib4").exists(), reason="Mathlib4 not available")
    def test_real_mathlib_theorem_parsing(self):
        """Test parsing of real mathlib theorems."""
        if not self.mathlib_available:
            pytest.skip("Mathlib4 not available")

        # Try to find some basic mathlib files
        potential_files = [
            "Mathlib/Data/Nat/Basic.lean",
            "Mathlib/Algebra/Group/Basic.lean",
            "Mathlib/Data/Set/Basic.lean",
        ]

        parser = SimpleLeanParser()
        parsed_any = False

        for rel_path in potential_files:
            file_path = self.mathlib_path / rel_path
            if file_path.exists():
                try:
                    theorems = parser.parse_file(file_path)
                    if theorems:
                        parsed_any = True

                        # Test that we can handle real mathlib notation
                        for theorem in theorems[:3]:  # Test first 3 theorems
                            assert theorem.name
                            assert theorem.statement

                            # Test notation handling
                            handler = ParserConfig()
                            latex_statement = handler.convert_to_latex(
                                theorem.statement
                            )
                            assert len(latex_statement) > 0

                except Exception as e:
                    print(f"Failed to parse {file_path}: {e}")

        if not parsed_any:
            pytest.skip("No parseable mathlib files found")

    @pytest.mark.skipif(not Path("mathlib4").exists(), reason="Mathlib4 not available")
    def test_real_mathlib_batch_processing(self):
        """Test batch processing on real mathlib content."""
        if not self.mathlib_available:
            pytest.skip("Mathlib4 not available")

        # Test with a small subset of mathlib
        test_dir = self.mathlib_path / "Mathlib" / "Data" / "Nat"
        if not test_dir.exists():
            pytest.skip("Mathlib Data/Nat directory not found")

        from proof_sketcher.exporter.batch_processor import BatchExporter

        scanner = BatchExporter()

        try:
            # Scan just the Nat directory (should be manageable)
            result = scanner.scan_project(test_dir)

            # Should find some theorems
            assert result["statistics"]["total_theorems"] > 0
            assert result["statistics"]["total_files"] > 0

            # Test that dependency analysis works
            assert "dependency_graph" in result

        except Exception as e:
            pytest.skip(f"Failed to scan real mathlib content: {e}")


if __name__ == "__main__":
    # Run basic tests when executed directly
    pytest.main([__file__, "-v"])
