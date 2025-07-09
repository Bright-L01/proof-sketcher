"""
Real integration tests for the complete proof sketcher pipeline.
These tests verify that the entire system works together correctly.
"""

from pathlib import Path

import pytest

from src.proof_sketcher.ai.anthropic_client import AnthropicClient
from src.proof_sketcher.ai.offline_client import OfflineClient
from src.proof_sketcher.exporter.html import HTMLExporter
from src.proof_sketcher.exporter.markdown import MarkdownExporter
from src.proof_sketcher.exporter.models import ExportContext, ExportOptions
from src.proof_sketcher.generator.ai_generator_fixed import FixedAIGenerator
from src.proof_sketcher.generator.offline import OfflineGenerator
from src.proof_sketcher.parser.lean_parser import LeanParser


class TestEndToEndPipeline:
    """Test the complete pipeline from parsing to export."""

    def test_parse_generate_export_offline(self, sample_lean_file, output_dir):
        """Test complete pipeline with offline generation."""
        # 1. Parse Lean file
        parser = LeanParser()
        parse_result = parser.parse_file(sample_lean_file)

        # Verify parsing worked
        assert parse_result.success
        assert len(parse_result.theorems) == 1

        theorem = parse_result.theorems[0]
        assert theorem.name == "add_comm"
        assert theorem.statement != ""
        assert theorem.statement != "Unknown"
        assert "a + b = b + a" in theorem.statement

        # 2. Generate explanation
        generator = OfflineGenerator()
        sketch = generator.generate_proof_sketch(theorem)

        # Verify generation worked
        assert sketch.theorem_name == "add_comm"
        assert sketch.theorem_statement != ""
        assert sketch.theorem_statement == theorem.statement
        assert len(sketch.introduction) > 0
        assert len(sketch.key_steps) > 0
        assert len(sketch.conclusion) > 0

        # 3. Export to markdown
        options = ExportOptions(output_dir=output_dir)
        exporter = MarkdownExporter(options)
        context = ExportContext(
            format="markdown", output_dir=output_dir, sketches=[sketch]
        )

        result = exporter.export_single(sketch, context)

        # Verify export worked
        assert result.success
        assert len(result.files_created) == 1

        output_file = result.files_created[0]
        assert output_file.exists()
        assert output_file.suffix == ".md"

        # 4. Verify output content
        content = output_file.read_text()
        assert theorem.name in content
        assert theorem.statement in content
        assert sketch.introduction in content
        assert "## Statement" in content
        assert "## Explanation" in content
        assert "## Proof Steps" in content

        # Check that statement is NOT empty
        assert "```lean\n\n```" not in content  # No empty code blocks
        assert "```lean\n" + theorem.statement in content

    def test_parse_generate_export_ai(
        self, sample_lean_file, output_dir, mock_anthropic_client
    ):
        """Test complete pipeline with AI generation."""
        # 1. Parse
        parser = LeanParser()
        parse_result = parser.parse_file(sample_lean_file)
        assert parse_result.success
        theorem = parse_result.theorems[0]

        # 2. Generate with AI
        generator = FixedAIGenerator(ai_client=mock_anthropic_client)
        sketch = generator.generate_proof_sketch(theorem)

        # Verify AI generation
        assert sketch.theorem_name == "add_comm"
        assert sketch.theorem_statement == theorem.statement
        assert len(sketch.key_steps) > 0

        # 3. Export to HTML
        options = ExportOptions(output_dir=output_dir)
        exporter = HTMLExporter(options)
        context = ExportContext(format="html", output_dir=output_dir, sketches=[sketch])

        result = exporter.export_single(sketch, context)
        assert result.success

        # 4. Verify HTML output
        html_file = result.files_created[0]
        assert html_file.exists()
        assert html_file.suffix == ".html"

        content = html_file.read_text()
        assert theorem.name in content
        assert theorem.statement in content
        # HTML should escape the statement properly
        assert "∀" in content or "&forall;" in content

    def test_multiple_theorems_pipeline(self, complex_lean_file, output_dir):
        """Test pipeline with multiple theorems."""
        # 1. Parse multiple theorems
        parser = LeanParser()
        parse_result = parser.parse_file(complex_lean_file)

        assert parse_result.success
        assert len(parse_result.theorems) >= 2  # At least zero_add and mul_add

        # Verify all theorems have non-empty statements
        for theorem in parse_result.theorems:
            assert theorem.statement != ""
            assert theorem.statement != "Unknown"
            assert theorem.name != ""

        # 2. Generate explanations for all
        generator = OfflineGenerator()
        sketches = []

        for theorem in parse_result.theorems:
            sketch = generator.generate_proof_sketch(theorem)
            assert sketch.theorem_statement == theorem.statement
            sketches.append(sketch)

        # 3. Export all sketches
        options = ExportOptions(output_dir=output_dir)
        exporter = MarkdownExporter(options)
        context = ExportContext(
            format="markdown", output_dir=output_dir, sketches=sketches
        )

        result = exporter.export_multiple(sketches, context)
        assert result.success

        # Should create one file per theorem
        assert len(result.files_created) >= len(sketches)

        # Verify each file contains correct content
        for i, sketch in enumerate(sketches):
            # Find the file for this theorem
            theorem_file = None
            for file in result.files_created:
                if sketch.theorem_name in file.name:
                    theorem_file = file
                    break

            assert (
                theorem_file is not None
            ), f"No file found for theorem {sketch.theorem_name}"
            assert theorem_file.exists()

            content = theorem_file.read_text()
            assert sketch.theorem_name in content
            assert sketch.theorem_statement in content
            assert sketch.introduction in content

    def test_error_recovery_pipeline(self, malformed_lean_file, output_dir):
        """Test pipeline behavior with malformed input."""
        # 1. Parse malformed file
        parser = LeanParser()
        parse_result = parser.parse_file(malformed_lean_file)

        # Should handle gracefully
        if not parse_result.success:
            assert len(parse_result.errors) > 0
            return  # Expected failure

        # If parsing succeeds partially, test that we can still process
        if parse_result.theorems:
            generator = OfflineGenerator()

            for theorem in parse_result.theorems:
                # Even malformed theorems should not crash the generator
                try:
                    sketch = generator.generate_proof_sketch(theorem)
                    assert sketch.theorem_name == theorem.name
                    assert sketch.theorem_statement == theorem.statement
                except Exception as e:
                    pytest.fail(f"Generator crashed on theorem {theorem.name}: {e}")

    def test_empty_file_pipeline(self, empty_lean_file, output_dir):
        """Test pipeline with empty file."""
        parser = LeanParser()
        parse_result = parser.parse_file(empty_lean_file)

        assert parse_result.success
        assert len(parse_result.theorems) == 0
        assert len(parse_result.errors) == 0

        # Should be able to export empty results
        options = ExportOptions(output_dir=output_dir)
        exporter = MarkdownExporter(options)
        context = ExportContext(format="markdown", output_dir=output_dir, sketches=[])

        result = exporter.export_multiple([], context)
        assert result.success

    def test_batch_processing(self, sample_files, output_dir):
        """Test processing multiple files in batch."""
        parser = LeanParser()
        all_theorems = []

        # Parse all files
        for file in sample_files:
            parse_result = parser.parse_file(file)
            assert parse_result.success
            all_theorems.extend(parse_result.theorems)

        # Should have found theorems in all files
        assert len(all_theorems) >= len(sample_files)

        # Generate explanations for all
        generator = OfflineGenerator()
        all_sketches = []

        for theorem in all_theorems:
            sketch = generator.generate_proof_sketch(theorem)
            assert sketch.theorem_statement == theorem.statement
            all_sketches.append(sketch)

        # Export all together
        options = ExportOptions(output_dir=output_dir)
        exporter = MarkdownExporter(options)
        context = ExportContext(
            format="markdown", output_dir=output_dir, sketches=all_sketches
        )

        result = exporter.export_multiple(all_sketches, context)
        assert result.success

        # Should create files for all theorems
        assert len(result.files_created) >= len(all_sketches)

        # Verify no empty statements made it through
        for file in result.files_created:
            if file.suffix == ".md":
                content = file.read_text()
                # Should not have empty code blocks
                assert "```lean\n\n```" not in content
                assert "```lean\n\n\n```" not in content


class TestComponentIntegration:
    """Test integration between specific components."""

    def test_parser_generator_integration(self, sample_theorem):
        """Test parser output works with generator input."""
        # Offline generator
        offline_gen = OfflineGenerator()
        offline_sketch = offline_gen.generate_proof_sketch(sample_theorem)

        assert offline_sketch.theorem_name == sample_theorem.name
        assert offline_sketch.theorem_statement == sample_theorem.statement
        assert len(offline_sketch.key_steps) > 0

        # AI generator with offline client
        ai_gen = FixedAIGenerator(ai_client=OfflineClient())
        ai_sketch = ai_gen.generate_proof_sketch(sample_theorem)

        assert ai_sketch.theorem_name == sample_theorem.name
        assert ai_sketch.theorem_statement == sample_theorem.statement
        assert len(ai_sketch.key_steps) > 0

    def test_generator_exporter_integration(self, sample_proof_sketch, output_dir):
        """Test generator output works with exporter input."""
        # Test with markdown exporter
        options = ExportOptions(output_dir=output_dir)
        md_exporter = MarkdownExporter(options)
        context = ExportContext(
            format="markdown", output_dir=output_dir, sketches=[sample_proof_sketch]
        )

        result = md_exporter.export_single(sample_proof_sketch, context)
        assert result.success

        md_file = result.files_created[0]
        content = md_file.read_text()
        assert sample_proof_sketch.theorem_name in content
        assert sample_proof_sketch.theorem_statement in content
        assert sample_proof_sketch.introduction in content

        # Test with HTML exporter
        html_exporter = HTMLExporter(options)
        html_context = ExportContext(
            format="html", output_dir=output_dir, sketches=[sample_proof_sketch]
        )

        result = html_exporter.export_single(sample_proof_sketch, html_context)
        assert result.success

        html_file = result.files_created[0]
        content = html_file.read_text()
        assert sample_proof_sketch.theorem_name in content
        assert sample_proof_sketch.theorem_statement in content

    def test_ai_client_integration(self, sample_theorem):
        """Test AI client integration."""
        # Test offline client
        offline_client = OfflineClient()
        assert offline_client.is_available()

        response = offline_client.generate("Explain this theorem")
        assert isinstance(response, str)
        assert len(response) > 0

        # Test Anthropic client without API key
        anthropic_client = AnthropicClient()
        assert not anthropic_client.is_available()  # No API key

        # Should still work with fallback
        response = anthropic_client.generate("Explain this theorem")
        assert isinstance(response, str)
        assert len(response) > 0
        assert "unavailable" in response


class TestRegressionTests:
    """Test for specific bugs that were previously fixed."""

    def test_empty_statement_bug_fixed(self, sample_lean_file):
        """
        Regression test for DEBT-001: Empty theorem statements.
        This was the critical bug where theorem statements were empty.
        """
        parser = LeanParser()
        parse_result = parser.parse_file(sample_lean_file)

        assert parse_result.success
        assert len(parse_result.theorems) == 1

        theorem = parse_result.theorems[0]

        # CRITICAL: These should NOT be empty
        assert theorem.statement != ""
        assert theorem.statement != "Unknown"
        assert theorem.statement is not None

        # Should contain actual mathematical content
        assert "a + b = b + a" in theorem.statement
        assert "Nat" in theorem.statement

        # Test through the complete pipeline
        generator = OfflineGenerator()
        sketch = generator.generate_proof_sketch(theorem)

        # Sketch should preserve the statement
        assert sketch.theorem_statement == theorem.statement
        assert sketch.theorem_statement != ""

        # Export should include the statement
        import tempfile

        from src.proof_sketcher.exporter.markdown import MarkdownExporter
        from src.proof_sketcher.exporter.models import ExportContext, ExportOptions

        with tempfile.TemporaryDirectory() as tmpdir:
            options = ExportOptions(output_dir=Path(tmpdir))
            exporter = MarkdownExporter(options)
            context = ExportContext(
                format="markdown", output_dir=Path(tmpdir), sketches=[sketch]
            )

            result = exporter.export_single(sketch, context)
            assert result.success

            output_file = result.files_created[0]
            content = output_file.read_text()

            # Should NOT have empty code blocks
            assert "```lean\n\n```" not in content
            assert "```lean\n\n\n```" not in content

            # Should have the actual statement
            assert theorem.statement in content

    def test_ai_client_fallback_works(self, sample_theorem):
        """Test that AI client fallback works when API unavailable."""
        # Test with no API key
        generator = FixedAIGenerator()  # Will use offline fallback
        sketch = generator.generate_proof_sketch(sample_theorem)

        assert sketch.theorem_name == sample_theorem.name
        assert sketch.theorem_statement == sample_theorem.statement
        assert len(sketch.key_steps) > 0

        # Should work even without AI
        assert sketch.introduction != ""
        assert sketch.conclusion != ""

    def test_parser_handles_various_formats(self, temp_dir):
        """Test parser handles different Lean theorem formats."""
        test_cases = [
            # Simple theorem
            "theorem simple : True := trivial",
            # Theorem with parameters
            "theorem with_params (n : Nat) : n = n := by rfl",
            # Theorem with complex statement
            "theorem complex (a b c : Nat) : (a + b) + c = a + (b + c) := by ring",
            # Lemma instead of theorem
            "lemma test_lemma : 1 + 1 = 2 := by norm_num",
            # With docstring
            "/-- Test docstring -/\ntheorem with_doc : True := trivial",
        ]

        parser = LeanParser()

        for i, content in enumerate(test_cases):
            test_file = temp_dir / f"test_{i}.lean"
            test_file.write_text(content)

            result = parser.parse_file(test_file)
            assert result.success, f"Failed to parse: {content}"
            assert (
                len(result.theorems) == 1
            ), f"Expected 1 theorem, got {len(result.theorems)} for: {content}"

            theorem = result.theorems[0]
            assert theorem.statement != "", f"Empty statement for: {content}"
            assert theorem.statement != "Unknown", f"Unknown statement for: {content}"
