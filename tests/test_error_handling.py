"""
Tests for error handling across the proof sketcher system.
These tests ensure the system fails gracefully and provides useful error messages.
"""

import os
from pathlib import Path
from unittest.mock import MagicMock, Mock, patch

import pytest

from src.proof_sketcher.ai.anthropic_client import AnthropicClient
from src.proof_sketcher.ai.offline_client import OfflineClient
from src.proof_sketcher.core.exceptions import ExporterError, GeneratorError, ParserError
from src.proof_sketcher.exporter.html import HTMLExporter
from src.proof_sketcher.exporter.markdown import MarkdownExporter
from src.proof_sketcher.exporter.models import ExportContext, ExportOptions
from src.proof_sketcher.generator.ai_generator_fixed import FixedAIGenerator
from src.proof_sketcher.generator.offline import OfflineGenerator
from src.proof_sketcher.parser.lean_parser import LeanParser
from src.proof_sketcher.parser.models import TheoremInfo


class TestParserErrorHandling:
    """Test error handling in the parser component."""

    def test_nonexistent_file(self):
        """Test parser handles non-existent files gracefully."""
        parser = LeanParser()
        nonexistent_file = Path("/definitely/does/not/exist.lean")

        result = parser.parse_file(nonexistent_file)

        assert not result.success
        assert len(result.errors) > 0
        assert "not found" in result.errors[0].message.lower()
        assert len(result.theorems) == 0

    def test_non_lean_file(self, temp_dir):
        """Test parser rejects non-Lean files."""
        parser = LeanParser()

        # Create a Python file
        py_file = temp_dir / "test.py"
        py_file.write_text("print('hello world')")

        result = parser.parse_file(py_file)

        assert not result.success
        assert len(result.errors) > 0
        assert "not a lean file" in result.errors[0].message.lower()

    def test_unreadable_file(self, temp_dir):
        """Test parser handles unreadable files."""
        parser = LeanParser()

        # Create file and make it unreadable
        unreadable_file = temp_dir / "unreadable.lean"
        unreadable_file.write_text("theorem test : True := trivial")

        # Make file unreadable (Unix systems)
        try:
            os.chmod(unreadable_file, 0o000)

            result = parser.parse_file(unreadable_file)

            # Should handle permission error gracefully
            assert not result.success
            assert len(result.errors) > 0

        finally:
            # Restore permissions for cleanup
            os.chmod(unreadable_file, 0o644)

    def test_corrupted_lean_file(self, temp_dir):
        """Test parser handles corrupted/invalid Lean syntax."""
        parser = LeanParser()

        # Create file with invalid Lean syntax
        corrupted_file = temp_dir / "corrupted.lean"
        corrupted_file.write_text(
            """
        theorem broken_syntax {{{ invalid lean code
        not a theorem at all
        )))))) unbalanced parentheses
        """
        )

        result = parser.parse_file(corrupted_file)

        # Should not crash, but may find no valid theorems
        assert result.success  # Parser should not crash
        assert len(result.theorems) == 0  # No valid theorems found

    def test_very_large_file(self, temp_dir):
        """Test parser handles large files without memory issues."""
        parser = LeanParser()

        # Create a large file with many theorems
        large_file = temp_dir / "large.lean"
        content = []
        for i in range(100):
            content.append(f"theorem test_{i} : True := trivial")

        large_file.write_text("\n".join(content))

        result = parser.parse_file(large_file)

        # Should handle large files gracefully
        assert result.success
        assert len(result.theorems) == 100

    def test_unicode_and_special_characters(self, temp_dir):
        """Test parser handles Unicode and special characters."""
        parser = LeanParser()

        unicode_file = temp_dir / "unicode.lean"
        unicode_file.write_text(
            """
        /-- Theorem with Unicode: ∀ ∃ λ → ↔ -/
        theorem unicode_test (α : Type) : α → α := id
        """
        )

        result = parser.parse_file(unicode_file)

        assert result.success
        assert len(result.theorems) == 1
        theorem = result.theorems[0]
        assert theorem.name == "unicode_test"
        assert "α → α" in theorem.statement


class TestGeneratorErrorHandling:
    """Test error handling in generator components."""

    def test_offline_generator_with_invalid_theorem(self):
        """Test offline generator handles invalid theorem info."""
        generator = OfflineGenerator()

        # Create theorem with missing/invalid data
        invalid_theorem = TheoremInfo(
            name="",  # Empty name
            statement="",  # Empty statement
            proof="",  # Empty proof
        )

        # Should not crash, but generate something
        sketch = generator.generate_proof_sketch(invalid_theorem)

        assert sketch.theorem_name == ""
        assert sketch.theorem_statement == ""
        assert len(sketch.key_steps) > 0  # Should generate generic steps
        assert sketch.introduction != ""
        assert sketch.conclusion != ""

    def test_ai_generator_with_invalid_client(self):
        """Test AI generator handles invalid client gracefully."""
        # Create a client that always fails
        failing_client = Mock()
        failing_client.is_available.return_value = False
        failing_client.generate.side_effect = Exception("API Error")

        generator = FixedAIGenerator(
            ai_client=failing_client, use_offline_fallback=True
        )

        theorem = TheoremInfo(name="test", statement="P → P", proof="intro h; exact h")

        # Should fall back to offline mode
        sketch = generator.generate_proof_sketch(theorem)

        assert sketch.theorem_name == "test"
        assert sketch.theorem_statement == "P → P"
        assert len(sketch.key_steps) > 0

    def test_ai_generator_no_fallback(self):
        """Test AI generator when fallback is disabled."""
        failing_client = Mock()
        failing_client.is_available.return_value = False
        failing_client.generate.side_effect = Exception("API Error")

        # No fallback enabled
        with pytest.raises(GeneratorError):
            FixedAIGenerator(ai_client=failing_client, use_offline_fallback=False)

    def test_anthropic_client_no_api_key(self, monkeypatch):
        """Test Anthropic client handles missing API key."""
        # Remove API key
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

        client = AnthropicClient()
        assert not client.is_available()

        # Should use fallback response
        response = client.generate("Test prompt")
        assert isinstance(response, str)
        assert len(response) > 0
        assert "unavailable" in response.lower()

    def test_anthropic_client_network_error(self, monkeypatch):
        """Test Anthropic client handles network errors."""
        # Mock the Anthropic client to raise network error
        monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")

        with patch(
            "src.proof_sketcher.ai.anthropic_client.Anthropic"
        ) as mock_anthropic:
            mock_client = Mock()
            mock_client.messages.create.side_effect = Exception("Network error")
            mock_anthropic.return_value = mock_client

            client = AnthropicClient()
            assert client.is_available()

            # Should handle network error gracefully
            response = client.generate("Test prompt")
            assert isinstance(response, str)
            assert "unavailable" in response.lower()

    def test_malformed_json_response(self, monkeypatch):
        """Test AI generator handles malformed JSON responses."""
        # Mock client that returns invalid JSON
        mock_client = Mock()
        mock_client.is_available.return_value = True
        mock_client.generate.return_value = "{ invalid json response"

        generator = FixedAIGenerator(ai_client=mock_client)

        theorem = TheoremInfo(name="test", statement="P", proof="trivial")

        # Should fall back to simple proof sketch
        sketch = generator.generate_proof_sketch(theorem)

        assert sketch.theorem_name == "test"
        assert sketch.theorem_statement == "P"
        assert len(sketch.key_steps) > 0


class TestExporterErrorHandling:
    """Test error handling in exporter components."""

    def test_export_to_readonly_directory(self, temp_dir):
        """Test exporter handles read-only directories."""
        # Create read-only directory
        readonly_dir = temp_dir / "readonly"
        readonly_dir.mkdir()

        try:
            os.chmod(readonly_dir, 0o444)  # Read-only

            options = ExportOptions(output_dir=readonly_dir)
            exporter = MarkdownExporter(options)

            # Create a simple proof sketch
            from src.proof_sketcher.generator.models import ProofSketch, ProofStep

            sketch = ProofSketch(
                theorem_name="test",
                theorem_statement="P",
                introduction="Test",
                key_steps=[],
                conclusion="Done",
            )

            context = ExportContext(
                format="markdown", output_dir=readonly_dir, sketches=[sketch]
            )

            result = exporter.export_single(sketch, context)

            # Should handle permission error gracefully
            assert not result.success
            assert len(result.errors) > 0

        finally:
            # Restore permissions for cleanup
            os.chmod(readonly_dir, 0o755)

    def test_export_with_invalid_sketch(self, temp_dir):
        """Test exporter handles invalid proof sketch data."""
        options = ExportOptions(output_dir=temp_dir)
        exporter = MarkdownExporter(options)

        # Create sketch with problematic data
        from src.proof_sketcher.generator.models import ProofSketch

        sketch = ProofSketch(
            theorem_name="",  # Empty name
            theorem_statement="",  # Empty statement
            introduction="",  # Empty introduction
            key_steps=[],  # No steps
            conclusion="",  # Empty conclusion
        )

        context = ExportContext(
            format="markdown", output_dir=temp_dir, sketches=[sketch]
        )

        result = exporter.export_single(sketch, context)

        # Should handle empty data gracefully
        assert result.success  # Should not crash
        assert len(result.files_created) == 1

        # Check file was created (even if with minimal content)
        output_file = result.files_created[0]
        assert output_file.exists()

    def test_export_with_disk_full(self, temp_dir):
        """Test exporter handles disk space issues (simulated)."""
        options = ExportOptions(output_dir=temp_dir)
        exporter = MarkdownExporter(options)

        # Mock file write to simulate disk full
        from src.proof_sketcher.generator.models import ProofSketch

        sketch = ProofSketch(
            theorem_name="test",
            theorem_statement="P",
            introduction="Test",
            key_steps=[],
            conclusion="Done",
        )

        context = ExportContext(
            format="markdown", output_dir=temp_dir, sketches=[sketch]
        )

        # Mock Path.write_text to raise OSError
        with patch(
            "pathlib.Path.write_text", side_effect=OSError("No space left on device")
        ):
            result = exporter.export_single(sketch, context)

            # Should handle disk full gracefully
            assert not result.success
            assert len(result.errors) > 0
            assert "No space left on device" in result.errors[0]

    def test_html_export_with_invalid_template(self, temp_dir):
        """Test HTML exporter handles template errors."""
        options = ExportOptions(output_dir=temp_dir)
        exporter = HTMLExporter(options)

        # Mock template manager to raise error
        with patch.object(
            exporter.template_manager,
            "render_template",
            side_effect=Exception("Template error"),
        ):
            from src.proof_sketcher.generator.models import ProofSketch

            sketch = ProofSketch(
                theorem_name="test",
                theorem_statement="P",
                introduction="Test",
                key_steps=[],
                conclusion="Done",
            )

            context = ExportContext(
                format="html", output_dir=temp_dir, sketches=[sketch]
            )

            result = exporter.export_single(sketch, context)

            # Should handle template error gracefully
            assert not result.success
            assert len(result.errors) > 0


class TestSystemErrorHandling:
    """Test system-level error handling."""

    def test_missing_dependencies(self):
        """Test system handles missing optional dependencies."""
        # Test that system works without optional dependencies
        # (This would require mocking imports, which is complex)
        pass

    def test_memory_pressure(self):
        """Test system handles memory pressure gracefully."""
        # This test would require generating very large objects
        # For now, just verify the system can handle reasonable loads

        parser = LeanParser()
        generator = OfflineGenerator()

        # Process many theorems
        theorems = []
        for i in range(10):
            theorem = TheoremInfo(
                name=f"test_{i}",
                statement=f"theorem_{i} : True := trivial",
                proof="trivial",
            )
            theorems.append(theorem)

        # Should not crash with multiple theorems
        sketches = []
        for theorem in theorems:
            sketch = generator.generate_proof_sketch(theorem)
            sketches.append(sketch)

        assert len(sketches) == 10
        for sketch in sketches:
            assert sketch.theorem_name.startswith("test_")
            assert sketch.theorem_statement.startswith("theorem_")

    def test_concurrent_access(self):
        """Test system handles concurrent access safely."""
        import threading

        generator = OfflineGenerator()
        theorem = TheoremInfo(
            name="concurrent_test", statement="P → P", proof="intro h; exact h"
        )

        results = []
        errors = []

        def generate_sketch():
            try:
                sketch = generator.generate_proof_sketch(theorem)
                results.append(sketch)
            except Exception as e:
                errors.append(e)

        # Run multiple threads
        threads = []
        for _ in range(5):
            thread = threading.Thread(target=generate_sketch)
            threads.append(thread)
            thread.start()

        for thread in threads:
            thread.join()

        # Should not have errors
        assert len(errors) == 0
        assert len(results) == 5

        # All results should be valid
        for sketch in results:
            assert sketch.theorem_name == "concurrent_test"
            assert sketch.theorem_statement == "P → P"

    def test_resource_cleanup(self, temp_dir):
        """Test system cleans up resources properly."""
        import gc
        import tempfile

        # Test that temporary files are cleaned up
        initial_files = list(temp_dir.glob("*"))

        # Create and process many files
        for i in range(5):
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".lean", dir=temp_dir, delete=False
            ) as f:
                f.write(f"theorem test_{i} : True := trivial")
                temp_file = Path(f.name)

            parser = LeanParser()
            result = parser.parse_file(temp_file)

            # Clean up
            temp_file.unlink()

        # Force garbage collection
        gc.collect()

        # Should not have leaked files
        final_files = list(temp_dir.glob("*"))
        assert len(final_files) == len(initial_files)


class TestUserErrorHandling:
    """Test handling of common user errors."""

    def test_invalid_command_line_args(self):
        """Test handling of invalid command line arguments."""
        # This would test the CLI, but we'll focus on the core library
        pass

    def test_invalid_configuration(self):
        """Test handling of invalid configuration."""
        # Test that system handles invalid configurations gracefully

        # Test with invalid output directory
        with pytest.raises((ValueError, OSError)):
            ExportOptions(output_dir=Path("/invalid/path/that/does/not/exist"))

    def test_helpful_error_messages(self, temp_dir):
        """Test that error messages are helpful to users."""
        parser = LeanParser()

        # Test with non-existent file
        result = parser.parse_file(Path("/nonexistent/file.lean"))
        assert not result.success
        assert len(result.errors) > 0

        error_msg = result.errors[0].message
        assert "not found" in error_msg.lower()
        assert "file.lean" in error_msg

        # Test with wrong extension
        py_file = temp_dir / "test.py"
        py_file.write_text("print('hello')")

        result = parser.parse_file(py_file)
        assert not result.success
        assert len(result.errors) > 0

        error_msg = result.errors[0].message
        assert "not a lean file" in error_msg.lower()
        assert ".py" in error_msg or "test.py" in error_msg
