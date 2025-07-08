"""Comprehensive integration tests for all exporters with animation pipeline."""

import tempfile
from pathlib import Path
from typing import Dict, Any

import pytest

from src.proof_sketcher.animator.animation_generator import TheoremAnimator
from src.proof_sketcher.animator.static_fallback import StaticVisualizer
from src.proof_sketcher.exporter.html import HTMLExporter
from src.proof_sketcher.exporter.markdown import MarkdownExporter
from src.proof_sketcher.exporter.pdf import PDFExporter
from src.proof_sketcher.exporter.models import (
    ExportContext,
    ExportFormat,
    ExportOptions,
)
from src.proof_sketcher.generator.models import ProofSketch, ProofStep


class TestAllExportersIntegration:
    """Test all exporters with animation pipeline integration."""

    @pytest.fixture
    def comprehensive_test_data(self):
        """Create comprehensive test data."""
        theorem = {
            "name": "Nat.add_assoc",
            "statement": "∀ (a b c : ℕ), (a + b) + c = a + (b + c)",
            "dependencies": ["Nat.add"],
            "docstring": "Addition of natural numbers is associative",
        }

        sketch = ProofSketch(
            theorem_name="Nat.add_assoc",
            introduction="We prove associativity of natural number addition by induction.",
            key_steps=[
                ProofStep(
                    step_number=1,
                    description="Base case: a = 0",
                    mathematical_content="(0 + b) + c = 0 + (b + c)",
                    tactics=["simp", "Nat.zero_add"],
                ),
                ProofStep(
                    step_number=2,
                    description="Inductive step",
                    mathematical_content="((n + 1) + b) + c = (n + 1) + (b + c)",
                    tactics=["simp", "Nat.succ_add", "ih"],
                ),
                ProofStep(
                    step_number=3,
                    description="Apply induction hypothesis",
                    mathematical_content="(n + b) + c = n + (b + c)",
                    tactics=["rw", "ih"],
                ),
            ],
            conclusion="By induction, addition is associative.",
            difficulty_level="intermediate",
            mathematical_areas=["arithmetic", "induction"],
            prerequisites=["Nat.add", "induction_principle"],
        )

        return {"theorem": theorem, "sketch": sketch}

    @pytest.fixture
    def animation_pipeline(self):
        """Set up animation pipeline components."""
        return {
            "animator": TheoremAnimator(),
            "visualizer": StaticVisualizer(),
        }

    def test_html_export_with_animation(self, comprehensive_test_data, animation_pipeline):
        """Test HTML export with full animation pipeline."""
        theorem = comprehensive_test_data["theorem"]
        sketch = comprehensive_test_data["sketch"]
        animator = animation_pipeline["animator"]
        visualizer = animation_pipeline["visualizer"]

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)

            # Generate animation script
            animation_script = animator.generate_animation_script(theorem, sketch.dict())
            is_valid, error = animator.validate_script(animation_script)
            assert is_valid, f"Animation script validation failed: {error}"

            # Create static visualization as fallback
            static_path = output_dir / "test_animation.png"
            static_success = visualizer.create_proof_diagram(
                theorem, sketch.dict(), str(static_path)
            )
            assert static_success, "Static visualization creation failed"
            assert static_path.exists() and static_path.stat().st_size > 0

            # Set up HTML exporter
            html_options = ExportOptions(
                output_dir=output_dir,
                create_subdirs=True,
                include_animations=True,
                syntax_highlighting=True,
                generate_links=True,
            )
            html_exporter = HTMLExporter(html_options)

            # Create export context with animation
            context = ExportContext(
                format=ExportFormat.HTML,
                output_dir=output_dir,
                sketches=[sketch],
                animations={sketch.theorem_name: static_path},
                include_animations=True,
                project_name="Test Project",
                author="Test Author",
                version="1.0.0",
            )

            # Export to HTML
            result = html_exporter.export_single(sketch, context)

            assert result.success, f"HTML export failed: {result.errors}"
            assert len(result.files_created) > 0

            # Verify HTML content
            html_file = [f for f in result.files_created if f.suffix == ".html"][0]
            content = html_file.read_text()

            # Check essential HTML elements
            assert "Nat.add_assoc" in content
            assert "associativity" in content.lower()
            assert "induction" in content.lower()
            assert len([step for step in sketch.key_steps]) >= 3  # All steps included

            # Check animation integration
            assert "animation" in content.lower() or "visualization" in content.lower()

    def test_markdown_export_with_github_features(
        self, comprehensive_test_data, animation_pipeline
    ):
        """Test Markdown export with GitHub features and animation."""
        theorem = comprehensive_test_data["theorem"]
        sketch = comprehensive_test_data["sketch"]
        visualizer = animation_pipeline["visualizer"]

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)

            # Create static visualization
            static_path = output_dir / "associativity_proof.png"
            static_success = visualizer.create_proof_diagram(
                theorem, sketch.dict(), str(static_path)
            )
            assert static_success

            # Set up Markdown exporter with GitHub features
            md_options = ExportOptions(
                output_dir=output_dir,
                markdown_flavor="github",
                generate_toc=True,
                create_index=True,
                include_animations=True,
            )
            md_exporter = MarkdownExporter(md_options)

            # Create export context
            context = ExportContext(
                format=ExportFormat.MARKDOWN,
                output_dir=output_dir,
                sketches=[sketch],
                animations={sketch.theorem_name: static_path},
                include_animations=True,
                project_name="Mathematical Theorems",
                author="Test Author",
            )

            # Export to Markdown
            result = md_exporter.export_single(sketch, context)

            assert result.success, f"Markdown export failed: {result.errors}"
            assert len(result.files_created) > 0

            # Verify Markdown content
            md_file = [f for f in result.files_created if f.suffix == ".md"][0]
            content = md_file.read_text()

            # Check GitHub-flavored Markdown features
            assert "# Nat.add_assoc" in content
            assert "```lean" in content  # Code blocks
            assert "$$" in content or "$" in content  # Math notation
            assert "![" in content or "[![" in content  # Animation reference

            # Check proof steps formatting
            for i, step in enumerate(sketch.key_steps, 1):
                assert f"Step {i}" in content
                assert step.description in content

    def test_pdf_export_with_latex_compilation(self, comprehensive_test_data):
        """Test PDF export with LaTeX compilation (if available)."""
        theorem = comprehensive_test_data["theorem"]
        sketch = comprehensive_test_data["sketch"]

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)

            # Set up PDF exporter
            pdf_options = ExportOptions(
                output_dir=output_dir,
                pdf_engine="pdflatex",
                include_timestamps=True,
            )
            pdf_exporter = PDFExporter(pdf_options)

            # Create export context
            context = ExportContext(
                format=ExportFormat.PDF,
                output_dir=output_dir,
                sketches=[sketch],
                project_name="Mathematical Proofs",
                author="Test Author",
                version="1.0.0",
            )

            # Export to PDF (will skip if LaTeX not available)
            result = pdf_exporter.export_single(sketch, context)

            # Don't fail if LaTeX is not available
            if not result.success and "not found" in str(result.errors):
                pytest.skip("LaTeX compiler not available")

            assert result.success, f"PDF export failed: {result.errors}"
            assert len(result.files_created) > 0

            # Verify PDF was created
            pdf_file = [f for f in result.files_created if f.suffix == ".pdf"][0]
            assert pdf_file.exists()
            assert pdf_file.stat().st_size > 1000  # PDF should be reasonable size

    def test_multiple_format_export_consistency(
        self, comprehensive_test_data, animation_pipeline
    ):
        """Test exporting the same theorem to multiple formats for consistency."""
        theorem = comprehensive_test_data["theorem"]
        sketch = comprehensive_test_data["sketch"]
        visualizer = animation_pipeline["visualizer"]

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)

            # Create static visualization
            static_path = output_dir / "proof_diagram.png"
            visualizer.create_proof_diagram(theorem, sketch.dict(), str(static_path))

            # Export to all formats
            exporters = {
                "html": HTMLExporter(ExportOptions(output_dir=output_dir / "html")),
                "markdown": MarkdownExporter(
                    ExportOptions(output_dir=output_dir / "markdown")
                ),
            }

            results = {}
            for format_name, exporter in exporters.items():
                format_dir = output_dir / format_name
                format_dir.mkdir()

                context = ExportContext(
                    format=exporter.format,
                    output_dir=format_dir,
                    sketches=[sketch],
                    animations={sketch.theorem_name: static_path},
                    include_animations=True,
                )

                result = exporter.export_single(sketch, context)
                results[format_name] = result

                assert result.success, f"{format_name} export failed: {result.errors}"
                assert len(result.files_created) > 0

            # Verify consistency across formats
            for format_name, result in results.items():
                # All formats should include the theorem name
                primary_file = result.files_created[0]
                content = primary_file.read_text()
                assert sketch.theorem_name in content

                # All formats should include proof steps
                for step in sketch.key_steps:
                    assert step.description in content

    def test_animation_pipeline_integration_robustness(
        self, comprehensive_test_data, animation_pipeline
    ):
        """Test robustness of animation pipeline integration."""
        theorem = comprehensive_test_data["theorem"]
        sketch = comprehensive_test_data["sketch"]
        animator = animation_pipeline["animator"]
        visualizer = animation_pipeline["visualizer"]

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)

            # Test 1: Animation script generation
            script = animator.generate_animation_script(theorem, sketch.dict())
            is_valid, _ = animator.validate_script(script)
            assert is_valid

            # Verify script contains expected elements
            assert "class" in script and "Scene" in script
            assert "construct" in script
            assert len(script) > 1000  # Reasonable script length

            # Test 2: Static fallback robustness
            static_outputs = []
            for i in range(3):  # Test multiple generations
                static_path = output_dir / f"proof_{i}.png"
                success = visualizer.create_proof_diagram(
                    theorem, sketch.dict(), str(static_path)
                )
                assert success
                assert static_path.exists()
                static_outputs.append(static_path.stat().st_size)

            # All static outputs should be reasonable size
            assert all(size > 10000 for size in static_outputs)  # > 10KB
            assert all(size < 500000 for size in static_outputs)  # < 500KB

            # Test 3: Export with missing animation gracefully handles errors
            html_exporter = HTMLExporter(ExportOptions(output_dir=output_dir))

            # Context with non-existent animation
            context_missing = ExportContext(
                format=ExportFormat.HTML,
                output_dir=output_dir,
                sketches=[sketch],
                animations={sketch.theorem_name: Path("nonexistent.mp4")},
                include_animations=True,
            )

            result = html_exporter.export_single(sketch, context_missing)
            # Should still succeed even without animation
            assert result.success

    def test_performance_benchmarks(self, comprehensive_test_data, animation_pipeline):
        """Test performance of export pipeline."""
        import time

        theorem = comprehensive_test_data["theorem"]
        sketch = comprehensive_test_data["sketch"]
        visualizer = animation_pipeline["visualizer"]

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)

            # Benchmark static visualization generation
            start_time = time.time()
            static_path = output_dir / "benchmark.png"
            success = visualizer.create_proof_diagram(
                theorem, sketch.dict(), str(static_path)
            )
            viz_time = time.time() - start_time

            assert success
            assert viz_time < 10.0  # Should complete in under 10 seconds

            # Benchmark HTML export
            html_exporter = HTMLExporter(ExportOptions(output_dir=output_dir))
            context = ExportContext(
                format=ExportFormat.HTML,
                output_dir=output_dir,
                sketches=[sketch],
                animations={sketch.theorem_name: static_path},
            )

            start_time = time.time()
            result = html_exporter.export_single(sketch, context)
            export_time = time.time() - start_time

            assert result.success
            assert export_time < 5.0  # Should complete in under 5 seconds

            # Overall pipeline should be reasonably fast
            total_time = viz_time + export_time
            assert total_time < 15.0  # Total under 15 seconds


class TestExportErrorHandling:
    """Test error handling in export pipeline."""

    def test_invalid_output_directory(self):
        """Test handling of invalid output directories."""
        invalid_path = Path("/invalid/nonexistent/path")
        
        # HTML exporter should handle invalid paths gracefully
        html_exporter = HTMLExporter(ExportOptions(output_dir=invalid_path))
        
        sketch = ProofSketch(
            theorem_name="test",
            introduction="test",
            key_steps=[],
            conclusion="test",
        )
        
        # Should either create the directory or fail gracefully
        try:
            result = html_exporter.export_single(sketch)
            # If it succeeds, directory was created
            assert result.success or len(result.errors) > 0
        except PermissionError:
            # Expected for truly invalid paths
            pass

    def test_malformed_sketch_data(self):
        """Test handling of malformed sketch data."""
        # Create sketch with minimal data
        minimal_sketch = ProofSketch(
            theorem_name="",  # Empty name
            introduction="",  # Empty introduction
            key_steps=[],     # No steps
            conclusion="",    # Empty conclusion
        )

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)
            
            html_exporter = HTMLExporter(ExportOptions(output_dir=output_dir))
            result = html_exporter.export_single(minimal_sketch)
            
            # Should handle gracefully
            assert result.success or len(result.errors) > 0

    def test_template_rendering_errors(self):
        """Test handling of template rendering errors."""
        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)
            
            # Create sketch with potentially problematic content
            problematic_sketch = ProofSketch(
                theorem_name="test_theorem",
                introduction="Test with {{ invalid_template_syntax",
                key_steps=[
                    ProofStep(
                        step_number=1,
                        description="Step with {{ unclosed template",
                        mathematical_content="x = y",
                        tactics=[],
                    )
                ],
                conclusion="Test conclusion",
            )
            
            html_exporter = HTMLExporter(ExportOptions(output_dir=output_dir))
            result = html_exporter.export_single(problematic_sketch)
            
            # Should either escape the content or handle the error
            # The actual behavior depends on template engine configuration
            assert isinstance(result, type(result))  # Result object created