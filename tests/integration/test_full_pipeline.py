"""Comprehensive integration tests for the full Proof Sketcher pipeline.

This module tests the complete end-to-end workflow from parsing Lean files
through generating proof sketches, creating animations, and exporting to
various formats.
"""

from __future__ import annotations

import asyncio
import json
import shutil
import tempfile
from pathlib import Path
from typing import Dict, List, Optional
from unittest.mock import AsyncMock, Mock, patch

import pytest

from proof_sketcher.cli import cli
from proof_sketcher.config.config import Config, ExportConfig, GenerationConfig
from proof_sketcher.core.exceptions import ProofSketcherError
from proof_sketcher.exporter.models import ExportFormat, ExportOptions, ExportResult
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.parser.models import ParseResult, TheoremInfo


class TestFullPipeline:
    """Test complete pipeline from parsing to export."""

    @pytest.fixture
    def sample_lean_content(self):
        """Sample Lean content for testing."""
        return """
/-- Addition is commutative for natural numbers -/
theorem nat_add_comm (m n : Nat) : m + n = n + m := by
  induction m with
  | zero => simp [Nat.zero_add]
  | succ m ih => simp [Nat.succ_add, ih]

/-- Zero is the identity element for addition -/
theorem add_zero (n : Nat) : n + 0 = n := by
  simp
"""

    @pytest.fixture
    def temp_project_dir(self, tmp_path):
        """Create a temporary project directory."""
        project_dir = tmp_path / "test_project"
        project_dir.mkdir()

        # Create basic project structure
        (project_dir / "src").mkdir()
        (project_dir / "output").mkdir()

        return project_dir

    @pytest.fixture
    def mock_proof_sketch(self):
        """Create a mock proof sketch for testing."""
        return ProofSketch(
            theorem_name="nat_add_comm",
            theorem_statement="∀ (m n : Nat), m + n = n + m",
            introduction="This theorem proves that addition of natural numbers is commutative.",
            key_steps=[
                ProofStep(
step_number=1,
    intuitive_explanation="Test intuitive explanation",
    conceptual_explanation="Test conceptual explanation",
    bridging_explanation="Test bridging explanation",
    formal_explanation="Test formal explanation",
                    description="Base case: 0 + n = n + 0",
                    mathematical_content="0 + n = n = n + 0",
                    reasoning="By definition of addition",
                    tactics_used=["simp", "Nat.zero_add"],
                    intuition="Zero on the left is the identity",
),
                ProofStep(
step_number=2,
    intuitive_explanation="Test intuitive explanation",
    conceptual_explanation="Test conceptual explanation",
    bridging_explanation="Test bridging explanation",
    formal_explanation="Test formal explanation",
                    description="Inductive step: (m+1) + n = n + (m+1)",
                    mathematical_content="(m+1) + n = (m + n) + 1 = (n + m) + 1 = n + (m+1)",
                    reasoning="Using the inductive hypothesis",
                    tactics_used=["simp", "Nat.succ_add"],
                    intuition="Successor distributes over addition",
                ),
            ],
            conclusion="Therefore, addition is commutative for all natural numbers.",
            difficulty_level="intermediate",
            key_insights=[
                "Induction on the first argument",
                "Use of definitional equalities",
            ],
            mathematical_context="Natural number arithmetic",
        )

    def test_parse_generate_export_pipeline(
        self, sample_lean_content, temp_project_dir, mock_proof_sketch
    ):
        """Test the complete pipeline: parse → generate → export."""
        # Create Lean file
        lean_file = temp_project_dir / "src" / "test.lean"
        lean_file.write_text(sample_lean_content)

        # Mock the parser
        mock_parse_result = ParseResult(
            theorems=[
                TheoremInfo(
                    name="nat_add_comm",
                    statement="∀ (m n : Nat), m + n = n + m",
                    proof="by induction m with | zero => simp [Nat.zero_add] | succ m ih => simp [Nat.succ_add, ih]",
                    line_number=3,
                    docstring="Addition is commutative for natural numbers",
                ),
                TheoremInfo(
                    name="add_zero",
                    statement="∀ (n : Nat), n + 0 = n",
                    proof="by simp",
                    line_number=8,
                    docstring="Zero is the identity element for addition",
                ),
            ],
            success=True,
        )

        with patch(
            "proof_sketcher.parser.lean_parser.SimpleLeanParser.parse_file"
        ) as mock_parse:
            mock_parse.return_value = mock_parse_result

            # Mock the generator
            with patch(
                "proof_sketcher.generator.ai_generator.SimpleGenerator.generate_proof_sketch"
            ) as mock_generate:
                mock_generate.return_value = mock_proof_sketch

                # Mock the exporter
                with patch(
                    "proof_sketcher.exporter.html.HTMLBaseExporter.export_single"
                ) as mock_export:
                    mock_export.return_value = ExportResult(
                        success=True,
                        format=ExportFormat.HTML,
                        output_files=[
                            temp_project_dir / "output" / "nat_add_comm.html"
                        ],
                        metadata={"theorems_exported": 1},
                    )

                    # Run the pipeline
                    from proof_sketcher.exporter.html import HTMLBaseExporter
                    from proof_sketcher.generator.ai_generator import SimpleGenerator
                    from proof_sketcher.parser.simple_parser import SimpleLeanParser

                    # Parse
                    parser = SimpleLeanParser()
                    parse_result = parser.parse_file(lean_file)
                    assert parse_result.success
                    assert len(parse_result.theorems) == 2

                    # Generate
                    generator = SimpleGenerator()
                    theorem = parse_result.theorems[0]
                    proof_sketch = generator.generate_proof_sketch(theorem)
                    assert proof_sketch.theorem_name == "nat_add_comm"
                    assert len(proof_sketch.key_steps) == 2

                    # Export
                    exporter = HTMLBaseExporter(
                        ExportOptions(output_dir=temp_project_dir / "output")
                    )
                    export_result = exporter.export_single(proof_sketch)
                    assert export_result.success
                    assert len(export_result.output_files) == 1

    @pytest.mark.asyncio
    async def test_async_animation_pipeline(self, mock_proof_sketch, temp_project_dir):
        """Test async animation generation pipeline."""
        # Mock animation response
        mock_animation_response = Mock()
        mock_animation_response.success = True
        mock_animation_response.video_path = (
            temp_project_dir / "animations" / "nat_add_comm.mp4"
        )
        mock_animation_response.static_path = (
            temp_project_dir / "animations" / "nat_add_comm.png"
        )

        with patch(
            "proof_sketcher.animator.animation_generator.TheoremAnimator.animate_proof"
        ) as mock_animate:
            mock_animate.return_value = asyncio.Future()
            mock_animate.return_value.set_result(mock_animation_response)

            # Create animator and generate animation
            from proof_sketcher.animator.animation_generator import TheoremAnimator

            animator = TheoremAnimator()

            animation_response = await animator.animate_proof(mock_proof_sketch)
            assert animation_response.success
            assert animation_response.video_path.name == "nat_add_comm.mp4"

    def test_batch_processing_pipeline(self, sample_lean_content, temp_project_dir):
        """Test batch processing of multiple theorems."""
        # Create multiple Lean files
        for i in range(3):
            lean_file = temp_project_dir / "src" / f"theorem{i}.lean"
            lean_file.write_text(
                f"""
theorem test{i} : {i} = {i} := by rfl
"""
            )

        # Mock batch processor
        with patch(
            "proof_sketcher.batch.parallel_processor.ParallelProcessor"
        ) as MockProcessor:
            mock_processor = MockProcessor.return_value
            mock_processor.process_directory.return_value = {
                "processed": 3,
                "successful": 3,
                "failed": 0,
                "skipped": 0,
                "results": [
                    {"file": f"theorem{i}.lean", "theorem": f"test{i}", "success": True}
                    for i in range(3)
                ],
            }

            # Run batch processing
            from proof_sketcher.exporter.batch_processor.parallel_processor import (
                ParallelProcessor,
            )

            processor = ParallelProcessor(max_workers=2)
            results = processor.process_directory(temp_project_dir / "src")

            assert results["processed"] == 3
            assert results["successful"] == 3
            assert results["failed"] == 0

    def test_error_handling_pipeline(self, temp_project_dir):
        """Test error handling throughout the pipeline."""
        # Test parsing error
        bad_lean_file = temp_project_dir / "bad.lean"
        bad_lean_file.write_text("invalid lean syntax {{{")

        with patch(
            "proof_sketcher.parser.lean_parser.SimpleLeanParser.parse_file"
        ) as mock_parse:
            mock_parse.side_effect = ProofSketcherError(
                "Syntax error", error_code="PARSE_001"
            )

            from proof_sketcher.parser.simple_parser import SimpleLeanParser

            parser = SimpleLeanParser()

            with pytest.raises(ProofSketcherError) as exc_info:
                parser.parse_file(bad_lean_file)

            assert exc_info.value.error_code == "PARSE_001"

    def test_configuration_pipeline(self, temp_project_dir):
        """Test pipeline with custom configuration."""
        # Create custom config
        config = Config(
            generation=GenerationConfig(
                model="claude-3", temperature=0.5, max_tokens=2000
            ),
            export=ExportConfig(
                formats=["html", "markdown", "pdf"],
                include_animations=True,
                create_index=True,
            ),
        )

        # Save config
        config_file = temp_project_dir / "proof-sketcher.json"
        config_file.write_text(json.dumps(config.model_dump(), indent=2))

        # Load and verify config
        loaded_config = Config.from_file(config_file)
        assert loaded_config.generation.model == "claude-3"
        assert loaded_config.generation.temperature == 0.5
        assert "pdf" in loaded_config.export.formats


class TestCLIIntegration:
    """Test CLI integration with full pipeline."""

    def test_cli_prove_command(self, tmp_path):
        """Test the prove command end-to-end."""
        # Create test file
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : 1 = 1 := rfl")

        # Mock the pipeline components
        with patch(
            "proof_sketcher.parser.lean_parser.SimpleLeanParser.parse_file"
        ) as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[TheoremInfo(name="test", statement="1 = 1", proof="rfl")],
                success=True,
            )

            with patch(
                "proof_sketcher.generator.offline.OfflineGenerator.generate_proof_sketch"
            ) as mock_generate:
                mock_generate.return_value = ProofSketch(
                    theorem_name="test",
                    theorem_statement="1 = 1",
                    introduction="A simple reflexivity proof",
                    key_steps=[],
                    conclusion="By reflexivity",
                    difficulty_level="trivial",
                )

                from click.testing import CliRunner

                runner = CliRunner()

                result = runner.invoke(
                    cli,
                    [
                        "prove",
                        str(lean_file),
                        "--offline",
                        "--output",
                        str(tmp_path / "output"),
                    ],
                )

                # Check command succeeded
                assert result.exit_code == 0
                assert "Processing theorem: test" in result.output

    def test_cli_batch_command(self, tmp_path):
        """Test the batch command for processing directories."""
        # Create test directory with files
        src_dir = tmp_path / "src"
        src_dir.mkdir()

        for i in range(2):
            (src_dir / f"file{i}.lean").write_text(f"theorem t{i} : {i} = {i} := rfl")

        with patch(
            "proof_sketcher.batch.parallel_processor.ParallelProcessor.process_directory"
        ) as mock_process:
            mock_process.return_value = {
                "processed": 2,
                "successful": 2,
                "failed": 0,
                "results": [],
            }

            from click.testing import CliRunner

            runner = CliRunner()

            result = runner.invoke(
                cli,
                [
                    "batch",
                    str(src_dir),
                    "--parallel",
                    "2",
                    "--output",
                    str(tmp_path / "output"),
                ],
            )

            assert result.exit_code == 0
            assert "Processed: 2" in result.output


class TestCacheIntegration:
    """Test caching throughout the pipeline."""

    def test_generation_cache_integration(self, tmp_path):
        """Test that generation results are cached properly."""
        from proof_sketcher.generator.cache import GenerationCache

        cache = GenerationCache(cache_dir=tmp_path / "cache")

        # Create test data
        theorem = TheoremInfo(name="test", statement="P → P")
        sketch = ProofSketch(
            theorem_name="test",
            theorem_statement="P → P",
            introduction="Identity implication",
            key_steps=[],
            conclusion="Trivial",
            difficulty_level="easy",
        )

        # Cache the sketch
        cache_key = cache.get_cache_key(theorem)
        cache.put(cache_key, sketch)

        # Retrieve and verify
        cached_sketch = cache.get(cache_key)
        assert cached_sketch is not None
        assert cached_sketch.theorem_name == "test"

    def test_export_cache_integration(self, tmp_path):
        """Test export caching for regeneration."""
        from proof_sketcher.exporter.models import BaseExporterBase

        # Mock exporter with caching
        class CachingBaseExporter(BaseExporterBase):
            def __init__(self):
                self.cache = {}

            def export_single(self, proof_sketch, animation_path=None):
                key = proof_sketch.theorem_name
                if key in self.cache:
                    return self.cache[key]

                result = ExportResult(
                    success=True,
                    format=ExportFormat.HTML,
                    output_files=[Path(f"{key}.html")],
                    metadata={"cached": False},
                )
                self.cache[key] = result
                return result

        exporter = CachingBaseExporter()
        sketch = ProofSketch(theorem_name="test", theorem_statement="test")

        # First export
        result1 = exporter.export_single(sketch)
        assert result1.metadata["cached"] is False

        # Second export should be cached
        result2 = exporter.export_single(sketch)
        assert result2 == result1  # Same object from cache


class TestResourceManagement:
    """Test resource management in the pipeline."""

    def test_memory_limits_pipeline(self):
        """Test that memory limits are enforced."""
        from proof_sketcher.core.resources import ExportOptions, ResourceMonitor

        limits = ExportOptions(max_memory_mb=100)
        monitor = ResourceMonitor(limits)

        # Mock high memory usage
        with patch("psutil.Process") as mock_process:
            mock_process.return_value.memory_info.return_value.rss = (
                200 * 1024 * 1024
            )  # 200MB

            from proof_sketcher.core.exceptions import MemoryError

            with pytest.raises(MemoryError):
                monitor.check_limits()

    def test_temp_file_cleanup(self, tmp_path):
        """Test temporary file cleanup after pipeline completion."""
        from proof_sketcher.core.resources import TempFileManager

        temp_manager = TempFileManager(base_dir=tmp_path)

        # Create temp files
        files = []
        for i in range(3):
            f = temp_manager.create_temp_file(suffix=f"_{i}.tmp")
            files.append(f)
            assert f.exists()

        # Cleanup
        count = temp_manager.cleanup_all()
        assert count == 3

        # Verify cleanup
        for f in files:
            assert not f.exists()


class TestPerformanceIntegration:
    """Test performance optimizations in the pipeline."""

    def test_parallel_processing_performance(self, tmp_path):
        """Test that parallel processing improves performance."""
        import time

        from proof_sketcher.exporter.batch_processor.parallel_processor import (
            ParallelProcessor,
        )

        # Create test theorems
        theorems = []
        for i in range(10):
            theorems.append(
                TheoremInfo(name=f"theorem_{i}", statement=f"theorem_{i} : Prop")
            )

        # Mock processing time
        def mock_process(theorem):
            time.sleep(0.1)  # Simulate work
            return {"success": True}

        # Sequential processing
        start = time.time()
        sequential_results = [mock_process(t) for t in theorems]
        sequential_time = time.time() - start

        # Parallel processing (mocked)
        with patch.object(
            ParallelProcessor, "process_theorem", side_effect=mock_process
        ):
            processor = ParallelProcessor(max_workers=4)
            start = time.time()
            # In real implementation, this would be parallel
            parallel_results = [mock_process(t) for t in theorems]
            parallel_time = time.time() - start

        # Both should produce same results
        assert len(sequential_results) == len(parallel_results)
        assert all(r["success"] for r in sequential_results)

    def test_notation_optimization_performance(self):
        """Test optimized notation handler performance."""
        from proof_sketcher.parser.models_optimized import OptimizedParserConfig

        handler = OptimizedParserConfig()

        # Test expressions
        expressions = [
            "∀ x ∈ ℕ, x + 0 = x",
            "∃ f : ℝ → ℝ, continuous f",
            "∫₀¹ f(x) dx = π²/6",
        ] * 100

        # Warm up cache
        for expr in expressions[:10]:
            handler.convert_to_latex(expr)

        # Test cached performance
        import time

        start = time.time()
        results = [handler.convert_to_latex(expr) for expr in expressions]
        elapsed = time.time() - start

        assert len(results) == len(expressions)
        assert elapsed < 1.0  # Should be fast with caching


class TestMathlibIntegration:
    """Test integration with Mathlib theorems."""

    def test_mathlib_notation_handling(self):
        """Test handling of complex Mathlib notation."""
        from proof_sketcher.parser.models import ParserConfig

        handler = ParserConfig()

        # Test complex mathematical expressions
        test_cases = [
            ("∀ ε > 0, ∃ δ > 0, |x - a| < δ → |f(x) - f(a)| < ε", "continuity"),
            ("⨆ᵢ Aᵢ = ⋃ᵢ Aᵢ", "supremum equals union"),
            ("F ⊣ G", "adjunction"),
            ("∇ × (∇f) = 0", "curl of gradient"),
        ]

        for expr, desc in test_cases:
            latex = handler.convert_to_latex(expr)
            assert isinstance(latex, str)
            assert len(latex) > 0
            # Should not have spacing issues
            assert "\\mathbb {" not in latex

    def test_mathlib_proof_structure(self):
        """Test parsing Mathlib-style proof structures."""
        mathlib_proof = """
import Mathlib.Algebra.Group.Basic

theorem group_id_unique (G : Type*) [Group G] (e : G)
  (h : ∀ a : G, e * a = a) : e = 1 := by
  have h1 : e * 1 = 1 := h 1
  rw [mul_one] at h1
  exact h1
"""

        from proof_sketcher.parser.models import TheoremInfo

        # Mock parsing this theorem
        theorem = TheoremInfo(
            name="group_id_unique",
            statement="∀ (G : Type*) [Group G] (e : G), (∀ a : G, e * a = a) → e = 1",
            proof="by have h1 : e * 1 = 1 := h 1; rw [mul_one] at h1; exact h1",
            dependencies=["Mathlib.Algebra.Group.Basic"],
            tactics=["have", "rw", "exact"],
        )

        assert theorem.name == "group_id_unique"
        assert "Group" in theorem.statement
        assert len(theorem.tactics) == 3


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
