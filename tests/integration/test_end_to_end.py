"""End-to-end integration tests for Proof Sketcher."""

from __future__ import annotations

import asyncio
import json
import time
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from proof_sketcher.cli import cli
from proof_sketcher.config.config import Config
from proof_sketcher.parser.models import TheoremInfo


@pytest.fixture
def test_data_dir():
    """Get test data directory."""
    return Path(__file__).parent.parent / "data"


@pytest.fixture
def temp_output_dir(tmp_path):
    """Create temporary output directory."""
    output_dir = tmp_path / "test_output"
    output_dir.mkdir(exist_ok=True)
    return output_dir


class TestSimpleTheoremPipeline:
    """Test full pipeline with simple theorems."""

    def test_simple_theorem_full_pipeline(self, test_data_dir, temp_output_dir):
        """Test: Lean file → Parse → Generate → Animate → Export."""
        # Create test Lean file
        lean_file = test_data_dir / "simple_theorem.lean"
        lean_file.parent.mkdir(exist_ok=True)
        lean_file.write_text(
            """
/-- Addition of zero is the identity -/
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl
"""
        )

        runner = CliRunner()

        # Test parsing
        parse_result = runner.invoke(
            cli,
            ["parse", str(lean_file), "--output", str(temp_output_dir / "parsed.json")],
        )
        assert parse_result.exit_code == 0

        # Verify parsed output
        parsed_file = temp_output_dir / "parsed.json"
        assert parsed_file.exists()
        parsed_data = json.loads(parsed_file.read_text())
        assert parsed_data["theorems"][0]["name"] == "add_zero"

        # Test generation (with mock Claude API)
        with patch(
            "proof_sketcher.generator.claude.ClaudeClient.generate"
        ) as mock_generate:
            mock_generate.return_value = {
                "explanation": "This theorem states that adding zero to any natural number leaves it unchanged.",
                "key_steps": ["Apply reflexivity"],
                "intuition": "Zero is the additive identity",
            }

            generate_result = runner.invoke(
                cli,
                [
                    "generate",
                    str(parsed_file),
                    "--output",
                    str(temp_output_dir / "proof_sketch.json"),
                ],
            )
            assert generate_result.exit_code == 0

        # Test export to HTML
        export_result = runner.invoke(
            cli,
            [
                "export",
                str(temp_output_dir / "proof_sketch.json"),
                "--format",
                "html",
                "--output",
                str(temp_output_dir / "output.html"),
            ],
        )
        assert export_result.exit_code == 0

        # Verify HTML output
        html_file = temp_output_dir / "output.html"
        assert html_file.exists()
        html_content = html_file.read_text()
        assert "add_zero" in html_content
        assert "additive identity" in html_content

    def test_offline_mode_pipeline(self, test_data_dir, temp_output_dir):
        """Test pipeline in offline mode without API calls."""
        lean_file = test_data_dir / "offline_test.lean"
        lean_file.write_text(
            """
theorem simple_eq : 1 + 1 = 2 := by
  norm_num
"""
        )

        runner = CliRunner()

        # Test offline prove command
        result = runner.invoke(
            cli,
            ["prove", str(lean_file), "--offline", "--output", str(temp_output_dir)],
        )
        assert result.exit_code == 0

        # Check generated files
        output_files = list(temp_output_dir.glob("*"))
        assert any(f.suffix == ".json" for f in output_files)
        assert any(f.suffix == ".html" for f in output_files)


class TestMathlibTheoremPipeline:
    """Test with real mathlib-style theorems."""

    @pytest.mark.integration
    def test_mathlib_theorem_pipeline(self, temp_output_dir):
        """Test with real mathlib theorem."""
        lean_content = """
import Mathlib.Data.Nat.Basic

/-- Commutativity of natural number addition -/
theorem nat_add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero => simp [Nat.zero_add]
  | succ n ih => simp [Nat.succ_add, ih]
"""

        lean_file = temp_output_dir / "mathlib_theorem.lean"
        lean_file.write_text(lean_content)

        runner = CliRunner()

        # Full pipeline test
        with patch(
            "proof_sketcher.generator.claude.ClaudeClient.generate"
        ) as mock_generate:
            mock_generate.return_value = {
                "explanation": "Proves that addition of natural numbers is commutative.",
                "key_steps": [
                    "Base case: 0 + m = m + 0",
                    "Inductive step: If n + m = m + n, then (n+1) + m = m + (n+1)",
                ],
                "intuition": "We can swap the order of addition by induction on the first argument.",
            }

            result = runner.invoke(
                cli,
                [
                    "prove",
                    str(lean_file),
                    "--format",
                    "all",
                    "--output",
                    str(temp_output_dir / "mathlib_output"),
                ],
            )
            assert result.exit_code == 0

        # Verify multiple output formats
        output_dir = temp_output_dir / "mathlib_output"
        assert (output_dir / "nat_add_comm.html").exists()
        assert (output_dir / "nat_add_comm.md").exists()
        assert (output_dir / "nat_add_comm.json").exists()


class TestBatchProcessing:
    """Test batch processing of multiple theorems."""

    def test_batch_processing(self, test_data_dir, temp_output_dir):
        """Test processing multiple theorems."""
        # Create multiple theorem files
        theorems = [
            ("theorem1.lean", "theorem eq1 : 1 = 1 := rfl"),
            ("theorem2.lean", "theorem eq2 : 2 = 2 := rfl"),
            ("theorem3.lean", "theorem eq3 : 3 = 3 := rfl"),
        ]

        batch_dir = test_data_dir / "batch"
        batch_dir.mkdir(exist_ok=True)

        for filename, content in theorems:
            (batch_dir / filename).write_text(content)

        runner = CliRunner()

        # Test batch command
        start_time = time.time()
        result = runner.invoke(
            cli,
            [
                "batch",
                str(batch_dir),
                "--pattern",
                "*.lean",
                "--output",
                str(temp_output_dir),
                "--parallel",
                "2",
                "--offline",  # Use offline mode for testing
            ],
        )
        elapsed_time = time.time() - start_time

        assert result.exit_code == 0

        # Verify all theorems processed
        for filename, _ in theorems:
            base_name = filename.replace(".lean", "")
            assert (temp_output_dir / f"{base_name}.json").exists()

        # Check batch report
        report_file = temp_output_dir / "batch_report.json"
        assert report_file.exists()
        report = json.loads(report_file.read_text())
        assert report["total_files"] == 3
        assert report["successful"] == 3
        assert report["failed"] == 0
        assert "elapsed_time" in report


class TestErrorRecovery:
    """Test graceful handling of failures."""

    def test_error_recovery(self, test_data_dir, temp_output_dir):
        """Test graceful handling of failures."""
        # Create files with various errors
        error_files = [
            ("syntax_error.lean", "theorem broken"),  # Syntax error
            ("valid.lean", "theorem valid : 1 = 1 := rfl"),  # Valid
            ("empty.lean", ""),  # Empty file
        ]

        error_dir = test_data_dir / "errors"
        error_dir.mkdir(exist_ok=True)

        for filename, content in error_files:
            (error_dir / filename).write_text(content)

        runner = CliRunner()

        # Test batch processing with errors
        result = runner.invoke(
            cli,
            [
                "batch",
                str(error_dir),
                "--output",
                str(temp_output_dir),
                "--continue-on-error",
                "--offline",
            ],
        )

        # Should complete despite errors
        assert result.exit_code == 0

        # Check report
        report_file = temp_output_dir / "batch_report.json"
        report = json.loads(report_file.read_text())
        assert report["successful"] >= 1  # At least valid.lean should succeed
        assert report["failed"] >= 1  # At least one should fail
        assert "errors" in report

    @pytest.mark.asyncio
    async def test_timeout_handling(self, temp_output_dir):
        """Test handling of timeouts."""
        from proof_sketcher.generator.claude import ClaudeClient

        # Mock a slow API call
        async def slow_generate(*args, **kwargs):
            await asyncio.sleep(10)  # Simulate slow response
            return {}

        client = ClaudeClient()
        client.timeout = 1.0  # 1 second timeout

        with patch.object(client, "_generate", side_effect=slow_generate):
            with pytest.raises(asyncio.TimeoutError):
                await client.generate_proof_sketch(
                    TheoremInfo(
                        name="test",
                        statement="Prop",
                        proof="",
                        docstring=None,
                        tactics=[],
                        dependencies=[],
                    )
                )

    def test_memory_limit_handling(self, temp_output_dir):
        """Test memory limit enforcement."""
        from proof_sketcher.core.resources import ResourceManager

        manager = ResourceManager()
        manager.memory_limit_mb = 1  # Very low limit

        # Should raise when exceeding limit
        with pytest.raises(MemoryError):
            # Allocate large data
            large_data = [0] * (10 * 1024 * 1024)  # 10MB
            manager.check_memory_usage()


# Performance benchmarks
class TestPerformanceBenchmarks:
    """Performance benchmark tests."""

    @pytest.mark.benchmark
    def test_single_theorem_performance(
        self, benchmark, test_data_dir, temp_output_dir
    ):
        """Benchmark single theorem processing."""
        lean_file = test_data_dir / "perf_test.lean"
        lean_file.write_text("theorem perf : 1 = 1 := rfl")

        runner = CliRunner()

        def process_theorem():
            result = runner.invoke(
                cli,
                [
                    "prove",
                    str(lean_file),
                    "--offline",
                    "--output",
                    str(temp_output_dir / "perf"),
                ],
            )
            assert result.exit_code == 0

        # Benchmark the processing
        benchmark(process_theorem)

    @pytest.mark.benchmark
    def test_batch_performance(self, benchmark, test_data_dir, temp_output_dir):
        """Benchmark batch processing speed."""
        # Create 10 theorem files
        batch_dir = test_data_dir / "perf_batch"
        batch_dir.mkdir(exist_ok=True)

        for i in range(10):
            (batch_dir / f"theorem{i}.lean").write_text(
                f"theorem t{i} : {i} = {i} := rfl"
            )

        runner = CliRunner()

        def process_batch():
            result = runner.invoke(
                cli,
                [
                    "batch",
                    str(batch_dir),
                    "--parallel",
                    "4",
                    "--offline",
                    "--output",
                    str(temp_output_dir / "batch_perf"),
                ],
            )
            assert result.exit_code == 0

        # Benchmark batch processing
        stats = benchmark(process_batch)

        # Performance assertions
        assert stats.mean < 5.0  # Should complete in under 5 seconds
        assert stats.stddev < 1.0  # Should be consistent

    def test_cache_effectiveness(self, test_data_dir, temp_output_dir):
        """Test cache effectiveness."""
        lean_file = test_data_dir / "cache_test.lean"
        lean_file.write_text("theorem cached : 2 + 2 = 4 := rfl")

        runner = CliRunner()

        # First run - no cache
        start_time = time.time()
        result1 = runner.invoke(
            cli,
            [
                "prove",
                str(lean_file),
                "--offline",
                "--output",
                str(temp_output_dir / "cache1"),
            ],
        )
        first_run_time = time.time() - start_time
        assert result1.exit_code == 0

        # Second run - should use cache
        start_time = time.time()
        result2 = runner.invoke(
            cli,
            [
                "prove",
                str(lean_file),
                "--offline",
                "--output",
                str(temp_output_dir / "cache2"),
            ],
        )
        second_run_time = time.time() - start_time
        assert result2.exit_code == 0

        # Cache should make second run faster
        assert second_run_time < first_run_time * 0.5  # At least 50% faster


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
