#!/usr/bin/env python3
"""Comprehensive tests for batch processing functionality.

Tests the BatchProcessor class for handling multiple Lean files in parallel,
including resource management, error handling, and performance monitoring.
"""

import asyncio
import json
import tempfile
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, Mock, patch

import pytest

from src.proof_sketcher.core.batch_processor import (
    BatchJob,
    BatchProcessor,
    BatchResult,
    BatchStats,
)
from src.proof_sketcher.core.exceptions import BatchProcessingError
from src.proof_sketcher.exporter.models import ExportFormat
from src.proof_sketcher.parser.models import FileMetadata, ParseResult, TheoremInfo


class TestBatchJob:
    """Test BatchJob dataclass."""

    def test_batch_job_creation(self):
        """Test creating a batch job."""
        job = BatchJob(file_path=Path("test.lean"), priority=5)
        assert job.file_path == Path("test.lean")
        assert job.priority == 5
        assert job.metadata == {}

    def test_batch_job_with_metadata(self):
        """Test batch job with custom metadata."""
        metadata = {"project": "mathlib", "author": "test"}
        job = BatchJob(file_path=Path("test.lean"), priority=10, metadata=metadata)
        assert job.metadata == metadata


class TestBatchResult:
    """Test BatchResult dataclass."""

    def test_batch_result_creation(self):
        """Test creating a batch result."""
        result = BatchResult(
            file_path=Path("test.lean"),
            success=True,
            theorems_found=5,
            sketches_generated=4,
            exports_created=8,
        )
        assert result.file_path == Path("test.lean")
        assert result.success
        assert result.theorems_found == 5
        assert result.sketches_generated == 4
        assert result.exports_created == 8
        assert result.errors == []
        assert result.warnings == []

    def test_batch_result_with_errors(self):
        """Test batch result with errors and warnings."""
        result = BatchResult(
            file_path=Path("test.lean"),
            success=False,
            errors=["Parse error", "Invalid syntax"],
            warnings=["Deprecated feature used"],
        )
        assert not result.success
        assert len(result.errors) == 2
        assert len(result.warnings) == 1


class TestBatchStats:
    """Test BatchStats dataclass and display."""

    def test_batch_stats_creation(self):
        """Test creating batch statistics."""
        stats = BatchStats(
            total_files=10,
            successful_files=8,
            failed_files=2,
            total_theorems=50,
            total_sketches=45,
            total_exports=90,
            total_time_ms=5000,
            average_time_per_file_ms=500,
            average_time_per_theorem_ms=100,
            files_per_second=2.0,
            theorems_per_second=10.0,
            peak_memory_mb=512.5,
            error_summary={"Parse Error": 1, "Timeout": 1},
        )
        assert stats.total_files == 10
        assert stats.successful_files == 8
        assert stats.failed_files == 2
        assert stats.files_per_second == 2.0
        assert stats.peak_memory_mb == 512.5
        assert stats.error_summary["Parse Error"] == 1

    def test_batch_stats_display(self):
        """Test displaying batch statistics."""
        from io import StringIO

        from rich.console import Console

        buffer = StringIO()
        console = Console(file=buffer, force_terminal=True)

        stats = BatchStats(
            total_files=5,
            successful_files=4,
            failed_files=1,
            total_theorems=20,
            total_sketches=18,
            total_exports=36,
            total_time_ms=2500,
            average_time_per_file_ms=500,
            average_time_per_theorem_ms=125,
            files_per_second=2.0,
            theorems_per_second=8.0,
            peak_memory_mb=256.0,
            error_summary={"Parse Error": 1},
        )

        stats.display(console)
        output = buffer.getvalue()

        # Check key information is displayed
        assert "Batch Processing Summary" in output
        assert "Files Processed" in output
        assert "5" in output  # total files
        assert "4" in output  # successful files
        assert "80.0%" in output  # success rate
        assert "Error Summary" in output
        assert "Parse Error" in output


class TestBatchProcessor:
    """Test the main BatchProcessor class."""

    @pytest.fixture
    def temp_dir(self):
        """Create a temporary directory for tests."""
        with tempfile.TemporaryDirectory() as tmpdir:
            yield Path(tmpdir)

    @pytest.fixture
    def batch_processor(self):
        """Create a batch processor instance."""
        return BatchProcessor(
            max_workers=2,
            memory_limit_mb=512,
            use_enhanced_parser=True,
            export_formats=[ExportFormat.HTML],
        )

    def test_initialization(self):
        """Test batch processor initialization."""
        processor = BatchProcessor(
            max_workers=4,
            memory_limit_mb=1024,
            use_enhanced_parser=False,
            export_formats=[ExportFormat.HTML, ExportFormat.MARKDOWN],
        )
        assert processor.max_workers == 4
        assert processor.memory_limit_mb == 1024
        assert not processor.use_enhanced_parser
        assert len(processor.export_formats) == 2
        assert processor.jobs == []
        assert processor.results == []

    def test_discover_lean_files(self, batch_processor, temp_dir):
        """Test discovering Lean files in a directory."""
        # Create test files
        (temp_dir / "file1.lean").write_text("theorem test1 : 1 = 1 := rfl")
        (temp_dir / "file2.lean").write_text("theorem test2 : 2 = 2 := rfl")
        (temp_dir / "not_lean.txt").write_text("not a lean file")

        subdir = temp_dir / "subdir"
        subdir.mkdir()
        (subdir / "file3.lean").write_text("theorem test3 : 3 = 3 := rfl")

        # Test recursive discovery
        files = batch_processor.discover_lean_files(temp_dir, recursive=True)
        assert len(files) == 3
        assert all(f.suffix == ".lean" for f in files)

        # Test non-recursive discovery
        files = batch_processor.discover_lean_files(temp_dir, recursive=False)
        assert len(files) == 2

        # Test with exclude patterns
        files = batch_processor.discover_lean_files(
            temp_dir, recursive=True, exclude_patterns=["**/subdir/**"]
        )
        assert len(files) == 2

    def test_discover_lean_files_nonexistent(self, batch_processor):
        """Test discovering files in non-existent directory."""
        with pytest.raises(BatchProcessingError, match="Root path does not exist"):
            batch_processor.discover_lean_files(Path("/nonexistent"))

    def test_add_files(self, batch_processor, temp_dir):
        """Test adding files to the batch queue."""
        file1 = temp_dir / "file1.lean"
        file2 = temp_dir / "file2.lean"
        file1.write_text("theorem test1 : 1 = 1 := rfl")
        file2.write_text("theorem test2 : 2 = 2 := rfl")

        batch_processor.add_files([file1, file2], priority=5)
        assert len(batch_processor.jobs) == 2
        assert all(job.priority == 5 for job in batch_processor.jobs)

        # Test adding non-existent file
        batch_processor.add_files([Path("/nonexistent.lean")], priority=1)
        assert len(batch_processor.jobs) == 2  # Should not add non-existent

        # Test adding non-lean file
        txt_file = temp_dir / "not_lean.txt"
        txt_file.write_text("not lean")
        batch_processor.add_files([txt_file], priority=1)
        assert len(batch_processor.jobs) == 2  # Should not add non-lean

    def test_add_directory(self, batch_processor, temp_dir):
        """Test adding all files from a directory."""
        # Create test files
        (temp_dir / "file1.lean").write_text("theorem test1 : 1 = 1 := rfl")
        (temp_dir / "file2.lean").write_text("theorem test2 : 2 = 2 := rfl")

        batch_processor.add_directory(temp_dir, priority=10)
        assert len(batch_processor.jobs) == 2
        assert all(job.priority == 10 for job in batch_processor.jobs)

    @pytest.mark.asyncio
    async def test_process_batch_no_files(self, batch_processor, temp_dir):
        """Test processing with no files in queue."""
        output_dir = temp_dir / "output"

        with pytest.raises(BatchProcessingError, match="No files in batch queue"):
            await batch_processor.process_batch(output_dir)

    @pytest.mark.asyncio
    async def test_process_single_file_success(self, batch_processor, temp_dir):
        """Test successful processing of a single file."""
        # Create a test file
        test_file = temp_dir / "test.lean"
        test_file.write_text("theorem test : 1 + 1 = 2 := by simp")

        # Mock the parser and generator
        mock_parse_result = ParseResult(
            theorems=[
                TheoremInfo(
                    name="test",
                    statement="theorem test : 1 + 1 = 2",
                    proof="by simp",
                    dependencies=[],
                    line_number=1,
                )
            ],
            errors=[],
            warnings=[],
            metadata=FileMetadata(file_path=test_file, file_size=100, total_lines=1),
            parse_time_ms=10.0,
            success=True,
        )

        with patch.object(
            batch_processor.parser, "parse_file", return_value=mock_parse_result
        ):
            with patch.object(
                batch_processor.generator, "generate_proof_sketch"
            ) as mock_gen:
                mock_gen.return_value = MagicMock(theorem_name="test")

                # Add file and process
                batch_processor.add_files([test_file])
                output_dir = temp_dir / "output"

                stats = await batch_processor.process_batch(output_dir)

                # Verify results
                assert stats.total_files == 1
                assert stats.successful_files == 1
                assert stats.failed_files == 0
                assert stats.total_theorems == 1
                assert stats.total_sketches == 1

    @pytest.mark.asyncio
    async def test_process_single_file_parse_failure(self, batch_processor, temp_dir):
        """Test processing when parsing fails."""
        test_file = temp_dir / "test.lean"
        test_file.write_text("invalid lean syntax")

        mock_parse_result = ParseResult(
            theorems=[],
            errors=["Parse error: invalid syntax"],
            warnings=[],
            metadata=None,
            parse_time_ms=5.0,
            success=False,
        )

        with patch.object(
            batch_processor.parser, "parse_file", return_value=mock_parse_result
        ):
            batch_processor.add_files([test_file])
            output_dir = temp_dir / "output"

            stats = await batch_processor.process_batch(output_dir)

            assert stats.total_files == 1
            assert stats.successful_files == 0
            assert stats.failed_files == 1
            assert stats.total_theorems == 0

    def test_process_single_file_generation_failure(self, batch_processor, temp_dir):
        """Test handling generation failures gracefully."""
        test_file = temp_dir / "test.lean"
        test_file.write_text("theorem test : 1 = 1 := rfl")

        mock_parse_result = ParseResult(
            theorems=[
                TheoremInfo(
                    name="test",
                    statement="theorem test : 1 = 1",
                    proof="rfl",
                    dependencies=[],
                    line_number=1,
                )
            ],
            errors=[],
            warnings=[],
            metadata=FileMetadata(file_path=test_file, file_size=100, total_lines=1),
            parse_time_ms=10.0,
            success=True,
        )

        with patch.object(
            batch_processor.parser, "parse_file", return_value=mock_parse_result
        ):
            with patch.object(
                batch_processor.generator, "generate_proof_sketch"
            ) as mock_gen:
                mock_gen.side_effect = Exception("Generation failed")

                result = batch_processor._process_single_file(
                    BatchJob(file_path=test_file), temp_dir / "output"
                )

                assert result.success  # Should still succeed
                assert result.theorems_found == 1
                assert result.sketches_generated == 0
                assert len(result.warnings) == 1
                assert "Generation failed" in result.warnings[0]

    def test_calculate_stats(self, batch_processor):
        """Test statistics calculation."""
        # Create mock results
        batch_processor.results = [
            BatchResult(
                file_path=Path("file1.lean"),
                success=True,
                theorems_found=5,
                sketches_generated=5,
                exports_created=10,
                total_time_ms=1000,
            ),
            BatchResult(
                file_path=Path("file2.lean"),
                success=True,
                theorems_found=3,
                sketches_generated=3,
                exports_created=6,
                total_time_ms=800,
            ),
            BatchResult(
                file_path=Path("file3.lean"),
                success=False,
                theorems_found=0,
                sketches_generated=0,
                exports_created=0,
                errors=["Parse error"],
                total_time_ms=100,
            ),
        ]

        with patch.object(
            batch_processor.resource_monitor, "get_current_usage"
        ) as mock_usage:
            mock_usage.return_value = MagicMock(memory_mb=256.0)

            stats = batch_processor._calculate_stats(2000.0)

            assert stats.total_files == 3
            assert stats.successful_files == 2
            assert stats.failed_files == 1
            assert stats.total_theorems == 8
            assert stats.total_sketches == 8
            assert stats.total_exports == 16
            assert stats.total_time_ms == 2000.0
            assert stats.files_per_second == 1.5  # 3 files / 2 seconds
            assert stats.theorems_per_second == 4.0  # 8 theorems / 2 seconds
            assert stats.error_summary["Parse Error"] == 1

    def test_get_results_by_status(self, batch_processor):
        """Test separating results by status."""
        batch_processor.results = [
            BatchResult(file_path=Path("success1.lean"), success=True),
            BatchResult(file_path=Path("fail1.lean"), success=False),
            BatchResult(file_path=Path("success2.lean"), success=True),
        ]

        successful, failed = batch_processor.get_results_by_status()

        assert len(successful) == 2
        assert len(failed) == 1
        assert successful[0].file_path == Path("success1.lean")
        assert failed[0].file_path == Path("fail1.lean")

    def test_save_detailed_report(self, batch_processor, temp_dir):
        """Test saving detailed JSON report."""
        # Create mock results
        batch_processor.results = [
            BatchResult(
                file_path=Path("file1.lean"),
                success=True,
                theorems_found=5,
                sketches_generated=5,
                exports_created=10,
                parse_time_ms=100,
                generation_time_ms=200,
                export_time_ms=150,
                total_time_ms=450,
            )
        ]

        report_path = temp_dir / "report.json"
        batch_processor.save_detailed_report(report_path)

        assert report_path.exists()

        # Load and verify report
        with open(report_path) as f:
            report = json.load(f)

        assert "timestamp" in report
        assert "configuration" in report
        assert report["configuration"]["max_workers"] == 2
        assert "results" in report
        assert len(report["results"]) == 1
        assert report["results"][0]["success"] is True
        assert report["results"][0]["theorems_found"] == 5

    @pytest.mark.asyncio
    async def test_parallel_processing(self, batch_processor, temp_dir):
        """Test parallel processing of multiple files."""
        # Create multiple test files
        files = []
        for i in range(3):
            file = temp_dir / f"file{i}.lean"
            file.write_text(f"theorem test{i} : {i} = {i} := rfl")
            files.append(file)

        mock_parse_results = []
        for i, file in enumerate(files):
            mock_parse_results.append(
                ParseResult(
                    theorems=[
                        TheoremInfo(
                            name=f"test{i}",
                            statement=f"theorem test{i} : {i} = {i}",
                            proof="rfl",
                            dependencies=[],
                            line_number=1,
                        )
                    ],
                    errors=[],
                    warnings=[],
                    metadata=FileMetadata(file_path=file, file_size=100, total_lines=1),
                    parse_time_ms=10.0,
                    success=True,
                )
            )

        with patch.object(batch_processor.parser, "parse_file") as mock_parse:
            mock_parse.side_effect = mock_parse_results

            with patch.object(
                batch_processor.generator, "generate_proof_sketch"
            ) as mock_gen:
                mock_gen.return_value = MagicMock(theorem_name="test")

                batch_processor.add_files(files)
                output_dir = temp_dir / "output"

                stats = await batch_processor.process_batch(output_dir)

                assert stats.total_files == 3
                assert stats.successful_files == 3
                assert stats.total_theorems == 3

    def test_export_sketches_html(self, batch_processor, temp_dir):
        """Test exporting sketches to HTML format."""
        from src.proof_sketcher.generator.models import ProofSketch, ProofStep

        sketches = [
            ProofSketch(
                theorem_name="test1",
                introduction="This is test 1",
                key_steps=[
                    ProofStep(
                        step_number=1,
                        description="Step 1",
                        tactics=["rfl"],
                        mathematical_content="1 = 1",
                    )
                ],
                conclusion="QED",
            )
        ]

        with patch("src.proof_sketcher.exporter.html.HTMLExporter") as MockExporter:
            mock_instance = MockExporter.return_value
            mock_instance.export_single.return_value = MagicMock(success=True)

            count = batch_processor._export_sketches(
                sketches, ExportFormat.HTML, temp_dir, Path("source.lean")
            )

            assert count == 1
            assert (temp_dir / "html").exists()

    def test_export_sketches_empty(self, batch_processor, temp_dir):
        """Test exporting empty sketch list."""
        count = batch_processor._export_sketches(
            [], ExportFormat.HTML, temp_dir, Path("source.lean")
        )
        assert count == 0

    def test_export_sketches_unsupported_format(self, batch_processor, temp_dir):
        """Test exporting with unsupported format."""
        from src.proof_sketcher.generator.models import ProofSketch

        sketches = [
            ProofSketch(
                theorem_name="test",
                introduction="intro",
                key_steps=[],
                conclusion="conclusion",
            )
        ]

        # Mock an unsupported format
        with pytest.raises(BatchProcessingError, match="Unsupported export format"):
            batch_processor._export_sketches(
                sketches,
                ExportFormat.PDF,  # PDF not implemented in _export_sketches
                temp_dir,
                Path("source.lean"),
            )

    @pytest.mark.asyncio
    async def test_memory_monitoring(self, batch_processor, temp_dir):
        """Test memory usage monitoring during processing."""
        test_file = temp_dir / "test.lean"
        test_file.write_text("theorem test : 1 = 1 := rfl")

        # Set low memory limit
        batch_processor.memory_limit_mb = 50

        mock_parse_result = ParseResult(
            theorems=[
                TheoremInfo(
                    name="test",
                    statement="theorem test : 1 = 1",
                    proof="rfl",
                    dependencies=[],
                    line_number=1,
                )
            ],
            errors=[],
            warnings=[],
            metadata=FileMetadata(file_path=test_file, file_size=100, total_lines=1),
            parse_time_ms=10.0,
            success=True,
        )

        with patch.object(
            batch_processor.parser, "parse_file", return_value=mock_parse_result
        ):
            with patch.object(
                batch_processor.generator, "generate_proof_sketch"
            ) as mock_gen:
                mock_gen.return_value = MagicMock(theorem_name="test")

                # Mock high memory usage
                with patch.object(
                    batch_processor.resource_monitor, "get_current_usage"
                ) as mock_usage:
                    mock_usage.return_value = MagicMock(memory_mb=100.0)

                    # Process should complete but log warning
                    batch_processor.add_files([test_file])
                    output_dir = temp_dir / "output"

                    with patch.object(
                        batch_processor.logger, "warning"
                    ) as mock_warning:
                        stats = await batch_processor.process_batch(output_dir)

                        # Should have logged memory warning
                        mock_warning.assert_called()
                        assert "Memory usage high" in str(mock_warning.call_args)

    def test_error_categorization(self, batch_processor):
        """Test error categorization in statistics."""
        batch_processor.results = [
            BatchResult(
                file_path=Path("file1.lean"),
                success=False,
                errors=["Connection timeout"],
            ),
            BatchResult(
                file_path=Path("file2.lean"), success=False, errors=["Out of memory"]
            ),
            BatchResult(
                file_path=Path("file3.lean"),
                success=False,
                errors=["Parse error: invalid syntax"],
            ),
            BatchResult(
                file_path=Path("file4.lean"),
                success=False,
                errors=["Generation failed"],
            ),
            BatchResult(
                file_path=Path("file5.lean"), success=False, errors=["Unknown error"]
            ),
        ]

        with patch.object(
            batch_processor.resource_monitor, "get_current_usage"
        ) as mock_usage:
            mock_usage.return_value = MagicMock(memory_mb=256.0)

            stats = batch_processor._calculate_stats(1000.0)

            assert stats.error_summary["Timeout"] == 1
            assert stats.error_summary["Memory"] == 1
            assert stats.error_summary["Parse Error"] == 1
            assert stats.error_summary["Generation Error"] == 1
            assert stats.error_summary["Other"] == 1


class TestBatchProcessorIntegration:
    """Integration tests for batch processor."""

    @pytest.mark.asyncio
    async def test_end_to_end_batch_processing(self):
        """Test complete batch processing workflow."""
        with tempfile.TemporaryDirectory() as tmpdir:
            temp_dir = Path(tmpdir)

            # Create test Lean files
            src_dir = temp_dir / "src"
            src_dir.mkdir()

            # Simple valid file
            (src_dir / "valid.lean").write_text(
                """
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ n ih => simp [add_succ, ih]
            """
            )

            # File with no theorems
            (src_dir / "empty.lean").write_text("-- Just comments")

            # Create processor
            processor = BatchProcessor(
                max_workers=1,
                memory_limit_mb=512,
                use_enhanced_parser=True,
                export_formats=[ExportFormat.HTML, ExportFormat.MARKDOWN],
            )

            # Add directory
            processor.add_directory(src_dir)

            # Process batch
            output_dir = temp_dir / "output"

            # We'll mock the parser and generator to avoid external dependencies
            mock_parse_valid = ParseResult(
                theorems=[
                    TheoremInfo(
                        name="add_comm",
                        statement="theorem add_comm (a b : Nat) : a + b = b + a",
                        proof="by induction a with | zero => simp | succ n ih => simp [add_succ, ih]",
                        dependencies=[],
                        line_number=2,
                    )
                ],
                errors=[],
                warnings=[],
                metadata=FileMetadata(
                    file_path=src_dir / "valid.lean", file_size=150, total_lines=5
                ),
                parse_time_ms=15.0,
                success=True,
            )

            mock_parse_empty = ParseResult(
                theorems=[],
                errors=[],
                warnings=[],
                metadata=FileMetadata(
                    file_path=src_dir / "empty.lean", file_size=20, total_lines=1
                ),
                parse_time_ms=5.0,
                success=True,
            )

            with patch.object(processor.parser, "parse_file") as mock_parse:

                def parse_side_effect(file_path):
                    if file_path.name == "valid.lean":
                        return mock_parse_valid
                    else:
                        return mock_parse_empty

                mock_parse.side_effect = parse_side_effect

                with patch.object(
                    processor.generator, "generate_proof_sketch"
                ) as mock_gen:
                    from src.proof_sketcher.generator.models import (
                        ProofSketch,
                        ProofStep,
                    )

                    mock_gen.return_value = ProofSketch(
                        theorem_name="add_comm",
                        introduction="This theorem proves commutativity of addition",
                        key_steps=[
                            ProofStep(
                                step_number=1,
                                description="Base case",
                                tactics=["simp"],
                                mathematical_content="0 + b = b + 0",
                            ),
                            ProofStep(
                                step_number=2,
                                description="Inductive step",
                                tactics=["simp", "ih"],
                                mathematical_content="(n+1) + b = b + (n+1)",
                            ),
                        ],
                        conclusion="Addition is commutative",
                    )

                    # Mock exporters
                    with patch(
                        "src.proof_sketcher.exporter.html.HTMLExporter"
                    ) as MockHTML:
                        with patch(
                            "src.proof_sketcher.exporter.markdown.MarkdownExporter"
                        ) as MockMD:
                            mock_html = MockHTML.return_value
                            mock_md = MockMD.return_value

                            mock_html.export_single.return_value = MagicMock(
                                success=True
                            )
                            mock_md.export_single.return_value = MagicMock(success=True)

                            # Run batch processing
                            stats = await processor.process_batch(output_dir)

            # Verify results
            assert stats.total_files == 2
            assert stats.successful_files == 2  # Both files parsed successfully
            assert stats.failed_files == 0
            assert stats.total_theorems == 1  # Only valid.lean has theorems
            assert stats.total_sketches == 1
            assert stats.total_exports == 2  # 1 sketch × 2 formats

            # Save report
            report_path = temp_dir / "batch_report.json"
            processor.save_detailed_report(report_path)
            assert report_path.exists()

            # Verify report content
            with open(report_path) as f:
                report = json.load(f)

            assert len(report["results"]) == 2
            assert report["configuration"]["max_workers"] == 1
            assert report["configuration"]["export_formats"] == ["html", "markdown"]
