"""Unit tests for CLI commands."""

import json
import tempfile
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock

import pytest
from click.testing import CliRunner

from proof_sketcher.cli.commands.prove import prove
from proof_sketcher.cli.commands.batch import batch
from proof_sketcher.cli.commands.cache import cache
from proof_sketcher.cli.commands.config import config as config_cmd
from proof_sketcher.cli.commands.info import info
from proof_sketcher.cli.commands.optimize import optimize
from proof_sketcher.cli.commands.performance import performance
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.parser.models import ParseResult, TheoremInfo


class TestProveCommand:
    """Test the prove command."""
    
    def test_prove_basic_theorem(self, tmp_path):
        """Test basic theorem proving."""
        # Create test file
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : 1 = 1 := rfl")
        
        runner = CliRunner()
        
        with patch('proof_sketcher.parser.lean_parser.LeanParser.parse_file') as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[TheoremInfo(name="test", statement="1 = 1", proof="rfl")],
                success=True
            )
            
            with patch('proof_sketcher.generator.ai_generator.AIGenerator.generate_proof_sketch') as mock_gen:
                mock_gen.return_value = ProofSketch(
                    theorem_name="test",
                    theorem_statement="1 = 1",
                    introduction="Simple equality",
                    key_steps=[],
                    conclusion="By reflexivity",
                    difficulty_level="trivial"
                )
                
                with patch('proof_sketcher.exporter.html.HTMLExporter.export_single') as mock_export:
                    mock_export.return_value = Mock(success=True, output_files=[Path("test.html")])
                    
                    result = runner.invoke(prove, [str(lean_file)])
                    assert result.exit_code == 0
                    assert "Processing theorem: test" in result.output
    
    def test_prove_offline_mode(self, tmp_path):
        """Test prove command in offline mode."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        runner = CliRunner()
        
        with patch('proof_sketcher.parser.lean_parser.LeanParser.parse_file') as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[TheoremInfo(name="test", statement="True", proof="trivial")],
                success=True
            )
            
            with patch('proof_sketcher.generator.offline.OfflineGenerator.generate_proof_sketch') as mock_gen:
                mock_gen.return_value = ProofSketch(
                    theorem_name="test",
                    theorem_statement="True",
                    introduction="Always true",
                    key_steps=[],
                    conclusion="Trivial",
                    difficulty_level="trivial"
                )
                
                result = runner.invoke(prove, [str(lean_file), '--offline'])
                assert result.exit_code == 0
    
    def test_prove_with_custom_output(self, tmp_path):
        """Test prove command with custom output directory."""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        output_dir = tmp_path / "output"
        
        runner = CliRunner()
        
        with patch('proof_sketcher.parser.lean_parser.LeanParser.parse_file') as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[TheoremInfo(name="test", statement="True", proof="trivial")],
                success=True
            )
            
            with patch('proof_sketcher.generator.ai_generator.AIGenerator.generate_proof_sketch') as mock_gen:
                mock_gen.return_value = ProofSketch(
                    theorem_name="test",
                    theorem_statement="True",
                    introduction="Always true",
                    key_steps=[],
                    conclusion="Trivial",
                    difficulty_level="trivial"
                )
                
                result = runner.invoke(prove, [str(lean_file), '--output', str(output_dir)])
                assert result.exit_code == 0
    
    def test_prove_error_handling(self, tmp_path):
        """Test prove command error handling."""
        nonexistent_file = tmp_path / "nonexistent.lean"
        
        runner = CliRunner()
        result = runner.invoke(prove, [str(nonexistent_file)])
        assert result.exit_code != 0
        assert "does not exist" in result.output


class TestBatchCommand:
    """Test the batch command."""
    
    def test_batch_processing(self, tmp_path):
        """Test batch processing of multiple files."""
        # Create test directory
        src_dir = tmp_path / "src"
        src_dir.mkdir()
        
        # Create test files
        for i in range(3):
            (src_dir / f"theorem{i}.lean").write_text(f"theorem t{i} : Nat := {i}")
        
        runner = CliRunner()
        
        with patch('proof_sketcher.batch.parallel_processor.ParallelProcessor.process_directory') as mock_process:
            mock_process.return_value = {
                'processed': 3,
                'successful': 3,
                'failed': 0,
                'results': []
            }
            
            result = runner.invoke(batch, [str(src_dir)])
            assert result.exit_code == 0
            assert "Processed: 3" in result.output
    
    def test_batch_with_parallel_workers(self, tmp_path):
        """Test batch processing with custom worker count."""
        src_dir = tmp_path / "src"
        src_dir.mkdir()
        (src_dir / "test.lean").write_text("theorem test : Nat := 0")
        
        runner = CliRunner()
        
        with patch('proof_sketcher.batch.parallel_processor.ParallelProcessor.process_directory') as mock_process:
            mock_process.return_value = {
                'processed': 1,
                'successful': 1,
                'failed': 0,
                'results': []
            }
            
            result = runner.invoke(batch, [str(src_dir), '--parallel', '4'])
            assert result.exit_code == 0
    
    def test_batch_with_filters(self, tmp_path):
        """Test batch processing with file filters."""
        src_dir = tmp_path / "src"
        src_dir.mkdir()
        (src_dir / "include.lean").write_text("theorem include : Nat := 0")
        (src_dir / "exclude.lean").write_text("theorem exclude : Nat := 1")
        
        runner = CliRunner()
        
        with patch('proof_sketcher.batch.parallel_processor.ParallelProcessor.process_directory') as mock_process:
            mock_process.return_value = {
                'processed': 1,
                'successful': 1,
                'failed': 0,
                'results': []
            }
            
            result = runner.invoke(batch, [str(src_dir), '--include', 'include*'])
            assert result.exit_code == 0


class TestCacheCommand:
    """Test the cache command."""
    
    def test_cache_stats(self, tmp_path):
        """Test cache statistics display."""
        runner = CliRunner()
        
        with patch('proof_sketcher.generator.cache.GenerationCache') as MockCache:
            mock_cache = MockCache.return_value
            mock_cache.stats.return_value = {
                'total_entries': 10,
                'total_size': 1024,
                'hit_rate': 0.75
            }
            
            result = runner.invoke(cache, ['stats'])
            assert result.exit_code == 0
            assert "Total entries: 10" in result.output
    
    def test_cache_clear(self, tmp_path):
        """Test cache clearing."""
        runner = CliRunner()
        
        with patch('proof_sketcher.generator.cache.GenerationCache') as MockCache:
            mock_cache = MockCache.return_value
            mock_cache.clear.return_value = 5
            
            result = runner.invoke(cache, ['clear'])
            assert result.exit_code == 0
            assert "Cleared 5 entries" in result.output
    
    def test_cache_prune(self, tmp_path):
        """Test cache pruning."""
        runner = CliRunner()
        
        with patch('proof_sketcher.generator.cache.GenerationCache') as MockCache:
            mock_cache = MockCache.return_value
            mock_cache.prune.return_value = 3
            
            result = runner.invoke(cache, ['prune'])
            assert result.exit_code == 0
            assert "Pruned 3 entries" in result.output


class TestConfigCommand:
    """Test the config command."""
    
    def test_config_show(self, tmp_path):
        """Test showing configuration."""
        runner = CliRunner()
        
        with patch('proof_sketcher.config.config.Config.load') as mock_load:
            mock_config = Mock()
            mock_config.model_dump.return_value = {"generation": {"model": "claude-3"}}
            mock_load.return_value = mock_config
            
            result = runner.invoke(config_cmd, ['show'])
            assert result.exit_code == 0
    
    def test_config_set(self, tmp_path):
        """Test setting configuration values."""
        runner = CliRunner()
        
        with patch('proof_sketcher.config.config.Config.load') as mock_load:
            with patch('proof_sketcher.config.config.Config.save') as mock_save:
                mock_config = Mock()
                mock_load.return_value = mock_config
                
                result = runner.invoke(config_cmd, ['set', 'generation.model', 'claude-3'])
                assert result.exit_code == 0
    
    def test_config_reset(self, tmp_path):
        """Test resetting configuration."""
        runner = CliRunner()
        
        with patch('proof_sketcher.config.config.Config.reset') as mock_reset:
            result = runner.invoke(config_cmd, ['reset'])
            assert result.exit_code == 0
            mock_reset.assert_called_once()


class TestInfoCommand:
    """Test the info command."""
    
    def test_info_basic(self, tmp_path):
        """Test basic info display."""
        runner = CliRunner()
        
        with patch('proof_sketcher.parser.lean_parser.LeanParser.parse_file') as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[
                    TheoremInfo(name="theorem1", statement="P", proof="trivial"),
                    TheoremInfo(name="theorem2", statement="Q", proof="trivial")
                ],
                success=True
            )
            
            lean_file = tmp_path / "test.lean"
            lean_file.write_text("theorem test : True := trivial")
            
            result = runner.invoke(info, [str(lean_file)])
            assert result.exit_code == 0
            assert "Found 2 theorems" in result.output
    
    def test_info_detailed(self, tmp_path):
        """Test detailed info display."""
        runner = CliRunner()
        
        with patch('proof_sketcher.parser.lean_parser.LeanParser.parse_file') as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[TheoremInfo(
                    name="test",
                    statement="True",
                    proof="trivial",
                    docstring="A test theorem"
                )],
                success=True
            )
            
            lean_file = tmp_path / "test.lean"
            lean_file.write_text("theorem test : True := trivial")
            
            result = runner.invoke(info, [str(lean_file), '--detailed'])
            assert result.exit_code == 0
    
    def test_info_dependencies(self, tmp_path):
        """Test dependency analysis."""
        runner = CliRunner()
        
        with patch('proof_sketcher.parser.lean_parser.LeanParser.parse_file') as mock_parse:
            mock_parse.return_value = ParseResult(
                theorems=[TheoremInfo(
                    name="test",
                    statement="True",
                    proof="trivial",
                    dependencies=["Mathlib.Logic.Basic"]
                )],
                success=True
            )
            
            lean_file = tmp_path / "test.lean"
            lean_file.write_text("import Mathlib.Logic.Basic\ntheorem test : True := trivial")
            
            result = runner.invoke(info, [str(lean_file), '--dependencies'])
            assert result.exit_code == 0


class TestOptimizeCommand:
    """Test the optimize command."""
    
    def test_optimize_cache(self, tmp_path):
        """Test cache optimization."""
        runner = CliRunner()
        
        with patch('proof_sketcher.optimizations.smart_cache.SmartCache.optimize') as mock_optimize:
            mock_optimize.return_value = {"optimized": 5, "size_reduced": 1024}
            
            result = runner.invoke(optimize, ['cache'])
            assert result.exit_code == 0
            assert "Optimized 5 entries" in result.output
    
    def test_optimize_batch(self, tmp_path):
        """Test batch optimization."""
        runner = CliRunner()
        
        with patch('proof_sketcher.optimizations.batch_api.BatchOptimizer.optimize') as mock_optimize:
            mock_optimize.return_value = {"parallel_efficiency": 0.85}
            
            result = runner.invoke(optimize, ['batch'])
            assert result.exit_code == 0
    
    def test_optimize_export(self, tmp_path):
        """Test export optimization."""
        runner = CliRunner()
        
        with patch('proof_sketcher.optimizations.export_streaming.ExportOptimizer.optimize') as mock_optimize:
            mock_optimize.return_value = {"streaming_enabled": True}
            
            result = runner.invoke(optimize, ['export'])
            assert result.exit_code == 0


class TestPerformanceCommand:
    """Test the performance command."""
    
    def test_performance_benchmark(self, tmp_path):
        """Test performance benchmarking."""
        runner = CliRunner()
        
        # Create test file
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch('proof_sketcher.optimizations.performance.PerformanceBenchmark.run') as mock_benchmark:
            mock_benchmark.return_value = {
                "parse_time": 0.1,
                "generate_time": 2.5,
                "export_time": 0.5,
                "total_time": 3.1
            }
            
            result = runner.invoke(performance, ['benchmark', str(lean_file)])
            assert result.exit_code == 0
            assert "Parse time: 0.1s" in result.output
    
    def test_performance_profile(self, tmp_path):
        """Test performance profiling."""
        runner = CliRunner()
        
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch('proof_sketcher.optimizations.performance.PerformanceProfiler.profile') as mock_profile:
            mock_profile.return_value = {
                "hotspots": ["function1", "function2"],
                "memory_usage": 128
            }
            
            result = runner.invoke(performance, ['profile', str(lean_file)])
            assert result.exit_code == 0
    
    def test_performance_monitor(self, tmp_path):
        """Test performance monitoring."""
        runner = CliRunner()
        
        with patch('proof_sketcher.optimizations.performance.PerformanceMonitor.start') as mock_monitor:
            result = runner.invoke(performance, ['monitor'])
            assert result.exit_code == 0
            mock_monitor.assert_called_once()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])