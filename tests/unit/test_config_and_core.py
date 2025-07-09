"""Unit tests for configuration and core modules."""

import json
import tempfile
import time
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.config.config import Config, GenerationConfig, ExportConfig, AnimationConfig
from proof_sketcher.core.batch_processor import BatchProcessor
from proof_sketcher.core.context_optimizer import ContextOptimizer, OptimizationResult
from proof_sketcher.core.monitoring import SystemMonitor, PerformanceMetrics, AlertManager
from proof_sketcher.core.optimization import OptimizationEngine, OptimizationStrategy
from proof_sketcher.core.performance import PerformanceTracker, PerformanceReport
from proof_sketcher.core.resources import ResourceManager, TempFileManager, MemoryManager
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.parser.models import TheoremInfo


@pytest.fixture
def sample_config():
    """Create a sample configuration for testing."""
    return Config(
        generation=GenerationConfig(
            model="claude-3",
            temperature=0.7,
            max_tokens=2000,
            timeout_seconds=30
        ),
        export=ExportConfig(
            formats=["html", "markdown"],
            output_dir="output",
            include_animations=True,
            create_index=True
        ),
        animation=AnimationConfig(
            enable_animations=True,
            video_quality="high",
            frame_rate=30,
            duration_seconds=60
        )
    )


@pytest.fixture
def sample_theorem():
    """Create a sample theorem for testing."""
    return TheoremInfo(
        name="test_theorem",
        statement="∀ n : ℕ, n + 0 = n",
        proof="by simp",
        line_number=10,
        complexity_score=3
    )


@pytest.fixture
def sample_proof_sketch():
    """Create a sample proof sketch for testing."""
    return ProofSketch(
        theorem_name="test_theorem",
        theorem_statement="∀ n : ℕ, n + 0 = n",
        introduction="This theorem proves the right identity of addition.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="Apply simplification",
                mathematical_content="n + 0 = n",
                reasoning="By definition of addition",
                tactics_used=["simp"],
                intuition="Zero doesn't change the value"
            )
        ],
        conclusion="Therefore, zero is the right identity for addition.",
        difficulty_level="easy"
    )


class TestConfig:
    """Test configuration management."""
    
    def test_config_creation(self, sample_config):
        """Test configuration creation."""
        assert sample_config.generation.model == "claude-3"
        assert sample_config.generation.temperature == 0.7
        assert sample_config.export.formats == ["html", "markdown"]
        assert sample_config.animation.enable_animations is True
    
    def test_config_validation(self):
        """Test configuration validation."""
        # Valid configuration
        config = Config(
            generation=GenerationConfig(temperature=0.5)
        )
        assert config.generation.temperature == 0.5
        
        # Invalid temperature
        with pytest.raises(ValueError):
            Config(generation=GenerationConfig(temperature=2.0))
        
        # Invalid max_tokens
        with pytest.raises(ValueError):
            Config(generation=GenerationConfig(max_tokens=-1))
    
    def test_config_serialization(self, sample_config):
        """Test configuration serialization."""
        config_dict = sample_config.model_dump()
        
        assert isinstance(config_dict, dict)
        assert "generation" in config_dict
        assert "export" in config_dict
        assert "animation" in config_dict
        assert config_dict["generation"]["model"] == "claude-3"
    
    def test_config_file_operations(self, sample_config, tmp_path):
        """Test configuration file save/load operations."""
        config_file = tmp_path / "config.json"
        
        # Save configuration
        sample_config.save_to_file(config_file)
        assert config_file.exists()
        
        # Load configuration
        loaded_config = Config.from_file(config_file)
        assert loaded_config.generation.model == sample_config.generation.model
        assert loaded_config.export.formats == sample_config.export.formats
    
    def test_config_merging(self):
        """Test configuration merging."""
        base_config = Config(
            generation=GenerationConfig(model="claude-3", temperature=0.7)
        )
        
        override_config = Config(
            generation=GenerationConfig(temperature=0.5, max_tokens=1500)
        )
        
        merged = base_config.merge(override_config)
        
        assert merged.generation.model == "claude-3"  # From base
        assert merged.generation.temperature == 0.5   # From override
        assert merged.generation.max_tokens == 1500   # From override
    
    def test_config_environment_variables(self):
        """Test configuration from environment variables."""
        with patch.dict('os.environ', {
            'PROOF_SKETCHER_MODEL': 'claude-3-sonnet',
            'PROOF_SKETCHER_TEMPERATURE': '0.8',
            'PROOF_SKETCHER_OUTPUT_DIR': '/tmp/output'
        }):
            config = Config.from_environment()
            
            assert config.generation.model == "claude-3-sonnet"
            assert config.generation.temperature == 0.8
            assert config.export.output_dir == "/tmp/output"


class TestBatchProcessor:
    """Test batch processing functionality."""
    
    def test_batch_processor_initialization(self, sample_config):
        """Test batch processor initialization."""
        processor = BatchProcessor(config=sample_config)
        assert processor.config == sample_config
        assert processor.parser is not None
        assert processor.generator is not None
        assert processor.exporter is not None
    
    def test_process_single_file(self, sample_theorem, sample_config, tmp_path):
        """Test processing a single file."""
        processor = BatchProcessor(config=sample_config)
        
        # Create test file
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("theorem test : True := trivial")
        
        with patch.object(processor.parser, 'parse_file') as mock_parse:
            mock_parse.return_value = Mock(
                success=True,
                theorems=[sample_theorem],
                has_errors=False
            )
            
            with patch.object(processor.generator, 'generate_proof_sketch') as mock_generate:
                mock_generate.return_value = ProofSketch(
                    theorem_name="test",
                    theorem_statement="True",
                    introduction="Test",
                    key_steps=[],
                    conclusion="Trivial",
                    difficulty_level="trivial"
                )
                
                result = processor.process_file(lean_file)
                
                assert result["success"] is True
                assert result["theorems_processed"] == 1
                assert len(result["proof_sketches"]) == 1
    
    def test_batch_processing_with_errors(self, sample_config, tmp_path):
        """Test batch processing with error handling."""
        processor = BatchProcessor(config=sample_config)
        
        # Create files with mixed content
        good_file = tmp_path / "good.lean"
        good_file.write_text("theorem good : True := trivial")
        
        bad_file = tmp_path / "bad.lean"
        bad_file.write_text("invalid lean syntax")
        
        files = [good_file, bad_file]
        
        with patch.object(processor, 'process_file') as mock_process:
            mock_process.side_effect = [
                {"success": True, "theorems_processed": 1},
                {"success": False, "error": "Parse error"}
            ]
            
            results = processor.process_batch(files)
            
            assert results["total_files"] == 2
            assert results["successful_files"] == 1
            assert results["failed_files"] == 1
    
    def test_processing_progress_tracking(self, sample_config, tmp_path):
        """Test progress tracking during batch processing."""
        processor = BatchProcessor(config=sample_config)
        
        # Create multiple files
        files = []
        for i in range(5):
            file_path = tmp_path / f"theorem{i}.lean"
            file_path.write_text(f"theorem t{i} : Nat := {i}")
            files.append(file_path)
        
        progress_updates = []
        
        def track_progress(current, total, file_name):
            progress_updates.append((current, total, file_name))
        
        processor.progress_callback = track_progress
        
        with patch.object(processor, 'process_file') as mock_process:
            mock_process.return_value = {"success": True, "theorems_processed": 1}
            
            processor.process_batch(files)
            
            assert len(progress_updates) == 5
            assert progress_updates[-1][0] == 5  # Final progress


class TestContextOptimizer:
    """Test context optimization functionality."""
    
    def test_context_optimizer_initialization(self):
        """Test context optimizer initialization."""
        optimizer = ContextOptimizer()
        assert optimizer.optimization_strategies is not None
        assert optimizer.context_analyzer is not None
    
    def test_context_analysis(self, sample_proof_sketch):
        """Test context analysis for optimization."""
        optimizer = ContextOptimizer()
        
        context = optimizer.analyze_context(sample_proof_sketch)
        
        assert "complexity_score" in context
        assert "content_length" in context
        assert "mathematical_areas" in context
        assert "optimization_opportunities" in context
    
    def test_optimization_strategy_selection(self, sample_proof_sketch):
        """Test optimization strategy selection."""
        optimizer = ContextOptimizer()
        
        strategies = optimizer.select_optimization_strategies(sample_proof_sketch)
        
        assert isinstance(strategies, list)
        assert len(strategies) > 0
        assert all(hasattr(s, 'apply') for s in strategies)
    
    def test_context_optimization(self, sample_proof_sketch):
        """Test context optimization application."""
        optimizer = ContextOptimizer()
        
        result = optimizer.optimize_context(sample_proof_sketch)
        
        assert isinstance(result, OptimizationResult)
        assert result.optimized_sketch is not None
        assert result.optimization_applied is not None
        assert result.performance_improvement >= 0
    
    def test_mathematical_context_optimization(self, sample_proof_sketch):
        """Test mathematical context-specific optimization."""
        optimizer = ContextOptimizer()
        
        # Test with different mathematical contexts
        contexts = ["algebra", "analysis", "topology", "logic"]
        
        for context in contexts:
            sketch = sample_proof_sketch
            sketch.mathematical_context = context
            
            result = optimizer.optimize_for_mathematical_context(sketch)
            
            assert result.mathematical_context == context
            assert len(result.key_insights) >= len(sketch.key_insights)


class TestSystemMonitor:
    """Test system monitoring functionality."""
    
    def test_system_monitor_initialization(self):
        """Test system monitor initialization."""
        monitor = SystemMonitor()
        assert monitor.metrics_collector is not None
        assert monitor.alert_manager is not None
    
    def test_performance_metrics_collection(self):
        """Test performance metrics collection."""
        monitor = SystemMonitor()
        
        with patch('psutil.cpu_percent') as mock_cpu:
            mock_cpu.return_value = 45.5
            
            with patch('psutil.virtual_memory') as mock_memory:
                mock_memory.return_value = Mock(percent=62.3, available=1024*1024*1024)
                
                metrics = monitor.collect_metrics()
                
                assert isinstance(metrics, PerformanceMetrics)
                assert metrics.cpu_usage == 45.5
                assert metrics.memory_usage == 62.3
                assert metrics.memory_available > 0
    
    def test_alert_system(self):
        """Test alert system for performance issues."""
        monitor = SystemMonitor()
        alert_manager = AlertManager()
        
        # Test high CPU alert
        high_cpu_metrics = PerformanceMetrics(
            cpu_usage=95.0,
            memory_usage=50.0,
            disk_usage=30.0,
            timestamp=time.time()
        )
        
        alerts = alert_manager.check_alerts(high_cpu_metrics)
        
        assert len(alerts) > 0
        assert any("CPU" in alert.message for alert in alerts)
        assert any(alert.severity == "high" for alert in alerts)
    
    def test_metrics_history_tracking(self):
        """Test metrics history tracking."""
        monitor = SystemMonitor()
        
        # Collect multiple metrics over time
        for i in range(5):
            with patch('psutil.cpu_percent', return_value=i * 10):
                with patch('psutil.virtual_memory', return_value=Mock(percent=i * 15)):
                    monitor.collect_metrics()
                    time.sleep(0.01)  # Small delay
        
        history = monitor.get_metrics_history()
        
        assert len(history) == 5
        assert all(isinstance(m, PerformanceMetrics) for m in history)
        assert history[0].cpu_usage != history[-1].cpu_usage


class TestOptimizationEngine:
    """Test optimization engine functionality."""
    
    def test_optimization_engine_initialization(self):
        """Test optimization engine initialization."""
        engine = OptimizationEngine()
        assert engine.strategies is not None
        assert engine.performance_tracker is not None
    
    def test_optimization_strategy_registration(self):
        """Test optimization strategy registration."""
        engine = OptimizationEngine()
        
        class TestStrategy(OptimizationStrategy):
            def can_optimize(self, target):
                return True
            
            def optimize(self, target):
                return target
            
            def estimate_improvement(self, target):
                return 0.1
        
        test_strategy = TestStrategy()
        engine.register_strategy("test", test_strategy)
        
        assert "test" in engine.strategies
        assert engine.strategies["test"] == test_strategy
    
    def test_automatic_optimization(self, sample_proof_sketch):
        """Test automatic optimization selection and application."""
        engine = OptimizationEngine()
        
        # Mock strategies
        mock_strategy = Mock()
        mock_strategy.can_optimize.return_value = True
        mock_strategy.estimate_improvement.return_value = 0.2
        mock_strategy.optimize.return_value = sample_proof_sketch
        
        engine.register_strategy("mock", mock_strategy)
        
        result = engine.optimize_automatically(sample_proof_sketch)
        
        assert result is not None
        mock_strategy.can_optimize.assert_called_with(sample_proof_sketch)
        mock_strategy.optimize.assert_called_with(sample_proof_sketch)
    
    def test_optimization_performance_tracking(self, sample_proof_sketch):
        """Test optimization performance tracking."""
        engine = OptimizationEngine()
        
        with patch.object(engine.performance_tracker, 'track_optimization') as mock_track:
            mock_strategy = Mock()
            mock_strategy.can_optimize.return_value = True
            mock_strategy.optimize.return_value = sample_proof_sketch
            
            engine.register_strategy("test", mock_strategy)
            engine.optimize_automatically(sample_proof_sketch)
            
            mock_track.assert_called()


class TestPerformanceTracker:
    """Test performance tracking functionality."""
    
    def test_performance_tracker_initialization(self):
        """Test performance tracker initialization."""
        tracker = PerformanceTracker()
        assert tracker.metrics is not None
        assert tracker.benchmarks is not None
    
    def test_operation_timing(self):
        """Test operation timing functionality."""
        tracker = PerformanceTracker()
        
        def test_operation():
            time.sleep(0.01)
            return "result"
        
        result = tracker.time_operation("test_op", test_operation)
        
        assert result == "result"
        assert "test_op" in tracker.metrics
        assert tracker.metrics["test_op"]["duration"] > 0
    
    def test_performance_report_generation(self):
        """Test performance report generation."""
        tracker = PerformanceTracker()
        
        # Record some operations
        tracker.record_operation("parse", 0.5, {"theorems": 5})
        tracker.record_operation("generate", 2.0, {"sketches": 5})
        tracker.record_operation("export", 1.0, {"files": 5})
        
        report = tracker.generate_report()
        
        assert isinstance(report, PerformanceReport)
        assert "parse" in report.operation_times
        assert "generate" in report.operation_times
        assert report.total_time > 0
        assert report.average_operation_time > 0
    
    def test_benchmark_comparison(self):
        """Test benchmark comparison functionality."""
        tracker = PerformanceTracker()
        
        # Set baseline
        tracker.set_baseline("operation_x", 1.0)
        
        # Record new measurement
        tracker.record_operation("operation_x", 0.8, {})
        
        comparison = tracker.compare_to_baseline("operation_x")
        
        assert comparison["improvement"] > 0
        assert comparison["percentage_change"] < 0  # Faster is negative change


class TestResourceManager:
    """Test resource management functionality."""
    
    def test_resource_manager_initialization(self):
        """Test resource manager initialization."""
        manager = ResourceManager()
        assert manager.temp_file_manager is not None
        assert manager.memory_manager is not None
    
    def test_temporary_file_management(self, tmp_path):
        """Test temporary file management."""
        temp_manager = TempFileManager(base_dir=tmp_path)
        
        # Create temporary files
        temp_files = []
        for i in range(3):
            temp_file = temp_manager.create_temp_file(suffix=f"_{i}.tmp")
            temp_file.write_text(f"Content {i}")
            temp_files.append(temp_file)
            assert temp_file.exists()
        
        # Cleanup specific file
        temp_manager.cleanup_file(temp_files[0])
        assert not temp_files[0].exists()
        assert temp_files[1].exists()
        
        # Cleanup all
        remaining = temp_manager.cleanup_all()
        assert remaining == 2
        assert not any(f.exists() for f in temp_files[1:])
    
    def test_memory_management(self):
        """Test memory management functionality."""
        memory_manager = MemoryManager()
        
        # Test memory monitoring
        usage = memory_manager.get_current_usage()
        assert usage["memory_mb"] > 0
        assert usage["memory_percent"] > 0
        
        # Test memory cleanup
        cleaned = memory_manager.cleanup_unused()
        assert isinstance(cleaned, dict)
        assert "freed_mb" in cleaned
    
    def test_resource_context_manager(self, tmp_path):
        """Test resource context manager."""
        manager = ResourceManager()
        
        with manager.managed_resources() as resources:
            # Create temporary resources
            temp_file = resources.temp_file_manager.create_temp_file()
            temp_file.write_text("test content")
            
            # Allocate some memory (simulated)
            large_data = ["data"] * 1000
            resources.track_memory_usage(large_data)
            
            assert temp_file.exists()
        
        # Resources should be cleaned up after context exit
        assert not temp_file.exists()
    
    def test_resource_limits_enforcement(self):
        """Test resource limits enforcement."""
        manager = ResourceManager(
            max_memory_mb=100,
            max_temp_files=5
        )
        
        # Test memory limit
        with patch.object(manager.memory_manager, 'get_current_usage') as mock_usage:
            mock_usage.return_value = {"memory_mb": 150, "memory_percent": 75}
            
            with pytest.raises(MemoryError):
                manager.check_resource_limits()
        
        # Test temp file limit
        with patch.object(manager.temp_file_manager, 'get_file_count') as mock_count:
            mock_count.return_value = 10
            
            with pytest.raises(RuntimeError):
                manager.check_resource_limits()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])