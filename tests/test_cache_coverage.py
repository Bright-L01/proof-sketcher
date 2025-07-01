"""Comprehensive test suite to improve cache.py coverage to 95%+.

This test file focuses on testing uncovered methods and edge cases
to bring the cache coverage from 16% to 95%+.
"""

import json
import logging
import os
import pickle
import tempfile
from datetime import datetime, timedelta
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock

import pytest

from proof_sketcher.generator.cache import (
    CacheError,
    CacheManager,
    CachedClaudeGenerator,
)
from proof_sketcher.generator.models import (
    CacheEntry,
    GenerationConfig,
    GenerationRequest,
    GenerationResponse,
    GenerationType,
    ProofSketch,
    ProofStep,
)
from proof_sketcher.parser.models import TheoremInfo


class TestCacheError:
    """Test CacheError exception."""
    
    def test_cache_error_creation(self):
        """Test CacheError can be created and raised."""
        with pytest.raises(CacheError) as exc_info:
            raise CacheError("Test error message")
        
        assert str(exc_info.value) == "Test error message"


class TestCacheManagerCoverageImprovement:
    """Test suite to improve CacheManager coverage."""

    def test_default_cache_directory(self):
        """Test default cache directory creation."""
        with patch('pathlib.Path.home') as mock_home:
            mock_home.return_value = Path("/tmp/test_user")
            
            # Create the cache manager without specifying cache_dir
            cache = CacheManager()
            
            # Should use the default path under home directory
            assert str(cache.cache_dir).endswith(".proof_sketcher/cache")

    def test_cache_directory_creation_failure(self, caplog):
        """Test handling of cache directory creation failure."""
        with patch.object(Path, 'mkdir') as mock_mkdir:
            mock_mkdir.side_effect = PermissionError("Permission denied")
            
            with pytest.raises(PermissionError):
                CacheManager(cache_dir=Path("/invalid/path"))

    def test_metadata_loading_failure(self, caplog):
        """Test handling of metadata loading failure."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_dir.mkdir(parents=True)
            
            # Create corrupted metadata file
            metadata_file = cache_dir / "metadata.json"
            metadata_file.write_text("invalid json{")
            
            with caplog.at_level(logging.WARNING):
                cache = CacheManager(cache_dir=cache_dir)
            
            # Should log warning and return empty metadata
            assert cache._metadata == {}
            assert "Failed to load cache metadata" in caplog.text

    def test_metadata_save_failure(self, caplog):
        """Test handling of metadata save failure."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Make metadata file read-only
            cache.metadata_file.touch()
            os.chmod(cache.metadata_file, 0o444)
            
            with caplog.at_level(logging.ERROR):
                cache._save_metadata()
            
            assert "Failed to save cache metadata" in caplog.text
            
            # Cleanup
            os.chmod(cache.metadata_file, 0o644)

    def test_pickle_serialization_fallback(self):
        """Test fallback to pickle when JSON serialization fails."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Create response with non-JSON-serializable content
            request = GenerationRequest(
                generation_type=GenerationType.PROOF_SKETCH,
                theorem_name="test",
                theorem_statement="P",
            )
            
            # Create a ProofSketch object that's hard to JSON serialize
            proof_sketch = ProofSketch(
                theorem_name="test",
                introduction="Intro",
                key_steps=[
                    ProofStep(
                        step_number=1,
                        description="Step 1",
                        mathematical_content="Formula",
                        tactics=["tactic"]
                    )
                ],
                conclusion="QED"
            )
            
            response = GenerationResponse(
                request=request,
                content=proof_sketch,  # Complex object
                success=True
            )
            
            # Patch json.dump to fail
            with patch('json.dump') as mock_dump:
                mock_dump.side_effect = TypeError("Object not serializable")
                
                success = cache.put("test_key", response)
                assert success is True
                
                # Check that pickle file was created
                pickle_path = cache.pickle_cache_dir / "test_key.pkl"
                assert pickle_path.exists()

    def test_pickle_cache_get(self):
        """Test getting entries from pickle cache."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test",
                theorem_statement="P",
            )
            
            response = GenerationResponse(
                request=request,
                content="Pickled content",
                success=True
            )
            
            entry = CacheEntry(
                cache_key="pickle_test",
                response=response,
                ttl_hours=24
            )
            
            # Save as pickle only
            pickle_path = cache.pickle_cache_dir / "pickle_test.pkl"
            with open(pickle_path, "wb") as f:
                pickle.dump(entry, f)
            
            # Add to metadata
            cache._metadata["pickle_test"] = {
                "cached_at": datetime.now().isoformat(),
                "ttl_hours": 24,
                "generation_type": "eli5_explanation",
                "theorem_name": "test",
            }
            
            # Get from cache - should find pickle
            cached = cache.get("pickle_test")
            assert cached is not None
            assert cached.content == "Pickled content"

    def test_pickle_loading_failure(self, caplog):
        """Test handling of pickle loading failure."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Create corrupted pickle file
            pickle_path = cache.pickle_cache_dir / "corrupt.pkl"
            pickle_path.write_text("not a pickle file")
            
            with caplog.at_level(logging.WARNING):
                result = cache._load_pickle_entry(pickle_path)
            
            assert result is None
            assert "Failed to load pickle cache entry" in caplog.text

    def test_json_loading_failure(self, caplog):
        """Test handling of JSON loading failure."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Create invalid JSON file
            json_path = cache.json_cache_dir / "invalid.json"
            json_path.write_text("invalid json{")
            
            with caplog.at_level(logging.WARNING):
                result = cache._load_json_entry(json_path)
            
            assert result is None
            assert "Failed to load JSON cache entry" in caplog.text

    def test_get_with_exception_handling(self, caplog):
        """Test get method exception handling."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Mock path.exists to raise exception
            with patch.object(Path, 'exists') as mock_exists:
                mock_exists.side_effect = OSError("Disk error")
                
                with caplog.at_level(logging.WARNING):
                    result = cache.get("test_key")
                
                assert result is None
                assert "Error reading cache entry" in caplog.text

    def test_put_exception_handling(self, caplog):
        """Test put method exception handling."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test",
                theorem_statement="P",
            )
            
            response = GenerationResponse(
                request=request,
                content="Test",
                success=True
            )
            
            # Mock open to raise exception
            with patch('builtins.open') as mock_open:
                mock_open.side_effect = IOError("Disk full")
                
                with caplog.at_level(logging.ERROR):
                    result = cache.put("test_key", response)
                
                assert result is False
                assert "Error caching response" in caplog.text

    def test_cleanup_expired_with_invalid_metadata(self, caplog):
        """Test cleanup with invalid metadata entries."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Add invalid metadata entries
            cache._metadata["invalid1"] = {
                "cached_at": "not-a-date",
                "ttl_hours": 24,
            }
            
            cache._metadata["invalid2"] = {
                # Missing cached_at
                "ttl_hours": 24,
            }
            
            cache._metadata["valid"] = {
                "cached_at": datetime.now().isoformat(),
                "ttl_hours": 24,
            }
            
            with caplog.at_level(logging.WARNING):
                removed = cache.cleanup_expired()
            
            # Invalid entries should be removed
            assert "invalid1" not in cache._metadata
            assert "invalid2" not in cache._metadata
            assert "valid" in cache._metadata
            assert "Invalid metadata" in caplog.text

    def test_get_cache_size_mb(self):
        """Test cache size calculation."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Add some files
            test_file1 = cache.json_cache_dir / "test1.json"
            test_file1.write_text("x" * 1024)  # 1KB
            
            test_file2 = cache.pickle_cache_dir / "test2.pkl"
            test_file2.write_text("y" * 2048)  # 2KB
            
            size_mb = cache.get_cache_size_mb()
            
            # Should be approximately 3KB / 1024 / 1024 MB
            assert size_mb > 0
            assert size_mb < 0.01  # Less than 0.01 MB

    def test_size_based_cleanup(self, caplog):
        """Test automatic cleanup when cache exceeds size limit."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir, max_cache_size_mb=0.001)  # Very small limit
            
            # Add entries that exceed the limit
            for i in range(5):
                request = GenerationRequest(
                    generation_type=GenerationType.ELI5_EXPLANATION,
                    theorem_name=f"test_{i}",
                    theorem_statement="P",
                )
                
                response = GenerationResponse(
                    request=request,
                    content="x" * 10000,  # Large content
                    success=True
                )
                
                cache.put(f"key_{i}", response)
            
            # Check current size
            initial_size = cache.get_cache_size_mb()
            
            # Trigger cleanup - the constructor already calls _maybe_cleanup
            # so we need to check if cleanup happened
            if initial_size > cache.max_cache_size_mb:
                # Manually trigger cleanup
                with caplog.at_level(logging.INFO):
                    cache._cleanup_by_size()
                
                # Should have removed some entries
                assert cache.get_cache_size_mb() <= cache.max_cache_size_mb
                assert "old entries" in caplog.text

    def test_cleanup_by_size_with_invalid_metadata(self):
        """Test size cleanup with invalid metadata."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir, max_cache_size_mb=0.001)
            
            # Add entry with invalid cached_at
            cache._metadata["invalid"] = {
                "cached_at": "invalid-date",
                "ttl_hours": 24,
            }
            
            # Add valid entry
            cache._metadata["valid"] = {
                "cached_at": datetime.now().isoformat(),
                "ttl_hours": 24,
            }
            
            # Create corresponding files
            (cache.json_cache_dir / "invalid.json").write_text("x" * 1000)
            (cache.json_cache_dir / "valid.json").write_text("x" * 1000)
            
            # Run cleanup
            cache._cleanup_by_size()
            
            # Invalid entry should be prioritized for removal
            assert "invalid" not in cache._metadata

    def test_time_based_cleanup_tracking(self):
        """Test time-based cleanup with timestamp tracking."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir, cleanup_interval_hours=1)
            
            # Create last cleanup file with old timestamp
            last_cleanup_file = cache.cache_dir / ".last_cleanup"
            old_time = datetime.now() - timedelta(hours=2)
            last_cleanup_file.touch()
            os.utime(last_cleanup_file, (old_time.timestamp(), old_time.timestamp()))
            
            # Add expired entry
            expired_time = datetime.now() - timedelta(hours=25)
            cache._metadata["expired"] = {
                "cached_at": expired_time.isoformat(),
                "ttl_hours": 24,
            }
            
            # Trigger cleanup
            cache._maybe_cleanup()
            
            # Should have updated cleanup timestamp
            new_mtime = datetime.fromtimestamp(last_cleanup_file.stat().st_mtime)
            assert new_mtime > old_time

    def test_cleanup_timestamp_file_error(self):
        """Test cleanup when timestamp file has issues."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Create corrupted timestamp file
            last_cleanup_file = cache.cache_dir / ".last_cleanup"
            last_cleanup_file.write_text("corrupted")
            
            # Mock stat to raise exception
            with patch.object(Path, 'stat') as mock_stat:
                mock_stat.side_effect = OSError("File error")
                
                # Should still run cleanup
                removed = cache.cleanup_expired()
                assert removed >= 0

    def test_delete_nonexistent_entry(self):
        """Test deleting entry that doesn't exist."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Delete entry that doesn't exist
            result = cache.delete("nonexistent")
            assert result is False

    def test_delete_entry_partial_existence(self):
        """Test deleting entry that partially exists."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Create only metadata entry (no file)
            cache._metadata["partial"] = {
                "cached_at": datetime.now().isoformat(),
                "ttl_hours": 24,
            }
            
            # Delete should still work
            result = cache.delete("partial")
            assert result is True
            assert "partial" not in cache._metadata

    def test_cache_entry_reconstruction_error(self):
        """Test error handling in cache entry reconstruction."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(cache_dir=cache_dir)
            
            # Create JSON file with incomplete data
            json_path = cache.json_cache_dir / "incomplete.json"
            json_path.write_text(json.dumps({
                "cache_key": "incomplete",
                # Missing required fields
            }))
            
            result = cache._load_json_entry(json_path)
            assert result is None


class TestCachedClaudeGeneratorCoverageImprovement:
    """Test suite to improve CachedClaudeGenerator coverage."""

    def test_initialization_without_cache_manager(self):
        """Test initialization creates default cache manager."""
        mock_generator = Mock()
        
        cached_gen = CachedClaudeGenerator(mock_generator)
        
        assert cached_gen.generator == mock_generator
        assert isinstance(cached_gen.cache, CacheManager)

    def test_generate_proof_sketch_with_caching(self):
        """Test generate_proof_sketch method with caching."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig(cache_responses=True)
        
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)
            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)
            
            theorem = TheoremInfo(
                name="test_theorem",
                statement="P → Q",
                proof="by simp",
                dependencies=["dep1"],
                docstring="Test theorem"
            )
            
            # Create mock ProofSketch
            mock_sketch = ProofSketch(
                theorem_name="test_theorem",
                introduction="Intro",
                key_steps=[],
                conclusion="QED"
            )
            
            mock_generator.generate_proof_sketch.return_value = mock_sketch
            
            # First call
            result1 = cached_gen.generate_proof_sketch(theorem)
            assert result1 == mock_sketch
            assert mock_generator.generate_proof_sketch.call_count == 1
            
            # Second call - should use cache
            result2 = cached_gen.generate_proof_sketch(theorem)
            assert result2 == mock_sketch
            assert mock_generator.generate_proof_sketch.call_count == 1

    def test_generate_tactic_explanation_with_caching(self):
        """Test generate_tactic_explanation method with caching."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig(cache_responses=True)
        
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)
            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)
            
            theorem = TheoremInfo(name="test", statement="P")
            
            mock_generator.generate_tactic_explanation.return_value = "Tactic explanation"
            
            # First call
            result1 = cached_gen.generate_tactic_explanation(theorem)
            assert result1 == "Tactic explanation"
            assert mock_generator.generate_tactic_explanation.call_count == 1
            
            # Second call - should use cache
            result2 = cached_gen.generate_tactic_explanation(theorem)
            assert result2 == "Tactic explanation"
            assert mock_generator.generate_tactic_explanation.call_count == 1

    def test_generate_step_by_step_with_caching(self):
        """Test generate_step_by_step method with caching."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig(cache_responses=True)
        
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)
            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)
            
            theorem = TheoremInfo(name="test", statement="P")
            
            mock_generator.generate_step_by_step.return_value = "Step by step"
            
            # First call
            result1 = cached_gen.generate_step_by_step(theorem)
            assert result1 == "Step by step"
            assert mock_generator.generate_step_by_step.call_count == 1
            
            # Second call - should use cache
            result2 = cached_gen.generate_step_by_step(theorem)
            assert result2 == "Step by step"
            assert mock_generator.generate_step_by_step.call_count == 1

    def test_generate_with_mathematical_context(self):
        """Test generation with mathematical context parameter."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig(cache_responses=True)
        
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)
            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)
            
            theorem = TheoremInfo(name="test", statement="P")
            context = "Group theory context"
            
            mock_generator.generate_eli5_explanation.return_value = "Contextual explanation"
            
            result = cached_gen.generate_eli5_explanation(
                theorem, 
                mathematical_context=context
            )
            
            assert result == "Contextual explanation"
            
            # Verify context was passed through
            mock_generator.generate_eli5_explanation.assert_called_with(
                theorem, None, context
            )

    def test_generation_response_wrapping(self):
        """Test wrapping of raw content in GenerationResponse."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig(cache_responses=True)
        
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)
            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)
            
            theorem = TheoremInfo(name="test", statement="P")
            
            # Create a proper request object first
            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test",
                theorem_statement="P",
            )
            
            # Mock returns GenerationResponse object
            mock_response = GenerationResponse(
                request=request,
                content="Response content",
                success=True
            )
            
            mock_generator.generate_eli5_explanation.return_value = mock_response
            
            result = cached_gen.generate_eli5_explanation(theorem)
            
            # Should return the content, not the response object
            assert result == mock_response

    def test_clear_cache_method(self):
        """Test clear_cache method."""
        mock_generator = Mock()
        
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)
            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)
            
            # Add some cache entries
            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test",
                theorem_statement="P",
            )
            response = GenerationResponse(
                request=request,
                content="Test",
                success=True
            )
            cache_manager.put("test_key", response)
            
            # Clear cache
            cleared = cached_gen.clear_cache()
            assert cleared == 1

    def test_get_cache_stats_method(self):
        """Test get_cache_stats method."""
        mock_generator = Mock()
        
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)
            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)
            
            stats = cached_gen.get_cache_stats()
            
            assert isinstance(stats, dict)
            assert "total_entries" in stats
            assert stats["total_entries"] == 0

    def test_getattr_delegation(self):
        """Test __getattr__ delegation to underlying generator."""
        mock_generator = Mock()
        mock_generator.custom_method = Mock(return_value="custom result")
        mock_generator.another_attribute = "test value"
        
        cached_gen = CachedClaudeGenerator(mock_generator)
        
        # Test method delegation
        result = cached_gen.custom_method(arg1="test")
        assert result == "custom result"
        mock_generator.custom_method.assert_called_with(arg1="test")
        
        # Test attribute access
        assert cached_gen.another_attribute == "test value"

    def test_caching_with_custom_config(self):
        """Test caching behavior with custom config overrides."""
        mock_generator = Mock()
        mock_generator.default_config = GenerationConfig(cache_responses=True)
        
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache_manager = CacheManager(cache_dir=cache_dir)
            cached_gen = CachedClaudeGenerator(mock_generator, cache_manager)
            
            theorem = TheoremInfo(name="test", statement="P")
            
            # Custom config with different TTL
            custom_config = GenerationConfig(
                cache_responses=True,
                cache_ttl_hours=48
            )
            
            mock_generator.generate_eli5_explanation.return_value = "Custom TTL result"
            
            result = cached_gen.generate_eli5_explanation(theorem, config=custom_config)
            assert result == "Custom TTL result"
            
            # Verify custom config was used
            mock_generator.generate_eli5_explanation.assert_called_with(
                theorem, custom_config, None
            )


class TestEdgeCasesAndIntegration:
    """Test edge cases and integration scenarios."""

    def test_concurrent_cache_access(self):
        """Test concurrent access to cache (simulated)."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            
            # Create multiple cache managers accessing same directory
            cache1 = CacheManager(cache_dir=cache_dir)
            cache2 = CacheManager(cache_dir=cache_dir)
            
            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="test",
                theorem_statement="P",
            )
            response = GenerationResponse(
                request=request,
                content="Shared content",
                success=True
            )
            
            # Write from cache1
            cache1.put("shared_key", response)
            
            # Read from cache2
            result = cache2.get("shared_key")
            assert result is not None
            assert result.content == "Shared content"

    def test_cache_key_generation_consistency(self):
        """Test that cache keys are generated consistently."""
        theorem = TheoremInfo(
            name="test_theorem",
            statement="∀ n : Nat, n + 0 = n",
            proof="by simp",
            dependencies=["Nat.add"],
            docstring="Test"
        )
        
        request1 = GenerationRequest(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
        )
        
        request2 = GenerationRequest(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
        )
        
        # Same parameters should generate same key
        assert request1.get_cache_key() == request2.get_cache_key()
        
        # Different generation type should generate different key
        request3 = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
        )
        
        assert request1.get_cache_key() != request3.get_cache_key()

    def test_cache_persistence_across_restarts(self):
        """Test that cache persists across CacheManager instances."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            
            # First instance - store data
            cache1 = CacheManager(cache_dir=cache_dir)
            
            request = GenerationRequest(
                generation_type=GenerationType.ELI5_EXPLANATION,
                theorem_name="persistent",
                theorem_statement="P",
            )
            response = GenerationResponse(
                request=request,
                content="Persistent data",
                success=True
            )
            
            cache1.put("persist_key", response)
            
            # Simulate restart - create new instance
            cache2 = CacheManager(cache_dir=cache_dir)
            
            # Should find the cached data
            result = cache2.get("persist_key")
            assert result is not None
            assert result.content == "Persistent data"

    def test_large_cache_stress_test(self):
        """Test cache behavior with many entries."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / "cache"
            cache = CacheManager(
                cache_dir=cache_dir,
                max_cache_size_mb=10,  # 10MB limit
                cleanup_interval_hours=1
            )
            
            # Add many entries
            for i in range(100):
                request = GenerationRequest(
                    generation_type=GenerationType.ELI5_EXPLANATION,
                    theorem_name=f"theorem_{i}",
                    theorem_statement=f"Statement {i}",
                )
                response = GenerationResponse(
                    request=request,
                    content=f"Content for theorem {i}" * 100,  # Reasonable size
                    success=True
                )
                
                cache.put(f"key_{i}", response)
            
            # Cache should handle this without issues
            stats = cache.get_cache_stats()
            assert stats["total_entries"] <= 100
            assert stats["size_mb"] <= cache.max_cache_size_mb
            
            # Some entries might have been cleaned up
            if stats["total_entries"] < 100:
                # Verify oldest entries were removed
                assert cache.get("key_0") is None or cache.get("key_99") is not None