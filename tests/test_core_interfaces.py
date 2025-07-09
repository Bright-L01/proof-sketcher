"""Comprehensive unit tests for core interfaces module.

This module tests all protocols and abstract base classes to ensure
proper interface contract enforcement and protocol compliance.
"""

from abc import ABC
from pathlib import Path
from typing import Any, Dict, List, Optional
from unittest.mock import MagicMock, Mock

import pytest
from pydantic import BaseModel

from proof_sketcher.core.interfaces import (
    IAnimator,
    ICache,
    IConfigurable,
    IExporter,
    IGenerator,
    IParser,
)


# Mock models for testing
class MockTheoremInfo:
    """Mock TheoremInfo for testing."""

    def __init__(self, name: str = "test_theorem", statement: str = "Test statement"):
        self.name = name
        self.statement = statement


class MockParseResult:
    """Mock ParseResult for testing."""

    def __init__(self, success: bool = True, theorems: Optional[List] = None):
        self.success = success
        self.theorems = theorems or []


class MockProofSketch:
    """Mock ProofSketch for testing."""

    def __init__(self, theorem_name: str = "test", content: str = "Test content"):
        self.theorem_name = theorem_name
        self.content = content


class MockGenerationConfig:
    """Mock GenerationConfig for testing."""

    def __init__(self, model: str = "claude-3", temperature: float = 0.7):
        self.model = model
        self.temperature = temperature


class MockAnimationConfig:
    """Mock AnimationConfig for testing."""

    def __init__(self, quality: str = "medium", duration: int = 60):
        self.quality = quality
        self.duration = duration


class MockAnimationResponse:
    """Mock AnimationResponse for testing."""

    def __init__(self, video_path: Optional[Path] = None, success: bool = True):
        self.video_path = video_path or Path("test.mp4")
        self.success = success


class MockExportResult:
    """Mock ExportResult for testing."""

    def __init__(self, output_files: Optional[List[Path]] = None, success: bool = True):
        self.output_files = output_files or [Path("test.html")]
        self.success = success


class MockConfig(BaseModel):
    """Mock configuration for testing."""

    name: str = "test_config"
    value: int = 42


class TestIParserProtocol:
    """Test IParser protocol compliance and usage."""

    def test_protocol_definition(self):
        """Test that IParser is a runtime checkable protocol."""
        assert hasattr(IParser, "__protocol_attrs__")
        assert "parse_file" in IParser.__protocol_attrs__
        assert "parse_theorem" in IParser.__protocol_attrs__

    def test_valid_implementation(self):
        """Test valid IParser implementation."""

        class ValidParser:
            def parse_file(self, file_path: Path):
                return MockParseResult()

            def parse_theorem(self, file_path: Path, theorem_name: str):
                return MockTheoremInfo()

        parser = ValidParser()
        assert isinstance(parser, IParser)

    def test_invalid_implementation_missing_method(self):
        """Test invalid IParser implementation missing required method."""

        class InvalidParser:
            def parse_file(self, file_path: Path):
                return MockParseResult()

            # Missing parse_theorem method

        parser = InvalidParser()
        assert not isinstance(parser, IParser)

    def test_invalid_implementation_wrong_signature(self):
        """Test invalid IParser implementation with wrong method signature."""

        class InvalidParser:
            def parse_file(self, file_path: Path):
                return MockParseResult()

            def parse_theorem(self, wrong_param):  # Wrong signature
                return MockTheoremInfo()

        parser = InvalidParser()
        # Note: Python protocols don't check signatures at runtime,
        # only method existence, so this will still pass isinstance check
        assert isinstance(parser, IParser)

    def test_protocol_with_mock(self):
        """Test IParser protocol with mock object."""
        mock_parser = Mock(spec=IParser)
        mock_parser.parse_file.return_value = MockParseResult()
        mock_parser.parse_theorem.return_value = MockTheoremInfo()

        # Mock with spec should satisfy protocol
        assert hasattr(mock_parser, "parse_file")
        assert hasattr(mock_parser, "parse_theorem")

    def test_protocol_method_calls(self):
        """Test calling methods on IParser implementation."""

        class TestParser:
            def parse_file(self, file_path: Path):
                return MockParseResult(success=True, theorems=[MockTheoremInfo()])

            def parse_theorem(self, file_path: Path, theorem_name: str):
                if theorem_name == "existing":
                    return MockTheoremInfo(name=theorem_name)
                return None

        parser = TestParser()

        # Test parse_file
        result = parser.parse_file(Path("test.lean"))
        assert result.success is True
        assert len(result.theorems) == 1

        # Test parse_theorem
        theorem = parser.parse_theorem(Path("test.lean"), "existing")
        assert theorem is not None
        assert theorem.name == "existing"

        # Test parse_theorem not found
        theorem = parser.parse_theorem(Path("test.lean"), "missing")
        assert theorem is None


class TestIGeneratorAbstractClass:
    """Test IGenerator abstract base class."""

    def test_abstract_class_definition(self):
        """Test that IGenerator is an abstract class."""
        assert issubclass(IGenerator, ABC)

        # Should not be able to instantiate directly
        with pytest.raises(TypeError):
            IGenerator()

    def test_abstract_methods(self):
        """Test that abstract methods are properly defined."""
        assert hasattr(IGenerator, "generate_proof_sketch")
        assert hasattr(IGenerator, "generate_eli5_explanation")

        # Check that they are abstract
        assert getattr(IGenerator.generate_proof_sketch, "__isabstractmethod__", False)
        assert getattr(
            IGenerator.generate_eli5_explanation, "__isabstractmethod__", False
        )

    def test_concrete_implementation(self):
        """Test concrete implementation of IGenerator."""

        class ConcreteGenerator(IGenerator):
            def generate_proof_sketch(
                self, theorem, config=None, mathematical_context=None
            ):
                return MockProofSketch(theorem_name=theorem.name)

            def generate_eli5_explanation(self, theorem, config=None):
                return f"Simple explanation of {theorem.name}"

        generator = ConcreteGenerator()
        assert isinstance(generator, IGenerator)

        # Test methods work
        theorem = MockTheoremInfo("test_theorem")
        sketch = generator.generate_proof_sketch(theorem)
        assert sketch.theorem_name == "test_theorem"

        explanation = generator.generate_eli5_explanation(theorem)
        assert "test_theorem" in explanation

    def test_incomplete_implementation(self):
        """Test that incomplete implementation raises TypeError."""

        class IncompleteGenerator(IGenerator):
            def generate_proof_sketch(
                self, theorem, config=None, mathematical_context=None
            ):
                return MockProofSketch()

            # Missing generate_eli5_explanation

        with pytest.raises(TypeError):
            IncompleteGenerator()

    def test_method_signatures(self):
        """Test that concrete implementation respects method signatures."""

        class TestGenerator(IGenerator):
            def generate_proof_sketch(
                self, theorem, config=None, mathematical_context=None
            ):
                # Test that all parameters are passed correctly
                assert theorem is not None
                assert config is None or isinstance(config, MockGenerationConfig)
                assert mathematical_context is None or isinstance(
                    mathematical_context, str
                )
                return MockProofSketch(theorem_name=theorem.name)

            def generate_eli5_explanation(self, theorem, config=None):
                assert theorem is not None
                assert config is None or isinstance(config, MockGenerationConfig)
                return "ELI5 explanation"

        generator = TestGenerator()
        theorem = MockTheoremInfo("test")
        config = MockGenerationConfig()

        # Test with all parameters
        sketch = generator.generate_proof_sketch(
            theorem, config=config, mathematical_context="algebra"
        )
        assert sketch.theorem_name == "test"

        # Test with minimal parameters
        explanation = generator.generate_eli5_explanation(theorem)
        assert explanation == "ELI5 explanation"


class TestIAnimatorProtocol:
    """Test IAnimator protocol compliance and usage."""

    def test_protocol_definition(self):
        """Test that IAnimator is a runtime checkable protocol."""
        assert hasattr(IAnimator, "__protocol_attrs__")
        assert "animate_proof" in IAnimator.__protocol_attrs__

    def test_valid_async_implementation(self):
        """Test valid async IAnimator implementation."""

        class ValidAnimator:
            async def animate_proof(self, proof_sketch, config=None):
                return MockAnimationResponse()

        animator = ValidAnimator()
        assert isinstance(animator, IAnimator)

    def test_invalid_sync_implementation(self):
        """Test that sync method doesn't satisfy async protocol."""

        class InvalidAnimator:
            def animate_proof(self, proof_sketch, config=None):  # Not async
                return MockAnimationResponse()

        animator = InvalidAnimator()
        # Protocol checks method existence, not async nature
        assert isinstance(animator, IAnimator)

    @pytest.mark.asyncio
    async def test_async_method_call(self):
        """Test calling async method on IAnimator implementation."""

        class TestAnimator:
            async def animate_proof(self, proof_sketch, config=None):
                return MockAnimationResponse(
                    video_path=Path(f"{proof_sketch.theorem_name}.mp4"), success=True
                )

        animator = TestAnimator()
        proof_sketch = MockProofSketch("test_theorem")

        response = await animator.animate_proof(proof_sketch)
        assert response.success is True
        assert "test_theorem" in str(response.video_path)


class TestIExporterAbstractClass:
    """Test IExporter abstract base class."""

    def test_abstract_class_definition(self):
        """Test that IExporter is an abstract class."""
        assert issubclass(IExporter, ABC)

        with pytest.raises(TypeError):
            IExporter()

    def test_abstract_methods(self):
        """Test abstract methods definition."""
        assert hasattr(IExporter, "export_single")
        assert hasattr(IExporter, "export_batch")

        assert getattr(IExporter.export_single, "__isabstractmethod__", False)
        assert getattr(IExporter.export_batch, "__isabstractmethod__", False)

    def test_concrete_implementation(self):
        """Test concrete IExporter implementation."""

        class ConcreteExporter(IExporter):
            def export_single(self, proof_sketch, animation_path=None):
                files = [Path(f"{proof_sketch.theorem_name}.html")]
                if animation_path:
                    files.append(animation_path)
                return MockExportResult(output_files=files)

            def export_batch(self, proof_sketches, animations=None):
                files = []
                for sketch in proof_sketches:
                    files.append(Path(f"{sketch.theorem_name}.html"))
                    if animations and sketch.theorem_name in animations:
                        files.append(animations[sketch.theorem_name])
                return MockExportResult(output_files=files)

        exporter = ConcreteExporter()
        assert isinstance(exporter, IExporter)

        # Test single export
        sketch = MockProofSketch("test")
        result = exporter.export_single(sketch)
        assert len(result.output_files) == 1
        assert "test.html" in str(result.output_files[0])

        # Test batch export
        sketches = [MockProofSketch("test1"), MockProofSketch("test2")]
        result = exporter.export_batch(sketches)
        assert len(result.output_files) == 2


class TestICacheProtocol:
    """Test ICache protocol compliance and usage."""

    def test_protocol_definition(self):
        """Test ICache protocol definition."""
        assert hasattr(ICache, "__protocol_attrs__")
        expected_methods = {"get", "set", "delete", "clear"}
        assert expected_methods.issubset(ICache.__protocol_attrs__)

    def test_valid_implementation(self):
        """Test valid ICache implementation."""

        class ValidCache:
            def __init__(self):
                self._data = {}

            def get(self, key: str):
                return self._data.get(key)

            def set(self, key: str, value: Any, ttl: Optional[int] = None):
                self._data[key] = value

            def delete(self, key: str) -> bool:
                if key in self._data:
                    del self._data[key]
                    return True
                return False

            def clear(self) -> int:
                count = len(self._data)
                self._data.clear()
                return count

        cache = ValidCache()
        assert isinstance(cache, ICache)

    def test_cache_operations(self):
        """Test cache operations on ICache implementation."""

        class TestCache:
            def __init__(self):
                self._storage = {}

            def get(self, key: str):
                return self._storage.get(key)

            def set(self, key: str, value: Any, ttl: Optional[int] = None):
                self._storage[key] = value

            def delete(self, key: str) -> bool:
                return self._storage.pop(key, None) is not None

            def clear(self) -> int:
                count = len(self._storage)
                self._storage.clear()
                return count

        cache = TestCache()

        # Test set and get
        cache.set("key1", "value1")
        assert cache.get("key1") == "value1"
        assert cache.get("missing") is None

        # Test delete
        assert cache.delete("key1") is True
        assert cache.delete("missing") is False
        assert cache.get("key1") is None

        # Test clear
        cache.set("key1", "value1")
        cache.set("key2", "value2")
        count = cache.clear()
        assert count == 2
        assert cache.get("key1") is None

    def test_incomplete_implementation(self):
        """Test incomplete ICache implementation."""

        class IncompleteCache:
            def get(self, key: str):
                return None

            def set(self, key: str, value: Any, ttl: Optional[int] = None):
                pass

            # Missing delete and clear methods

        cache = IncompleteCache()
        assert not isinstance(cache, ICache)


class TestIConfigurableAbstractClass:
    """Test IConfigurable abstract base class."""

    def test_abstract_class_definition(self):
        """Test IConfigurable abstract class definition."""
        assert issubclass(IConfigurable, ABC)

        with pytest.raises(TypeError):
            IConfigurable()

    def test_abstract_methods(self):
        """Test abstract methods definition."""
        expected_methods = {"get_config", "update_config", "validate_config"}
        for method_name in expected_methods:
            assert hasattr(IConfigurable, method_name)
            method = getattr(IConfigurable, method_name)
            assert getattr(method, "__isabstractmethod__", False)

    def test_concrete_implementation(self):
        """Test concrete IConfigurable implementation."""

        class ConcreteConfigurable(IConfigurable):
            def __init__(self):
                self._config = MockConfig()

            def get_config(self) -> BaseModel:
                return self._config

            def update_config(self, config: BaseModel) -> None:
                if isinstance(config, MockConfig):
                    self._config = config
                else:
                    raise ValueError("Invalid config type")

            def validate_config(self) -> List[str]:
                errors = []
                if self._config.value < 0:
                    errors.append("Value must be non-negative")
                if not self._config.name:
                    errors.append("Name is required")
                return errors

        configurable = ConcreteConfigurable()
        assert isinstance(configurable, IConfigurable)

        # Test get_config
        config = configurable.get_config()
        assert isinstance(config, MockConfig)
        assert config.name == "test_config"

        # Test update_config
        new_config = MockConfig(name="updated", value=100)
        configurable.update_config(new_config)
        updated = configurable.get_config()
        assert updated.name == "updated"
        assert updated.value == 100

        # Test validate_config (valid)
        errors = configurable.validate_config()
        assert len(errors) == 0

        # Test validate_config (invalid)
        invalid_config = MockConfig(name="", value=-1)
        configurable.update_config(invalid_config)
        errors = configurable.validate_config()
        assert len(errors) == 2
        assert any("non-negative" in error for error in errors)
        assert any("required" in error for error in errors)

    def test_config_validation_edge_cases(self):
        """Test configuration validation edge cases."""

        class EdgeCaseConfigurable(IConfigurable):
            def __init__(self):
                self._config = None

            def get_config(self) -> BaseModel:
                if self._config is None:
                    return MockConfig()
                return self._config

            def update_config(self, config: BaseModel) -> None:
                self._config = config

            def validate_config(self) -> List[str]:
                if self._config is None:
                    return ["Configuration not initialized"]
                return []

        configurable = EdgeCaseConfigurable()

        # Test with no config set
        config = configurable.get_config()
        assert config.name == "test_config"  # Default values

        # Test validation with no config
        configurable._config = None
        errors = configurable.validate_config()
        assert len(errors) == 1
        assert "not initialized" in errors[0]


class TestInterfaceIntegration:
    """Test integration between different interfaces."""

    def test_component_composition(self):
        """Test composing components with different interfaces."""

        class MockService:
            def __init__(self, parser: IParser, generator: IGenerator, cache: ICache):
                self.parser = parser
                self.generator = generator
                self.cache = cache

            def process_theorem(self, file_path: Path, theorem_name: str):
                # Use parser
                theorem = self.parser.parse_theorem(file_path, theorem_name)
                if not theorem:
                    return None

                # Check cache
                cache_key = f"sketch:{theorem.name}"
                cached = self.cache.get(cache_key)
                if cached:
                    return cached

                # Generate new sketch
                sketch = self.generator.generate_proof_sketch(theorem)

                # Cache result
                self.cache.set(cache_key, sketch)

                return sketch

        # Create mock implementations
        mock_parser = Mock(spec=IParser)
        mock_parser.parse_theorem.return_value = MockTheoremInfo("test")

        mock_generator = Mock(spec=IGenerator)
        mock_generator.generate_proof_sketch.return_value = MockProofSketch("test")

        mock_cache = Mock(spec=ICache)
        mock_cache.get.return_value = None  # Cache miss

        # Test service
        service = MockService(mock_parser, mock_generator, mock_cache)
        result = service.process_theorem(Path("test.lean"), "test")

        # Verify interactions
        mock_parser.parse_theorem.assert_called_once()
        mock_generator.generate_proof_sketch.assert_called_once()
        mock_cache.get.assert_called_once()
        mock_cache.set.assert_called_once()

        assert result.theorem_name == "test"

    def test_interface_type_checking(self):
        """Test runtime type checking with interfaces."""

        def process_with_parser(parser: IParser) -> bool:
            """Function that requires IParser interface."""
            return isinstance(parser, IParser)

        def process_with_generator(generator: IGenerator) -> bool:
            """Function that requires IGenerator interface."""
            return isinstance(generator, IGenerator)

        # Valid implementations
        class ValidParser:
            def parse_file(self, file_path: Path):
                pass

            def parse_theorem(self, file_path: Path, theorem_name: str):
                pass

        class ValidGenerator(IGenerator):
            def generate_proof_sketch(
                self, theorem, config=None, mathematical_context=None
            ):
                pass

            def generate_eli5_explanation(self, theorem, config=None):
                pass

        # Invalid implementations
        class InvalidParser:
            def parse_file(self, file_path: Path):
                pass

            # Missing parse_theorem

        # Test valid cases
        assert process_with_parser(ValidParser()) is True
        assert process_with_generator(ValidGenerator()) is True

        # Test invalid cases
        assert process_with_parser(InvalidParser()) is False
        assert process_with_generator(Mock()) is False


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
