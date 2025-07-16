"""Unit tests for doc-gen4 plugin system."""

import json
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from proof_sketcher.docgen_plugin.content_generator import EducationalContentGenerator
from proof_sketcher.docgen_plugin.lake_facet import (
    EducationalLakeFacet,
    LakeFacetConfig,
)
from proof_sketcher.docgen_plugin.module_processor import ModuleProcessor
from proof_sketcher.docgen_plugin.template_engine import EducationalTemplateEngine


class TestModuleProcessor:
    """Test doc-gen4 module processor."""

    def test_processor_initialization(self):
        """Test processor initialization."""
        processor = ModuleProcessor()
        assert processor is not None
        assert processor.content_generator is not None
        assert processor.progressive_generator is not None

    def test_enhance_module_json_dict(self):
        """Test enhancing module JSON from dict."""
        processor = ModuleProcessor()

        sample_json = {
            "name": "Test.Module",
            "doc": "Test module",
            "declarations": [
                {
                    "name": "test_theorem",
                    "kind": "theorem",
                    "doc": "A test theorem",
                    "type": "∀ (n : ℕ), n + 0 = n",
                    "proof": "by simp",
                }
            ],
        }

        enhanced = processor.enhance_module_json(sample_json)

        assert enhanced["name"] == "Test.Module"
        assert enhanced["doc"] == "Test module"
        assert len(enhanced["declarations"]) == 1
        assert "educational_metadata" in enhanced
        assert enhanced["educational_metadata"]["total_declarations"] == 1

    def test_enhance_module_json_string(self):
        """Test enhancing module JSON from string."""
        processor = ModuleProcessor()

        sample_json = {
            "name": "Test.Module",
            "declarations": [
                {
                    "name": "test_theorem",
                    "kind": "theorem",
                    "type": "True",
                    "proof": "trivial",
                }
            ],
        }

        json_string = json.dumps(sample_json)
        enhanced = processor.enhance_module_json(json_string)

        assert enhanced["name"] == "Test.Module"
        assert len(enhanced["declarations"]) == 1

    def test_enhance_declaration_theorem(self):
        """Test enhancing a theorem declaration."""
        processor = ModuleProcessor()

        declaration = {
            "name": "add_comm",
            "kind": "theorem",
            "doc": "Addition is commutative",
            "type": "∀ (a b : ℕ), a + b = b + a",
            "proof": "by rw [add_comm]",
        }

        enhanced = processor._enhance_declaration(declaration)

        assert enhanced.name == "add_comm"
        assert enhanced.kind == "theorem"
        assert enhanced.doc == "Addition is commutative"
        assert enhanced.type == "∀ (a b : ℕ), a + b = b + a"
        assert enhanced.original_data == declaration
        # Educational content may or may not be generated depending on implementation

    def test_enhance_declaration_non_theorem(self):
        """Test enhancing a non-theorem declaration."""
        processor = ModuleProcessor()

        declaration = {
            "name": "test_def",
            "kind": "def",
            "doc": "A definition",
            "type": "ℕ → ℕ",
            "proof": "fun n => n + 1",
        }

        enhanced = processor._enhance_declaration(declaration)

        assert enhanced.name == "test_def"
        assert enhanced.kind == "def"
        assert (
            enhanced.educational_content is None
        )  # No educational content for definitions

    def test_get_educational_stats(self):
        """Test getting educational statistics."""
        processor = ModuleProcessor()

        enhanced_json = {
            "declarations": [
                {
                    "name": "theorem1",
                    "kind": "theorem",
                    "educational_content": {"some": "content"},
                },
                {"name": "theorem2", "kind": "theorem", "educational_content": None},
                {
                    "name": "lemma1",
                    "kind": "lemma",
                    "educational_content": {"some": "content"},
                },
                {"name": "def1", "kind": "def", "educational_content": None},
            ]
        }

        stats = processor.get_educational_stats(enhanced_json)

        assert stats["total_declarations"] == 4
        assert stats["educational_declarations"] == 2
        assert stats["theorem_count"] == 2
        assert stats["lemma_count"] == 1
        assert stats["educational_coverage"] == 50.0

    def test_batch_enhance_modules(self, temp_dir):
        """Test batch enhancing multiple modules."""
        processor = ModuleProcessor()

        # Create input directory with sample JSON files
        input_dir = temp_dir / "input"
        input_dir.mkdir()

        output_dir = temp_dir / "output"
        output_dir.mkdir()

        # Create sample module JSON
        sample_json = {
            "name": "Test.Module",
            "declarations": [
                {
                    "name": "test_theorem",
                    "kind": "theorem",
                    "type": "True",
                    "proof": "trivial",
                }
            ],
        }

        json_file = input_dir / "Test.Module.json"
        with open(json_file, "w") as f:
            json.dump(sample_json, f)

        processor.batch_enhance_modules(input_dir, output_dir)

        # Check output file was created
        output_file = output_dir / "Test.Module.json"
        assert output_file.exists()

        with open(output_file, "r") as f:
            enhanced = json.load(f)

        assert enhanced["name"] == "Test.Module"
        assert "educational_metadata" in enhanced


class TestEducationalContentGenerator:
    """Test educational content generator."""

    def test_generator_initialization(self):
        """Test generator initialization."""
        generator = EducationalContentGenerator()
        assert generator is not None
        assert generator.progressive_generator is not None
        assert generator.semantic_generator is not None

    def test_generate_content_from_docgen(self):
        """Test generating content from doc-gen4 data."""
        generator = EducationalContentGenerator()

        content = generator.generate_content_from_docgen(
            name="add_comm",
            statement="∀ (a b : ℕ), a + b = b + a",
            proof="by rw [add_comm]",
            docstring="Addition is commutative",
        )

        assert "progressive_explanations" in content
        assert "learning_pathway" in content
        assert "key_concepts" in content
        assert "metadata" in content
        assert "interactive_elements" in content
        assert "generated_at" in content

    def test_create_theorem_info(self):
        """Test creating TheoremInfo from doc-gen4 data."""
        generator = EducationalContentGenerator()

        theorem_info = generator._create_theorem_info(
            name="test_theorem",
            statement="1 + 1 = 2",
            proof="by rfl",
            docstring="Simple arithmetic",
        )

        assert theorem_info.name == "test_theorem"
        assert theorem_info.statement == "1 + 1 = 2"
        assert theorem_info.proof == "by rfl"
        assert theorem_info.docstring == "Simple arithmetic"

    def test_extract_dependencies(self):
        """Test extracting dependencies from statement and proof."""
        generator = EducationalContentGenerator()

        statement = "∀ (l : List α), l.length = 0 → l = []"
        proof = "by apply List.length_eq_zero"

        dependencies = generator._extract_dependencies(statement, proof)

        assert "List" in dependencies

    def test_extract_namespace(self):
        """Test extracting namespace from theorem name."""
        generator = EducationalContentGenerator()

        assert generator._extract_namespace("Nat.add_comm") == "Nat"
        assert generator._extract_namespace("List.Basic.append_nil") == "List.Basic"
        assert generator._extract_namespace("simple_theorem") is None

    def test_extract_tactics(self):
        """Test extracting tactics from proof."""
        generator = EducationalContentGenerator()

        proof = "by rw [add_comm]; simp; exact trivial"
        tactics = generator._extract_tactics(proof)

        assert "rw" in tactics
        assert "simp" in tactics
        assert "exact" in tactics

    def test_estimate_difficulty(self):
        """Test difficulty estimation."""
        generator = EducationalContentGenerator()

        # Short statement -> beginner
        short_statement = "1 + 1 = 2"
        assert generator._estimate_difficulty(short_statement) == "beginner"

        # Long statement -> advanced
        long_statement = "∀ (α : Type*) [CommRing α] (f : α → α) (h : ∀ x y, f (x + y) = f x + f y), ∃ c, ∀ x, f x = c * x"
        assert generator._estimate_difficulty(long_statement) == "advanced"


class TestEducationalTemplateEngine:
    """Test educational template engine."""

    def test_engine_initialization(self):
        """Test template engine initialization."""
        engine = EducationalTemplateEngine()
        assert engine is not None
        assert engine.env is not None

    def test_render_educational_declaration(self):
        """Test rendering educational declaration."""
        engine = EducationalTemplateEngine()

        declaration = {
            "name": "add_comm",
            "kind": "theorem",
            "type": "∀ (a b : ℕ), a + b = b + a",
            "doc": "Addition is commutative",
            "educational_content": {
                "progressive_explanations": {
                    "beginner": {
                        "title": "Understanding Addition Order",
                        "overview": "Addition order doesn't matter",
                    },
                    "intermediate": {
                        "title": "Commutativity Property",
                        "overview": "Formal proof of commutativity",
                    },
                    "advanced": {
                        "title": "Algebraic Structure",
                        "overview": "Commutative monoid structure",
                    },
                }
            },
        }

        html = engine.render_educational_declaration(declaration)

        assert isinstance(html, str)
        assert "add_comm" in html
        assert "theorem" in html
        assert "beginner" in html
        assert "intermediate" in html
        assert "advanced" in html

    def test_create_educational_assets(self, temp_dir):
        """Test creating educational assets."""
        engine = EducationalTemplateEngine()

        engine.create_educational_assets(temp_dir)

        css_file = temp_dir / "assets" / "educational.css"
        js_file = temp_dir / "assets" / "educational.js"

        assert css_file.exists()
        assert js_file.exists()
        assert css_file.stat().st_size > 0
        assert js_file.stat().st_size > 0

    def test_template_creation(self):
        """Test default template creation."""
        engine = EducationalTemplateEngine()

        template_dir = Path(engine.env.loader.searchpath[0])

        decl_template = template_dir / "educational_declaration.html"
        prog_template = template_dir / "progressive_explanation.html"
        mod_template = template_dir / "educational_module.html"

        assert decl_template.exists()
        assert prog_template.exists()
        assert mod_template.exists()


class TestLakeFacet:
    """Test Lake facet integration."""

    def test_config_creation(self, temp_dir):
        """Test Lake facet configuration."""
        config = LakeFacetConfig(
            input_dir=temp_dir / "input",
            output_dir=temp_dir / "output",
            enable_educational=True,
        )

        assert config.input_dir == temp_dir / "input"
        assert config.output_dir == temp_dir / "output"
        assert config.enable_educational is True
        assert config.educational_levels == ["beginner", "intermediate", "advanced"]

    def test_facet_initialization(self, temp_dir):
        """Test Lake facet initialization."""
        config = LakeFacetConfig(
            input_dir=temp_dir / "input", output_dir=temp_dir / "output"
        )

        facet = EducationalLakeFacet(config)

        assert facet.config == config
        assert facet.module_processor is not None
        assert facet.template_engine is not None
        assert facet.config.output_dir.exists()

    def test_process_module_docs(self, temp_dir):
        """Test processing module documentation."""
        input_dir = temp_dir / "input"
        output_dir = temp_dir / "output"
        input_dir.mkdir()
        output_dir.mkdir()

        config = LakeFacetConfig(input_dir=input_dir, output_dir=output_dir)
        facet = EducationalLakeFacet(config)

        # Create sample module JSON
        sample_json = {
            "name": "Test.Module",
            "declarations": [
                {
                    "name": "test_theorem",
                    "kind": "theorem",
                    "type": "True",
                    "proof": "trivial",
                }
            ],
        }

        json_file = input_dir / "Test.Module.json"
        with open(json_file, "w") as f:
            json.dump(sample_json, f)

        result = facet.process_module_docs("Test.Module")

        assert result["success"] is True
        assert result["module_name"] == "Test.Module"
        assert "enhanced_json_path" in result
        assert "educational_html_path" in result
        assert "stats" in result

    def test_process_nonexistent_module(self, temp_dir):
        """Test processing non-existent module."""
        config = LakeFacetConfig(
            input_dir=temp_dir / "input", output_dir=temp_dir / "output"
        )
        facet = EducationalLakeFacet(config)

        result = facet.process_module_docs("NonExistent.Module")

        assert "error" in result
        assert "Module JSON not found" in result["error"]

    def test_process_all_modules(self, temp_dir):
        """Test processing all modules."""
        input_dir = temp_dir / "input"
        output_dir = temp_dir / "output"
        input_dir.mkdir()
        output_dir.mkdir()

        config = LakeFacetConfig(input_dir=input_dir, output_dir=output_dir)
        facet = EducationalLakeFacet(config)

        # Create multiple sample modules
        for i in range(3):
            sample_json = {
                "name": f"Test.Module{i}",
                "declarations": [
                    {
                        "name": f"test_theorem_{i}",
                        "kind": "theorem",
                        "type": "True",
                        "proof": "trivial",
                    }
                ],
            }

            json_file = input_dir / f"Test.Module{i}.json"
            with open(json_file, "w") as f:
                json.dump(sample_json, f)

        results = facet.process_all_modules()

        assert results["total_modules"] == 3
        assert results["success_count"] == 3
        assert results["error_count"] == 0
        assert len(results["processed_modules"]) == 3

    def test_generate_educational_assets(self, temp_dir):
        """Test generating educational assets."""
        config = LakeFacetConfig(
            input_dir=temp_dir / "input", output_dir=temp_dir / "output"
        )
        facet = EducationalLakeFacet(config)

        facet.generate_educational_assets()

        css_file = temp_dir / "output" / "assets" / "educational.css"
        js_file = temp_dir / "output" / "assets" / "educational.js"

        assert css_file.exists()
        assert js_file.exists()

    def test_create_educational_index(self, temp_dir):
        """Test creating educational index."""
        config = LakeFacetConfig(
            input_dir=temp_dir / "input", output_dir=temp_dir / "output"
        )
        facet = EducationalLakeFacet(config)

        processing_results = {
            "processed_modules": [
                {
                    "module_name": "Test.Module",
                    "educational_html_path": "Test.Module_educational.html",
                    "stats": {
                        "total_declarations": 1,
                        "educational_declarations": 1,
                        "educational_coverage": 100.0,
                    },
                }
            ],
            "total_modules": 1,
            "success_count": 1,
            "error_count": 0,
        }

        index_path = facet.create_educational_index(processing_results)

        assert Path(index_path).exists()
        assert "educational_index.html" in index_path

        # Check content
        with open(index_path, "r") as f:
            content = f.read()

        assert "Educational Lean 4 Documentation" in content
        assert "Test.Module" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
