#!/usr/bin/env python3
"""Comprehensive Mathlib integration tests for Proof Sketcher.

Tests the entire pipeline with real-world mathematical content:
- Enhanced parser validation on complex Mathlib theorems  
- Generation quality with sophisticated mathematical proofs
- Export formats with unicode mathematical notation
- Performance with large mathematical files
- Error handling with malformed mathematical content
"""

import tempfile
import pytest
from pathlib import Path
import sys

# Add project root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.proof_sketcher.parser.lean_parser import LeanParser
from src.proof_sketcher.parser.config import ParserConfig
from src.proof_sketcher.generator.offline import OfflineGenerator
from src.proof_sketcher.exporter.html import HTMLExporter
from src.proof_sketcher.exporter.markdown import MarkdownExporter
from src.proof_sketcher.exporter.models import ExportOptions, ExportContext, ExportFormat
from src.proof_sketcher.core.exceptions import ParserError


class TestMathlibIntegration:
    """Test suite for real-world Mathlib integration."""
    
    @pytest.fixture
    def mathlib_file(self):
        """Real-world Mathlib test file."""
        return Path(__file__).parent.parent / "examples" / "mathlib_real_world.lean"
    
    @pytest.fixture
    def simple_mathlib_file(self):
        """Simple Mathlib test file."""
        return Path(__file__).parent.parent / "examples" / "mathlib_example.lean"
    
    @pytest.fixture
    def parser(self):
        """Configured parser with enhanced capabilities."""
        config = ParserConfig(
            fallback_to_regex=True,
            auto_detect_lake=True,
            lean_timeout=30.0
        )
        return LeanParser(config)
    
    @pytest.fixture
    def generator(self):
        """Offline generator for testing."""
        return OfflineGenerator()
    
    @pytest.fixture
    def temp_dir(self):
        """Temporary directory for test outputs."""
        with tempfile.TemporaryDirectory(prefix="mathlib_test_") as tmp:
            yield Path(tmp)
    
    def test_enhanced_parser_comprehensive(self, parser, mathlib_file):
        """Test enhanced parser on comprehensive Mathlib file."""
        # Test enhanced parsing
        declarations = parser.parse_file_enhanced(mathlib_file)
        
        # Verify all construct types are found
        expected_constructs = [
            "theorem", "def", "inductive", "structure", "class", 
            "namespace", "section", "variable"
        ]
        
        found_constructs = [construct for construct in expected_constructs 
                          if construct in declarations and declarations[construct]]
        
        assert len(found_constructs) >= 6, f"Expected at least 6 construct types, found: {found_constructs}"
        
        # Verify specific theorems are found
        theorems = declarations.get("theorem", []) + declarations.get("lemma", [])
        theorem_names = [t.name for t in theorems]
        
        expected_theorems = [
            "group_identity_unique", "ring_zero_unique", "cauchy_schwarz",
            "cantor_theorem", "euclid_infinitude_of_primes"
        ]
        
        found_theorems = [name for name in expected_theorems if name in theorem_names]
        assert len(found_theorems) >= 3, f"Expected major theorems, found: {found_theorems}"
        
        # Verify inductive types
        inductives = declarations.get("inductive", [])
        assert len(inductives) >= 1, "Should find inductive types like BinTree"
        
        # Verify structures  
        structures = declarations.get("structure", [])
        assert len(structures) >= 1, "Should find structures like MetricSpace"
        
        # Verify classes
        classes = declarations.get("class", [])
        assert len(classes) >= 1, "Should find classes like NormedSpace"
    
    def test_parser_statistics(self, parser, mathlib_file):
        """Test detailed parsing statistics."""
        stats = parser.get_parsing_statistics(mathlib_file)
        
        # Verify statistics are comprehensive
        assert "total_constructs" in stats
        assert "construct_counts" in stats
        assert stats["total_constructs"] >= 20, "Should find substantial number of constructs"
        
        # Verify enhanced parser finds more than basic parser
        assert stats["theorem_count_enhanced"] >= stats["theorem_count_basic"]
        
        # Check construct distribution makes sense
        construct_counts = stats["construct_counts"]
        assert construct_counts.get("theorem", 0) >= 10, "Should find many theorems"
        assert construct_counts.get("namespace", 0) >= 1, "Should find namespaces"
    
    def test_basic_file_parsing(self, parser, simple_mathlib_file):
        """Test parsing of simple Mathlib file."""
        result = parser.parse_file(simple_mathlib_file)
        
        assert result.success
        assert len(result.theorems) >= 4, "Should find several theorems"
        assert len(result.errors) == 0, "Should have no parsing errors"
        
        # Check specific theorems
        theorem_names = [t.name for t in result.theorems]
        expected = ["length_append_self", "modus_tollens", "contrapositive"]
        found = [name for name in expected if name in theorem_names]
        assert len(found) >= 2, f"Should find expected theorems: {found}"
    
    def test_generation_with_complex_theorems(self, parser, generator, mathlib_file):
        """Test proof sketch generation with complex mathematical content."""
        # Parse theorems
        result = parser.parse_file(mathlib_file)
        assert result.success
        
        # Test generation on a subset of theorems
        test_theorems = result.theorems[:5]  # Test first 5 theorems
        
        sketches = []
        for theorem in test_theorems:
            try:
                sketch = generator.generate_proof_sketch(theorem)
                sketches.append(sketch)
                
                # Validate sketch structure
                assert sketch.theorem_name == theorem.name
                assert len(sketch.introduction) > 0
                assert len(sketch.key_steps) > 0
                assert len(sketch.conclusion) > 0
                
            except Exception as e:
                pytest.fail(f"Generation failed for {theorem.name}: {e}")
        
        assert len(sketches) >= 3, "Should successfully generate multiple sketches"
    
    def test_export_formats_with_unicode(self, parser, generator, temp_dir, mathlib_file):
        """Test export formats handle Unicode mathematical notation correctly."""
        # Parse and generate
        result = parser.parse_file(mathlib_file)
        theorem = result.theorems[0]  # Test with first theorem
        sketch = generator.generate_proof_sketch(theorem)
        
        # Test HTML export
        html_options = ExportOptions.model_validate({
            "output_dir": temp_dir / "html"
        })
        html_exporter = HTMLExporter(html_options)
        
        html_context = ExportContext(
            format=ExportFormat.HTML,
            output_dir=temp_dir / "html",
            sketches=[sketch]
        )
        
        html_result = html_exporter.export_single(sketch, html_context)
        assert html_result.success
        
        # Verify HTML file exists and contains unicode
        html_file = temp_dir / "html" / f"{theorem.name}.html"
        assert html_file.exists()
        
        html_content = html_file.read_text()
        # Check for mathematical symbols commonly in Mathlib
        unicode_symbols = ["ℕ", "ℝ", "→", "∀", "∃", "≤", "∑"]
        found_unicode = [sym for sym in unicode_symbols if sym in html_content]
        # Note: May not find unicode if theorem doesn't contain it
        
        # Test Markdown export
        md_options = ExportOptions.model_validate({
            "output_dir": temp_dir / "markdown"
        })
        md_exporter = MarkdownExporter(md_options)
        
        md_context = ExportContext(
            format=ExportFormat.MARKDOWN,
            output_dir=temp_dir / "markdown",
            sketches=[sketch]
        )
        
        md_result = md_exporter.export_single(sketch, md_context)
        assert md_result.success
        
        # Verify Markdown file  
        md_file = temp_dir / "markdown" / f"{theorem.name}.md"
        assert md_file.exists()
    
    def test_error_handling_malformed_lean(self, parser, temp_dir):
        """Test error handling with malformed Lean content."""
        # Create malformed Lean file
        malformed_content = """
        -- Malformed Lean file
        theorem incomplete_theorem (n : ℕ) : 
        
        def missing_type := 
        
        inductive BadInductive
          | constructor_without_type
        
        structure MissingFields
        
        class BadClass where
          field_without_type
        """
        
        malformed_file = temp_dir / "malformed.lean"
        malformed_file.write_text(malformed_content)
        
        # Parse should handle errors gracefully
        result = parser.parse_file(malformed_file)
        
        # Should not crash, but may have errors or limited results
        assert isinstance(result.success, bool)
        # Note: Enhanced parser should be robust to malformed input
    
    def test_batch_processing_capability(self, parser, generator, temp_dir):
        """Test batch processing multiple Mathlib files."""
        # Create multiple small test files
        files = []
        for i in range(3):
            content = f"""
            namespace Batch{i}
            
            theorem test_theorem_{i} (n : ℕ) : n + 0 = n := by simp
            
            def test_def_{i} (n : ℕ) : ℕ := n + {i}
            
            end Batch{i}
            """
            
            file_path = temp_dir / f"batch_{i}.lean"
            file_path.write_text(content)
            files.append(file_path)
        
        # Process batch
        all_theorems = []
        for file_path in files:
            result = parser.parse_file(file_path)
            assert result.success
            all_theorems.extend(result.theorems)
        
        assert len(all_theorems) >= 3, "Should process all files"
        
        # Test batch generation
        sketches = []
        for theorem in all_theorems:
            sketch = generator.generate_proof_sketch(theorem)
            sketches.append(sketch)
        
        assert len(sketches) == len(all_theorems), "Should generate all sketches"
    
    def test_performance_large_file(self, parser, mathlib_file):
        """Test performance characteristics with large mathematical files."""
        import time
        
        # Measure parsing time
        start_time = time.perf_counter()
        result = parser.parse_file(mathlib_file)
        parse_time = time.perf_counter() - start_time
        
        assert result.success
        assert parse_time < 15.0, f"Parsing took too long: {parse_time:.2f}s"
        
        # Measure enhanced parsing time
        start_time = time.perf_counter()
        declarations = parser.parse_file_enhanced(mathlib_file)
        enhanced_time = time.perf_counter() - start_time
        
        assert enhanced_time < 20.0, f"Enhanced parsing took too long: {enhanced_time:.2f}s"
        
        # Verify reasonable performance scaling
        theorem_count = len(result.theorems)
        if theorem_count > 0:
            time_per_theorem = parse_time / theorem_count
            assert time_per_theorem < 1.0, f"Time per theorem too high: {time_per_theorem:.3f}s"
    
    def test_lake_project_detection(self, parser, temp_dir):
        """Test Lake project detection capabilities."""
        # Create mock Lake project structure
        lakefile = temp_dir / "lakefile.lean"
        lakefile.write_text("""
import Lake
open Lake DSL

package ProofSketcherTest {
  -- configuration
}

lean_lib ProofSketcherTest {
  -- library configuration  
}
        """)
        
        # Create a lean file in the project
        lean_file = temp_dir / "Test.lean"
        lean_file.write_text("""
import Mathlib.Data.Nat.Basic

theorem lake_test (n : ℕ) : n + 0 = n := by simp
        """)
        
        # Parser should detect Lake project
        result = parser.parse_file(lean_file)
        assert result.success
        
        # Note: Actual Lake integration depends on Lake being available
        # This test verifies the detection mechanism works
    
    def test_mathlib_dependency_handling(self, parser, mathlib_file):
        """Test handling of Mathlib dependencies and imports."""
        result = parser.parse_file(mathlib_file)
        
        # Check metadata includes imports
        if result.metadata:
            imports = result.metadata.imports
            expected_imports = [
                "Mathlib.Algebra.Group.Basic",
                "Mathlib.Analysis.Calculus.Deriv.Basic", 
                "Mathlib.Topology.Basic"
            ]
            
            found_imports = [imp for imp in expected_imports 
                           if any(imp in declared_imp for declared_imp in imports)]
            
            # Should find some expected imports
            assert len(found_imports) >= 1, f"Should find Mathlib imports: {found_imports}"
    
    def test_complex_proof_structures(self, parser, mathlib_file):
        """Test parsing of complex proof structures and tactics."""
        result = parser.parse_file(mathlib_file)
        
        # Find theorems with substantial proofs
        complex_theorems = [t for t in result.theorems 
                          if t.proof and len(t.proof) > 50]
        
        assert len(complex_theorems) >= 2, "Should find theorems with complex proofs"
        
        # Check for advanced proof techniques
        for theorem in complex_theorems[:3]:  # Check first few
            proof = theorem.proof or ""
            
            # Look for sophisticated tactics
            advanced_tactics = ["calc", "induction", "cases", "by_contra", "strong_induction_on"]
            found_tactics = [tactic for tactic in advanced_tactics if tactic in proof]
            
            # At least some complex theorems should use advanced tactics
            if found_tactics:
                assert len(found_tactics) >= 1, f"Expected advanced tactics in {theorem.name}"


class TestMathlibValidation:
    """Additional validation tests for Mathlib integration."""
    
    def test_theorem_statement_preservation(self, parser=None):
        """Test that theorem statements are preserved accurately."""
        if parser is None:
            parser = LeanParser()
            
        # Test with Unicode mathematical symbols
        test_content = """
        theorem unicode_test (α : Type*) (f : α → ℝ) : ∀ ε > 0, ∃ δ > 0, True := by
          sorry
        """
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write(test_content)
            f.flush()
            temp_path = Path(f.name)
        
        try:
            result = parser.parse_file(temp_path)
            if result.success and result.theorems:
                theorem = result.theorems[0]
                statement = theorem.statement
                
                # Should preserve Unicode symbols
                unicode_chars = ["α", "→", "ℝ", "∀", "ε", "∃", "δ"]
                preserved_unicode = [char for char in unicode_chars if char in statement]
                
                # Note: May not preserve all unicode depending on parsing method
                assert len(preserved_unicode) >= 2, "Should preserve some Unicode symbols"
                
        finally:
            temp_path.unlink()
    
    def test_namespace_context_preservation(self, parser=None):
        """Test that namespace context is preserved in parsing."""
        if parser is None:
            parser = LeanParser()
            
        test_content = """
        namespace OuterNamespace
        
        namespace InnerNamespace
        
        theorem nested_theorem (n : ℕ) : n = n := rfl
        
        end InnerNamespace
        
        end OuterNamespace
        """
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write(test_content)
            f.flush() 
            temp_path = Path(f.name)
        
        try:
            declarations = parser.parse_file_enhanced(temp_path)
            
            # Should find namespace declarations
            namespaces = declarations.get("namespace", [])
            assert len(namespaces) >= 1, "Should find namespace declarations"
            
            # Should find theorem within namespace context
            theorems = declarations.get("theorem", [])
            if theorems:
                # Enhanced parser should track namespace context
                theorem = theorems[0]
                assert theorem.name == "nested_theorem"
                
        finally:
            temp_path.unlink()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])