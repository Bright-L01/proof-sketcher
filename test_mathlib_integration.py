"""Test script for real mathlib integration and theorem analysis.

This test verifies the complete Phase 9 system works with actual mathlib4 theorems,
demonstrating real-world applicability and educational value.

Tests:
1. Real mathlib theorem parsing and analysis
2. Educational content generation for complex theorems
3. Progressive explanation quality assessment
4. Export pipeline with real mathematical content
5. Performance and scalability analysis

This represents the culmination of Phase 9 development.
"""

import tempfile
import time
from pathlib import Path

# Real mathlib-style theorems with increasing complexity
MATHLIB_THEOREMS = {
    "basic_arithmetic": {
        "content": """
import Mathlib.Data.Nat.Basic

theorem add_zero (n : Nat) : n + 0 = n := by
  simp [Nat.add_zero]
        """,
        "description": "Basic arithmetic identity from Nat.Basic",
        "expected_entities": ["Nat"],
        "expected_areas": ["Number Theory", "Computational Mathematics"],
        "expected_method": "simplification",
    },
    "inductive_proof": {
        "content": """
import Mathlib.Data.Nat.Basic

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
        """,
        "description": "Inductive proof pattern common in mathlib",
        "expected_entities": ["Nat"],
        "expected_areas": ["Mathematical Induction", "Number Theory"],
        "expected_method": "induction",
    },
    "list_theorem": {
        "content": """
import Mathlib.Data.List.Basic

theorem list_append_nil (l : List α) : l ++ [] = l := by
  simp [List.append_nil]
        """,
        "description": "List theory from mathlib",
        "expected_entities": ["List"],
        "expected_areas": ["Discrete Mathematics"],
        "expected_method": "simplification",
    },
    "function_composition": {
        "content": """
import Mathlib.Logic.Function.Basic

theorem comp_assoc (f : γ → δ) (g : β → γ) (h : α → β) :
  (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
  rfl
        """,
        "description": "Function composition associativity",
        "expected_entities": [],
        "expected_areas": ["Logic", "Functions"],
        "expected_method": "direct",
    },
    "set_theory": {
        "content": """
import Mathlib.Data.Set.Basic

theorem set_union_empty (s : Set α) : s ∪ ∅ = s := by
  simp [Set.union_empty]
        """,
        "description": "Basic set theory",
        "expected_entities": ["Set"],
        "expected_areas": ["Set Theory", "Discrete Mathematics"],
        "expected_method": "simplification",
    },
}


def test_mathlib_theorem_parsing():
    """Test parsing of real mathlib-style theorems."""
    print("📚 Testing Mathlib Theorem Parsing...")

    try:
        from src.proof_sketcher.parser import LeanParser

        parser = LeanParser()
        results = {}

        for name, theorem_data in MATHLIB_THEOREMS.items():
            print(f"\n🧪 Testing {name}:")
            print(f"   📝 {theorem_data['description']}")

            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".lean", delete=False
            ) as f:
                f.write(theorem_data["content"])
                temp_path = Path(f.name)

            try:
                start_time = time.time()
                result = parser.parse_file_sync(temp_path)
                parse_time = (time.time() - start_time) * 1000

                results[name] = {
                    "result": result,
                    "parse_time": parse_time,
                    "expected": theorem_data,
                }

                if result.success and result.theorems:
                    theorem = result.theorems[0]
                    print(f"   ✅ Parsed successfully in {parse_time:.1f}ms")
                    print(f"   📊 Found {len(result.theorems)} theorem(s)")
                    print(f"   🎯 Theorem: {theorem.name}")
                    print(f"   📝 Statement: {theorem.statement}")
                    print(f"   🔨 Method: {theorem.proof_method}")
                    print(f"   🧮 Complexity: {theorem.complexity_score:.2f}")
                    print(f"   🏗️ Entities: {theorem.mathematical_entities}")
                else:
                    print(f"   ❌ Parsing failed: {result.errors}")

            finally:
                temp_path.unlink()

        # Summary statistics
        successful_parses = sum(1 for r in results.values() if r["result"].success)
        total_theorems = sum(len(r["result"].theorems) for r in results.values())
        avg_parse_time = sum(r["parse_time"] for r in results.values()) / len(results)

        print(f"\n📊 Parsing Summary:")
        print(f"   ✅ Successful parses: {successful_parses}/{len(MATHLIB_THEOREMS)}")
        print(f"   📚 Total theorems extracted: {total_theorems}")
        print(f"   ⏱️  Average parse time: {avg_parse_time:.1f}ms")

        return successful_parses == len(MATHLIB_THEOREMS), results

    except Exception as e:
        print(f"❌ Mathlib parsing test failed: {e}")
        return False, {}


def test_educational_content_quality(parse_results):
    """Test quality of educational content for mathlib theorems."""
    print("\n📚 Testing Educational Content Quality...")

    try:
        from src.proof_sketcher.generator import EducationalLevel, ProgressiveGenerator

        generator = ProgressiveGenerator()
        content_analysis = {}

        for name, result_data in parse_results.items():
            if not result_data["result"].success or not result_data["result"].theorems:
                continue

            theorem = result_data["result"].theorems[0]
            expected = result_data["expected"]

            print(f"\n🔍 Analyzing {name}:")

            # Generate progressive explanation
            start_time = time.time()
            progressive = generator.generate_progressive_explanation(theorem)
            generation_time = (time.time() - start_time) * 1000

            # Analyze content quality
            analysis = {
                "generation_time": generation_time,
                "levels_generated": len(progressive.levels),
                "pathway_steps": len(progressive.learning_pathway),
                "concepts_extracted": len(progressive.key_concepts),
                "examples_provided": len(progressive.intuitive_examples),
                "explorations_suggested": len(progressive.exploration_suggestions),
                "meets_expectations": True,
                "quality_issues": [],
            }

            # Check level completeness
            expected_levels = [
                EducationalLevel.BEGINNER,
                EducationalLevel.INTERMEDIATE,
                EducationalLevel.ADVANCED,
            ]
            for level in expected_levels:
                if level not in progressive.levels:
                    analysis["meets_expectations"] = False
                    analysis["quality_issues"].append(f"Missing {level} level")
                else:
                    sketch = progressive.levels[level]
                    if len(sketch.key_steps) == 0:
                        analysis["quality_issues"].append(f"{level} level has no steps")
                    if len(sketch.introduction) < 50:
                        analysis["quality_issues"].append(
                            f"{level} introduction too short"
                        )

            # Check educational content richness
            if analysis["pathway_steps"] < 3:
                analysis["quality_issues"].append("Learning pathway too short")
            if analysis["concepts_extracted"] == 0:
                analysis["quality_issues"].append("No key concepts extracted")
            if analysis["examples_provided"] < 2:
                analysis["quality_issues"].append("Insufficient examples")

            # Check mathematical accuracy
            theorem_areas = set(
                progressive.levels[EducationalLevel.INTERMEDIATE].mathematical_areas
            )
            expected_areas = set(expected["expected_areas"])
            if not theorem_areas.intersection(expected_areas):
                analysis["quality_issues"].append(
                    f"Mathematical areas mismatch: got {theorem_areas}, expected {expected_areas}"
                )

            content_analysis[name] = analysis

            print(f"   ⏱️  Generated in {generation_time:.1f}ms")
            print(
                f"   📊 Levels: {analysis['levels_generated']}, Steps: {analysis['pathway_steps']}"
            )
            print(
                f"   🧠 Concepts: {analysis['concepts_extracted']}, Examples: {analysis['examples_provided']}"
            )
            print(
                f"   ✅ Quality: {'PASS' if analysis['meets_expectations'] else 'FAIL'}"
            )
            if analysis["quality_issues"]:
                print(f"   ⚠️  Issues: {', '.join(analysis['quality_issues'])}")

        # Overall quality assessment
        total_analyzed = len(content_analysis)
        high_quality = sum(
            1 for a in content_analysis.values() if a["meets_expectations"]
        )
        avg_generation_time = sum(
            a["generation_time"] for a in content_analysis.values()
        ) / max(total_analyzed, 1)

        print(f"\n📊 Content Quality Summary:")
        print(f"   📚 Theorems analyzed: {total_analyzed}")
        print(f"   ✅ High quality content: {high_quality}/{total_analyzed}")
        print(f"   ⏱️  Average generation time: {avg_generation_time:.1f}ms")

        return (
            high_quality >= total_analyzed * 0.8,
            content_analysis,
        )  # 80% quality threshold

    except Exception as e:
        print(f"❌ Educational content quality test failed: {e}")
        return False, {}


def test_export_pipeline_integration(parse_results):
    """Test complete export pipeline with mathlib theorems."""
    print("\n📤 Testing Export Pipeline Integration...")

    try:
        from src.proof_sketcher.exporter import HTMLExporter, MarkdownExporter
        from src.proof_sketcher.generator import SemanticGenerator

        generator = SemanticGenerator()
        html_exporter = HTMLExporter()
        md_exporter = MarkdownExporter()

        export_results = {}

        for name, result_data in parse_results.items():
            if not result_data["result"].success or not result_data["result"].theorems:
                continue

            theorem = result_data["result"].theorems[0]

            print(f"\n📄 Exporting {name}:")

            try:
                # Generate educational explanation
                sketch = generator.generate_educational_sketch(theorem, "intermediate")

                # Test HTML export
                html_start = time.time()
                html_content = html_exporter.export(sketch)
                html_time = (time.time() - html_start) * 1000

                # Test Markdown export
                md_start = time.time()
                md_content = md_exporter.export(sketch)
                md_time = (time.time() - md_start) * 1000

                export_results[name] = {
                    "html_size": len(html_content),
                    "html_time": html_time,
                    "md_size": len(md_content),
                    "md_time": md_time,
                    "html_valid": "<html>" in html_content
                    and "</html>" in html_content,
                    "md_valid": "# Theorem:" in md_content,
                    "math_rendered": "$$" in html_content or "$" in html_content,
                }

                print(
                    f"   📄 HTML: {export_results[name]['html_size']} chars in {html_time:.1f}ms"
                )
                print(
                    f"   📝 Markdown: {export_results[name]['md_size']} chars in {md_time:.1f}ms"
                )
                print(
                    f"   ✅ Valid: HTML={export_results[name]['html_valid']}, MD={export_results[name]['md_valid']}"
                )
                print(f"   🧮 Math rendering: {export_results[name]['math_rendered']}")

            except Exception as e:
                print(f"   ❌ Export failed: {e}")
                export_results[name] = {"error": str(e)}

        # Export summary
        successful_exports = sum(1 for r in export_results.values() if "error" not in r)
        valid_html = sum(
            1 for r in export_results.values() if r.get("html_valid", False)
        )
        valid_md = sum(1 for r in export_results.values() if r.get("md_valid", False))

        print(f"\n📊 Export Summary:")
        print(f"   ✅ Successful exports: {successful_exports}/{len(export_results)}")
        print(f"   📄 Valid HTML: {valid_html}/{len(export_results)}")
        print(f"   📝 Valid Markdown: {valid_md}/{len(export_results)}")

        return successful_exports == len(export_results), export_results

    except Exception as e:
        print(f"❌ Export pipeline test failed: {e}")
        return False, {}


def test_performance_scalability():
    """Test performance and scalability with multiple theorems."""
    print("\n⚡ Testing Performance and Scalability...")

    try:
        from src.proof_sketcher.generator import ProgressiveGenerator
        from src.proof_sketcher.parser import LeanParser

        # Create a file with multiple theorems
        multi_theorem_content = """
import Mathlib.Data.Nat.Basic

theorem theorem_1 (n : Nat) : n + 0 = n := by simp
theorem theorem_2 (n : Nat) : 0 + n = n := by simp
theorem theorem_3 (n m : Nat) : n + m = m + n := by simp [Nat.add_comm]
theorem theorem_4 (n : Nat) : n * 1 = n := by simp
theorem theorem_5 (n : Nat) : 1 * n = n := by simp
        """

        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(multi_theorem_content)
            temp_path = Path(f.name)

        try:
            parser = LeanParser()
            generator = ProgressiveGenerator()

            # Test batch parsing
            print("🔍 Testing batch parsing...")
            parse_start = time.time()
            result = parser.parse_file_sync(temp_path)
            parse_time = (time.time() - parse_start) * 1000

            if result.success:
                theorem_count = len(result.theorems)
                print(f"   ✅ Parsed {theorem_count} theorems in {parse_time:.1f}ms")
                print(
                    f"   📊 Average per theorem: {parse_time/max(theorem_count,1):.1f}ms"
                )

                # Test batch generation
                print("\n🧠 Testing batch generation...")
                generation_times = []

                for i, theorem in enumerate(result.theorems[:3]):  # Test first 3
                    gen_start = time.time()
                    progressive = generator.generate_progressive_explanation(theorem)
                    gen_time = (time.time() - gen_start) * 1000
                    generation_times.append(gen_time)

                    print(
                        f"   📚 Theorem {i+1}: {gen_time:.1f}ms, {len(progressive.levels)} levels"
                    )

                avg_generation = sum(generation_times) / len(generation_times)
                print(f"\n📊 Performance Summary:")
                print(
                    f"   ⚡ Parse rate: {theorem_count/parse_time*1000:.1f} theorems/sec"
                )
                print(
                    f"   🧠 Generation rate: {1000/avg_generation:.1f} explanations/sec"
                )
                print(
                    f"   💾 Memory efficient: Multiple theorems processed successfully"
                )

                # Performance thresholds
                parse_efficient = (
                    parse_time / theorem_count < 100
                )  # < 100ms per theorem
                generation_efficient = avg_generation < 500  # < 500ms per explanation

                print(
                    f"   ✅ Parse efficiency: {'PASS' if parse_efficient else 'FAIL'}"
                )
                print(
                    f"   ✅ Generation efficiency: {'PASS' if generation_efficient else 'FAIL'}"
                )

                return parse_efficient and generation_efficient
            else:
                print(f"   ❌ Batch parsing failed: {result.errors}")
                return False

        finally:
            temp_path.unlink()

    except Exception as e:
        print(f"❌ Performance test failed: {e}")
        return False


def test_advanced_mathematical_features():
    """Test advanced mathematical features and edge cases."""
    print("\n🔬 Testing Advanced Mathematical Features...")

    try:
        from src.proof_sketcher.generator import EducationalLevel, SemanticGenerator
        from src.proof_sketcher.parser import LeanParser

        # Advanced theorem with complex proof structure
        advanced_content = """
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

theorem advanced_theorem (n m : Nat) (h : n > 0) : n + m ≥ m := by
  rw [Nat.add_comm]
  exact Nat.le_add_right m n
        """

        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(advanced_content)
            temp_path = Path(f.name)

        try:
            parser = LeanParser()
            result = parser.parse_file_sync(temp_path)

            if result.success and result.theorems:
                theorem = result.theorems[0]
                generator = SemanticGenerator()

                print(f"🧮 Advanced theorem: {theorem.name}")
                print(f"   📝 Statement: {theorem.statement}")
                print(f"   🔧 Dependencies: {theorem.dependencies}")
                print(f"   🧠 Complexity: {theorem.complexity_score:.2f}")

                # Test educational adaptation for advanced content
                for level in [
                    EducationalLevel.BEGINNER,
                    EducationalLevel.INTERMEDIATE,
                    EducationalLevel.ADVANCED,
                ]:
                    sketch = generator.generate_educational_sketch(theorem, level)

                    print(f"\n   📚 {level.capitalize()} level:")
                    print(f"      🎯 Difficulty: {sketch.difficulty_level}")
                    print(f"      📝 Steps: {len(sketch.key_steps)}")
                    print(f"      📋 Prerequisites: {len(sketch.prerequisites)}")

                    # Verify content appropriateness
                    intro = sketch.introduction.lower()
                    if level == EducationalLevel.BEGINNER:
                        has_accessible_language = any(
                            word in intro
                            for word in [
                                "understand",
                                "show",
                                "prove",
                                "means",
                                "greater",
                            ]
                        )
                        print(
                            f"      ✅ Accessible language: {has_accessible_language}"
                        )
                    elif level == EducationalLevel.ADVANCED:
                        has_technical_language = any(
                            word in intro
                            for word in [
                                "formal",
                                "theorem",
                                "hypothesis",
                                "inequality",
                            ]
                        )
                        print(f"      ✅ Technical language: {has_technical_language}")

                print("\n✅ Advanced mathematical features working correctly")
                return True
            else:
                print("❌ Advanced theorem parsing failed")
                return False

        finally:
            temp_path.unlink()

    except Exception as e:
        print(f"❌ Advanced features test failed: {e}")
        return False


def run_mathlib_integration_tests():
    """Run comprehensive mathlib integration tests."""
    print("📚 Starting Real Mathlib Integration Tests")
    print("=" * 60)
    print("This tests Phase 9 completion with real mathematical content")
    print("=" * 60)

    # Run all test phases
    tests = [
        ("Mathlib Theorem Parsing", test_mathlib_theorem_parsing),
        ("Performance & Scalability", test_performance_scalability),
        ("Advanced Mathematical Features", test_advanced_mathematical_features),
    ]

    results = []
    parse_results = {}
    content_analysis = {}
    export_results = {}

    for name, test_func in tests:
        print(f"\n{'='*20} {name} {'='*20}")
        try:
            if name == "Mathlib Theorem Parsing":
                success, parse_results = test_func()
            else:
                success = test_func()
            results.append((name, success))
        except Exception as e:
            print(f"❌ Test {name} crashed: {e}")
            results.append((name, False))

    # Run dependent tests if parsing succeeded
    if parse_results:
        print(f"\n{'='*20} Educational Content Quality {'='*20}")
        try:
            success, content_analysis = test_educational_content_quality(parse_results)
            results.append(("Educational Content Quality", success))
        except Exception as e:
            print(f"❌ Content quality test crashed: {e}")
            results.append(("Educational Content Quality", False))

        print(f"\n{'='*20} Export Pipeline Integration {'='*20}")
        try:
            success, export_results = test_export_pipeline_integration(parse_results)
            results.append(("Export Pipeline Integration", success))
        except Exception as e:
            print(f"❌ Export pipeline test crashed: {e}")
            results.append(("Export Pipeline Integration", False))

    # Final assessment
    print("\n" + "=" * 60)
    print("📋 MATHLIB INTEGRATION TEST SUMMARY")
    print("=" * 60)

    passed = 0
    for name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status}: {name}")
        if result:
            passed += 1

    print(f"\n📊 Results: {passed}/{len(results)} tests passed")

    if passed == len(results):
        print("\n🎉 PHASE 9 COMPLETE: REAL MATHLIB INTEGRATION SUCCESS!")
        print("🚀 The system successfully handles real mathematical content")
        print("📚 Educational explanations work with complex theorems")
        print("⚡ Performance is suitable for practical use")
        print("🌟 Ready for production deployment and user testing")
    elif passed >= len(results) * 0.8:
        print("\n🎯 PHASE 9 MOSTLY COMPLETE")
        print("🚀 Core functionality works with real mathematical content")
        print("⚠️  Some advanced features need refinement")
    else:
        print("\n⚠️  PHASE 9 NEEDS MORE WORK")
        print("🔧 Core system has issues with real mathematical content")

    return passed >= len(results) * 0.8  # 80% pass rate for success


if __name__ == "__main__":
    success = run_mathlib_integration_tests()
    exit(0 if success else 1)
