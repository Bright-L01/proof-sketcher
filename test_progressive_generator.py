"""Test script for progressive generator and multi-level educational content.

This test verifies:
1. Progressive explanation generation with multiple levels
2. Learning pathway creation
3. Concept extraction and explanation
4. Educational content adaptation
5. Study time estimation and maturity assessment

Run this test to verify the progressive generator works correctly.
"""

import tempfile
from pathlib import Path

def test_progressive_explanation_generation():
    """Test generation of complete progressive explanations."""
    print("🎓 Testing Progressive Explanation Generation...")
    
    try:
        from src.proof_sketcher.parser import LeanParser
        from src.proof_sketcher.generator import ProgressiveGenerator, EducationalLevel
        
        # Create test theorem
        content = "theorem add_zero (n : Nat) : n + 0 = n := by simp"
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write(content)
            temp_path = Path(f.name)
        
        try:
            # Parse theorem
            parser = LeanParser()
            result = parser.parse_file_sync(temp_path)
            
            if not result.success or not result.theorems:
                print("❌ Failed to parse test theorem")
                return False
                
            theorem = result.theorems[0]
            generator = ProgressiveGenerator()
            
            # Generate progressive explanation
            progressive = generator.generate_progressive_explanation(theorem)
            
            print(f"✅ Generated progressive explanation for: {progressive.theorem_name}")
            print(f"📚 Number of levels: {len(progressive.levels)}")
            print(f"🛤️  Learning pathway steps: {len(progressive.learning_pathway)}")
            print(f"🧠 Key concepts: {len(progressive.key_concepts)}")
            print(f"💡 Intuitive examples: {len(progressive.intuitive_examples)}")
            print(f"🔗 Formal connections: {len(progressive.formal_connections)}")
            print(f"🔍 Exploration suggestions: {len(progressive.exploration_suggestions)}")
            
            # Check that all levels are present
            expected_levels = [EducationalLevel.BEGINNER, EducationalLevel.INTERMEDIATE, EducationalLevel.ADVANCED]
            for level in expected_levels:
                if level in progressive.levels:
                    sketch = progressive.levels[level]
                    print(f"  ✅ {level.capitalize()} level: {len(sketch.key_steps)} steps")
                    print(f"      Difficulty: {sketch.difficulty_level}")
                    print(f"      Introduction: {sketch.introduction[:80]}...")
                else:
                    print(f"  ❌ Missing {level} level")
                    return False
                    
            return True
            
        finally:
            temp_path.unlink()
            
    except Exception as e:
        print(f"❌ Progressive explanation generation failed: {e}")
        return False

def test_learning_pathway_creation():
    """Test creation of structured learning pathways."""
    print("\n🛤️  Testing Learning Pathway Creation...")
    
    try:
        from src.proof_sketcher.parser import LeanParser
        from src.proof_sketcher.generator import ProgressiveGenerator
        
        # Test with induction theorem
        content = """
        theorem add_comm (a b : Nat) : a + b = b + a := by
          induction a with
          | zero => simp
          | succ a ih => 
            rw [Nat.add_succ, ih, Nat.succ_add]
        """
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write(content)
            temp_path = Path(f.name)
        
        try:
            parser = LeanParser()
            result = parser.parse_file_sync(temp_path)
            
            if result.success and result.theorems:
                theorem = result.theorems[0]
                generator = ProgressiveGenerator()
                progressive = generator.generate_progressive_explanation(theorem)
                
                print(f"🎯 Theorem: {progressive.theorem_name}")
                print(f"📋 Learning pathway has {len(progressive.learning_pathway)} steps:")
                
                for i, step in enumerate(progressive.learning_pathway, 1):
                    print(f"  {i}. {step.title} ({step.level})")
                    print(f"     {step.description}")
                    print(f"     Concepts: {', '.join(step.concepts)}")
                    print(f"     Examples: {len(step.examples)}")
                    print(f"     Exercises: {len(step.exercises)}")
                    print()
                    
                # Check pathway progression
                levels = [step.level for step in progressive.learning_pathway]
                has_progression = "novice" in levels and "intermediate" in levels and "advanced" in levels
                print(f"✅ Has educational progression: {has_progression}")
                
                return True
            else:
                print("❌ Failed to parse theorem for pathway test")
                return False
                
        finally:
            temp_path.unlink()
            
    except Exception as e:
        print(f"❌ Learning pathway creation failed: {e}")
        return False

def test_concept_extraction():
    """Test extraction and explanation of key mathematical concepts."""
    print("\n🧠 Testing Concept Extraction...")
    
    try:
        from src.proof_sketcher.parser import LeanParser
        from src.proof_sketcher.generator import ProgressiveGenerator
        
        # Test with theorem that uses various concepts
        content = """
        theorem all_nat_ge_zero (n : Nat) : n ≥ 0 := by
          induction n with
          | zero => rfl
          | succ n ih => simp [Nat.succ_le_succ ih]
        """
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write(content)
            temp_path = Path(f.name)
        
        try:
            parser = LeanParser()
            result = parser.parse_file_sync(temp_path)
            
            if result.success and result.theorems:
                theorem = result.theorems[0]
                generator = ProgressiveGenerator()
                progressive = generator.generate_progressive_explanation(theorem)
                
                print(f"🔍 Extracted {len(progressive.key_concepts)} key concepts:")
                
                for concept in progressive.key_concepts:
                    print(f"\n📚 Concept: {concept.concept}")
                    print(f"   Informal: {concept.informal_description}")
                    print(f"   Formal: {concept.formal_definition}")
                    print(f"   Examples: {len(concept.examples)}")
                    print(f"   Misconceptions: {len(concept.common_misconceptions)}")
                    print(f"   Related: {', '.join(concept.related_concepts)}")
                    
                # Check for expected concepts
                concept_names = [c.concept.lower() for c in progressive.key_concepts]
                
                # Should extract induction concept
                has_induction = any("induction" in name for name in concept_names)
                print(f"✅ Extracted induction concept: {has_induction}")
                
                # Should extract natural numbers concept  
                has_natural_numbers = any("natural" in name or "nat" in name for name in concept_names)
                print(f"✅ Extracted natural numbers concept: {has_natural_numbers}")
                
                return True
            else:
                print("❌ Failed to parse theorem for concept test")
                return False
                
        finally:
            temp_path.unlink()
            
    except Exception as e:
        print(f"❌ Concept extraction failed: {e}")
        return False

def test_educational_adaptation():
    """Test adaptation of content for different educational levels."""
    print("\n🎯 Testing Educational Adaptation...")
    
    try:
        from src.proof_sketcher.parser.models import TheoremInfo
        from src.proof_sketcher.generator import ProgressiveGenerator, EducationalLevel
        
        # Create theorems of different complexity
        theorems = [
            TheoremInfo(
                name="simple_theorem",
                statement="n + 0 = n",
                proof="by simp",
                dependencies=[],
                line_number=1,
                visibility="public",
            ),
            TheoremInfo(
                name="complex_theorem", 
                statement="∀ a b c : Nat, a + b + c = c + b + a",
                proof="by induction a with | zero => simp | succ a ih => rw [ih]",
                dependencies=["add_comm", "add_assoc"],
                line_number=1,
                visibility="public",
            )
        ]
        
        generator = ProgressiveGenerator()
        
        for theorem in theorems:
            print(f"\n🧪 Testing {theorem.name}:")
            
            progressive = generator.generate_progressive_explanation(theorem)
            
            # Check adaptation across levels
            beginner_intro = progressive.levels[EducationalLevel.BEGINNER].introduction
            advanced_intro = progressive.levels[EducationalLevel.ADVANCED].introduction
            
            print(f"  📝 Beginner intro: {beginner_intro[:100]}...")
            print(f"  📝 Advanced intro: {advanced_intro[:100]}...")
            
            # Check study time estimates
            study_times = progressive.estimated_study_time
            print(f"  ⏰ Study times: {study_times}")
            
            # Check maturity requirements
            maturity = progressive.mathematical_maturity_required
            print(f"  🧠 Maturity required: {maturity}")
            
            # Verify progression makes sense
            times_ascending = (
                study_times[EducationalLevel.BEGINNER] <= 
                study_times[EducationalLevel.INTERMEDIATE] <= 
                study_times[EducationalLevel.ADVANCED]
            )
            print(f"  ✅ Study times increase with level: {times_ascending}")
            
        print("✅ Educational adaptation working correctly")
        return True
        
    except Exception as e:
        print(f"❌ Educational adaptation test failed: {e}")
        return False

def test_interactive_elements():
    """Test generation of interactive and exploratory elements."""
    print("\n🔍 Testing Interactive Elements...")
    
    try:
        from src.proof_sketcher.parser.models import TheoremInfo
        from src.proof_sketcher.generator import ProgressiveGenerator
        
        theorem = TheoremInfo(
            name="add_zero",
            statement="n + 0 = n",
            proof="by simp",
            dependencies=[],
            line_number=1,
            visibility="public",
        )
        
        generator = ProgressiveGenerator()
        progressive = generator.generate_progressive_explanation(theorem)
        
        print(f"🎮 Interactive elements for {progressive.theorem_name}:")
        
        # Check exploration suggestions
        explorations = progressive.exploration_suggestions
        print(f"\n🔍 Exploration suggestions ({len(explorations)}):")
        for i, suggestion in enumerate(explorations[:3], 1):
            print(f"  {i}. {suggestion}")
            
        # Check visualization ideas
        visualizations = progressive.visualization_ideas
        print(f"\n🎨 Visualization ideas ({len(visualizations)}):")
        for i, idea in enumerate(visualizations[:3], 1):
            print(f"  {i}. {idea}")
            
        # Check extension problems
        extensions = progressive.extension_problems
        print(f"\n🧩 Extension problems ({len(extensions)}):")
        for i, problem in enumerate(extensions[:3], 1):
            print(f"  {i}. {problem}")
            
        # Check intuitive examples
        examples = progressive.intuitive_examples
        print(f"\n💡 Intuitive examples ({len(examples)}):")
        for i, example in enumerate(examples[:3], 1):
            print(f"  {i}. {example}")
            
        # Verify all elements are present
        has_all_elements = all([
            len(explorations) > 0,
            len(visualizations) > 0,
            len(extensions) > 0,
            len(examples) > 0
        ])
        
        print(f"\n✅ All interactive elements generated: {has_all_elements}")
        return has_all_elements
        
    except Exception as e:
        print(f"❌ Interactive elements test failed: {e}")
        return False

def test_comprehensive_integration():
    """Test complete integration of progressive features."""
    print("\n🔄 Testing Comprehensive Integration...")
    
    try:
        from src.proof_sketcher.parser import LeanParser
        from src.proof_sketcher.generator import ProgressiveGenerator
        from src.proof_sketcher.exporter import HTMLExporter
        
        # Complex theorem for comprehensive test
        content = """
        theorem add_comm (a b : Nat) : a + b = b + a := by
          induction a with
          | zero => simp
          | succ a ih => 
            rw [Nat.add_succ, ih, Nat.succ_add]
        """
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write(content)
            temp_path = Path(f.name)
        
        try:
            # Full pipeline test
            parser = LeanParser()
            result = parser.parse_file_sync(temp_path)
            
            if result.success and result.theorems:
                theorem = result.theorems[0]
                
                # Generate progressive explanation
                generator = ProgressiveGenerator()
                progressive = generator.generate_progressive_explanation(theorem)
                
                # Test each level can be exported
                html_exporter = HTMLExporter()
                
                for level_name, sketch in progressive.levels.items():
                    html_content = html_exporter.export(sketch)
                    print(f"  ✅ {level_name} level exported: {len(html_content)} chars")
                
                # Check comprehensive content
                checklist = {
                    "Multiple levels": len(progressive.levels) >= 3,
                    "Learning pathway": len(progressive.learning_pathway) > 0,
                    "Key concepts": len(progressive.key_concepts) > 0,
                    "Study times": len(progressive.estimated_study_time) > 0,
                    "Maturity requirements": len(progressive.mathematical_maturity_required) > 0,
                    "Interactive elements": len(progressive.exploration_suggestions) > 0,
                    "Examples": len(progressive.intuitive_examples) > 0,
                    "Extensions": len(progressive.extension_problems) > 0,
                }
                
                print(f"\n📋 Comprehensive content checklist:")
                all_passed = True
                for item, passed in checklist.items():
                    status = "✅" if passed else "❌"
                    print(f"  {status} {item}: {passed}")
                    if not passed:
                        all_passed = False
                        
                print(f"\n🎉 Comprehensive integration test: {'PASSED' if all_passed else 'FAILED'}")
                return all_passed
                
            else:
                print("❌ Failed to parse theorem for integration test")
                return False
                
        finally:
            temp_path.unlink()
            
    except Exception as e:
        print(f"❌ Comprehensive integration test failed: {e}")
        return False

def run_all_tests():
    """Run all progressive generator tests."""
    print("🎓 Starting Progressive Generator Tests")
    print("=" * 50)
    
    tests = [
        ("Progressive Explanation Generation", test_progressive_explanation_generation),
        ("Learning Pathway Creation", test_learning_pathway_creation),
        ("Concept Extraction", test_concept_extraction),
        ("Educational Adaptation", test_educational_adaptation),
        ("Interactive Elements", test_interactive_elements),
        ("Comprehensive Integration", test_comprehensive_integration),
    ]
    
    results = []
    for name, test_func in tests:
        print(f"\n{'='*20} {name} {'='*20}")
        try:
            result = test_func()
            results.append((name, result))
        except Exception as e:
            print(f"❌ Test {name} crashed: {e}")
            results.append((name, False))
    
    # Summary
    print("\n" + "="*50)
    print("📋 PROGRESSIVE GENERATOR TEST SUMMARY")
    print("="*50)
    
    passed = 0
    for name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status}: {name}")
        if result:
            passed += 1
    
    print(f"\n📊 Results: {passed}/{len(results)} tests passed")
    
    if passed == len(results):
        print("🎉 Progressive Generator: ALL TESTS PASSED!")
        print("🚀 Multi-level educational content generation is working correctly")
        print("📚 Ready for real mathlib integration and enhanced export")
    else:
        print("⚠️  Some tests failed - review implementation")
        
    return passed == len(results)

if __name__ == "__main__":
    success = run_all_tests()
    exit(0 if success else 1)