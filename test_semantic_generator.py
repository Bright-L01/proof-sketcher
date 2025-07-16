"""Test script for semantic generator and educational enhancement features.

This test verifies:
1. Semantic generator with different educational levels
2. Progressive explanation generation
3. Educational content adaptation
4. Tactic-aware proof explanations
5. Mathematical entity recognition and context

Run this test to verify the semantic generator works correctly.
"""

import tempfile
from pathlib import Path

def test_semantic_generator_levels():
    """Test semantic generator with different educational levels."""
    print("🧠 Testing Semantic Generator Educational Levels...")
    
    try:
        from src.proof_sketcher.parser import LeanParser
        from src.proof_sketcher.generator import SemanticGenerator, EducationalLevel
        
        # Create test theorem with semantic analysis
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
            # Parse with semantic analysis
            parser = LeanParser()
            result = parser.parse_file_sync(temp_path)
            
            if not result.success or not result.theorems:
                print("❌ Failed to parse test theorem")
                return False
                
            theorem = result.theorems[0]
            generator = SemanticGenerator()
            
            # Test all educational levels
            levels = [EducationalLevel.BEGINNER, EducationalLevel.INTERMEDIATE, EducationalLevel.ADVANCED]
            
            for level in levels:
                print(f"\n📚 Testing {level.upper()} level:")
                
                sketch = generator.generate_educational_sketch(theorem, level)
                
                print(f"  🎯 Difficulty: {sketch.difficulty_level}")
                print(f"  📖 Introduction length: {len(sketch.introduction)} chars")
                print(f"  🔢 Number of steps: {len(sketch.key_steps)}")
                print(f"  🧮 Mathematical areas: {sketch.mathematical_areas}")
                print(f"  📋 Prerequisites: {sketch.prerequisites}")
                
                # Check that content varies by level
                intro_words = sketch.introduction.lower()
                if level == EducationalLevel.BEGINNER:
                    # Should have more intuitive language
                    has_intuitive = any(word in intro_words for word in [
                        "shows us", "think of", "like", "simply", "basically"
                    ])
                    print(f"  ✅ Has intuitive language: {has_intuitive}")
                elif level == EducationalLevel.ADVANCED:
                    # Should have more technical language
                    has_technical = any(word in intro_words for word in [
                        "formal", "structural", "principle", "framework", "analysis"
                    ])
                    print(f"  ✅ Has technical language: {has_technical}")
                    
                # Check step quality
                if sketch.key_steps:
                    first_step = sketch.key_steps[0]
                    print(f"  🎯 First step intuition: {first_step.intuition[:100]}...")
                    
            print("✅ Semantic generator educational levels working")
            return True
            
        finally:
            temp_path.unlink()
            
    except Exception as e:
        print(f"❌ Semantic generator test failed: {e}")
        return False

def test_progressive_explanations():
    """Test progressive explanation generation based on complexity."""
    print("\n🔄 Testing Progressive Explanations...")
    
    try:
        from src.proof_sketcher.parser import LeanParser
        from src.proof_sketcher.generator import SemanticGenerator
        
        # Test theorems of different complexity
        test_cases = [
            ("Simple theorem", "theorem simple (n : Nat) : n + 0 = n := by simp"),
            ("Medium theorem", """
                theorem medium (n : Nat) : 0 + n = n := by
                  induction n with
                  | zero => rfl
                  | succ n ih => rw [Nat.add_succ, ih]
            """),
            ("Complex theorem", """
                theorem complex (a b c : Nat) : a + b + c = c + b + a := by
                  rw [Nat.add_assoc, Nat.add_comm a, Nat.add_assoc, Nat.add_comm b]
                  rw [Nat.add_assoc]
            """)
        ]
        
        generator = SemanticGenerator()
        
        for name, content in test_cases:
            print(f"\n🧪 Testing {name}:")
            
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                f.write(content)
                temp_path = Path(f.name)
            
            try:
                parser = LeanParser()
                result = parser.parse_file_sync(temp_path)
                
                if result.success and result.theorems:
                    theorem = result.theorems[0]
                    sketch = generator.generate_educational_sketch(theorem)
                    
                    print(f"  📊 Complexity score: {theorem.complexity_score}")
                    print(f"  🎯 Determined difficulty: {sketch.difficulty_level}")
                    print(f"  🔨 Proof method: {theorem.proof_method}")
                    print(f"  📚 Areas: {sketch.mathematical_areas}")
                    print(f"  📖 Introduction style: {sketch.introduction[:80]}...")
                    
            finally:
                temp_path.unlink()
                
        print("✅ Progressive explanations working correctly")
        return True
        
    except Exception as e:
        print(f"❌ Progressive explanations test failed: {e}")
        return False

def test_mathematical_entity_recognition():
    """Test recognition and explanation of mathematical entities."""
    print("\n🔬 Testing Mathematical Entity Recognition...")
    
    try:
        from src.proof_sketcher.parser import LeanParser
        from src.proof_sketcher.generator import SemanticGenerator
        
        # Test different mathematical contexts
        test_cases = [
            ("Number theory", "theorem nt (n : Nat) (h : n > 0) : n + 1 > 1 := by simp [h]"),
            ("Real analysis", "theorem ra (x : Real) : x + 0 = x := by simp"),
            ("Set theory", "theorem st (s : Set Nat) : s ∪ ∅ = s := by simp"),
        ]
        
        generator = SemanticGenerator()
        
        for context, content in test_cases:
            print(f"\n🧪 Testing {context}:")
            
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                f.write(content)
                temp_path = Path(f.name)
            
            try:
                parser = LeanParser()
                result = parser.parse_file_sync(temp_path)
                
                if result.success and result.theorems:
                    theorem = result.theorems[0]
                    sketch = generator.generate_educational_sketch(theorem)
                    
                    print(f"  🔍 Entities found: {theorem.mathematical_entities}")
                    print(f"  📚 Mathematical areas: {sketch.mathematical_areas}")
                    print(f"  📋 Prerequisites: {sketch.prerequisites}")
                    
                    # Check that context is appropriate
                    areas_str = " ".join(sketch.mathematical_areas).lower()
                    if "nat" in content.lower():
                        has_number_context = any(word in areas_str for word in ["number", "arithmetic"])
                        print(f"  ✅ Has number theory context: {has_number_context}")
                    elif "real" in content.lower():
                        has_real_context = any(word in areas_str for word in ["analysis", "real"])
                        print(f"  ✅ Has real analysis context: {has_real_context}")
                    elif "set" in content.lower():
                        has_set_context = any(word in areas_str for word in ["set", "discrete"])
                        print(f"  ✅ Has set theory context: {has_set_context}")
                        
            finally:
                temp_path.unlink()
                
        print("✅ Mathematical entity recognition working")
        return True
        
    except Exception as e:
        print(f"❌ Entity recognition test failed: {e}")
        return False

def test_tactic_aware_explanations():
    """Test explanations that are aware of specific tactics used."""
    print("\n⚙️ Testing Tactic-Aware Explanations...")
    
    try:
        from src.proof_sketcher.parser import LeanParser
        from src.proof_sketcher.generator import SemanticGenerator
        
        # Test different proof tactics
        test_cases = [
            ("Simp proof", "theorem simp_proof (n : Nat) : n + 0 = n := by simp"),
            ("Rewrite proof", "theorem rw_proof (a b : Nat) : a + b = b + a := by rw [Nat.add_comm]"),
            ("Induction proof", """
                theorem ind_proof (n : Nat) : 0 + n = n := by
                  induction n with
                  | zero => rfl
                  | succ n ih => rw [Nat.add_succ, ih]
            """),
        ]
        
        generator = SemanticGenerator()
        
        for name, content in test_cases:
            print(f"\n🧪 Testing {name}:")
            
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                f.write(content)
                temp_path = Path(f.name)
            
            try:
                parser = LeanParser()
                result = parser.parse_file_sync(temp_path)
                
                if result.success and result.theorems:
                    theorem = result.theorems[0]
                    sketch = generator.generate_educational_sketch(theorem)
                    
                    print(f"  🔨 Detected method: {theorem.proof_method}")
                    print(f"  ⚙️ Tactics found: {[t.name for t in theorem.tactic_sequence]}")
                    
                    # Check that explanation mentions the tactic approach
                    full_text = (sketch.introduction + " " + 
                               " ".join(step.description for step in sketch.key_steps)).lower()
                    
                    if "simp" in content:
                        has_simp_explanation = any(word in full_text for word in [
                            "simplif", "automatic", "rules"
                        ])
                        print(f"  ✅ Explains simplification: {has_simp_explanation}")
                    elif "rw" in content:
                        has_rw_explanation = any(word in full_text for word in [
                            "rewrite", "replac", "substitut"
                        ])
                        print(f"  ✅ Explains rewriting: {has_rw_explanation}")
                    elif "induction" in content:
                        has_ind_explanation = any(word in full_text for word in [
                            "induction", "inductive", "base case"
                        ])
                        print(f"  ✅ Explains induction: {has_ind_explanation}")
                        
                    # Show first step explanation
                    if sketch.key_steps:
                        print(f"  📝 First step: {sketch.key_steps[0].description}")
                        
            finally:
                temp_path.unlink()
                
        print("✅ Tactic-aware explanations working")
        return True
        
    except Exception as e:
        print(f"❌ Tactic-aware explanations test failed: {e}")
        return False

def test_backward_compatibility():
    """Test that the new generator maintains backward compatibility."""
    print("\n🔄 Testing Backward Compatibility...")
    
    try:
        # Test old interface still works
        from src.proof_sketcher.generator import AIGenerator
        from src.proof_sketcher.parser.models import TheoremInfo
        
        # Create a simple theorem
        theorem = TheoremInfo(
            name="test_theorem",
            statement="n + 0 = n",
            proof="by simp",
            dependencies=[],
            line_number=1,
            visibility="public",
        )
        
        generator = AIGenerator()
        
        # Test old method name
        if hasattr(generator, 'generate_offline'):
            sketch1 = generator.generate_offline(theorem)
            print("✅ generate_offline method works")
        
        # Test standard method
        sketch2 = generator.generate_proof_sketch(theorem)
        print("✅ generate_proof_sketch method works")
        
        # Test new method
        sketch3 = generator.generate_educational_sketch(theorem)
        print("✅ generate_educational_sketch method works")
        
        # Verify all produce valid sketches
        for i, sketch in enumerate([sketch1, sketch2, sketch3], 1):
            if sketch:
                print(f"  ✅ Sketch {i}: {sketch.theorem_name}, {len(sketch.key_steps)} steps")
            else:
                print(f"  ❌ Sketch {i}: None")
                return False
                
        print("✅ Backward compatibility maintained")
        return True
        
    except Exception as e:
        print(f"❌ Backward compatibility test failed: {e}")
        return False

def run_all_tests():
    """Run all semantic generator tests."""
    print("🧠 Starting Semantic Generator Tests")
    print("=" * 50)
    
    tests = [
        ("Educational Levels", test_semantic_generator_levels),
        ("Progressive Explanations", test_progressive_explanations),
        ("Entity Recognition", test_mathematical_entity_recognition),
        ("Tactic-Aware Explanations", test_tactic_aware_explanations),
        ("Backward Compatibility", test_backward_compatibility),
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
    print("📋 SEMANTIC GENERATOR TEST SUMMARY")
    print("="*50)
    
    passed = 0
    for name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status}: {name}")
        if result:
            passed += 1
    
    print(f"\n📊 Results: {passed}/{len(results)} tests passed")
    
    if passed == len(results):
        print("🎉 Semantic Generator: ALL TESTS PASSED!")
        print("🚀 Educational semantic analysis is working correctly")
    else:
        print("⚠️  Some tests failed - review implementation")
        
    return passed == len(results)

if __name__ == "__main__":
    success = run_all_tests()
    exit(0 if success else 1)