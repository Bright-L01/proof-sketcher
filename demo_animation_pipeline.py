#!/usr/bin/env python3
"""
Animation Pipeline Demo

This script demonstrates the complete animation pipeline with real theorem
animation generation and robust fallback to static visualization.
"""

import tempfile
import time
from pathlib import Path
from typing import Dict, Any

# Set matplotlib backend before any other imports
import matplotlib
matplotlib.use('Agg')

from src.proof_sketcher.animator.manim_server import ManimMCPServer
from src.proof_sketcher.animator.animation_generator import TheoremAnimator
from src.proof_sketcher.animator.static_fallback import StaticVisualizer
from src.proof_sketcher.parser.models import TheoremInfo
from src.proof_sketcher.generator.models import ProofSketch, ProofStep


def create_test_theorem() -> Dict[str, Any]:
    """Create test theorem data."""
    return {
        "name": "Nat.add_comm",
        "statement": "∀ (a b : ℕ), a + b = b + a",
        "proof": "by exact Nat.add_comm a b",
        "dependencies": ["Nat.add_comm"],
        "docstring": "Commutativity of natural number addition",
        "tactics": ["exact", "Nat.add_comm"]
    }


def create_test_proof_sketch() -> Dict[str, Any]:
    """Create test proof sketch."""
    return {
        "theorem_name": "Nat.add_comm",
        "introduction": "We prove that addition of natural numbers is commutative.",
        "key_steps": [
            {
                "step_number": 1,
                "description": "Apply the commutativity property of natural number addition",
                "mathematical_content": "a + b = b + a",
                "tactics": ["exact", "Nat.add_comm"]
            },
            {
                "step_number": 2,
                "description": "The theorem follows directly from the definition",
                "mathematical_content": "b + a",
                "tactics": ["rfl"]
            }
        ],
        "conclusion": "Therefore, addition is commutative for all natural numbers.",
        "difficulty_level": "beginner",
        "mathematical_areas": ["arithmetic", "natural_numbers"],
        "prerequisites": ["basic_arithmetic"]
    }


def demo_animation_generation():
    """Demonstrate animation script generation."""
    print("🎬 Animation Generation Demo")
    print("=" * 50)
    
    # Create test data
    theorem = create_test_theorem()
    sketch = create_test_proof_sketch()
    
    print(f"📝 Theorem: {theorem['name']}")
    print(f"📄 Statement: {theorem['statement']}")
    print(f"🔧 Steps: {len(sketch['key_steps'])}")
    print()
    
    # Generate animation script
    print("🔨 Generating Manim animation script...")
    animator = TheoremAnimator()
    
    start_time = time.time()
    script = animator.generate_animation_script(theorem, sketch)
    generation_time = (time.time() - start_time) * 1000
    
    print(f"✅ Script generated in {generation_time:.1f}ms")
    print(f"📏 Script length: {len(script)} characters")
    
    # Validate script
    print("🔍 Validating script...")
    is_valid, error = animator.validate_script(script)
    
    if is_valid:
        print("✅ Script validation passed")
    else:
        print(f"❌ Script validation failed: {error}")
        return
    
    # Show script preview
    print("\n📋 Script Preview:")
    print("-" * 30)
    lines = script.split('\n')
    for i, line in enumerate(lines[:20]):  # Show first 20 lines
        print(f"{i+1:2d}: {line}")
    
    if len(lines) > 20:
        print(f"... and {len(lines) - 20} more lines")
    
    print("-" * 30)
    print()
    
    return script


def demo_manim_integration():
    """Demonstrate Manim MCP server integration."""
    print("🖥️  Manim MCP Server Demo")
    print("=" * 50)
    
    # Initialize server
    server = ManimMCPServer()
    
    print("🔧 Server Status:")
    print(f"  Manim Available: {server.manim_available}")
    print(f"  Temp Directory: {server.temp_dir}")
    print()
    
    if not server.manim_available:
        print("⚠️  Manim not available - will demonstrate fallback")
        print("   To install Manim: pip install manim")
        return None
    
    # Create simple test script
    test_script = '''from manim import *

class TestAnimation(Scene):
    def construct(self):
        title = Text("Manim Integration Test", font_size=48)
        self.play(Write(title))
        self.wait(1)
        
        formula = MathTex(r"E = mc^2")
        formula.next_to(title, DOWN)
        self.play(Write(formula))
        self.wait(2)
        
        self.play(FadeOut(title), FadeOut(formula))
'''
    
    # Try to create animation
    with tempfile.NamedTemporaryFile(suffix='.mp4', delete=False) as f:
        output_path = f.name
    
    try:
        print("🎬 Attempting to create animation...")
        result = server.create_animation_sync(
            test_script,
            output_path,
            quality="low_quality",  # Faster for demo
            scene_name="TestAnimation"
        )
        
        if result["success"]:
            print("✅ Animation created successfully!")
            print(f"📁 Output: {result['output']}")
            print(f"📏 File size: {result.get('size_bytes', 0)} bytes")
            return result["output"]
        else:
            print(f"❌ Animation failed: {result['error']}")
            if "timeout" in result:
                print("   (Animation timed out)")
            return None
            
    finally:
        # Cleanup
        Path(output_path).unlink(missing_ok=True)


def demo_static_fallback():
    """Demonstrate static visualization fallback."""
    print("📊 Static Visualization Demo") 
    print("=" * 50)
    
    # Initialize visualizer
    visualizer = StaticVisualizer()
    
    print("🔧 Visualizer Status:")
    print(f"  Available: {visualizer.is_available()}")
    print(f"  Supported Formats: {', '.join(visualizer.get_supported_formats())}")
    print()
    
    if not visualizer.is_available():
        print("⚠️  Matplotlib not available - static visualization disabled")
        print("   To install: pip install matplotlib")
        return None
    
    # Create test data
    theorem = create_test_theorem()
    sketch = create_test_proof_sketch()
    
    # Create static diagram
    with tempfile.NamedTemporaryFile(suffix='.png', delete=False) as f:
        output_path = f.name
    
    try:
        print("🎨 Creating static proof diagram...")
        start_time = time.time()
        
        success = visualizer.create_proof_diagram(theorem, sketch, output_path)
        
        creation_time = (time.time() - start_time) * 1000
        
        if success:
            print(f"✅ Static diagram created in {creation_time:.1f}ms")
            
            file_size = Path(output_path).stat().st_size
            print(f"📁 Output: {output_path}")
            print(f"📏 File size: {file_size:,} bytes")
            
            # Keep file for inspection
            final_path = "demo_proof_diagram.png"
            Path(output_path).rename(final_path)
            print(f"💾 Saved as: {final_path}")
            
            return final_path
        else:
            print("❌ Static diagram creation failed")
            return None
            
    except Exception as e:
        print(f"❌ Error creating static diagram: {e}")
        Path(output_path).unlink(missing_ok=True)
        return None


def demo_error_visualization():
    """Demonstrate error visualization."""
    print("⚠️  Error Visualization Demo")
    print("=" * 50)
    
    visualizer = StaticVisualizer()
    
    if not visualizer.is_available():
        print("⚠️  Matplotlib not available - skipping error visualization")
        return None
    
    with tempfile.NamedTemporaryFile(suffix='.png', delete=False) as f:
        output_path = f.name
    
    try:
        print("🚨 Creating error visualization...")
        
        success = visualizer.create_error_diagram(
            "Animation generation failed: Manim script compilation error",
            output_path,
            "This can happen when the generated Manim script has syntax issues or missing dependencies"
        )
        
        if success:
            print("✅ Error diagram created")
            
            # Keep file for inspection
            final_path = "demo_error_diagram.png"
            Path(output_path).rename(final_path)
            print(f"💾 Saved as: {final_path}")
            
            return final_path
        else:
            print("❌ Error diagram creation failed")
            return None
            
    except Exception as e:
        print(f"❌ Error creating error diagram: {e}")
        Path(output_path).unlink(missing_ok=True)
        return None


def demo_complete_pipeline():
    """Demonstrate complete animation pipeline."""
    print("🚀 Complete Animation Pipeline Demo")
    print("=" * 60)
    
    # Create comprehensive test data
    theorem = {
        "name": "List.length_append",
        "statement": "∀ (l1 l2 : List α), (l1 ++ l2).length = l1.length + l2.length",
        "proof": "by induction on l1",
        "dependencies": ["List.length", "List.append"],
        "docstring": "The length of the concatenation of two lists equals the sum of their lengths"
    }
    
    sketch = {
        "theorem_name": "List.length_append",
        "introduction": "We prove by induction that the length of concatenated lists equals the sum of their individual lengths.",
        "key_steps": [
            {
                "step_number": 1,
                "description": "Base case: empty list",
                "mathematical_content": "([] ++ l2).length = [].length + l2.length",
                "tactics": ["simp", "List.length"]
            },
            {
                "step_number": 2, 
                "description": "Inductive step: cons case",
                "mathematical_content": "((h :: t) ++ l2).length = (h :: t).length + l2.length",
                "tactics": ["simp", "List.length", "ih"]
            },
            {
                "step_number": 3,
                "description": "Apply induction hypothesis",
                "mathematical_content": "1 + t.length + l2.length",
                "tactics": ["rw", "ih"]
            }
        ],
        "conclusion": "By induction, the theorem holds for all lists.",
        "difficulty_level": "intermediate",
        "mathematical_areas": ["data_structures", "induction"],
        "prerequisites": ["list_operations", "mathematical_induction"]
    }
    
    print(f"📝 Complex Theorem: {theorem['name']}")
    print(f"🎯 Difficulty: {sketch['difficulty_level']}")
    print(f"🔧 Proof Steps: {len(sketch['key_steps'])}")
    print()
    
    # Try animation generation
    print("🎬 Step 1: Generate Manim Animation")
    print("-" * 40)
    
    animator = TheoremAnimator()
    script = animator.generate_animation_script(theorem, sketch)
    
    is_valid, error = animator.validate_script(script)
    if is_valid:
        print("✅ Animation script generated and validated")
        
        # Try Manim rendering
        server = ManimMCPServer()
        if server.manim_available:
            print("🎥 Attempting Manim rendering...")
            # Would try actual rendering here
            print("⚠️  Skipping actual rendering for demo (can be slow)")
        else:
            print("⚠️  Manim not available, proceeding to fallback")
    else:
        print(f"❌ Script validation failed: {error}")
    
    print()
    
    # Fallback to static visualization
    print("📊 Step 2: Static Visualization Fallback")
    print("-" * 40)
    
    visualizer = StaticVisualizer()
    if visualizer.is_available():
        output_path = demo_static_fallback()
        if output_path:
            print(f"✅ Fallback visualization successful: {output_path}")
        else:
            print("❌ Fallback visualization failed")
    else:
        print("⚠️  Static visualization not available")
    
    print()
    print("🏁 Pipeline Demo Complete!")
    print("=" * 60)


def main():
    """Run all animation pipeline demos."""
    print("🎯 Proof Sketcher Animation Pipeline Demo")
    print("=" * 60)
    print("This demo showcases the complete animation pipeline including:")
    print("• Manim script generation")
    print("• MCP server integration") 
    print("• Static visualization fallback")
    print("• Error handling and visualization")
    print()
    
    try:
        # Demo 1: Animation Generation
        demo_animation_generation()
        print()
        
        # Demo 2: Manim Integration
        demo_manim_integration()
        print()
        
        # Demo 3: Static Fallback
        demo_static_fallback()
        print()
        
        # Demo 4: Error Visualization
        demo_error_visualization()
        print()
        
        # Demo 5: Complete Pipeline
        demo_complete_pipeline()
        
    except KeyboardInterrupt:
        print("\n⚠️  Demo interrupted by user")
    except Exception as e:
        print(f"\n❌ Demo failed with error: {e}")
        import traceback
        traceback.print_exc()
    
    print("\n🎉 Animation Pipeline Demo Complete!")
    print("Generated files:")
    for filename in ["demo_proof_diagram.png", "demo_error_diagram.png"]:
        if Path(filename).exists():
            print(f"  • {filename}")


if __name__ == "__main__":
    main()