#!/usr/bin/env python3
"""
Comprehensive Export System Demo - Milestone 2.2

This demonstrates the complete multi-format export system with:
- HTML export with doc-gen4 compatibility
- Markdown export with GitHub features  
- PDF export via LaTeX
- Animation pipeline integration
- Static visualization fallback
"""

import tempfile
import time
from pathlib import Path
from typing import Dict, Any

# Set matplotlib backend before any other imports
import matplotlib
matplotlib.use('Agg')

from src.proof_sketcher.animator.animation_generator import TheoremAnimator
from src.proof_sketcher.animator.static_fallback import StaticVisualizer
from src.proof_sketcher.exporter.html import HTMLExporter
from src.proof_sketcher.exporter.markdown import MarkdownExporter
from src.proof_sketcher.exporter.pdf import PDFExporter
from src.proof_sketcher.exporter.models import (
    ExportContext,
    ExportFormat,
    ExportOptions,
)
from src.proof_sketcher.generator.models import ProofSketch, ProofStep


def create_comprehensive_test_theorem() -> Dict[str, Any]:
    """Create a comprehensive theorem for testing all export features."""
    return {
        "name": "List.length_append",
        "statement": "∀ (l1 l2 : List α), (l1 ++ l2).length = l1.length + l2.length",
        "proof": "by induction on l1",
        "dependencies": ["List.length", "List.append", "Nat.add"],
        "docstring": "The length of the concatenation of two lists equals the sum of their lengths",
        "mathematical_areas": ["data_structures", "induction", "arithmetic"]
    }


def create_comprehensive_proof_sketch() -> ProofSketch:
    """Create a comprehensive proof sketch with rich content."""
    return ProofSketch(
        theorem_name="List.length_append",
        introduction=(
            "We prove by induction that the length of concatenated lists equals "
            "the sum of their individual lengths. This fundamental property connects "
            "list operations with arithmetic and demonstrates the power of structural induction."
        ),
        key_steps=[
            ProofStep(
                step_number=1,
                description="Base case: empty list",
                mathematical_content="([] ++ l2).length = [].length + l2.length",
                tactics=["simp", "List.length", "List.nil_append"],
            ),
            ProofStep(
                step_number=2,
                description="Simplify the base case",
                mathematical_content="l2.length = 0 + l2.length",
                tactics=["simp", "List.length_nil", "Nat.zero_add"],
            ),
            ProofStep(
                step_number=3,
                description="Inductive step: cons case",
                mathematical_content="((h :: t) ++ l2).length = (h :: t).length + l2.length",
                tactics=["simp", "List.length_cons", "List.cons_append"],
            ),
            ProofStep(
                step_number=4,
                description="Expand the cons case",
                mathematical_content="(h :: (t ++ l2)).length = (1 + t.length) + l2.length",
                tactics=["simp", "List.length_cons"],
            ),
            ProofStep(
                step_number=5,
                description="Apply induction hypothesis",
                mathematical_content="1 + (t ++ l2).length = 1 + t.length + l2.length",
                tactics=["rw", "ih"],
            ),
            ProofStep(
                step_number=6,
                description="Substitute induction hypothesis",
                mathematical_content="1 + (t.length + l2.length) = 1 + t.length + l2.length",
                tactics=["rw", "ih"],
            ),
            ProofStep(
                step_number=7,
                description="Apply associativity of addition",
                mathematical_content="(1 + t.length) + l2.length = 1 + t.length + l2.length",
                tactics=["rw", "Nat.add_assoc"],
            ),
        ],
        conclusion=(
            "By mathematical induction, we have proven that for all lists l1 and l2, "
            "the length of their concatenation equals the sum of their individual lengths. "
            "This property is fundamental to list theory and enables many other proofs."
        ),
        difficulty_level="intermediate",
        mathematical_areas=["data_structures", "induction", "arithmetic"],
        prerequisites=["List.length", "List.append", "mathematical_induction", "Nat.add_assoc"],
        key_insights=[
            "Structural induction mirrors the recursive definition of list concatenation",
            "The base case trivially holds due to the identity property of concatenation",
            "The inductive step leverages the associativity of natural number addition",
            "This proof demonstrates the connection between structural and mathematical properties"
        ]
    )


def demo_animation_generation():
    """Demonstrate animation script generation."""
    print("🎬 Step 1: Animation Generation")
    print("=" * 50)
    
    theorem = create_comprehensive_test_theorem()
    sketch = create_comprehensive_proof_sketch()
    
    print(f"📝 Theorem: {theorem['name']}")
    print(f"📊 Complexity: {len(sketch.key_steps)} proof steps")
    print()
    
    # Generate animation script
    animator = TheoremAnimator()
    start_time = time.time()
    
    script = animator.generate_animation_script(theorem, sketch.dict())
    generation_time = (time.time() - start_time) * 1000
    
    # Validate script
    is_valid, error = animator.validate_script(script)
    
    if is_valid:
        print(f"✅ Animation script generated in {generation_time:.1f}ms")
        print(f"📏 Script length: {len(script):,} characters")
        
        # Extract key metrics
        lines = script.split('\n')
        class_count = len([l for l in lines if 'class' in l and 'Scene' in l])
        method_count = len([l for l in lines if 'def ' in l])
        animation_calls = len([l for l in lines if 'self.play(' in l])
        math_expressions = len([l for l in lines if 'MathTex(' in l])
        
        print(f"🎭 Generated classes: {class_count}")
        print(f"🔧 Methods defined: {method_count}")
        print(f"🎥 Animation calls: {animation_calls}")
        print(f"🔢 Math expressions: {math_expressions}")
        
        return script
    else:
        print(f"❌ Script validation failed: {error}")
        return None


def demo_static_visualization():
    """Demonstrate static visualization generation."""
    print("📊 Step 2: Static Visualization Generation")
    print("=" * 50)
    
    theorem = create_comprehensive_test_theorem()
    sketch = create_comprehensive_proof_sketch()
    
    visualizer = StaticVisualizer()
    
    if not visualizer.is_available():
        print("⚠️  Static visualizer not available")
        return None
    
    output_path = "demo_export_proof_diagram.png"
    
    print("🎨 Generating proof diagram...")
    start_time = time.time()
    
    success = visualizer.create_proof_diagram(theorem, sketch.dict(), output_path)
    
    generation_time = (time.time() - start_time) * 1000
    
    if success and Path(output_path).exists():
        file_size = Path(output_path).stat().st_size
        print(f"✅ Static diagram created in {generation_time:.1f}ms")
        print(f"📁 Output: {output_path}")
        print(f"📏 File size: {file_size:,} bytes")
        
        return Path(output_path)
    else:
        print("❌ Static diagram generation failed")
        return None


def demo_html_export_with_animation(animation_path: Path):
    """Demonstrate HTML export with animation integration."""
    print("🌐 Step 3: HTML Export with Animation")
    print("=" * 50)
    
    theorem = create_comprehensive_test_theorem()
    sketch = create_comprehensive_proof_sketch()
    
    with tempfile.TemporaryDirectory() as tmpdir:
        output_dir = Path(tmpdir)
        
        # Configure HTML exporter with full features
        html_options = ExportOptions(
            output_dir=output_dir,
            create_subdirs=True,
            include_animations=True,
            syntax_highlighting=True,
            generate_links=True,
            create_index=True,
            include_timestamps=True,
        )
        
        html_exporter = HTMLExporter(html_options)
        
        # Create export context with animation
        context = ExportContext(
            format=ExportFormat.HTML,
            output_dir=output_dir,
            sketches=[sketch],
            animations={sketch.theorem_name: animation_path},
            include_animations=True,
            project_name="Proof Sketcher Demo",
            author="Export System Demo",
            version="2.2.0",
        )
        
        print("🔨 Exporting to HTML...")
        start_time = time.time()
        
        result = html_exporter.export_single(sketch, context)
        
        export_time = (time.time() - start_time) * 1000
        
        if result.success:
            print(f"✅ HTML export completed in {export_time:.1f}ms")
            print(f"📁 Files created: {len(result.files_created)}")
            
            # Copy files to persistent location
            persistent_dir = Path("demo_export_output/html")
            persistent_dir.mkdir(parents=True, exist_ok=True)
            
            import shutil
            copied_files = []
            for file_path in result.files_created:
                dest_path = persistent_dir / file_path.name
                shutil.copy2(file_path, dest_path)
                copied_files.append(dest_path)
            
            # Analyze HTML content
            html_file = [f for f in copied_files if f.suffix == ".html"][0]
            content = html_file.read_text()
            
            print(f"📄 Main HTML file: {html_file.name}")
            print(f"📏 Content length: {len(content):,} characters")
            
            # Check key features
            features_found = []
            if "doc-gen4" in content or "decl" in content:
                features_found.append("doc-gen4 compatibility")
            if "animation" in content.lower() or "video" in content.lower():
                features_found.append("animation integration")
            if "MathJax" in content or "katex" in content:
                features_found.append("math rendering")
            if "navigation" in content.lower() or "nav" in content:
                features_found.append("navigation")
            
            print(f"✨ Features detected: {', '.join(features_found)}")
            
            return copied_files
        else:
            print(f"❌ HTML export failed: {result.errors}")
            return []


def demo_markdown_export_with_github_features(animation_path: Path):
    """Demonstrate Markdown export with GitHub features."""
    print("📝 Step 4: Markdown Export with GitHub Features")
    print("=" * 50)
    
    theorem = create_comprehensive_test_theorem()
    sketch = create_comprehensive_proof_sketch()
    
    with tempfile.TemporaryDirectory() as tmpdir:
        output_dir = Path(tmpdir)
        
        # Configure Markdown exporter for GitHub
        md_options = ExportOptions(
            output_dir=output_dir,
            markdown_flavor="github",
            generate_toc=True,
            create_index=True,
            include_animations=True,
        )
        
        md_exporter = MarkdownExporter(md_options)
        
        # Create export context
        context = ExportContext(
            format=ExportFormat.MARKDOWN,
            output_dir=output_dir,
            sketches=[sketch],
            animations={sketch.theorem_name: animation_path},
            include_animations=True,
            project_name="Mathematical Theorems Collection",
            author="Proof Sketcher",
            version="2.2.0",
        )
        
        print("📝 Exporting to GitHub Markdown...")
        start_time = time.time()
        
        result = md_exporter.export_single(sketch, context)
        
        export_time = (time.time() - start_time) * 1000
        
        if result.success:
            print(f"✅ Markdown export completed in {export_time:.1f}ms")
            print(f"📁 Files created: {len(result.files_created)}")
            
            # Copy files to persistent location
            persistent_dir = Path("demo_export_output/markdown")
            persistent_dir.mkdir(parents=True, exist_ok=True)
            
            import shutil
            copied_files = []
            for file_path in result.files_created:
                dest_path = persistent_dir / file_path.name
                shutil.copy2(file_path, dest_path)
                copied_files.append(dest_path)
            
            # Analyze Markdown content
            md_file = [f for f in copied_files if f.suffix == ".md"][0]
            content = md_file.read_text()
            
            print(f"📄 Main Markdown file: {md_file.name}")
            print(f"📏 Content length: {len(content):,} characters")
            
            # Check GitHub features
            github_features = []
            if "```lean" in content:
                github_features.append("Lean code blocks")
            if "$$" in content or "$" in content:
                github_features.append("math notation")
            if "![" in content:
                github_features.append("image embedding")
            if "| " in content and " |" in content:
                github_features.append("tables")
            if "<details>" in content:
                github_features.append("collapsible sections")
            
            print(f"🐙 GitHub features: {', '.join(github_features)}")
            
            return copied_files
        else:
            print(f"❌ Markdown export failed: {result.errors}")
            return []


def demo_pdf_export():
    """Demonstrate PDF export (if LaTeX available)."""
    print("📄 Step 5: PDF Export via LaTeX")
    print("=" * 50)
    
    theorem = create_comprehensive_test_theorem()
    sketch = create_comprehensive_proof_sketch()
    
    with tempfile.TemporaryDirectory() as tmpdir:
        output_dir = Path(tmpdir)
        
        # Configure PDF exporter
        pdf_options = ExportOptions(
            output_dir=output_dir,
            pdf_engine="pdflatex",
            include_timestamps=True,
        )
        
        pdf_exporter = PDFExporter(pdf_options)
        
        # Create export context
        context = ExportContext(
            format=ExportFormat.PDF,
            output_dir=output_dir,
            sketches=[sketch],
            project_name="Mathematical Proof Collection",
            author="Proof Sketcher System",
            version="2.2.0",
        )
        
        print("🔨 Attempting PDF export...")
        start_time = time.time()
        
        result = pdf_exporter.export_single(sketch, context)
        
        export_time = (time.time() - start_time) * 1000
        
        if result.success:
            print(f"✅ PDF export completed in {export_time:.1f}ms")
            print(f"📁 Files created: {len(result.files_created)}")
            
            # Copy PDF to persistent location
            persistent_dir = Path("demo_export_output/pdf")
            persistent_dir.mkdir(parents=True, exist_ok=True)
            
            import shutil
            pdf_file = result.files_created[0]
            dest_path = persistent_dir / pdf_file.name
            shutil.copy2(pdf_file, dest_path)
            
            file_size = dest_path.stat().st_size
            print(f"📄 PDF file: {dest_path.name}")
            print(f"📏 File size: {file_size:,} bytes")
            
            return [dest_path]
        else:
            if "not found" in str(result.errors):
                print("⚠️  LaTeX compiler not available - skipping PDF export")
                print("   Install LaTeX (e.g., texlive, miktex) to enable PDF export")
            else:
                print(f"❌ PDF export failed: {result.errors}")
            return []


def demo_multi_format_consistency():
    """Demonstrate consistency across all export formats."""
    print("🔄 Step 6: Multi-Format Consistency Check")
    print("=" * 50)
    
    theorem = create_comprehensive_test_theorem()
    sketch = create_comprehensive_proof_sketch()
    
    # Create static visualization for all formats
    static_path = demo_static_visualization()
    if not static_path:
        print("⚠️  Cannot proceed without static visualization")
        return
    
    formats_exported = {
        "HTML": demo_html_export_with_animation(static_path),
        "Markdown": demo_markdown_export_with_github_features(static_path),
        "PDF": demo_pdf_export(),
    }
    
    print("\n📊 Export Summary:")
    print("=" * 30)
    
    total_files = 0
    successful_formats = 0
    
    for format_name, files in formats_exported.items():
        if files:
            successful_formats += 1
            total_files += len(files)
            print(f"✅ {format_name}: {len(files)} files")
        else:
            print(f"❌ {format_name}: Failed")
    
    print(f"\n🎯 Results: {successful_formats}/3 formats successful")
    print(f"📁 Total files created: {total_files}")
    
    # Check content consistency
    if successful_formats >= 2:
        print("\n🔍 Content Consistency Check:")
        # All formats should contain the theorem name
        theorem_name_found = 0
        step_count_consistent = 0
        
        for format_name, files in formats_exported.items():
            if files:
                primary_file = files[0]
                try:
                    content = primary_file.read_text()
                    if sketch.theorem_name in content:
                        theorem_name_found += 1
                    
                    # Count proof steps mentioned
                    step_mentions = sum(1 for step in sketch.key_steps 
                                       if step.description in content)
                    if step_mentions >= len(sketch.key_steps) * 0.8:  # 80% threshold
                        step_count_consistent += 1
                except:
                    pass
        
        print(f"📝 Theorem name consistency: {theorem_name_found}/{successful_formats}")
        print(f"🔢 Proof steps consistency: {step_count_consistent}/{successful_formats}")
    
    return formats_exported


def main():
    """Run the complete export system demo."""
    print("🚀 Proof Sketcher Export System Demo")
    print("Milestone 2.2: Multi-Format Export System")
    print("=" * 60)
    print()
    
    try:
        # Step 1: Animation generation
        animation_script = demo_animation_generation()
        print()
        
        # Step 2: Static visualization
        static_path = demo_static_visualization()
        print()
        
        if static_path:
            # Step 3-6: All export formats
            export_results = demo_multi_format_consistency()
            
            print("\n" + "=" * 60)
            print("🎉 EXPORT SYSTEM DEMO COMPLETE!")
            print("=" * 60)
            
            # Final validation
            success_count = sum(1 for files in export_results.values() if files)
            
            print(f"✅ Animation script generation: {'WORKING' if animation_script else 'FAILED'}")
            print(f"✅ Static visualization: {'WORKING' if static_path else 'FAILED'}")
            print(f"✅ HTML export: {'WORKING' if export_results.get('HTML') else 'FAILED'}")
            print(f"✅ Markdown export: {'WORKING' if export_results.get('Markdown') else 'FAILED'}")
            print(f"✅ PDF export: {'WORKING' if export_results.get('PDF') else 'SKIPPED'}")
            
            print(f"\n🎯 Overall Success Rate: {success_count}/3 export formats")
            
            if success_count >= 2:
                print("✨ MILESTONE 2.2 COMPLETE: Multi-format export system operational!")
            else:
                print("⚠️  Some export formats failed - check logs above")
            
            print("\n📁 Generated files available in demo_export_output/")
            
        else:
            print("❌ Demo failed at static visualization step")
    
    except Exception as e:
        print(f"\n❌ Demo failed with error: {e}")
        import traceback
        traceback.print_exc()
    
    print(f"\n📁 Check demo_export_output/ for generated files")


if __name__ == "__main__":
    main()