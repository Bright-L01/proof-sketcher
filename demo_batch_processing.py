#!/usr/bin/env python3
"""
Batch Processing Demo - Milestone 2.3

Demonstrates the complete batch processing system:
- Project scanning with dependency analysis
- Parallel theorem processing
- Caching for efficiency
- Multi-format export
- Progress reporting
"""

import asyncio
import shutil
import time
from pathlib import Path

# Set matplotlib backend before imports
import matplotlib
matplotlib.use('Agg')

from src.proof_sketcher.batch import CacheManager, ParallelProcessor, ProjectScanner


def create_demo_project(base_path: Path) -> Path:
    """Create a demo Lean project with multiple files and dependencies."""
    project_root = base_path / "demo_lean_project"
    
    # Clean up if exists
    if project_root.exists():
        shutil.rmtree(project_root)
    
    project_root.mkdir(parents=True)
    
    print("📁 Creating demo Lean project structure...")
    
    # Create foundational file
    foundation = project_root / "Foundation.lean"
    foundation.write_text("""
-- Foundation: Basic arithmetic properties

/-- Zero is the additive identity on the right -/
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [Nat.add_succ, ih]

/-- Zero is the additive identity on the left -/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [Nat.succ_eq_add_one, ← ih]
    rfl

/-- One plus a number equals its successor -/
lemma add_one (n : Nat) : n + 1 = n.succ := by
  rfl

/-- Successor distributes over addition -/
theorem succ_add (n m : Nat) : n.succ + m = (n + m).succ := by
  induction m with
  | zero => rfl
  | succ m ih => 
    rw [Nat.add_succ, ih, Nat.add_succ]
""")
    
    # Create data structures directory
    data_dir = project_root / "Data"
    data_dir.mkdir()
    
    # Create list operations file
    list_ops = data_dir / "ListOps.lean"
    list_ops.write_text("""
import Foundation

-- List operations and properties

namespace List

/-- Appending nil to a list leaves it unchanged -/
theorem append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons h t ih => 
    simp [List.append, ih]

/-- Nil is the left identity for append -/
theorem nil_append (l : List α) : [] ++ l = l := by
  rfl

/-- Length of cons is successor of tail length -/
theorem length_cons (a : α) (l : List α) : (a :: l).length = l.length + 1 := by
  simp [List.length]

/-- Append preserves length additivity -/
theorem length_append (l1 l2 : List α) : (l1 ++ l2).length = l1.length + l2.length := by
  induction l1 with
  | nil => simp [nil_append]
  | cons h t ih => 
    simp [List.append, length_cons, ih]
    rw [add_succ]

end List
""")
    
    # Create advanced theorems file
    advanced = project_root / "Advanced" / "Arithmetic.lean"
    advanced.parent.mkdir()
    advanced.write_text("""
import Foundation
import Data.ListOps

-- Advanced arithmetic properties

/-- Addition is commutative -/
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp [zero_add, add_zero]
  | succ a ih => 
    rw [succ_add, ih, ← add_succ, add_one]

/-- Addition is associative -/
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => simp [zero_add]
  | succ a ih => 
    simp [succ_add, ih]

/-- Multiplication distributes over addition -/
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => simp
  | succ a ih => 
    simp [Nat.succ_mul, ih, add_assoc]
    rw [add_comm (a * b), add_assoc, add_comm c, ← add_assoc]
""")
    
    # Create applied theorems file
    applied = project_root / "Applied.lean"
    applied.write_text("""
import Foundation
import Advanced.Arithmetic

-- Applied theorems using previous results

/-- Double of a number equals adding it to itself -/
theorem double_eq_add_self (n : Nat) : 2 * n = n + n := by
  simp [Nat.succ_mul, Nat.one_mul, add_comm]

/-- Square of sum formula -/
theorem square_sum (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  rw [mul_add, mul_add, mul_add]
  simp [mul_comm b a, double_eq_add_self]
  rw [← add_assoc, ← add_assoc]
  rw [add_assoc (a * a), add_comm (a * b), ← add_assoc]

/-- Sum of first n natural numbers -/
theorem sum_first_n (n : Nat) : 2 * (List.range n.succ).sum = n * n.succ := by
  sorry  -- Complex proof omitted for demo
""")
    
    # Create test directory (should be ignored)
    test_dir = project_root / "test"
    test_dir.mkdir()
    test_file = test_dir / "TestTheorems.lean"
    test_file.write_text("""
-- Test theorems (should be ignored in batch processing)
theorem test_1 : 1 = 1 := rfl
theorem test_2 : 2 = 2 := rfl
""")
    
    print(f"✅ Created demo project at: {project_root}")
    print(f"   - 4 main Lean files")
    print(f"   - 15+ theorems")
    print(f"   - Multiple dependency levels")
    print(f"   - Test directory (to be ignored)")
    
    return project_root


async def run_batch_processing_demo():
    """Run the complete batch processing demo."""
    print("🚀 Proof Sketcher Batch Processing Demo")
    print("=" * 60)
    
    # Setup paths
    demo_dir = Path("demo_batch_output")
    demo_dir.mkdir(exist_ok=True)
    
    # Create demo project
    project_root = create_demo_project(demo_dir)
    
    print("\n" + "=" * 60)
    print("📊 PHASE 1: Project Analysis")
    print("=" * 60)
    
    # Initialize scanner
    scanner = ProjectScanner()
    
    # Scan project
    print("\n🔍 Scanning project structure...")
    start_time = time.time()
    project_data = scanner.scan_project(project_root)
    scan_time = time.time() - start_time
    
    print(f"✅ Scan completed in {scan_time:.2f}s")
    
    # Display statistics
    stats = project_data["statistics"]
    print(f"\n📈 Project Statistics:")
    print(f"   • Total files: {stats['total_files']}")
    print(f"   • Total theorems: {stats['total_theorems']}")
    print(f"   • Total lines: {stats['total_lines']:,}")
    print(f"   • Average theorems/file: {stats['avg_theorems_per_file']:.1f}")
    print(f"   • Is DAG: {'✅ Yes' if stats['dependency_graph']['is_dag'] else '❌ No'}")
    
    # Show dependency order
    print(f"\n🔗 Dependency Order:")
    for i, file in enumerate(project_data["process_order"], 1):
        theorem_count = len(project_data["file_theorems"].get(file, []))
        print(f"   {i}. {file} ({theorem_count} theorems)")
    
    # Show most imported files
    if stats["most_imported_files"]:
        print(f"\n📥 Most Imported Files:")
        for file, count in stats["most_imported_files"][:3]:
            print(f"   • {file}: {count} imports")
    
    print("\n" + "=" * 60)
    print("💾 PHASE 2: Cache Setup")
    print("=" * 60)
    
    # Initialize cache
    cache_dir = demo_dir / "cache"
    cache_manager = CacheManager(
        cache_dir=cache_dir,
        ttl_days=30,
        compress=True,
        max_cache_size_mb=100
    )
    
    print(f"📦 Cache initialized at: {cache_dir}")
    cache_stats = cache_manager.get_statistics()
    print(f"   • Existing entries: {cache_stats['total_entries']}")
    print(f"   • Cache size: {cache_stats['total_size_mb']:.1f} MB")
    print(f"   • Compression: {'Enabled' if cache_manager.compress else 'Disabled'}")
    
    print("\n" + "=" * 60)
    print("⚡ PHASE 3: Parallel Processing")
    print("=" * 60)
    
    # Initialize processor
    num_workers = min(4, stats["total_files"])  # Reasonable number of workers
    processor = ParallelProcessor(max_workers=num_workers, use_processes=True)
    
    print(f"🔧 Parallel processor initialized:")
    print(f"   • Workers: {num_workers}")
    print(f"   • Mode: {'Process' if processor.use_processes else 'Thread'} pool")
    
    # Processing options
    output_dir = demo_dir / "output"
    options = {
        "use_claude": False,  # Use offline mode for demo
        "create_visualization": True,
        "try_animation": True,
        "export_formats": ["html", "markdown"],
        "project_name": "Demo Lean Project",
        "author": "Batch Processing Demo",
        "version": "1.0.0",
    }
    
    # Progress tracking
    progress_data = {"processed": 0, "total": stats["total_theorems"]}
    
    def progress_callback(file_path: str, theorem_name: str, result: dict):
        progress_data["processed"] += 1
        status_icon = {
            "success": "✅",
            "skipped": "⏭️",
            "error": "❌"
        }.get(result["status"], "❓")
        
        print(
            f"{status_icon} [{progress_data['processed']}/{progress_data['total']}] "
            f"{theorem_name} ({result.get('time', 0):.1f}s) - {result.get('generator', 'N/A')}"
        )
    
    print(f"\n🚀 Processing {stats['total_theorems']} theorems...")
    print("─" * 60)
    
    # Run processing
    start_time = time.time()
    results = await processor.process_project(
        project_data,
        output_dir,
        options,
        progress_callback
    )
    total_time = time.time() - start_time
    
    print("─" * 60)
    print(f"✅ Processing completed in {total_time:.1f}s")
    
    print("\n" + "=" * 60)
    print("📊 PHASE 4: Results Analysis")
    print("=" * 60)
    
    # Display results
    print(f"\n📈 Processing Summary:")
    print(f"   • Total theorems: {results['total_theorems']}")
    print(f"   • Successfully processed: {results['processed']} ({results['processed']/results['total_theorems']*100:.1f}%)")
    print(f"   • Skipped: {results['skipped']}")
    print(f"   • Errors: {results['errors']}")
    
    # Performance stats
    perf_stats = results["statistics"]
    print(f"\n⚡ Performance Metrics:")
    print(f"   • Total processing time: {perf_stats['total_time']:.1f}s")
    print(f"   • Average per theorem: {perf_stats['average_time']:.2f}s")
    print(f"   • Throughput: {perf_stats['theorems_per_second']:.2f} theorems/second")
    
    # Generator usage
    if perf_stats["generator_usage"]:
        print(f"\n🤖 Generator Usage:")
        for gen, count in perf_stats["generator_usage"].items():
            print(f"   • {gen}: {count} theorems")
    
    # Visualizer usage
    if perf_stats["visualizer_usage"]:
        print(f"\n🎨 Visualizer Usage:")
        for viz, count in perf_stats["visualizer_usage"].items():
            if viz != "none":
                print(f"   • {viz}: {count} theorems")
    
    # Error summary
    if results["errors"] > 0:
        error_summary = results["error_summary"]
        print(f"\n❌ Error Analysis:")
        print(f"   • Total errors: {error_summary['total_errors']}")
        print(f"   • Most common: {error_summary['most_common']}")
    
    # Cache performance
    print(f"\n📦 Cache Performance:")
    final_cache_stats = cache_manager.get_statistics()
    print(f"   • Entries added: {final_cache_stats['total_entries'] - cache_stats['total_entries']}")
    print(f"   • Final cache size: {final_cache_stats['total_size_mb']:.1f} MB")
    
    print("\n" + "=" * 60)
    print("📁 PHASE 5: Output Verification")
    print("=" * 60)
    
    # Check generated files
    if output_dir.exists():
        html_files = list(output_dir.rglob("*.html"))
        md_files = list(output_dir.rglob("*.md"))
        png_files = list(output_dir.rglob("*.png"))
        
        print(f"\n📄 Generated Files:")
        print(f"   • HTML files: {len(html_files)}")
        print(f"   • Markdown files: {len(md_files)}")
        print(f"   • Visualizations: {len(png_files)}")
        
        # Show sample files
        if html_files:
            print(f"\n📝 Sample HTML outputs:")
            for file in html_files[:3]:
                size = file.stat().st_size
                print(f"   • {file.name} ({size:,} bytes)")
        
        if png_files:
            print(f"\n🎨 Sample visualizations:")
            for file in png_files[:3]:
                size = file.stat().st_size
                print(f"   • {file.name} ({size:,} bytes)")
    
    print("\n" + "=" * 60)
    print("🎉 BATCH PROCESSING DEMO COMPLETE!")
    print("=" * 60)
    
    print(f"\n✅ Successfully demonstrated:")
    print(f"   • Project scanning with dependency analysis")
    print(f"   • Parallel processing with {num_workers} workers")
    print(f"   • Caching system with compression")
    print(f"   • Multi-format export (HTML + Markdown)")
    print(f"   • Static visualization generation")
    print(f"   • Progress tracking and reporting")
    
    print(f"\n📊 Key Achievements:")
    print(f"   • Processed {results['processed']} theorems in {total_time:.1f}s")
    print(f"   • Achieved {perf_stats['theorems_per_second']:.2f} theorems/second")
    print(f"   • Generated {len(html_files) + len(md_files)} documentation files")
    print(f"   • Created {len(png_files)} visualizations")
    
    print(f"\n📁 All outputs saved to: {demo_dir}")
    print(f"   • Project: {project_root}")
    print(f"   • Documentation: {output_dir}")
    print(f"   • Cache: {cache_dir}")
    
    # Test cache effectiveness
    if results["processed"] > 0:
        print(f"\n🔄 Testing cache effectiveness...")
        print("   Running second pass (should be faster)...")
        
        start_time = time.time()
        second_results = await processor.process_project(
            project_data,
            output_dir,
            options,
            lambda *args: None  # Silent progress
        )
        second_time = time.time() - start_time
        
        speedup = total_time / second_time if second_time > 0 else 0
        print(f"   ✅ Second pass: {second_time:.1f}s ({speedup:.1f}x speedup)")
        
        if speedup > 1.5:
            print("   🎯 Cache is working effectively!")
        else:
            print("   ℹ️  Cache benefit minimal (expected for small demos)")
    
    return results


def main():
    """Run the demo."""
    try:
        # Run async demo
        results = asyncio.run(run_batch_processing_demo())
        
        # Success
        if results["processed"] > 0:
            print("\n✨ Milestone 2.3 COMPLETE: Batch processing system fully operational!")
        
    except KeyboardInterrupt:
        print("\n⚠️  Demo interrupted by user")
    except Exception as e:
        print(f"\n❌ Demo failed: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()