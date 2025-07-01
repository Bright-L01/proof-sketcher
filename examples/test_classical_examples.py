#!/usr/bin/env python3
"""Test script to run proof-sketcher on classical mathematics examples."""

import subprocess
import sys
from pathlib import Path

# Define the classical example files
EXAMPLE_FILES = {
    "Group Theory": "classical/group_theory.lean",
    "Real Analysis": "classical/real_analysis.lean", 
    "Point Set Topology": "classical/topology.lean"
}

# Define specific theorems to test from each area
TEST_THEOREMS = {
    "Group Theory": [
        "unique_identity",
        "unique_inverse",
        "left_cancellation",
        "order_of_identity"
    ],
    "Real Analysis": [
        "supremum_property",
        "squeeze_theorem",
        "intermediate_value_theorem"
    ],
    "Point Set Topology": [
        "open_sets_form_topology",
        "hausdorff_separation",
        "compact_subset_hausdorff_closed",
        "continuous_image_compact"
    ]
}

def run_proof_sketcher(file_path: str, theorem_name: str, output_format: str = "markdown"):
    """Run proof-sketcher on a specific theorem."""
    cmd = [
        "python", "-m", "proof_sketcher",
        "prove", str(file_path),
        "--theorem", theorem_name,
        "--format", output_format,
        "--output", "output/classical"
    ]
    
    print(f"\n{'='*60}")
    print(f"Running: {' '.join(cmd)}")
    print(f"{'='*60}")
    
    try:
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode == 0:
            print(f"✓ Successfully generated explanation for {theorem_name}")
            if result.stdout:
                print("\nOutput:")
                print(result.stdout)
        else:
            print(f"✗ Failed to generate explanation for {theorem_name}")
            if result.stderr:
                print("\nError:")
                print(result.stderr)
            if result.stdout:
                print("\nOutput:")
                print(result.stdout)
        
        return result.returncode == 0
        
    except Exception as e:
        print(f"✗ Exception occurred: {e}")
        return False

def main():
    """Test proof-sketcher on classical mathematics examples."""
    
    print("Testing Proof Sketcher on Classical Mathematics Examples")
    print("=" * 60)
    
    examples_dir = Path(__file__).parent
    success_count = 0
    total_count = 0
    
    for area, filename in EXAMPLE_FILES.items():
        file_path = examples_dir / filename
        
        if not file_path.exists():
            print(f"\n✗ {area} file not found: {file_path}")
            continue
            
        print(f"\n\n{'#'*60}")
        print(f"# Testing {area} Examples")
        print(f"{'#'*60}")
        
        theorems = TEST_THEOREMS.get(area, [])
        
        for theorem in theorems:
            total_count += 1
            if run_proof_sketcher(file_path, theorem):
                success_count += 1
    
    # Summary
    print(f"\n\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    print(f"Total theorems tested: {total_count}")
    print(f"Successful: {success_count}")
    print(f"Failed: {total_count - success_count}")
    print(f"Success rate: {success_count/total_count*100:.1f}%")
    
    # Check if output files were created
    output_dir = examples_dir / "output" / "classical"
    if output_dir.exists():
        output_files = list(output_dir.glob("*.md"))
        print(f"\nGenerated {len(output_files)} output files in {output_dir}")
        
        if output_files:
            print("\nGenerated files:")
            for f in sorted(output_files)[:10]:  # Show first 10
                print(f"  - {f.name}")
            if len(output_files) > 10:
                print(f"  ... and {len(output_files) - 10} more")
    
    return 0 if success_count == total_count else 1

if __name__ == "__main__":
    sys.exit(main())