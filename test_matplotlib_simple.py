#!/usr/bin/env python3
"""
Simple matplotlib test to debug static visualization issues.
"""

import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
from pathlib import Path

def test_simple_plot():
    """Test basic matplotlib functionality."""
    
    # Create a simple plot
    fig, ax = plt.subplots(figsize=(8, 6))
    ax.plot([1, 2, 3, 4], [1, 4, 2, 3], 'bo-')
    ax.set_title("Simple Test Plot")
    ax.set_xlabel("X")
    ax.set_ylabel("Y")
    
    # Save the plot
    output_path = "test_simple_plot.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close(fig)
    
    # Check if file was created
    if Path(output_path).exists():
        size = Path(output_path).stat().st_size
        print(f"✅ Simple plot created: {output_path} ({size} bytes)")
        if size > 0:
            return True
        else:
            print("❌ File created but empty")
            return False
    else:
        print("❌ File not created")
        return False

def test_complex_plot():
    """Test more complex matplotlib features."""
    
    from matplotlib.patches import FancyBboxPatch, Circle
    
    fig, ax = plt.subplots(figsize=(10, 8))
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis('off')
    
    # Add some shapes
    box = FancyBboxPatch(
        (1, 7), 8, 1.5,
        boxstyle="round,pad=0.1",
        facecolor='lightblue',
        edgecolor='darkblue'
    )
    ax.add_patch(box)
    
    # Add text
    ax.text(5, 7.75, "Test Complex Visualization", 
            fontsize=16, ha='center', va='center')
    
    # Add circle
    circle = Circle((5, 4), 1, facecolor='yellow', edgecolor='orange')
    ax.add_patch(circle)
    
    # Save
    output_path = "test_complex_plot.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight', 
                facecolor='white', edgecolor='none')
    plt.close(fig)
    
    # Check
    if Path(output_path).exists():
        size = Path(output_path).stat().st_size
        print(f"✅ Complex plot created: {output_path} ({size} bytes)")
        return size > 0
    else:
        print("❌ Complex plot not created")
        return False

if __name__ == "__main__":
    print("🧪 Testing matplotlib functionality...")
    
    print("\n1. Simple plot test:")
    simple_ok = test_simple_plot()
    
    print("\n2. Complex plot test:")
    complex_ok = test_complex_plot()
    
    print(f"\n📊 Results:")
    print(f"  Simple plot: {'✅' if simple_ok else '❌'}")
    print(f"  Complex plot: {'✅' if complex_ok else '❌'}")
    
    if simple_ok and complex_ok:
        print("🎉 Matplotlib working correctly!")
    else:
        print("⚠️ Matplotlib issues detected")
    
    # Show created files
    print("\nFiles created:")
    for filename in ["test_simple_plot.png", "test_complex_plot.png"]:
        if Path(filename).exists():
            size = Path(filename).stat().st_size
            print(f"  • {filename} ({size} bytes)")
        else:
            print(f"  • {filename} (not found)")