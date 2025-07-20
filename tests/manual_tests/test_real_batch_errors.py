#!/usr/bin/env python3
"""
Real Batch Error Test
=====================

Test the actual batch exporter to see how it handles failures in practice.
"""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

# Add the src directory to the path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from proof_sketcher.exporter.batch_processor import BatchExporter
from proof_sketcher.generator.models import ProofSketch, ProofStep


def create_test_sketch(name: str, valid: bool = True) -> ProofSketch:
    """Create a test proof sketch."""
    try:
        step = ProofStep(
            step_number=1,
            intuitive_explanation="Test step explanation",
            conceptual_explanation="Test conceptual explanation",
            bridging_explanation="Test bridging explanation",
            formal_explanation="Test formal explanation",
            mathematical_content="Test content",
        )

        sketch = ProofSketch(
            theorem_name=name if valid else "bad/name/with/slashes",
            theorem_statement="Test theorem statement",
            intuitive_overview="Test intuitive overview",
            conceptual_overview="Test conceptual overview",
            bridging_overview="Test bridging overview",
            formal_overview="Test formal overview",
            key_steps=[step],
            intuitive_conclusion="Test intuitive conclusion",
            conceptual_conclusion="Test conceptual conclusion",
            bridging_conclusion="Test bridging conclusion",
            formal_conclusion="Test formal conclusion",
            proof_strategy="direct",
        )
        return sketch
    except Exception as e:
        print(f"Error creating sketch for {name}: {e}")
        raise


def test_batch_export_with_failures():
    """Test batch export handling failures gracefully."""
    print("🧪 Testing Real Batch Export Error Handling")
    print("=" * 50)

    # Create temporary directory
    test_dir = Path(tempfile.mkdtemp())
    print(f"Using test directory: {test_dir}")

    # Create test sketches - some will cause issues
    sketches = []

    # Good sketches
    for i in range(3):
        sketch = create_test_sketch(f"good_theorem_{i}")
        sketches.append(sketch)

    # Bad sketch with problematic filename
    try:
        bad_sketch = create_test_sketch("bad/filename/with/slashes", valid=False)
        sketches.append(bad_sketch)
    except:
        print("Note: Could not create bad sketch due to validation")

    # More good sketches
    for i in range(2):
        sketch = create_test_sketch(f"another_good_theorem_{i}")
        sketches.append(sketch)

    print(f"Created {len(sketches)} test sketches")

    # Test batch export
    batch_exporter = BatchExporter(test_dir / "export_test")

    print("\nRunning batch export...")
    results = batch_exporter.export_multiple(sketches, formats=["markdown", "html"])

    # Check results
    markdown_files = results.get("markdown", [])
    html_files = results.get("html", [])

    print(f"\nResults:")
    print(f"- Markdown files created: {len(markdown_files)}")
    print(f"- HTML files created: {len(html_files)}")

    # Verify files exist
    markdown_dir = test_dir / "export_test" / "markdown"
    html_dir = test_dir / "export_test" / "html"

    actual_md_files = list(markdown_dir.glob("*.md")) if markdown_dir.exists() else []
    actual_html_files = list(html_dir.glob("*.html")) if html_dir.exists() else []

    print(f"- Actual markdown files on disk: {len(actual_md_files)}")
    print(f"- Actual HTML files on disk: {len(actual_html_files)}")

    # Check if most exports succeeded
    expected_successes = len(sketches)  # All should succeed now with valid names
    success_rate_md = (
        len(actual_md_files) / expected_successes if expected_successes > 0 else 0
    )
    success_rate_html = (
        len(actual_html_files) / expected_successes if expected_successes > 0 else 0
    )

    print(f"\nSuccess rates:")
    print(f"- Markdown: {success_rate_md:.1%}")
    print(f"- HTML: {success_rate_html:.1%}")

    # Check for index files
    index_md = test_dir / "export_test" / "README.md"
    index_html = test_dir / "export_test" / "index.html"

    print(f"\nIndex files:")
    print(f"- README.md created: {index_md.exists()}")
    print(f"- index.html created: {index_html.exists()}")

    # Assessment
    print("\n" + "=" * 50)
    print("📊 BATCH ERROR HANDLING ASSESSMENT")
    print("=" * 50)

    if success_rate_md >= 0.8 and success_rate_html >= 0.8:
        print("✅ EXCELLENT: Batch processing handled errors gracefully")
        print("   - High success rate despite potential issues")
        print("   - Process completed without crashing")
        print("   - Individual failures didn't stop batch operation")
    elif success_rate_md >= 0.5 and success_rate_html >= 0.5:
        print("⚠️  GOOD: Batch processing mostly resilient")
        print("   - Moderate success rate")
        print("   - Some failures may have occurred")
    else:
        print("❌ POOR: Batch processing not resilient to errors")
        print("   - Low success rate")
        print("   - Too many failures")

    print(f"\nTest directory preserved at: {test_dir}")
    print("You can inspect the generated files and logs there.")

    return success_rate_md >= 0.8 and success_rate_html >= 0.8


if __name__ == "__main__":
    success = test_batch_export_with_failures()
    print(f"\nOverall test result: {'PASSED' if success else 'FAILED'}")
    sys.exit(0 if success else 1)
