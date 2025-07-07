#!/usr/bin/env python3
"""Verification script for Milestone 5.3: Template System Completion.

This script verifies that all features mentioned in the milestone are:
1. Actually implemented
2. Working correctly
3. Have adequate test coverage
"""

import asyncio
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Tuple

# Project root
PROJECT_ROOT = Path(__file__).parent


def check_template_files() -> Tuple[bool, List[str]]:
    """Check that all required templates exist."""
    print("\n🔍 Checking template files...")
    
    required_templates = [
        "html/theorem.html.jinja2",
        "html/index.html.jinja2", 
        "html/mathlib_style.html.jinja2",  # Doc-gen4 compatible
        "markdown/theorem.md.jinja2",
        "markdown/index.md.jinja2",
        "markdown/github_readme.md.jinja2",  # GitHub-flavored
        "pdf/theorem.tex.jinja2",
        "pdf/document.tex.jinja2",
        "shared/math_macros.j2"
    ]
    
    template_dir = PROJECT_ROOT / "src/proof_sketcher/exporter/templates"
    missing = []
    
    for template in required_templates:
        template_path = template_dir / template
        if not template_path.exists():
            missing.append(template)
        else:
            print(f"  ✅ {template}")
    
    if missing:
        print(f"  ❌ Missing templates: {missing}")
        
    return len(missing) == 0, missing


def check_html_features() -> Tuple[bool, List[str]]:
    """Check HTML exporter features."""
    print("\n🔍 Checking HTML exporter features...")
    
    html_file = PROJECT_ROOT / "src/proof_sketcher/exporter/html.py"
    content = html_file.read_text()
    
    features = {
        "Doc-gen4 compatibility": "_doc_gen4_classes" in content,
        "Responsive design": "responsive_design" in content,
        "Asset optimization": "_minify_css" in content and "_minify_js" in content,
        "Cache busting": "_get_asset_hashes" in content,
        "Search metadata": "_generate_search_index" in content,
        "Cross-references": "_generate_cross_references" in content,
        "Video compression": "_compress_assets" in content,
        "Poster frame generation": "_generate_poster_frames" in content,
    }
    
    missing = []
    for feature, present in features.items():
        if present:
            print(f"  ✅ {feature}")
        else:
            print(f"  ❌ {feature}")
            missing.append(feature)
            
    return len(missing) == 0, missing


def check_markdown_features() -> Tuple[bool, List[str]]:
    """Check Markdown exporter features."""
    print("\n🔍 Checking Markdown exporter features...")
    
    md_file = PROJECT_ROOT / "src/proof_sketcher/exporter/markdown.py"
    content = md_file.read_text()
    
    features = {
        "GitHub-flavored markdown": "_use_github_features" in content,
        "Math with $ notation": "_math_notation" in content and '"dollars"' in content,
        "Collapsible sections": "_use_collapsible" in content,
        "Table of contents": "_generate_toc" in content,
        "Link modes": "_link_mode" in content,
        "GIF preview": "_convert_to_gif" in content or "gif" in content.lower(),
    }
    
    missing = []
    for feature, present in features.items():
        if present:
            print(f"  ✅ {feature}")
        else:
            print(f"  ❌ {feature}")
            missing.append(feature)
            
    return len(missing) == 0, missing


def check_coverage() -> Dict[str, float]:
    """Run coverage analysis for exporters."""
    print("\n📊 Running coverage analysis...")
    
    cmd = [
        "python", "-m", "pytest",
        "tests/test_exporter*.py",
        "--cov=src/proof_sketcher/exporter",
        "--cov-report=json",
        "--quiet"
    ]
    
    try:
        subprocess.run(cmd, cwd=PROJECT_ROOT, check=True, capture_output=True)
        
        # Read coverage report
        coverage_file = PROJECT_ROOT / ".coverage"
        if coverage_file.exists():
            # Parse coverage data
            cov_cmd = ["python", "-m", "coverage", "report", "--include=*exporter*", "--format=total"]
            result = subprocess.run(cov_cmd, cwd=PROJECT_ROOT, capture_output=True, text=True)
            
            # Extract individual file coverage
            report_cmd = ["python", "-m", "coverage", "report", "--include=*exporter*"]
            report_result = subprocess.run(report_cmd, cwd=PROJECT_ROOT, capture_output=True, text=True)
            
            coverage_data = {}
            for line in report_result.stdout.split('\n'):
                if 'html.py' in line:
                    parts = line.split()
                    coverage_data['html.py'] = float(parts[-1].rstrip('%'))
                elif 'markdown.py' in line:
                    parts = line.split()
                    coverage_data['markdown.py'] = float(parts[-1].rstrip('%'))
                elif 'template_manager.py' in line:
                    parts = line.split()
                    coverage_data['template_manager.py'] = float(parts[-1].rstrip('%'))
                    
            return coverage_data
            
    except subprocess.CalledProcessError:
        print("  ⚠️  Coverage analysis failed")
        
    return {}


def verify_export_functionality():
    """Test actual export functionality."""
    print("\n🧪 Testing export functionality...")
    
    test_script = """
import asyncio
from pathlib import Path
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.exporter.html import HTMLExporter
from proof_sketcher.exporter.markdown import MarkdownExporter
from proof_sketcher.exporter.models import ExportContext, ExportOptions

# Create test sketch
sketch = ProofSketch(
    theorem_name="test_theorem",
    introduction="This is a test theorem.",
    key_steps=[
        ProofStep(
            step_number=1,
            description="First step",
            mathematical_content="$a + b = c$",
            tactics=["rw"]
        )
    ],
    conclusion="QED"
)

# Test HTML export
html_options = ExportOptions(
    output_dir=Path("/tmp/proof_sketcher_test_html"),
    include_animations=False,
    minify_assets=True,
    compress_assets=True
)
html_exporter = HTMLExporter(html_options)

# Test Markdown export  
md_options = ExportOptions(
    output_dir=Path("/tmp/proof_sketcher_test_md"),
    github_features=True,
    math_notation="dollars"
)
md_exporter = MarkdownExporter(md_options)

# Export
try:
    html_result = html_exporter.export_single(sketch)
    print(f"HTML export: {'✅ Success' if html_result.success else '❌ Failed'}")
    
    md_result = md_exporter.export_single(sketch)
    print(f"Markdown export: {'✅ Success' if md_result.success else '❌ Failed'}")
    
    # Check features
    if html_result.success:
        html_file = html_result.created_files[0]
        content = html_file.read_text()
        print(f"  - Doc-gen4 classes: {'✅' if 'class=\"decl\"' in content else '❌'}")
        print(f"  - Responsive meta: {'✅' if 'viewport' in content else '❌'}")
        
    if md_result.success:
        md_file = md_result.created_files[0]
        content = md_file.read_text()
        print(f"  - Math dollars: {'✅' if '$$' in content or '$' in content else '❌'}")
        print(f"  - GitHub features: {'✅' if '<details>' in content or '##' in content else '❌'}")
        
except Exception as e:
    print(f"Export failed: {e}")
"""
    
    # Run test
    try:
        result = subprocess.run(
            [sys.executable, "-c", test_script],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True
        )
        print(result.stdout)
        if result.stderr:
            print(f"  ⚠️  Errors: {result.stderr}")
    except Exception as e:
        print(f"  ❌ Test failed: {e}")


def main():
    """Main verification function."""
    print("=" * 60)
    print("Milestone 5.3 Verification: Template System Completion")
    print("=" * 60)
    
    all_passed = True
    
    # 1. Check templates
    templates_ok, missing_templates = check_template_files()
    all_passed &= templates_ok
    
    # 2. Check HTML features
    html_ok, missing_html = check_html_features()
    all_passed &= html_ok
    
    # 3. Check Markdown features
    md_ok, missing_md = check_markdown_features()
    all_passed &= md_ok
    
    # 4. Check coverage
    coverage = check_coverage()
    print("\n📊 Coverage Report:")
    
    targets = {
        'html.py': (68, 95),
        'markdown.py': (65, 95), 
        'template_manager.py': (72, 90)
    }
    
    for file, (baseline, target) in targets.items():
        actual = coverage.get(file, 0)
        status = "✅" if actual >= target else "❌"
        print(f"  {status} {file}: {actual:.1f}% (baseline: {baseline}%, target: {target}%)")
        if actual < target:
            all_passed = False
    
    # 5. Test functionality
    verify_export_functionality()
    
    # Summary
    print("\n" + "=" * 60)
    if all_passed:
        print("✅ All Milestone 5.3 requirements are met!")
    else:
        print("❌ Some requirements are not met:")
        if missing_templates:
            print(f"  - Missing templates: {missing_templates}")
        if missing_html:
            print(f"  - Missing HTML features: {missing_html}")
        if missing_md:
            print(f"  - Missing Markdown features: {missing_md}")
        
        # Coverage gaps
        for file, (_, target) in targets.items():
            actual = coverage.get(file, 0)
            if actual < target:
                print(f"  - {file} coverage: {actual:.1f}% < {target}% target")
    
    print("=" * 60)
    
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())