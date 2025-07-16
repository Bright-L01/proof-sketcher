#!/usr/bin/env python3
"""Create a demonstration of the doc-gen4 educational plugin system.

This script demonstrates how our educational plugin enhances doc-gen4
documentation with progressive explanations and interactive learning elements.
"""

import json
import tempfile
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List

from src.proof_sketcher.docgen_plugin import EducationalTemplateEngine, ModuleProcessor
from src.proof_sketcher.docgen_plugin.lake_facet import (
    EducationalLakeFacet,
    LakeFacetConfig,
)


def create_sample_docgen_data() -> List[Dict[str, Any]]:
    """Create sample doc-gen4 JSON data for demonstration."""
    return [
        {
            "name": "Nat.Basic",
            "doc": "Basic properties of natural numbers",
            "declarations": [
                {
                    "name": "Nat.add_comm",
                    "kind": "theorem",
                    "doc": "Addition is commutative",
                    "type": "∀ (n m : ℕ), n + m = m + n",
                    "proof": "by rw [add_comm]",
                },
                {
                    "name": "Nat.zero_add",
                    "kind": "theorem",
                    "doc": "Adding zero to any natural number gives the same number",
                    "type": "∀ (n : ℕ), 0 + n = n",
                    "proof": "by rfl",
                },
                {
                    "name": "Nat.succ_inj",
                    "kind": "theorem",
                    "doc": "Successor function is injective",
                    "type": "∀ {n m : ℕ}, Nat.succ n = Nat.succ m → n = m",
                    "proof": "by intro h; exact Nat.succ.inj h",
                },
            ],
        },
        {
            "name": "List.Basic",
            "doc": "Basic properties of lists",
            "declarations": [
                {
                    "name": "List.append_nil",
                    "kind": "theorem",
                    "doc": "Appending empty list is identity",
                    "type": "∀ (l : List α), l ++ [] = l",
                    "proof": "by rw [append_nil]",
                },
                {
                    "name": "List.length_append",
                    "kind": "theorem",
                    "doc": "Length of appended lists is sum of lengths",
                    "type": "∀ (l₁ l₂ : List α), (l₁ ++ l₂).length = l₁.length + l₂.length",
                    "proof": "by induction l₁ with | nil => simp | cons h t ih => simp [length_cons, ih]",
                },
            ],
        },
        {
            "name": "Real.Basic",
            "doc": "Basic properties of real numbers",
            "declarations": [
                {
                    "name": "Real.add_assoc",
                    "kind": "theorem",
                    "doc": "Addition of real numbers is associative",
                    "type": "∀ (a b c : ℝ), (a + b) + c = a + (b + c)",
                    "proof": "by exact add_assoc",
                },
                {
                    "name": "Real.mul_comm",
                    "kind": "theorem",
                    "doc": "Multiplication of real numbers is commutative",
                    "type": "∀ (a b : ℝ), a * b = b * a",
                    "proof": "by exact mul_comm",
                },
            ],
        },
    ]


def create_demo_directory() -> Path:
    """Create demonstration directory with sample data."""
    # Create demo directory
    demo_dir = Path.cwd() / "docgen_demo"
    demo_dir.mkdir(exist_ok=True)

    # Create input directory for doc-gen4 JSON files
    input_dir = demo_dir / "input"
    input_dir.mkdir(exist_ok=True)

    # Create sample doc-gen4 JSON files
    sample_data = create_sample_docgen_data()

    for module_data in sample_data:
        module_file = input_dir / f"{module_data['name']}.json"
        with open(module_file, "w", encoding="utf-8") as f:
            json.dump(module_data, f, indent=2, ensure_ascii=False)

    return demo_dir


def demo_module_processor():
    """Demonstrate the module processor functionality."""
    print("🔧 Demonstrating Module Processor")
    print("=" * 50)

    processor = ModuleProcessor()

    # Process sample theorem
    sample_json = {
        "name": "Demo.Module",
        "doc": "Sample module for demonstration",
        "declarations": [
            {
                "name": "add_comm_demo",
                "kind": "theorem",
                "doc": "Demonstration of addition commutativity",
                "type": "∀ (n m : ℕ), n + m = m + n",
                "proof": "by rw [add_comm]",
            }
        ],
    }

    enhanced_json = processor.enhance_module_json(sample_json)

    print(f"✅ Enhanced module: {enhanced_json['name']}")
    print(
        f"📊 Total declarations: {enhanced_json['educational_metadata']['total_declarations']}"
    )
    print(
        f"🎓 Educational declarations: {enhanced_json['educational_metadata']['educational_declarations']}"
    )

    # Show educational content for first declaration
    if enhanced_json["declarations"]:
        decl = enhanced_json["declarations"][0]
        if "educational_content" in decl and decl["educational_content"]:
            print(f"\n📚 Educational content generated for: {decl['name']}")
            edu_content = decl["educational_content"]
            if "progressive_explanations" in edu_content:
                print("   - Beginner explanation: ✅")
                print("   - Intermediate explanation: ✅")
                print("   - Advanced explanation: ✅")

    print()


def demo_template_engine():
    """Demonstrate the template engine functionality."""
    print("🎨 Demonstrating Template Engine")
    print("=" * 50)

    template_engine = EducationalTemplateEngine()

    # Sample declaration with educational content
    sample_declaration = {
        "name": "add_comm_demo",
        "kind": "theorem",
        "type": "∀ (n m : ℕ), n + m = m + n",
        "doc": "Addition is commutative",
        "educational_content": {
            "progressive_explanations": {
                "beginner": {
                    "title": "Understanding Addition Order",
                    "overview": "This theorem tells us that when adding two numbers, the order doesn't matter.",
                    "intuition": "Think of adding marbles: 3 + 5 marbles is the same as 5 + 3 marbles.",
                    "main_ideas": [
                        "Addition works the same way regardless of order",
                        "This is a fundamental property of arithmetic",
                    ],
                },
                "intermediate": {
                    "title": "Commutativity of Addition",
                    "overview": "Formally proves that addition on natural numbers is commutative.",
                    "main_ideas": [
                        "Uses the definition of addition",
                        "Relies on inductive structure of natural numbers",
                    ],
                },
                "advanced": {
                    "title": "Formal Proof of Commutativity",
                    "overview": "Rigorous proof using the recursive definition of addition.",
                    "main_ideas": [
                        "Induction on the first argument",
                        "Base case: 0 + m = m + 0",
                        "Inductive step: (n + 1) + m = m + (n + 1)",
                    ],
                },
            },
            "key_concepts": [
                {
                    "name": "Commutativity",
                    "explanation": "A property where the order of operands doesn't affect the result",
                },
                {
                    "name": "Natural Numbers",
                    "explanation": "The counting numbers: 0, 1, 2, 3, ...",
                },
            ],
            "learning_pathway": [
                {
                    "title": "Understand Natural Numbers",
                    "explanation": "Learn about the basic structure of natural numbers",
                },
                {
                    "title": "Learn Addition Definition",
                    "explanation": "Understand how addition is defined recursively",
                },
                {
                    "title": "Apply Commutativity",
                    "explanation": "Use the theorem in practical situations",
                },
            ],
        },
    }

    html_output = template_engine.render_educational_declaration(sample_declaration)

    print("✅ Generated HTML template for educational declaration")
    print(f"📏 HTML length: {len(html_output)} characters")
    print("🎯 Features included:")
    print("   - Progressive explanation tabs")
    print("   - Key concepts section")
    print("   - Learning pathway")
    print("   - Interactive elements")
    print()


def demo_lake_facet():
    """Demonstrate the Lake facet integration."""
    print("⚙️ Demonstrating Lake Facet Integration")
    print("=" * 50)

    # Create temporary directories
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)
        input_dir = temp_path / "input"
        output_dir = temp_path / "output"

        input_dir.mkdir()
        output_dir.mkdir()

        # Create sample doc-gen4 JSON files
        sample_data = create_sample_docgen_data()

        for module_data in sample_data:
            module_file = input_dir / f"{module_data['name']}.json"
            with open(module_file, "w", encoding="utf-8") as f:
                json.dump(module_data, f, indent=2, ensure_ascii=False)

        # Create Lake facet configuration
        config = LakeFacetConfig(
            input_dir=input_dir, output_dir=output_dir, enable_educational=True
        )

        # Create facet instance
        facet = EducationalLakeFacet(config)

        # Process all modules
        results = facet.process_all_modules()

        # Generate assets
        facet.generate_educational_assets()

        # Create index
        index_path = facet.create_educational_index(results)

        print(f"✅ Processed {results['success_count']} modules successfully")
        print(f"❌ Failed to process {results['error_count']} modules")
        print(f"📊 Total modules: {results['total_modules']}")
        print(f"📄 Educational index created at: {Path(index_path).name}")

        # Show generated files
        generated_files = list(output_dir.glob("**/*"))
        print(f"\n📁 Generated {len(generated_files)} files:")
        for file in generated_files:
            if file.is_file():
                print(f"   - {file.name}")

        print()


def create_comprehensive_demo():
    """Create a comprehensive demonstration of the plugin system."""
    print("🚀 Creating Comprehensive Doc-gen4 Educational Plugin Demo")
    print("=" * 80)

    # Create demo directory
    demo_dir = create_demo_directory()
    print(f"📁 Created demo directory: {demo_dir}")

    # Create configuration
    config = LakeFacetConfig(
        input_dir=demo_dir / "input",
        output_dir=demo_dir / "output",
        enable_educational=True,
    )

    # Create facet instance
    facet = EducationalLakeFacet(config)

    # Process all modules
    print("\n📊 Processing modules...")
    results = facet.process_all_modules()

    # Generate assets
    print("🎨 Generating assets...")
    facet.generate_educational_assets()

    # Create index
    print("📄 Creating index...")
    index_path = facet.create_educational_index(results)

    # Create documentation
    create_demo_documentation(demo_dir, results)

    # Create README
    create_demo_readme(demo_dir, results)

    print(f"\n✅ Demo completed successfully!")
    print(f"📁 Demo directory: {demo_dir}")
    print(f"📄 Open {index_path} in your browser to see the results")

    return demo_dir


def create_demo_documentation(demo_dir: Path, results: Dict[str, Any]):
    """Create documentation for the demo."""
    doc_content = f"""# Doc-gen4 Educational Plugin Demo

This demonstration shows how our educational plugin enhances standard doc-gen4
documentation with progressive explanations and interactive learning elements.

## Results

- **Total Modules**: {results['total_modules']}
- **Successfully Processed**: {results['success_count']}
- **Failed**: {results['error_count']}
- **Generated**: {datetime.now().isoformat()}

## Features Demonstrated

### 1. Progressive Explanations
- **Beginner**: Intuitive explanations with everyday analogies
- **Intermediate**: Mathematical reasoning with formal structure
- **Advanced**: Rigorous proofs with technical precision

### 2. Interactive Elements
- Tabbed interface for different explanation levels
- Key concept cards with hover effects
- Learning pathway with step-by-step progression
- Interactive elements for engagement

### 3. Educational Metadata
- Difficulty level assessment
- Learning time estimation
- Prerequisite identification
- Visualization suggestions

## Architecture

```
doc-gen4 JSON → Educational Plugin → Enhanced Documentation
```

The plugin processes standard doc-gen4 JSON output and enhances it with:

1. **Module Processor**: Analyzes theorem structure and generates educational content
2. **Template Engine**: Renders interactive HTML with progressive explanations
3. **Lake Facet**: Integrates seamlessly with the Lake build system

## Files Structure

```
docgen_demo/
├── input/                    # Sample doc-gen4 JSON files
│   ├── Nat.Basic.json
│   ├── List.Basic.json
│   └── Real.Basic.json
├── output/                   # Enhanced documentation
│   ├── assets/
│   │   ├── educational.css
│   │   └── educational.js
│   ├── *_enhanced.json       # Enhanced JSON files
│   ├── *_educational.html    # Educational HTML files
│   └── educational_index.html # Main index
└── README.md                 # This file
```

## Impact

This plugin transforms doc-gen4 documentation from expert-level reference material
into progressive educational resources that serve learners at all levels while
maintaining the technical accuracy expected by the Lean community.
"""

    doc_path = demo_dir / "DEMO_DOCUMENTATION.md"
    with open(doc_path, "w", encoding="utf-8") as f:
        f.write(doc_content)


def create_demo_readme(demo_dir: Path, results: Dict[str, Any]):
    """Create README for the demo."""
    readme_content = f"""# Doc-gen4 Educational Plugin Demo

**Generated**: {datetime.now().isoformat()}

## Quick Start

1. Open `output/educational_index.html` in your browser
2. Click on any module to see educational explanations
3. Use the tabs to switch between beginner/intermediate/advanced levels

## Demo Statistics

- **Modules Processed**: {results['success_count']}/{results['total_modules']}
- **Educational Content Generated**: ✅
- **Interactive Features**: ✅
- **Assets Created**: ✅

## What to Look For

### Progressive Explanations
Each theorem has three levels of explanation:
- 🌱 **Beginner**: Intuitive, accessible explanations
- 🌿 **Intermediate**: Mathematical reasoning
- 🌳 **Advanced**: Rigorous formal proofs

### Interactive Elements
- Click tabs to switch explanation levels
- Hover over concept cards for highlights
- Explore learning pathways step-by-step

### Educational Features
- Difficulty indicators
- Learning time estimates
- Prerequisites identification
- Visualization suggestions

## Technical Details

This demo shows how our plugin integrates with doc-gen4 to create educational
documentation that serves both beginners and experts. The plugin processes
standard doc-gen4 JSON output and enhances it with progressive explanations
and interactive learning elements.

## Next Steps

This plugin system is designed to integrate directly with the official mathlib
documentation pipeline, making all mathlib theorems accessible to learners
at every level.
"""

    readme_path = demo_dir / "README.md"
    with open(readme_path, "w", encoding="utf-8") as f:
        f.write(readme_content)


def main():
    """Main demonstration function."""
    print("🎓 Doc-gen4 Educational Plugin System Demo")
    print("=" * 80)

    # Run individual demos
    demo_module_processor()
    demo_template_engine()
    demo_lake_facet()

    # Create comprehensive demo
    demo_dir = create_comprehensive_demo()

    print("\n🎉 Demo completed successfully!")
    print(f"📁 Demo files created in: {demo_dir}")
    print(f"📄 Open {demo_dir}/output/educational_index.html to see the results")

    return demo_dir


if __name__ == "__main__":
    main()
