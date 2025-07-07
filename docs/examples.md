# Examples and Usage Guide

Comprehensive examples demonstrating Proof Sketcher's capabilities across different mathematical domains.

## Quick Start Examples

### Basic Arithmetic Theorem

```lean
-- examples/basic/add_zero.lean
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]
```

**Generate explanation:**
```bash
proof-sketcher prove examples/basic/add_zero.lean
```

**Expected output:**
- Natural language explanation of mathematical induction
- Step-by-step breakdown of the proof strategy
- HTML output with mathematical formatting

### List Operations

```lean
-- examples/basic/list_append.lean
theorem append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [List.cons_append, ih]
```

**Usage:**
```bash
proof-sketcher prove examples/basic/list_append.lean --format html --output ./docs/
```

## Mathematical Domains

### Algebra Examples

#### Commutativity of Addition

```lean
-- examples/algebra/add_comm.lean
import Mathlib.Data.Nat.Basic

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_add, ih, add_succ]
```

#### Ring Properties

```lean
-- examples/algebra/ring_properties.lean
import Mathlib.Algebra.Ring.Basic

variable {R : Type*} [Ring R]

theorem ring_sub_self (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_right_neg]
```

### Analysis Examples

#### Continuity

```lean
-- examples/analysis/continuous.lean
import Mathlib.Topology.Continuous

theorem continuous_const {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] 
    (b : β) : Continuous (fun _ : α => b) := by
  exact continuous_const
```

#### Limits

```lean
-- examples/analysis/limits.lean
import Mathlib.Analysis.SpecificLimits.Basic

theorem tendsto_const_nhds {α β : Type*} [TopologicalSpace β] (a : α) (b : β) :
    Tendsto (fun _ : α => b) (𝓝 a) (𝓝 b) := by
  exact tendsto_const_nhds
```

### Logic Examples

#### Propositional Logic

```lean
-- examples/logic/prop_logic.lean
theorem modus_ponens (P Q : Prop) : P → (P → Q) → Q := by
  intro hp hpq
  exact hpq hp
```

#### Predicate Logic

```lean
-- examples/logic/predicate.lean
theorem exists_intro {α : Type*} (P : α → Prop) (a : α) (h : P a) : ∃ x, P x := by
  use a
  exact h
```

## Command-Line Usage Examples

### Basic Processing

```bash
# Process single file
proof-sketcher prove theorem.lean

# Process with specific output format
proof-sketcher prove theorem.lean --format markdown

# Process with custom output directory
proof-sketcher prove theorem.lean --output ./proofs/
```

### Batch Processing

```bash
# Process entire directory
proof-sketcher batch ./lean-files/ --output ./explanations/

# Process with file pattern
proof-sketcher batch ./src/ --pattern "*.lean" --recursive

# Process with concurrency control
proof-sketcher batch ./mathlib/ --max-workers 4
```

### Configuration Examples

```bash
# Show current configuration
proof-sketcher config show

# Validate configuration
proof-sketcher config validate

# Save configuration template
proof-sketcher config save --output my-config.yaml
```

### Cache Management

```bash
# Show cache status
proof-sketcher cache status

# Clear specific entries
proof-sketcher cache clear --pattern "algebra_*"

# Clear all cache
proof-sketcher cache clear --all
```

## Output Format Examples

### HTML Output

**Input:** Simple theorem
```lean
theorem simple : 1 + 1 = 2 := by norm_num
```

**Output:** `simple.html`
```html
<!DOCTYPE html>
<html>
<head>
    <title>simple - Proof Explanation</title>
    <script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
    <script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
</head>
<body>
    <h1>simple</h1>
    <div class="theorem-statement">
        <p><strong>Statement:</strong> \(1 + 1 = 2\)</p>
    </div>
    <div class="explanation">
        <p>This theorem establishes the basic arithmetic fact that one plus one equals two...</p>
    </div>
</body>
</html>
```

### Markdown Output

**Output:** `simple.md`
```markdown
# simple

**Statement:** $1 + 1 = 2$

## Introduction

This theorem establishes the basic arithmetic fact that one plus one equals two.

## Proof Steps

1. **Normalization**: We use `norm_num` to simplify the arithmetic expression
2. **Verification**: The tactic automatically verifies that $1 + 1 = 2$

## Conclusion

The equality $1 + 1 = 2$ follows directly from the definition of natural number arithmetic.
```

## Integration Examples

### VS Code Integration

```json
// .vscode/settings.json
{
  "proof-sketcher.autoGenerate": true,
  "proof-sketcher.outputFormat": "html",
  "proof-sketcher.showPreview": true
}
```

### GitHub Actions Integration

```yaml
# .github/workflows/proof-docs.yml
name: Generate Proof Documentation
on:
  push:
    paths: ['**/*.lean']

jobs:
  generate-docs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Setup Lean
        uses: leanprover/lean-action@v1
      - name: Install Proof Sketcher
        run: pip install proof-sketcher
      - name: Generate Documentation
        run: proof-sketcher batch ./src/ --output ./docs/proofs/
      - name: Deploy to GitHub Pages
        uses: peaceiris/actions-gh-pages@v3
        with:
          github_token: ${{ secrets.GITHUB_TOKEN }}
          publish_dir: ./docs/proofs/
```

### Makefile Integration

```makefile
# Makefile
.PHONY: docs clean-docs

docs:
	proof-sketcher batch ./src/ --output ./docs/proofs/ --format html
	proof-sketcher batch ./examples/ --output ./docs/examples/ --format markdown

clean-docs:
	rm -rf ./docs/proofs/ ./docs/examples/

docs-serve:
	cd docs && python -m http.server 8000
```

## Advanced Usage Patterns

### Custom Templates

```yaml
# .proof-sketcher.yaml
export:
  custom_templates:
    academic_paper:
      base: "html"
      template: "academic.html.j2"
      styles: ["academic.css"]
    
    blog_post:
      base: "markdown"
      template: "blog.md.j2"
      frontmatter: true
```

**Custom template:** `templates/academic.html.j2`
```html
<!DOCTYPE html>
<html>
<head>
    <title>{{ theorem_name }} - Mathematical Analysis</title>
    <style>
        .theorem { border-left: 4px solid #0066cc; padding-left: 1em; }
        .proof-step { margin: 1em 0; padding: 0.5em; background: #f8f9fa; }
    </style>
</head>
<body>
    <article class="theorem">
        <h1>{{ theorem_name }}</h1>
        <div class="statement">{{ statement }}</div>
        <div class="explanation">{{ introduction }}</div>
        
        {% for step in key_steps %}
        <div class="proof-step">
            <h3>Step {{ step.step_number }}: {{ step.description }}</h3>
            <p>{{ step.mathematical_content }}</p>
        </div>
        {% endfor %}
        
        <div class="conclusion">{{ conclusion }}</div>
    </article>
</body>
</html>
```

### Scripted Workflows

```python
# scripts/generate_course_materials.py
import subprocess
import yaml
from pathlib import Path

def generate_course_docs():
    """Generate documentation for all course materials."""
    
    # Load course configuration
    with open('course.yaml') as f:
        config = yaml.safe_load(f)
    
    for chapter in config['chapters']:
        chapter_dir = Path(f"chapters/{chapter['name']}")
        output_dir = Path(f"docs/{chapter['name']}")
        
        # Generate HTML for students
        subprocess.run([
            'proof-sketcher', 'batch', str(chapter_dir),
            '--output', str(output_dir / 'html'),
            '--format', 'html',
            '--template', 'student'
        ])
        
        # Generate instructor notes
        subprocess.run([
            'proof-sketcher', 'batch', str(chapter_dir),
            '--output', str(output_dir / 'instructor'),
            '--format', 'markdown',
            '--template', 'instructor',
            '--include-tactics'
        ])

if __name__ == '__main__':
    generate_course_docs()
```

### Performance Optimization

```bash
# Large repository processing
proof-sketcher batch ./mathlib/ \
    --output ./docs/ \
    --max-workers 8 \
    --cache-responses \
    --skip-animations \
    --compress-output

# Memory-constrained environment
proof-sketcher batch ./theorems/ \
    --output ./docs/ \
    --max-memory 2GB \
    --chunk-size 50 \
    --cleanup-temp
```

## Example Gallery

### Educational Examples

1. **First Steps in Proof** (`examples/tutorial/`)
   - Basic propositional logic
   - Simple arithmetic proofs
   - Introduction to tactics

2. **Undergraduate Mathematics** (`examples/undergraduate/`)
   - Linear algebra theorems
   - Calculus fundamentals
   - Abstract algebra basics

3. **Advanced Topics** (`examples/advanced/`)
   - Category theory
   - Algebraic topology
   - Real analysis

### Research Examples

1. **Formalized Papers** (`examples/papers/`)
   - Formalizations of published theorems
   - Complete proof developments
   - Bibliographic references

2. **Work in Progress** (`examples/wip/`)
   - Ongoing formalization projects
   - Experimental approaches
   - Draft theorems

### Domain-Specific Examples

1. **Computer Science** (`examples/cs/`)
   - Algorithm correctness
   - Data structure properties
   - Complexity theory

2. **Physics** (`examples/physics/`)
   - Mathematical physics
   - Quantum mechanics formalization
   - Classical mechanics

## Best Practices

### File Organization

```
project/
├── lean-packages/          # Lean dependencies
├── src/                    # Source theorems
│   ├── algebra/
│   ├── analysis/
│   └── logic/
├── docs/                   # Generated documentation
│   ├── html/
│   └── markdown/
├── examples/               # Example files
├── templates/              # Custom templates
└── .proof-sketcher.yaml   # Configuration
```

### Naming Conventions

```lean
-- Use descriptive names
theorem finite_sum_convergence : ... := by ...

-- Group related theorems
theorem ring_add_comm : ... := by ...
theorem ring_mul_comm : ... := by ...
theorem ring_distributive : ... := by ...

-- Use standard mathematical notation
theorem cauchy_schwarz_inequality : ... := by ...
theorem fundamental_theorem_calculus : ... := by ...
```

### Documentation Standards

```lean
/-- 
The Cauchy-Schwarz inequality for real inner product spaces.

This fundamental inequality relates the inner product of two vectors
to the product of their norms, providing a crucial tool in analysis.

## Mathematical Background
The inequality states that for vectors u, v in an inner product space:
|⟨u, v⟩| ≤ ∥u∥ ∥v∥

## Applications
- Optimization theory
- Probability theory (correlation coefficients)
- Functional analysis

## Related Results
- Triangle inequality
- Hölder's inequality
-/
theorem cauchy_schwarz_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : |⟨u, v⟩| ≤ ∥u∥ * ∥v∥ := by
  exact abs_inner_le_norm_mul_norm u v
```

## Troubleshooting Examples

### Common Issues

**Issue:** No theorems found in file
```bash
# Check file syntax
lean --check myfile.lean

# Verify file encoding
file --mime-encoding myfile.lean

# Test with simple theorem
echo "theorem test : True := trivial" > test.lean
proof-sketcher prove test.lean
```

**Issue:** Generation timeout
```bash
# Increase timeout
proof-sketcher prove myfile.lean --timeout 120

# Use offline mode
proof-sketcher prove myfile.lean --offline

# Process in smaller chunks
proof-sketcher batch ./src/ --chunk-size 10
```

**Issue:** Memory errors
```bash
# Limit memory usage
proof-sketcher prove myfile.lean --max-memory 1GB

# Clear cache
proof-sketcher cache clear

# Use streaming mode
proof-sketcher batch ./src/ --stream
```

For more troubleshooting information, see the [Troubleshooting Guide](troubleshooting.md).