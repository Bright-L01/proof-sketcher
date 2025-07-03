# 🚀 Quick Start Guide: Zero to First Proof in 5 Minutes

Get up and running with Proof Sketcher in just a few minutes. This guide takes you from installation to generating your first mathematical explanation.

## ⚡ 5-Minute Setup

### Step 1: Install Proof Sketcher (2 minutes)

**Option A: From GitHub (Recommended)**
```bash
# Clone and install
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
pip install -e .
```

**Option B: Direct install**
```bash
# Direct from GitHub
pip install git+https://github.com/Bright-L01/proof-sketcher.git
```

### Step 2: Verify Installation (30 seconds)
```bash
# Check that everything works
python -m proof_sketcher --version
# Expected output: Proof Sketcher, version 0.1.0

# See available commands
python -m proof_sketcher --help
```

### Step 3: Your First Proof (2 minutes)

**Create a simple theorem file:**
```bash
# Create your first theorem
cat > my_first_theorem.lean << 'EOF'
-- My first theorem for Proof Sketcher
import Mathlib.Data.Nat.Basic

namespace MyFirstProof

theorem add_zero (n : ℕ) : n + 0 = n := by
  simp

theorem add_comm (n m : ℕ) : n + m = m + n := by
  exact Nat.add_comm n m

end MyFirstProof
EOF
```

**Process the theorem:**
```bash
# Generate explanation
python -m proof_sketcher prove my_first_theorem.lean --format html
```

**View your results:**
```bash
# Open the generated documentation
open output/my_first_theorem.html  # macOS
# or
xdg-open output/my_first_theorem.html  # Linux
```

**🎉 Congratulations!** You've just generated your first automated mathematical explanation!

---

## 📚 What You Just Created

Your generated HTML includes:

✅ **Clear mathematical statements** in natural language  
✅ **Intuitive explanations** of what each theorem means  
✅ **Proof approaches** explaining the logical strategy  
✅ **Mathematical context** showing why theorems matter  
✅ **Beautiful formatting** with proper mathematical notation  

**Example output for `add_comm`:**
> **Commutativity of Addition**
>
> This fundamental theorem establishes that addition of natural numbers is commutative - the order of operands doesn't affect the result. For any natural numbers n and m, we have n + m = m + n.
>
> **Mathematical Significance**: This property is so fundamental that we often take it for granted, but it's actually a non-trivial result that must be proven from the basic axioms of natural numbers.

---

## 🎯 Next Steps: Explore More Features

### Try Different Output Formats

```bash
# Generate multiple formats at once
python -m proof_sketcher prove my_first_theorem.lean --format all

# This creates:
# output/my_first_theorem.html    - Web-ready documentation
# output/my_first_theorem.md      - GitHub-compatible Markdown  
# output/my_first_theorem.pdf     - Publication-quality PDF
# output/my_first_theorem.ipynb   - Interactive Jupyter notebook
```

### Use Built-in Examples

```bash
# List theorems in example files
python -m proof_sketcher list-theorems examples/classical/simple_examples.lean

# Process example files
python -m proof_sketcher prove examples/classical/group_theory.lean --format html
```

### Try Batch Processing

```bash
# Process multiple files at once
python -m proof_sketcher batch examples/ --recursive --formats html markdown
```

### Run the Interactive Demo

```bash
# Experience all features in a guided tour
python demos/live_demo_script.py --interactive
```

---

## 📖 Common Use Cases

### For Students: Understanding Proofs

```bash
# Create student-friendly explanations
python -m proof_sketcher prove course_theorems.lean \
  --format html \
  --output student_docs/
```

### For Educators: Course Material

```bash
# Generate course documentation
python -m proof_sketcher batch course_files/ \
  --recursive \
  --formats html pdf \
  --output course_website/
```

### For Researchers: Documentation

```bash
# Document research results
python -m proof_sketcher prove research_theorems.lean \
  --format all \
  --animate \
  --output paper_supplements/
```

---

## 🛠️ Configuration & Customization

### Basic Configuration

Create `.proof-sketcher.yaml` in your project:

```yaml
# Basic configuration
generator:
  style: mathematical  # or 'detailed', 'eli5'
  
export:
  output_dir: docs/
  html_theme: modern
  
cache:
  enabled: true
  ttl_hours: 24
```

### Advanced Options

```bash
# Verbose output for debugging
python -m proof_sketcher prove file.lean --verbose

# Offline mode (no AI, template-based explanations)
python -m proof_sketcher prove file.lean --offline

# Custom output directory
python -m proof_sketcher prove file.lean --output custom_docs/

# Specific theorem only
python -m proof_sketcher prove file.lean --theorem specific_theorem_name
```

---

## 🔧 Troubleshooting

### Common Issues & Solutions

**❌ "No theorems found"**
```bash
# Check file syntax
lean your_file.lean

# Use verbose mode for details
python -m proof_sketcher list-theorems your_file.lean --verbose
```

**❌ "Command not found"**
```bash
# Ensure proper installation
pip install -e . --force-reinstall

# Check Python path
which python
python -c "import proof_sketcher; print('OK')"
```

**❌ "Processing failed"**
```bash
# Try offline mode
python -m proof_sketcher prove file.lean --offline

# Check for syntax errors
python -m proof_sketcher prove file.lean --verbose
```

**❌ "Import errors"**
```bash
# For Lean files with mathlib dependencies
# Ensure you have Lake project setup correctly
lake update
lake build
```

### Getting Help

```bash
# Built-in help
python -m proof_sketcher --help
python -m proof_sketcher prove --help

# Check version and system info
python -m proof_sketcher system-info
```

**Still stuck?** 
- 📖 See [full documentation](README.md)
- 🐛 [Report issues](https://github.com/Bright-L01/proof-sketcher/issues)
- 💬 [Ask questions](https://github.com/Bright-L01/proof-sketcher/discussions)

---

## 🎯 Real Examples to Try

### 1. Basic Arithmetic
```lean
import Mathlib.Data.Nat.Basic

theorem my_theorem (n : ℕ) : n + 0 = n := by simp
```

### 2. Group Theory
```lean
import Mathlib.Algebra.Group.Defs

theorem identity_unique (G : Type*) [Group G] (e : G) 
  (h : ∀ a : G, e * a = a ∧ a * e = a) : e = 1 := by
  have : e = e * 1 := by rw [mul_one]
  rw [this, h]
```

### 3. Real Analysis
```lean
import Mathlib.Data.Real.Basic

theorem squeeze_example (f g h : ℝ → ℝ) (a L : ℝ)
  (h1 : ∀ x, f x ≤ g x) (h2 : ∀ x, g x ≤ h x) : 
  -- Proof implementation
  sorry
```

**Process any of these:**
```bash
python -m proof_sketcher prove your_example.lean --format html
```

---

## 🚀 Advanced Quick Start

### For Power Users (1 minute setup)

```bash
# One-liner setup and demo
git clone https://github.com/Bright-L01/proof-sketcher.git && \
cd proof-sketcher && \
pip install -e . && \
python -m proof_sketcher prove examples/classical/simple_examples.lean --format all && \
echo "🎉 Proof Sketcher is ready! Check the output/ directory."
```

### For Development

```bash
# Clone with development setup
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher

# Install with development dependencies
pip install -e ".[dev]"

# Run tests to verify
pytest

# Run the full demo
python demos/live_demo_script.py --quick
```

---

## 🎓 Learning Path

**Level 1: Basics (You're here!)**
- ✅ Install and verify
- ✅ Generate first explanation  
- ✅ Try different output formats

**Level 2: Regular Use**
- 📚 Read the [full documentation](README.md)
- 🎬 Watch the [example gallery](demos/EXAMPLE_GALLERY.md)
- ⚙️ Set up configuration for your workflow

**Level 3: Advanced**
- 🔧 Contribute to the project
- 🎯 Integrate with your research workflow
- 🌟 Share your use cases with the community

**Level 4: Expert**
- 🚀 Develop custom exporters
- 🤝 Contribute to core functionality
- 📖 Help others in the community

---

## 🌟 Share Your Success

**Got Proof Sketcher working?** We'd love to hear about it!

- ⭐ Star the project on [GitHub](https://github.com/Bright-L01/proof-sketcher)
- 💬 Share your experience in [Discussions](https://github.com/Bright-L01/proof-sketcher/discussions)
- 🐦 Tweet about it with #ProofSketcher
- 📧 Send feedback to brightliu@college.harvard.edu

---

## 📞 Support

**Need help?**
- 📖 [Full Documentation](README.md)
- 🎯 [Example Gallery](demos/EXAMPLE_GALLERY.md)
- 🔧 [Troubleshooting Guide](docs/TROUBLESHOOTING.md)
- 🐛 [GitHub Issues](https://github.com/Bright-L01/proof-sketcher/issues)
- 💬 [Community Discussions](https://github.com/Bright-L01/proof-sketcher/discussions)

**Ready to transform your mathematical documentation?**

🚀 **You're all set! Happy proving!** 🎓✨

---

*Made with ❤️ for the mathematical community*