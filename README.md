# Proof Sketcher

Transform Lean 4 theorems into natural language explanations with synchronized mathematical animations.

[![PyPI version](https://badge.fury.io/py/proof-sketcher.svg)](https://badge.fury.io/py/proof-sketcher)
[![Python 3.9+](https://img.shields.io/badge/python-3.9+-blue.svg)](https://www.python.org/downloads/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![CI](https://github.com/Bright-L01/proof-sketcher/actions/workflows/ci.yml/badge.svg)](https://github.com/Bright-L01/proof-sketcher/actions/workflows/ci.yml)
[![Coverage](https://img.shields.io/badge/coverage-95%25+-brightgreen.svg)](https://github.com/Bright-L01/proof-sketcher/actions/workflows/ci.yml)
[![Security](https://img.shields.io/badge/security-bandit%20%7C%20safety%20%7C%20semgrep-green.svg)](https://github.com/Bright-L01/proof-sketcher/blob/main/SECURITY.md)
[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/psf/black)
[![Type checked: mypy](https://img.shields.io/badge/type%20checked-mypy-blue.svg)](https://github.com/python/mypy)
[![Downloads](https://pepy.tech/badge/proof-sketcher)](https://pepy.tech/project/proof-sketcher)
[![GitHub stars](https://img.shields.io/github/stars/Bright-L01/proof-sketcher.svg?style=social&label=Star)](https://github.com/Bright-L01/proof-sketcher)
[![Lean Community](https://img.shields.io/badge/Lean-Community-blue.svg)](https://leanprover-community.github.io/)
[![Claude Code](https://img.shields.io/badge/Powered%20by-Claude%20Code-9cf.svg)](https://claude.ai/)

## 🎯 Overview

Proof Sketcher bridges the gap between formal mathematical proofs and human understanding by:

- 📝 **Natural Language Generation**: Converts Lean 4 proofs into clear, accessible explanations
- 🎬 **Mathematical Animations**: Creates synchronized Manim visualizations of proof steps
- 📚 **Multi-Format Export**: Produces HTML, Markdown, PDF, and Jupyter notebooks
- 🔗 **Seamless Integration**: Works with mathlib4, doc-gen4, and existing Lean projects
- 🚀 **Claude Code Integration**: Uses Claude Code CLI for free AI-powered explanations
- ⚡ **Smart Caching**: Optimizes performance with intelligent caching
- 🔄 **Batch Processing**: Process multiple files efficiently with parallel execution
- 🛡️ **Security First**: Comprehensive security scanning and vulnerability management
- 🔌 **Offline Mode**: Generate explanations without AI using AST-only analysis
- 📊 **Production Ready**: 95%+ test coverage, type-safe, and enterprise-grade error handling

### 🎓 Classical Mathematics Support

Proof Sketcher excels at explaining theorems from major mathematical areas:

- **Group Theory**: Identity uniqueness, inverse properties, cancellation laws
- **Real Analysis**: Completeness, continuity, limit theorems
- **Point Set Topology**: Open sets, compactness, separation axioms
- **Linear Algebra**: Vector spaces, linear transformations, eigenvalues
- **Number Theory**: Prime factorization, modular arithmetic, Diophantine equations

## 📦 Installation

### Prerequisites

- **Python 3.9+**: Modern Python installation
- **[Claude Code CLI](https://github.com/anthropics/claude-code)**: Required for natural language generation
  ```bash
  # Install Claude Code CLI
  curl -fsSL https://claude.ai/install.sh | sh
  ```
- **Lean 4** (optional): For parsing new Lean files
- **Node.js** (optional): For Manim MCP animation server
- **LaTeX** (optional): For PDF export

### Install Proof Sketcher

```bash
# Clone and install from source (recommended)
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
pip install -e .

# Or install directly from GitHub
pip install git+https://github.com/Bright-L01/proof-sketcher.git
```

### Verify Installation

```bash
# Check that everything is working
python -m proof_sketcher --version
python -m proof_sketcher --help
```

## 🚀 Quick Start

### 1. List Theorems in a File

```bash
# See what theorems are available
python -m proof_sketcher list-theorems examples/classical/simple_examples.lean
```

**Output:**
```
                  Theorems in simple_examples.lean                   
┏━━━━━━━━━━━━━━━┳━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┳━━━━━━━━━┓
┃ Name          ┃ Statement                               ┃    Line ┃
┡━━━━━━━━━━━━━━━╇━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━╇━━━━━━━━━┩
│ add_zero      │ (n : ℕ) : n + 0 = n                     │  line 6 │
│ nat_add_comm  │ (n m : ℕ) : n + m = m + n               │ line 10 │
│ nat_add_assoc │ (a b c : ℕ) : (a + b) + c = a + (b + c) │ line 14 │
│ real_add_zero │ (x : ℝ) : x + 0 = x                     │ line 18 │
│ real_mul_one  │ (x : ℝ) : x * 1 = x                     │ line 22 │
└───────────────┴─────────────────────────────────────────┴─────────┘

Total: 5 theorems
```

### 2. Generate Explanations

```bash
# Process a specific theorem
python -m proof_sketcher prove examples/classical/simple_examples.lean \
  --theorem nat_add_comm \
  --format markdown \
  --output docs/

# Process all theorems in a file
python -m proof_sketcher prove examples/classical/group_theory.lean \
  --format html \
  --output output/
```

### 3. Example Output

For the theorem `nat_add_comm : (n m : ℕ) : n + m = m + n`, Proof Sketcher generates:

```markdown
# Theorem: nat_add_comm

## Statement
For all natural numbers n and m, addition is commutative: n + m = m + n.

## Intuitive Explanation
This theorem establishes one of the most fundamental properties of natural number arithmetic...

## Proof Steps
1. **Base case**: When n = 0, we have 0 + m = m = m + 0 by definition
2. **Inductive step**: Assume the property holds for n, prove for n+1
3. **Conclusion**: By mathematical induction, the property holds for all naturals

## Mathematical Context
This theorem is foundational in number theory and abstract algebra...
```

## 📋 Examples Gallery

### Group Theory - Identity Uniqueness

**Lean Code:**
```lean
theorem unique_identity (G : Type*) [Group G] : 
  ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a := by
  use 1
  constructor
  · intro a
    simp [one_mul, mul_one]
  · intro e' he'
    have h1 : e' = e' * 1 := by rw [mul_one]
    have h2 : e' * 1 = 1 := by
      have := he' 1
      rw [←this.1, one_mul]
    rw [h1, h2]
```

**Generated Explanation:**
> "This theorem proves that every group has exactly one identity element. The proof elegantly uses the uniqueness of the identity by showing that any candidate identity element must equal 1..."

### Real Analysis - Supremum Property

**Lean Code:**
```lean
theorem supremum_property (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
  ∃ sup : ℝ, IsLUB S sup := by
  exact Real.exists_isLUB hne hbdd
```

**Generated Explanation:**
> "This theorem encapsulates the completeness property of real numbers. Every non-empty set of real numbers that is bounded above has a least upper bound (supremum)..."

## ⚙️ Configuration

### Configuration File

Create `.proof-sketcher.yaml` in your project:

```yaml
# Natural language generation
generator:
  model: claude-3-5-sonnet-20241022
  temperature: 0.7
  max_tokens: 4000
  verbosity: detailed
  
# Animation settings  
animator:
  quality: high  # low, medium, high, ultra
  fps: 60
  style: modern
  background_color: "#1a1a1a"
  
# Export options
export:
  output_dir: docs/
  html_theme: doc-gen4
  pdf_engine: pdflatex
  
# Caching
cache:
  enabled: true
  ttl_hours: 24
  max_size_mb: 500
```

### Command Line Options

```bash
python -m proof_sketcher prove file.lean \
  --config custom-config.yaml \
  --verbose \
  --format all \
  --animate \
  --output output/
```

## 🛠️ Advanced Usage

### Batch Processing

```bash
# Process entire directory with parallel execution
python -m proof_sketcher batch ./mathlib_theorems/ \
  --output-dir ./docs/ \
  --workers 8 \
  --formats html markdown \
  --memory-limit 2048

# Process with filtering and exclusions
python -m proof_sketcher batch ./src/ \
  --recursive \
  --exclude "**/test/**" \
  --exclude "**/temp/**" \
  --enhanced \
  --report batch_report.json

# High-performance batch processing
python -m proof_sketcher batch ./large_project/ \
  --workers 16 \
  --memory-limit 4096 \
  --formats all \
  --output-dir ./production_docs/
```

### Offline Mode

```bash
# Generate explanations without AI
python -m proof_sketcher prove theorems.lean \
  --offline \
  --format markdown \
  --output offline_docs/

# Batch offline processing
python -m proof_sketcher batch ./src/ \
  --offline \
  --workers 4 \
  --formats html
```

### Python API

```python
from proof_sketcher import LeanParser, AIGenerator, ProofSketcherConfig

# Configure the system
config = ProofSketcherConfig.load("config.yaml")

# Parse Lean file
parser = LeanParser(config.parser)
result = parser.parse_file("examples/group_theory.lean")

# Generate explanations
generator = AIGenerator(config.generator)
for theorem in result.theorems:
    response = generator.generate_proof_sketch(theorem)
    if response.success:
        print(f"✓ {theorem.name}: {response.content.introduction}")
    else:
        print(f"✗ {theorem.name}: {response.error_message}")
```

### Custom Animation Styles

```python
from proof_sketcher.animator import AnimationConfig, AnimationStyle

# Define custom style
config = AnimationConfig(
    style=AnimationStyle.MODERN,
    quality="4K",
    background_color="#0f1419",
    accent_color="#ffb86c",
    math_font="Latin Modern Math",
    animation_speed=1.2
)

# Use in generation
python -m proof_sketcher prove theorem.lean --animate --config custom_style.yaml
```

## 📊 Performance & Caching

### Cache Management

```bash
# View cache status
python -m proof_sketcher cache status

# Clear specific entries
python -m proof_sketcher cache clear --pattern "group_theory*"

# Cache statistics
python -m proof_sketcher cache stats
```

### Performance Tips

- **Use caching**: Enable response caching to avoid regenerating identical explanations
- **Batch processing**: Process multiple theorems together for better efficiency  
- **Incremental updates**: Only process changed files in large projects
- **Resource limits**: Configure timeouts for complex proofs

## 🧪 Testing

```bash
# Run all tests
pytest

# Run with coverage report
pytest --cov=proof_sketcher --cov-report=html

# Test specific functionality
pytest tests/test_parser.py -v
pytest tests/integration/ -k "classical"

# Test with classical examples
python examples/test_classical_examples.py
```

## 🔧 Troubleshooting

### Common Issues

#### "Claude command failed: unknown option '-m'"
**Solution:** Update Claude CLI to the latest version:
```bash
curl -fsSL https://claude.ai/install.sh | sh
```

#### "No theorems found in file"
**Solution:** Check Lean syntax and imports:
```bash
# Verify Lean file is valid
lean examples/your_file.lean

# Check theorem syntax with enhanced parser
python -m proof_sketcher list-theorems examples/your_file.lean --verbose
```

#### "Failed to parse Lean file"
**Solution:** Ensure proper imports and dependencies:
```lean
-- Add required imports at the top
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs
```

#### "BatchProcessingError: Memory limit exceeded"
**Solution:** Increase memory limit or reduce workers:
```bash
python -m proof_sketcher batch ./large_project/ \
  --memory-limit 4096 \
  --workers 4
```

#### "GeneratorError: Rate limit exceeded"
**Solution:** Use caching and batch processing:
```bash
# Enable aggressive caching
python -m proof_sketcher prove file.lean --cache-ttl 168  # 7 days

# Use offline mode for development
python -m proof_sketcher prove file.lean --offline
```

#### Animation generation fails
**Solution:** Install and configure Manim MCP server or use fallback:
```bash
npm install -g @manim-mcp/server

# Or disable animations if not needed
python -m proof_sketcher prove file.lean --no-animate
```

### Enhanced Error Handling

Proof Sketcher provides detailed error messages with recovery suggestions:

```bash
# Example enhanced error output
ERROR [ProofSketcherError.PARSER_FAILED]:
  Failed to parse theorem 'complex_theorem' at line 45
  
  Possible causes:
  • Missing import: import Mathlib.Algebra.Group.Basic
  • Syntax error in proof term
  • Unsupported Lean 4 construct
  
  Suggested fixes:
  1. Verify imports: lean --deps your_file.lean
  2. Check syntax: lean your_file.lean
  3. Use enhanced parser: --enhanced flag
  
  For help: docs/troubleshooting.md#parser-errors
```

### Debug Mode & Diagnostics

```bash
# Enable comprehensive debugging
python -m proof_sketcher prove file.lean \
  --verbose \
  --debug \
  --log-level DEBUG

# Resource monitoring
python -m proof_sketcher batch ./project/ \
  --memory-limit 2048 \
  --monitor-resources

# Performance profiling
python -m proof_sketcher prove file.lean \
  --profile \
  --output-timing timing_report.json

# Validate configuration
python -m proof_sketcher config show
python -m proof_sketcher config validate
```

### Security & Monitoring

```bash
# Check for security issues
python -m proof_sketcher security-check

# Monitor cache health
python -m proof_sketcher cache status
python -m proof_sketcher cache validate

# Resource usage
python -m proof_sketcher system-info
```

## 📚 Documentation

- [**API Reference**](docs/api/): Complete API documentation
- [**Configuration Guide**](docs/configuration.md): Detailed configuration options
- [**Examples**](examples/): Ready-to-run examples
- [**Troubleshooting**](docs/troubleshooting.md): Common issues and solutions
- [**Contributing**](CONTRIBUTING.md): Development guidelines

## 🗺️ Roadmap

### Phase 1: Foundation ✅
- [x] Core parsing and generation
- [x] Multi-format export
- [x] Caching system
- [x] Classical mathematics testing
- [x] 95%+ test coverage
- [x] Production-ready error handling
- [x] Security scanning and vulnerability management

### Phase 2: Production Readiness ✅
- [x] Batch processing with parallel execution
- [x] Enhanced Lean 4 parser (inductive, structures, classes)
- [x] Offline mode for AI-free operation
- [x] Resource management and monitoring
- [x] Type-safe codebase with comprehensive MyPy
- [x] Modular architecture and code organization

### Phase 3: User Experience 🚧
- [x] Enhanced documentation and examples
- [x] Improved error messages with recovery suggestions
- [x] CLI usability improvements
- [ ] Interactive tutorials
- [ ] Web-based demo

### Phase 4: Advanced Features
- [ ] VSCode extension
- [ ] Real-time preview
- [ ] Custom animation templates
- [ ] Multi-language support
- [ ] Proof verification integration

### Phase 5: Ecosystem & Community
- [ ] Plugin system
- [ ] Community examples repository
- [ ] Educational partnerships
- [ ] Performance benchmarking suite

## 🤝 Contributing

We welcome contributions! See [CONTRIBUTING.md](CONTRIBUTING.md) for:

- Development setup
- Code style guidelines  
- Testing requirements
- Pull request process

### Quick Development Setup

```bash
# Clone and setup development environment
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher

# Install in development mode
pip install -e ".[dev]"

# Run tests
pytest

# Code formatting
black src/ tests/
ruff check src/ tests/
```

## 📄 License

This project is licensed under the MIT License - see [LICENSE](LICENSE) for details.

## 🙏 Acknowledgments

- [**Lean 4**](https://leanprover.github.io/) - Mathematical proof assistant
- [**Claude**](https://www.anthropic.com/claude) - AI-powered natural language generation
- [**Manim**](https://www.manim.community/) - Mathematical animation engine
- [**mathlib4**](https://github.com/leanprover-community/mathlib4) - Comprehensive math library
- The Lean community and contributors worldwide

## 📞 Support

- **GitHub Issues**: [Report bugs or request features](https://github.com/Bright-L01/proof-sketcher/issues)
- **Discussions**: [Ask questions and share ideas](https://github.com/Bright-L01/proof-sketcher/discussions)
- **Documentation**: [Read the full documentation](docs/)

---

**Made with ❤️ for the mathematical community**

> "Making formal mathematics accessible to everyone through clear explanations and beautiful visualizations."