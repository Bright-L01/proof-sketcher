# 📐 Proof Sketcher

[![Python](https://img.shields.io/badge/python-3.10+-blue.svg)](https://www.python.org/downloads/)
[![Lean 4](https://img.shields.io/badge/Lean-4.0+-purple.svg)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![MathJax](https://img.shields.io/badge/MathJax-4.0-green.svg)](https://www.mathjax.org/)
[![Status: ALPHA](https://img.shields.io/badge/Status-ALPHA%20SOFTWARE-red.svg)](https://github.com/brightlikethelight/proof-sketcher)

# ⚠️ **ALPHA SOFTWARE WARNING** ⚠️

**THIS IS EXPERIMENTAL SOFTWARE WITH LIMITED FUNCTIONALITY**

**NOT SUITABLE FOR PRODUCTION USE**

---

## 🎯 **What It Does**

Proof Sketcher is an experimental tool that generates natural language explanations of Lean 4 theorems. This is alpha software with basic functionality only.

### ✨ **Current Working Features**

🔍 **Basic Parsing** - Extract simple theorems and lemmas from Lean 4 files
📝 **Template Generation** - Basic structured explanations using offline templates
📊 **HTML Export** - Simple HTML output with MathJax 4.0
📝 **Markdown Export** - Basic Markdown output
📚 **CLI Interface** - Command-line interface for basic operations

### ❌ **Known Limitations**

- **No AI Integration** - Template-based explanations only
- **No Animations** - Static output only
- **No PDF Export** - HTML and Markdown only
- **No LSP Integration** - Basic regex parsing only
- **Limited Test Coverage** - Many tests are broken
- **Security Issues** - Not suitable for production
- **No Documentation** - Minimal documentation available

---

## 🚀 **Current Status: ALPHA SOFTWARE**

### ✅ **Actually Working Features**

- **Simple Lean Parser**: Basic theorem extraction from .lean files
- **Offline Generation**: Template-based explanations (no API required)
- **HTML Export**: Simple HTML with MathJax 4.0 rendering
- **Markdown Export**: Basic Markdown output
- **CLI Commands**: `prove`, `list-theorems`, `version`, `formats`
- **Batch Processing**: Process multiple files (basic)

### 🚧 **Future Development (Not Current)**

- **AI Integration**: Claude API for enhanced explanations
- **Animations**: Manim integration for proof visualization
- **PDF Export**: LaTeX-quality typesetting
- **Doc-gen4 Integration**: Mathlib documentation enhancement
- **LSP Support**: Full semantic analysis
- **Test Coverage**: Comprehensive test suite
- **Security**: Production-ready security practices

---

## 📦 **Quick Start (Alpha)**

### Installation

```bash
# Clone and install
git clone https://github.com/brightlikethelight/proof-sketcher.git
cd proof-sketcher
pip install -e .
```

### Verify Installation

```bash
# Test basic functionality
python -m proof_sketcher --help
python -m proof_sketcher version
```

### Basic Usage

```bash
# List theorems in a file
python -m proof_sketcher list-theorems examples/classical/simple_examples.lean

# Generate explanation for a theorem
python -m proof_sketcher prove examples/classical/simple_examples.lean --theorem add_zero

# Export to markdown
python -m proof_sketcher prove examples/classical/simple_examples.lean --format markdown

# Show supported formats
python -m proof_sketcher formats
```

### ⚠️ **Alpha Limitations**

- **No Python API** - CLI only in alpha version
- **Limited Parsing** - Simple theorems only
- **No AI Features** - Template-based only
- **Basic Error Handling** - May crash on complex files
- **No Configuration** - Uses default settings only

---

## 🏗️ **Architecture (Alpha)**

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Simple Lean   │───▶│  Offline        │───▶│  Basic HTML/MD  │
│    Parser       │    │  Generator      │    │   Output        │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         ▼                       ▼                       ▼
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Regex-based   │    │   Hard-coded    │    │   Static Files  │
│   Extraction    │    │   Templates     │    │   (HTML/MD)     │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

### Alpha Components

- **🔍 Simple Parser**: Basic regex-based theorem extraction
- **📝 Offline Generator**: Template-based explanations (no AI)
- **🎨 Simple Exporters**: Basic HTML and Markdown output
- **📚 CLI Interface**: Command-line tools for basic operations

### Missing Components (Future)

- **Advanced Parser**: LSP-based semantic analysis
- **AI Generator**: Claude API integration
- **Rich Exporters**: PDF, Jupyter, animations
- **Web Interface**: Interactive documentation

---

## 🎓 **Use Cases**

### **For Researchers**

- **Publication Ready**: Generate theorem explanations for academic papers
- **Documentation**: Create accessible descriptions of formal proofs
- **Education**: Bridge formal and informal mathematics

### **For Educators**

- **Course Materials**: Explain formal proofs to students
- **Interactive Learning**: Convert Lean theorems to readable content
- **Assessment**: Document proof understanding and verification

### **For Lean Community**

- **Mathlib Documentation**: Enhanced theorem explanations
- **Knowledge Sharing**: Make formal proofs more accessible
- **Onboarding**: Help newcomers understand existing proofs

---

## 🔧 **Development**

### Project Structure

```
proof-sketcher/
├── src/proof_sketcher/
│   ├── parser/          # Lean 4 AST extraction
│   ├── generator/       # Explanation generation
│   ├── exporter/        # Multi-format output
│   └── cli.py          # Command-line interface
├── tests/              # Comprehensive test suite
├── examples/           # Sample Lean files and outputs
└── docs/              # Documentation and guides
```

### Contributing

```bash
# Development setup
git clone https://github.com/brightlikethelight/proof-sketcher.git
cd proof-sketcher
pip install -e ".[dev]"

# Run tests
pytest --cov=proof_sketcher

# Format code
black src/ tests/
ruff check src/ tests/
```

---

## 📊 **Technical Specifications**

| Feature | Status | Technology |
|---------|--------|------------|
| **Lean 4 Parsing** | ✅ Complete | Python subprocess, AST analysis |
| **Template Generation** | ✅ Working | Jinja2, structured templates |
| **HTML Export** | ✅ Production | MathJax 4.0, responsive CSS |
| **Mathematical Rendering** | ✅ Professional | LaTeX notation, symbol support |
| **Batch Processing** | ✅ Efficient | Parallel processing, progress tracking |
| **AI Integration** | 🚧 Planned | Claude API, contextual enhancement |
| **Animation Support** | 🚧 Research | Manim integration, dynamic visualization |

---

## 🌟 **Why Proof Sketcher?**

### **Unique Position**

- **First of its kind**: Dedicated Lean 4 to natural language tool
- **Modern Technology**: Built with latest web standards and rendering
- **Research Foundation**: Grounded in formal verification best practices
- **Extensible Design**: Modular architecture for future enhancements

### **Technical Innovation**

- **AST-Level Analysis**: Deep understanding of theorem structure
- **Template-Based Generation**: Consistent, reliable explanations
- **Professional Output**: Publication-quality mathematical rendering
- **Scalable Processing**: Handle large Lean projects efficiently

---

## 📚 **Documentation**

- **[API Reference](docs/api.md)** - Complete function documentation
- **[User Guide](docs/guide.md)** - Step-by-step tutorials
- **[Architecture](docs/architecture.md)** - Technical design details
- **[Contributing](docs/contributing.md)** - Development guidelines
- **[Examples](examples/)** - Sample inputs and outputs

---

## 🤝 **Community & Support**

- **GitHub Issues**: Bug reports and feature requests
- **Discussions**: Community Q&A and ideas
- **Contributing**: Welcome contributions from the Lean community
- **Academic Collaboration**: Open to research partnerships

---

## 📜 **License**

MIT License - See [LICENSE](LICENSE) for details.

---

<p align="center">
  <strong>Making formal mathematics accessible, one proof at a time.</strong> 🎓
</p>

<p align="center">
  <a href="mailto:brightliu@college.harvard.edu">Contact</a> •
  <a href="https://github.com/brightlikethelight/proof-sketcher/issues">Issues</a> •
  <a href="https://github.com/brightlikethelight/proof-sketcher/discussions">Discussions</a>
</p>
