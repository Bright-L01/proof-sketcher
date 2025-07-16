# 📐 Proof Sketcher

[![Python](https://img.shields.io/badge/python-3.10+-blue.svg)](https://www.python.org/downloads/)
[![Lean 4](https://img.shields.io/badge/Lean-4.0+-purple.svg)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![MathJax](https://img.shields.io/badge/MathJax-4.0-green.svg)](https://www.mathjax.org/)
[![Status: MVP](https://img.shields.io/badge/Status-Functional%20MVP-orange.svg)](https://github.com/Bright-L01/proof-sketcher)

**Transform formal proofs into accessible explanations** - Making Lean 4 theorems understandable through natural language and beautiful mathematical rendering.

---

## 🎯 **What It Does**

Proof Sketcher bridges the gap between formal verification and human understanding by automatically generating natural language explanations of Lean 4 theorems. Built for researchers, educators, and anyone working with formal mathematics.

### ✨ **Key Features**

🔍 **Smart Parsing** - Extract theorems and lemmas from Lean 4 files with full AST analysis
📝 **Natural Language Generation** - Template-based explanations with AI integration roadmap
📊 **Modern Export Formats** - HTML with MathJax 4.0, Markdown, and batch processing
🎨 **Beautiful Rendering** - Mathematical notation with professional typesetting
📚 **Batch Processing** - Handle entire Lean projects with auto-generated indices

---

## 🚀 **Current Status: Functional MVP**

### ✅ **Working Features**

- **Lean 4 Parser**: Complete AST extraction from theorem definitions
- **Template Generation**: Structured explanations with mathematical context
- **Modern HTML Export**: Professional output with MathJax 4.0 rendering
- **Batch Processing**: Handle multiple files with organized output
- **Mathematical Notation**: Beautiful rendering of Lean expressions
- **Auto-Indexing**: Generated table of contents and navigation

### 🚧 **Roadmap Features**

- **AI-Powered Explanations**: Claude integration for contextual insights
- **Interactive Animations**: Dynamic proof visualization with Manim
- **PDF Export**: LaTeX-quality typesetting for publications
- **Doc-gen4 Integration**: Seamless mathlib4 documentation workflow

---

## 📦 **Quick Start**

### Installation

```bash
# Clone and install
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
pip install -e .
```

### Verify Installation

```bash
# Test the complete pipeline
python test_mvp_pipeline.py
```

### Basic Usage

```python
from proof_sketcher.parser import LeanParser
from proof_sketcher.exporter import HTMLExporter

# Parse Lean file
parser = LeanParser()
theorems = parser.parse_file("my_theorems.lean")

# Generate explanations
exporter = HTMLExporter()
exporter.export_batch(theorems, output_dir="docs/")
```

### CLI Interface

```bash
# Process single file
proof-sketcher explain my_file.lean --output html

# Batch process project
proof-sketcher batch src/ --format html --with-index

# Generate documentation site
proof-sketcher docs src/ --output docs/ --with-nav
```

---

## 🏗️ **Architecture**

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Lean 4 AST   │───▶│  Template-Based │───▶│  Modern HTML    │
│    Parser       │    │   Generator     │    │   with MathJax  │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         ▼                       ▼                       ▼
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│  Theorem AST    │    │   Explanation   │    │  Professional   │
│   Extraction    │    │   Templates     │    │  Documentation  │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

### Core Components

- **🔍 Parser Module**: Lean 4 file analysis and AST extraction
- **📝 Generator Module**: Template-based explanation synthesis
- **🎨 Exporter Module**: Multi-format output with professional styling
- **📚 Documentation Engine**: Batch processing with organized navigation

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
git clone https://github.com/Bright-L01/proof-sketcher.git
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
  <a href="https://github.com/Bright-L01/proof-sketcher/issues">Issues</a> •
  <a href="https://github.com/Bright-L01/proof-sketcher/discussions">Discussions</a>
</p>
