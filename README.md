# Proof Sketcher

Transform Lean 4 theorems into natural language explanations with synchronized mathematical animations.

[![CI](https://github.com/Bright-L01/proof-sketcher/actions/workflows/ci.yml/badge.svg)](https://github.com/Bright-L01/proof-sketcher/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Python 3.9+](https://img.shields.io/badge/python-3.9+-blue.svg)](https://www.python.org/downloads/)
[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/psf/black)

## 🎯 Overview

Proof Sketcher bridges the gap between formal mathematical proofs and human understanding by:

- 📝 **Natural Language Generation**: Converts Lean 4 proofs into clear, accessible explanations
- 🎬 **Mathematical Animations**: Creates synchronized Manim visualizations of proof steps
- 📚 **Multi-Format Export**: Produces HTML, Markdown, PDF, and Jupyter notebooks
- 🔗 **Seamless Integration**: Works with mathlib4, doc-gen4, and existing Lean projects
- 🚀 **Claude Code Integration**: Uses Claude Code CLI for free AI-powered explanations
- ⚡ **Smart Caching**: Optimizes performance with intelligent caching

## 📦 Installation

### Prerequisites

- Python 3.9 or higher
- [Claude Code CLI](https://github.com/anthropics/claude-code) (required for natural language generation)

  ```bash
  # Install Claude Code CLI
  npm install -g claude-code
  ```

- Lean 4 (optional but recommended for full functionality)
- Lake build tool (comes with Lean 4)
- Node.js (optional, for Manim MCP server)
- LaTeX distribution (optional, for PDF export)

### Install from PyPI

```bash
pip install proof-sketcher
```

### Install from Source

```bash
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
pip install -e .
```

## 🚀 Quick Start

### Basic Usage

```bash
# Process a single Lean file
proof-sketcher prove example.lean

# Generate with animations
proof-sketcher prove example.lean --animate

# Export to specific format
proof-sketcher prove example.lean --format pdf --output docs/
```

### Python API

```python
from proof_sketcher import LeanParser, ClaudeGenerator, ManimAnimator

# Parse Lean file
parser = LeanParser()
result = parser.parse_file("example.lean")

# Generate explanation
generator = ClaudeGenerator()
for theorem in result.theorems:
    sketch = generator.generate_proof_sketch(theorem)
    print(f"Theorem: {theorem.name}")
    print(f"Explanation: {sketch.explanation}")
    
    # Generate animation (async)
    import asyncio
    animator = ManimAnimator()
    animation_response = asyncio.run(animator.animate_proof(sketch))
    if animation_response.success:
        print(f"Animation saved to: {animation_response.video_path}")
```

## ⚙️ Configuration

Proof Sketcher supports flexible configuration through multiple sources:

### Configuration File

Create `.proof-sketcher.yaml` in your project:

```yaml
# Natural language generation
generator:
  model: claude-3-5-sonnet-20241022
  temperature: 0.7
  max_tokens: 4000
  
# Animation settings  
animator:
  quality: high  # low, medium, high, ultra
  fps: 60
  style: modern
  
# Export options
export:
  output_dir: docs/
  html_theme: doc-gen4
  pdf_engine: pdflatex
```

### Environment Variables

```bash
export PROOF_SKETCHER_DEBUG=true
export PROOF_SKETCHER_GENERATOR_MODEL=claude-3-opus
export PROOF_SKETCHER_ANIMATOR_QUALITY=4K
```

### Command Line Options

```bash
proof-sketcher prove example.lean \
  --config custom-config.yaml \
  --verbose \
  --format all
```

## 📋 Features

### Natural Language Generation

- **Intelligent Explanations**: Claude AI understands mathematical concepts and proof techniques
- **Multiple Styles**: Choose between concise, detailed, or tutorial explanations
- **Context Awareness**: Incorporates theorem dependencies and mathematical background
- **LaTeX Support**: Preserves mathematical notation in explanations

### Animation System

- **Manim Integration**: High-quality mathematical animations via MCP protocol
- **Synchronized Steps**: Animations follow proof progression
- **Custom Styles**: Classic, modern, minimal, or educational presentation
- **Smart Timing**: Automatic duration calculation based on proof complexity

### Export Formats

#### HTML

- Compatible with doc-gen4 themes
- Interactive proof steps
- Embedded videos
- Syntax highlighting

#### Markdown

- GitHub-flavored markdown
- Collapsible proof sections
- KaTeX/MathJax support
- Cross-references

#### PDF

- Professional LaTeX formatting
- Custom document classes
- Bibliography support
- Hyperlinked references

#### Jupyter

- Interactive notebooks
- Code cells for exploration
- Rich media output
- Educational widgets

## 🛠️ Advanced Usage

### Processing Multiple Files

```bash
# Process directory recursively
proof-sketcher prove src/ --recursive

# Process specific theorems
proof-sketcher prove MyFile.lean --theorem "add_comm" --theorem "mul_assoc"

# Batch processing with pattern
proof-sketcher prove "src/**/*_basic.lean" --format html
```

### Custom Prompts

Create custom prompt templates in `prompts/`:

```python
# prompts/my_style.py
CONCISE_PROOF = """
Explain {theorem_name} in one paragraph for experts.
Focus on the key insight.
"""
```

### Animation Customization

```python
from proof_sketcher.animator import AnimationConfig, AnimationStyle, AnimationQuality

config = AnimationConfig(
    quality=AnimationQuality.ULTRA,
    fps=60,
    style=AnimationStyle.MODERN,
    background_color="#1a1a1a",
    math_font="Computer Modern",
    text_font="Arial",
    accent_color="#3498DB"
)
```

### Caching Strategy

```bash
# View cache status
proof-sketcher cache status

# Clear all cache (with confirmation)
proof-sketcher cache clear

# Clear cache without confirmation
proof-sketcher cache clear --force

# List cached items
proof-sketcher cache list

# Search for specific cached items
proof-sketcher cache list "add_comm"
```

## 📊 Performance

- **Parallel Processing**: Utilize multiple CPU cores for batch operations
- **Streaming Output**: See results as they're generated
- **Incremental Updates**: Only process changed theorems
- **Resource Limits**: Configurable timeouts and memory limits

## 🧪 Testing

```bash
# Run all tests
pytest

# Run with coverage
pytest --cov=proof_sketcher

# Run specific test suite
pytest tests/integration/

# Run with verbose output
pytest -v
```

## 🤝 Contributing

We welcome contributions! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for:

- Development setup
- Code style guidelines
- Pull request process
- Issue reporting

## 📚 Documentation

- [API Documentation](docs/api.md)
- [Configuration Guide](docs/configuration.md)
- [Examples](examples/)
- [Troubleshooting](docs/troubleshooting.md)

## 🗺️ Roadmap

- [ ] VSCode extension
- [ ] Real-time preview
- [ ] Custom animation templates
- [ ] Multi-language support
- [ ] Proof verification integration
- [ ] Collaborative features

## 📄 License

This project is licensed under the MIT License - see [LICENSE](LICENSE) for details.

## 🙏 Acknowledgments

- [Lean 4](https://leanprover.github.io/) mathematical proof assistant
- [Claude](https://www.anthropic.com/claude) by Anthropic
- [Manim](https://www.manim.community/) mathematical animation engine
- The Lean community and mathlib contributors

## 📮 Contact

- GitHub Issues: [Report bugs or request features](https://github.com/Bright-L01/proof-sketcher/issues)
- Discussions: [Join the conversation](https://github.com/Bright-L01/proof-sketcher/discussions)

---

Made with ❤️ by the Proof Sketcher team
