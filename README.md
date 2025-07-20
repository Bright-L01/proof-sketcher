# Proof-Sketcher (Alpha)

**⚠️ IMPORTANT: This is alpha software under active development. It is not ready for production use.**

## What is Proof-Sketcher?

Proof-Sketcher is an educational tool that generates natural language explanations for Lean 4 theorems. It parses Lean files and creates explanations at multiple educational levels to help students understand formal proofs.

## Current Status: Alpha (v0.1.0)

### ✅ What Works

- **Basic Lean parsing**: Extracts theorems from `.lean` files
- **Template-based explanations**: Generates explanations at 4 educational levels
- **Multiple export formats**: HTML and Markdown output
- **Security**: XSS protection and path sanitization implemented
- **Resource limits**: Memory and timeout protection

### ❌ Known Limitations

- **No concurrent user support**: Single-user only (critical limitation)
- **Template-based content**: Not AI-generated despite package names
- **LSP integration non-functional**: Use simple parser instead
- **Limited educational value**: Generic templates need improvement
- **Low test coverage**: Currently 11% (target: 80%)

### 🚧 Under Development

- Concurrent user support (required for classroom use)
- Improved educational content quality
- Real semantic analysis of proofs
- Integration with doc-gen4
- Comprehensive test suite

## Installation

### Requirements

- Python 3.10+
- Lean 4 (optional, for `.lean` file validation)

### Quick Start

```bash
# Clone the repository
git clone https://github.com/yourusername/proof-sketcher.git
cd proof-sketcher

# Install in development mode
pip install -e .

# Run basic example
proof-sketcher prove examples/basic.lean
```

## Usage

### Basic Usage

```bash
# Generate explanation for a single theorem
proof-sketcher prove theorem.lean

# Specify educational level (intuitive, conceptual, bridging, formal)
proof-sketcher prove theorem.lean --educational-level formal

# Export to HTML
proof-sketcher prove theorem.lean --format html

# Process multiple theorems
proof-sketcher batch process theorems/
```

### Educational Levels

1. **Intuitive**: Plain language explanation for beginners
2. **Conceptual**: Introduction of mathematical concepts
3. **Bridging**: Connection between informal and formal reasoning
4. **Formal**: Complete formal proof explanation

## Architecture

```
proof-sketcher/
├── src/proof_sketcher/
│   ├── parser/          # Lean file parsing
│   ├── generator/       # Explanation generation
│   ├── exporter/        # HTML/Markdown export
│   └── cli/            # Command-line interface
└── tests/              # Test suite
```

## Contributing

We welcome contributions! However, please be aware:

1. This is alpha software with significant architectural changes planned
2. Major refactoring is needed for concurrent user support
3. The codebase will change substantially before v1.0

See [CONTRIBUTING.md](CONTRIBUTING.md) for development setup.

## Honest Limitations

1. **Performance**: Cannot handle multiple concurrent users
2. **Content Quality**: Template-based explanations are generic
3. **Integration**: No working integration with other Lean tools
4. **Stability**: Alpha software with breaking changes expected

## Roadmap to Beta

1. **v0.2.0**: Fix concurrent user support (critical)
2. **v0.3.0**: Improve educational content quality
3. **v0.4.0**: Add real doc-gen4 integration
4. **v0.5.0**: Achieve 80% test coverage
5. **v0.6.0-beta**: First beta release

## License

MIT License - See [LICENSE](LICENSE) file

## Acknowledgments

- Lean 4 community for the excellent proof assistant
- Early alpha testers for valuable feedback

---

**Note**: This README reflects the actual current state of the software. Features marked as "planned" or "under development" are not yet implemented. Please set expectations accordingly.
