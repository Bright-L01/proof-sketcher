# Proof Sketcher Documentation

Welcome to the Proof Sketcher documentation. This tool transforms Lean 4 theorems into natural language explanations with beautiful visualizations.

## ⚠️ Alpha Software Warning

**This is alpha software with significant limitations. Please review [ALPHA_STATUS.md](../ALPHA_STATUS.md) before use.**

## Quick Links

- [Getting Started](getting-started.md) - Installation and first steps
- [User Guide](user-guide/index.md) - Comprehensive usage guide
- [CLI Reference](cli-reference.md) - Complete command reference
- [API Documentation](api/index.md) - Python API reference
- [Contributing](../CONTRIBUTING.md) - How to contribute

## Overview

Proof Sketcher bridges the gap between formal mathematical proofs in Lean 4 and human-readable explanations. It's designed to make formal mathematics more accessible to students, researchers, and anyone interested in understanding mathematical proofs.

### Key Features

- **Lean 4 Parser**: Extract theorem information from Lean files
- **Natural Language Generation**: Convert formal proofs to readable explanations
- **Multiple Export Formats**: HTML, Markdown, and more
- **Offline Mode**: Works without internet connection
- **CLI Interface**: Easy-to-use command-line tools

### Current Limitations (Alpha)

- Test coverage: 11%
- Security vulnerabilities: 69
- Limited theorem parsing capabilities
- No AI integration (offline mode only)
- Basic template-based explanations

## Installation

```bash
pip install proof-sketcher
```

For development installation:

```bash
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
pip install -e ".[dev,test]"
```

## Quick Start

1. List theorems in a Lean file:

   ```bash
   proof-sketcher list-theorems examples/simple.lean
   ```

2. Generate explanation for a theorem:

   ```bash
   proof-sketcher prove examples/simple.lean --theorem add_comm
   ```

3. Export to different formats:

   ```bash
   proof-sketcher prove file.lean --format html --output proof.html
   ```

## Architecture

```
proof-sketcher/
├── parser/      # Lean 4 parsing
├── generator/   # Explanation generation
├── exporter/    # Output formatting
└── cli/         # Command-line interface
```

## Roadmap

1. **Phase 1** (Current): Basic functionality
2. **Phase 2**: Improve test coverage to 70%
3. **Phase 3**: Security vulnerability fixes
4. **Phase 4**: AI integration
5. **Phase 5**: Production readiness

## Support

- [GitHub Issues](https://github.com/Bright-L01/proof-sketcher/issues)
- [Discussions](https://github.com/Bright-L01/proof-sketcher/discussions)
- [Contributing Guide](../CONTRIBUTING.md)

## License

MIT License - see [LICENSE](../LICENSE) for details.
