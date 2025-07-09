# Proof Sketcher

**⚠️ ALPHA SOFTWARE - EARLY DEVELOPMENT STAGE ⚠️**

An experimental tool for generating natural language explanations of Lean 4 theorems.

## ⚠️ Current Status: Development Phase

**This software is in early alpha development.** Many features are incomplete or experimental. See [Known Issues](#-known-issues) before using.

### What Currently Works ✅

- ✅ **CLI Interface**: Functional command-line interface
- ✅ **Basic Processing**: Can process Lean files and extract basic theorem information
- ✅ **Multi-format Export**: Generates HTML, Markdown, and Jupyter notebook outputs
- ✅ **Offline Mode**: Template-based explanation generation (no AI required)
- ✅ **Project Structure**: Well-organized codebase with modular design

### What Doesn't Work Yet ❌

- ❌ **AI Integration**: Claude API integration not fully functional
- ❌ **Lean Parsing**: Limited theorem extraction (often produces empty statements)
- ❌ **Animations**: Manim integration incomplete
- ❌ **Content Quality**: Generates generic template content, not theorem-specific explanations
- ❌ **Production Ready**: Multiple security and quality issues (see [Production Readiness](#-production-readiness))

## 🚀 Quick Start (Alpha Testing)

### Prerequisites

- Python 3.10+
- Lean 4 with Elan (optional - basic functionality works without)

### Installation

```bash
# Clone the repository
git clone https://github.com/yourusername/proof-sketcher
cd proof-sketcher

# Install in development mode
pip install -e .
```

### Basic Usage

```bash
# Create a simple test file
echo 'theorem test : 1 = 1 := rfl' > test.lean

# Generate documentation (offline mode)
python -m proof_sketcher prove test.lean --offline --format markdown

# Check output
ls output/
```

**Expected Output**: Basic HTML/Markdown files with template content (not theorem-specific content yet).

## 📋 Current Capabilities

### Working Features

1. **Command-Line Interface**
   ```bash
   python -m proof_sketcher --help
   python -m proof_sketcher prove file.lean --offline
   python -m proof_sketcher batch directory/ --offline
   ```

2. **File Processing**
   - Reads Lean files
   - Attempts basic theorem extraction
   - Generates structured output files

3. **Export Formats**
   - HTML with CSS styling
   - Markdown with LaTeX math
   - Jupyter notebooks (basic)

4. **Offline Mode**
   - Works without external API dependencies
   - Generates template-based explanations
   - Suitable for testing and development

### Experimental Features

- **Batch Processing**: Can process multiple files
- **Caching System**: Basic caching implementation
- **Configuration**: YAML-based configuration support

## ⚠️ Known Issues

### Critical Issues
- **Security Vulnerabilities**: 69 security issues identified (6 HIGH severity)
- **Empty Content**: Theorem statements often empty in output
- **Build Failures**: Lean extractor fails to build properly
- **Generic Output**: Explanations are template-based, not theorem-specific

### Code Quality Issues
- 3,625 linting violations
- 11% test coverage
- Multiple test modules broken
- Inconsistent formatting

### Limitations
- No real AI integration yet
- Limited Lean 4 parsing capabilities
- Animations not functional
- Performance issues (30+ seconds for simple theorems)

## 🛠️ Development Setup

### For Contributors

```bash
# Clone and setup development environment
git clone https://github.com/yourusername/proof-sketcher
cd proof-sketcher

# Install development dependencies
pip install -e ".[dev]"

# Run tests (many currently broken)
pytest

# Check code quality
flake8 src/proof_sketcher/
black --check src/proof_sketcher/
```

### Testing

```bash
# Run working tests only
pytest tests/test_core_utils.py tests/unit/test_coverage_boost.py

# Generate coverage report
pytest --cov=src/proof_sketcher --cov-report=html
```

**Current Test Status**: 29/33 tests passing, 11% coverage

## 📊 Production Readiness

**Status: NOT PRODUCTION READY**

| Component | Status | Issues |
|-----------|--------|---------|
| Security | ❌ Critical | 69 vulnerabilities |
| Code Quality | ❌ Poor | 3,625 violations |
| Test Coverage | ❌ Low | 11% coverage |
| Core Functionality | ⚠️ Limited | Basic parsing only |
| Documentation | ⚠️ Partial | This document |

**Estimated time to production readiness**: 4-6 weeks of focused development.

## 🔧 Configuration

Create `.proof-sketcher.yaml` in your project root:

```yaml
# Basic configuration
generation:
  offline_mode: true  # Recommended for current version
  timeout_seconds: 60

export:
  formats: ["html", "markdown"]
  output_dir: "output"
  
# Development settings
debug: true
verbose_logging: true
```

## 🤝 Contributing

**We welcome contributions!** This project needs help in several areas:

### High Priority Areas
1. **Security Fixes**: Address 69 security vulnerabilities
2. **Core Functionality**: Improve Lean theorem parsing
3. **Test Coverage**: Expand from 11% to 70%+
4. **Code Quality**: Fix 3,625 linting violations

### How to Contribute

1. Check the [issues page](https://github.com/yourusername/proof-sketcher/issues)
2. Focus on items labeled `good-first-issue` or `help-wanted`
3. Read `CONTRIBUTING.md` for guidelines
4. Submit pull requests with tests

### Development Priorities

1. **Fix security vulnerabilities** (especially pickle usage, XSS issues)
2. **Implement proper Lean parsing** (currently produces empty statements)
3. **Improve test coverage** (fix broken test modules)
4. **Code quality improvements** (formatting, linting)

## 📖 Documentation

### Available Documentation
- [Production Readiness Assessment](PRODUCTION_READINESS_ASSESSMENT.md)
- [Testing Milestone Report](TESTING_MILESTONE_REPORT.md)
- Basic API documentation (auto-generated)

### Missing Documentation
- User guide (in development)
- API reference (needs completion)
- Deployment guide (not ready yet)

## 🐛 Troubleshooting

### Common Issues

**"Empty theorem statements in output"**
- Known issue with current parser
- Working on improved Lean integration

**"Build failed" or "Lean extractor errors"**
- Lean extractor build is currently broken
- System falls back to basic text parsing

**"Security warnings"**
- Multiple known security issues
- Use only in development environments
- Do not deploy to production

### Getting Help

1. Check [existing issues](https://github.com/yourusername/proof-sketcher/issues)
2. Create a new issue with:
   - System information
   - Full error messages
   - Minimal reproduction example

## 📄 License

MIT License - see [LICENSE](LICENSE) file.

## ⚠️ Disclaimer

**This is alpha software under active development.** 

- **Not suitable for production use**
- **Contains known security vulnerabilities**
- **Core functionality is limited**
- **API may change significantly**

Use at your own risk and only in development environments.

---

**Last Updated**: 2025-07-08  
**Version**: 0.1.0-alpha  
**Development Status**: Alpha - Major features incomplete