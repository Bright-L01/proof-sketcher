# Contributing to Proof Sketcher

Thank you for your interest in contributing to Proof Sketcher! This guide will help you get started with contributing to the project.

## 🚀 Quick Start

### Development Setup

1. **Clone the repository**
   ```bash
   git clone https://github.com/Bright-L01/proof-sketcher.git
   cd proof-sketcher
   ```

2. **Set up development environment**
   ```bash
   # Create virtual environment
   python -m venv venv
   source venv/bin/activate  # On Windows: venv\Scripts\activate
   
   # Install in development mode with all dependencies
   pip install -e ".[dev]"
   ```

3. **Verify installation**
   ```bash
   # Run tests to ensure everything works
   pytest
   
   # Check code style
   black --check src/ tests/
   ruff check src/ tests/
   
   # Type checking
   mypy src/
   ```

### Prerequisites

- **Python 3.9+** (3.10+ recommended)
- **Claude Code CLI** for AI integration
- **Git** for version control
- **Node.js** (optional, for Manim MCP server)
- **LaTeX** (optional, for PDF export)

## 📋 How to Contribute

### Reporting Issues

Before creating an issue, please:

1. **Search existing issues** to avoid duplicates
2. **Use issue templates** when reporting bugs or requesting features
3. **Provide minimal reproduction cases** for bugs
4. **Include environment details** (OS, Python version, etc.)

### Suggesting Features

We welcome feature suggestions! Please:

1. **Check the roadmap** in README.md
2. **Use the feature request template**
3. **Explain the use case** and benefits
4. **Consider implementation complexity**
5. **Indicate willingness to contribute**

### Pull Requests

1. **Fork the repository**
2. **Create a feature branch** from `main`
   ```bash
   git checkout -b feature/your-feature-name
   ```
3. **Make your changes** following our guidelines
4. **Add tests** for new functionality
5. **Update documentation** if needed
6. **Submit a pull request**

#### PR Guidelines

- **One feature per PR** - keep changes focused
- **Write clear commit messages** using conventional commits
- **Include tests** for all new code
- **Maintain backwards compatibility** when possible
- **Update CHANGELOG.md** for significant changes

## 🧪 Testing

### Running Tests

```bash
# Run all tests
pytest

# Run with coverage
pytest --cov=proof_sketcher --cov-report=html

# Run specific test files
pytest tests/test_parser.py -v

# Run integration tests
pytest tests/integration/ -v

# Test with classical examples
python examples/test_classical_examples.py
```

### Writing Tests

- **Use descriptive test names**: `test_parser_handles_empty_file`
- **Test edge cases**: empty inputs, malformed data, etc.
- **Mock external dependencies**: API calls, file system, etc.
- **Aim for >90% coverage** for new code
- **Include integration tests** for complex features

### Test Structure

```
tests/
├── unit/              # Fast, isolated tests
│   ├── test_parser.py
│   ├── test_generator.py
│   └── test_exporter.py
├── integration/       # Component interaction tests
│   ├── test_end_to_end.py
│   └── test_mathlib_integration.py
└── fixtures/          # Test data and examples
    ├── lean_files/
    └── expected_outputs/
```

## 🎨 Code Style

### Python Style Guide

We follow PEP 8 with some modifications:

- **Line length**: 88 characters (Black default)
- **Quotes**: Double quotes for strings
- **Imports**: Grouped and sorted with isort
- **Type hints**: Required for all public functions
- **Docstrings**: Google style for all public APIs

### Code Formatting

```bash
# Format code
black src/ tests/

# Sort imports
isort src/ tests/

# Lint code
ruff check src/ tests/

# Type checking
mypy src/
```

### Pre-commit Hooks

We recommend using pre-commit hooks:

```bash
# Install pre-commit
pip install pre-commit

# Install hooks
pre-commit install

# Run manually
pre-commit run --all-files
```

## 🏗️ Architecture Guidelines

### Code Organization

- **Single responsibility**: Each module has one clear purpose
- **Dependency injection**: Use configuration objects
- **Error handling**: Use specific exception types
- **Logging**: Use structured logging with context
- **Testing**: Test-driven development preferred

### Module Structure

```
src/proof_sketcher/
├── __init__.py         # Package initialization
├── cli/               # Command-line interface
├── core/              # Core functionality and models
├── parser/            # Lean file parsing
├── generator/         # AI explanation generation
├── animator/          # Animation creation
└── exporter/          # Multi-format export
```

### Key Patterns

1. **Configuration-driven**: Use config objects, not globals
2. **Async-ready**: Support async/await where beneficial
3. **Resource management**: Use context managers
4. **Error recovery**: Graceful degradation when possible
5. **Performance**: Cache expensive operations

## 📝 Documentation

### Code Documentation

- **Docstrings**: All public functions and classes
- **Type hints**: Complete type annotations
- **Comments**: Explain "why", not "what"
- **Examples**: Include usage examples in docstrings

### Documentation Updates

When contributing:

1. **Update docstrings** for API changes
2. **Add examples** for new features
3. **Update README.md** for user-facing changes
4. **Add troubleshooting entries** for common issues

## 🔍 Review Process

### What We Look For

- **Correctness**: Does the code work as intended?
- **Testing**: Are there sufficient tests?
- **Documentation**: Is the code well-documented?
- **Style**: Does it follow our guidelines?
- **Performance**: Are there efficiency concerns?
- **Security**: Any security implications?

### Review Timeline

- **Initial response**: Within 2-3 days
- **Follow-up reviews**: Within 1-2 days
- **Merge decision**: Usually within 1 week

## 🌟 Areas for Contribution

### High Priority

- **Test coverage improvements** (aim for 95%+)
- **Documentation enhancements** (examples, tutorials)
- **Performance optimizations** (caching, parallel processing)
- **Error handling improvements** (better messages, recovery)

### Medium Priority

- **New export formats** (LaTeX themes, custom templates)
- **Enhanced animations** (new visual styles, transitions)
- **CLI improvements** (better help, auto-completion)
- **Configuration enhancements** (validation, schemas)

### Advanced Features

- **VSCode extension** integration
- **Real-time preview** capabilities
- **Custom animation templates**
- **Multi-language support**

## 🤝 Community

### Communication

- **GitHub Issues**: Bug reports and feature requests
- **GitHub Discussions**: Questions and general discussion
- **Pull Requests**: Code contributions and reviews

### Code of Conduct

Please note that this project is governed by our [Code of Conduct](CODE_OF_CONDUCT.md). By participating, you agree to abide by its terms.

### Recognition

Contributors are recognized in:

- **CHANGELOG.md**: For significant contributions
- **README.md**: For major features
- **GitHub**: Through contributor graphs and mentions

## 📚 Resources

### Learning Resources

- **Lean 4**: [Official Tutorial](https://leanprover.github.io/theorem_proving_in_lean4/)
- **Mathlib4**: [Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- **Manim**: [Documentation](https://docs.manim.community/)
- **Claude API**: [Documentation](https://docs.anthropic.com/)

### Development Tools

- **Claude Code CLI**: For AI integration testing
- **Lean 4**: For testing parser functionality
- **Manim**: For animation development
- **pytest**: For testing framework

## 🚀 Getting Help

### Where to Ask

1. **GitHub Issues**: Bug reports and feature requests
2. **GitHub Discussions**: General questions and ideas
3. **Code Comments**: Specific implementation questions

### What to Include

- **Environment details**: OS, Python version, dependencies
- **Minimal reproduction**: Smallest example that shows the issue
- **Expected vs actual**: What you expected vs what happened
- **Logs and errors**: Full error messages and stack traces

## 📜 License

By contributing to Proof Sketcher, you agree that your contributions will be licensed under the MIT License.

---

Thank you for contributing to Proof Sketcher! Together, we're making formal mathematics more accessible to everyone. 🎓✨