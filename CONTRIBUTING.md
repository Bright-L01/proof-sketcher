# Contributing to Proof-Sketcher

Thank you for your interest in contributing to Proof-Sketcher! This document provides guidelines for contributing to this alpha-stage project.

## Current State

**⚠️ IMPORTANT**: Proof-Sketcher is alpha software with significant architectural issues:

- Cannot handle concurrent users (major blocker)
- Template-based content generation (not AI)
- LSP integration is non-functional
- Low test coverage (11%)

Major refactoring is planned. Please coordinate before starting significant work.

## Development Setup

### Prerequisites

- Python 3.10+
- Git
- Lean 4 (optional, for testing with real files)

### Setting Up Development Environment

```bash
# Clone the repository
git clone https://github.com/yourusername/proof-sketcher.git
cd proof-sketcher

# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install in development mode with test dependencies
pip install -e ".[test,dev]"

# Install pre-commit hooks
pre-commit install

# Run tests to verify setup
pytest
```

### Code Style

We use:

- **Ruff** for linting and formatting
- **mypy** for type checking
- **Black** compatible formatting
- **Pre-commit** hooks for consistency

Run checks locally:

```bash
# Format code
ruff format .

# Lint code
ruff check . --fix

# Type check
mypy src/

# Run all pre-commit hooks
pre-commit run --all-files
```

## How to Contribute

### Reporting Issues

Before creating an issue:

1. Check existing issues (including closed ones)
2. Verify the issue exists in the latest version
3. Include minimal reproduction steps

### Priority Areas

We especially need help with:

1. **Concurrent User Support** (Critical)
   - Current code fails with multiple users
   - Requires architectural changes

2. **Test Coverage**
   - Current: 11%, Target: 80%
   - Focus on unit tests for core functionality

3. **Educational Content**
   - Improve template quality
   - Add theorem-specific explanations

4. **Documentation**
   - API documentation
   - Architecture documentation
   - User guides

### Pull Request Process

1. **Before Starting Work**
   - Check issues and discussions
   - For major changes, open an issue first
   - Coordinate to avoid duplicate work

2. **Development**
   - Create a feature branch from `main`
   - Write tests for new functionality
   - Ensure all tests pass
   - Update documentation

3. **Submitting PR**
   - Clear description of changes
   - Link related issues
   - Ensure CI passes
   - Be patient - we're a small team

### Commit Messages

Follow conventional commits:

```
feat: add support for new theorem type
fix: resolve concurrent user crash
docs: update API documentation
test: add parser unit tests
refactor: simplify explanation generator
```

## Testing

### Running Tests

```bash
# Run all tests
pytest

# Run with coverage
pytest --cov=proof_sketcher

# Run specific test file
pytest tests/unit/test_parser.py

# Run integration tests only
pytest tests/integration/
```

### Writing Tests

- Place unit tests in `tests/unit/`
- Place integration tests in `tests/integration/`
- Use descriptive test names
- Test edge cases and error conditions

Example test:

```python
def test_parser_handles_empty_file():
    """Parser should return empty result for empty file."""
    parser = SimpleLeanParser()
    result = parser.parse_file("empty.lean")
    assert result.success
    assert len(result.theorems) == 0
```

## Architecture Overview

```
src/proof_sketcher/
├── parser/          # Lean file parsing (use simple_parser.py)
├── generator/       # Explanation generation (template-based)
├── exporter/        # HTML/Markdown export
├── cli/            # Command-line interface
└── core/           # Shared utilities
```

### Key Design Decisions

1. **Parser**: Simple regex parser works; LSP client doesn't
2. **Generator**: Template-based, not AI (despite class names)
3. **Exporter**: Supports HTML and Markdown
4. **CLI**: Click-based interface

## Areas Needing Major Work

### 1. Concurrent User Support (Highest Priority)

- Current implementation uses global state
- No connection pooling or session management
- Requires fundamental redesign

### 2. Content Generation

- Replace generic templates with theorem-specific content
- Consider actual AI integration or improved templates
- Add mathematical accuracy

### 3. Testing Infrastructure

- Increase coverage from 11% to 80%
- Add performance benchmarks
- Add integration tests with real Lean files

## Questions?

- Open a discussion in GitHub Discussions
- Check existing issues and PRs
- Review the architecture documentation

## Code of Conduct

Please note that this project is released with a Contributor Code of Conduct. By participating in this project you agree to abide by its terms.

## License

By contributing, you agree that your contributions will be licensed under the MIT License.
