# Contributing to Proof Sketcher

Thank you for your interest in contributing to Proof Sketcher! This document provides guidelines for contributing to the project.

## ⚠️ Alpha Software Notice

This is alpha software with significant technical debt and known issues. We welcome contributions that:
- Improve code quality incrementally
- Fix bugs and security vulnerabilities
- Add test coverage
- Enhance documentation
- Implement missing features

## Code of Conduct

Please note that this project is released with a [Contributor Code of Conduct](CODE_OF_CONDUCT.md). By participating in this project you agree to abide by its terms.

## How to Contribute

### Reporting Issues

1. Check [ALPHA_STATUS.md](../ALPHA_STATUS.md) to see if your issue is already known
2. Search existing issues to avoid duplicates
3. Use the appropriate issue template
4. Provide as much detail as possible

### Submitting Pull Requests

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Make your changes following our coding standards
4. Add tests for new functionality
5. Ensure all tests pass (`pytest`)
6. Update documentation as needed
7. Commit your changes (`git commit -m 'feat: add amazing feature'`)
8. Push to your branch (`git push origin feature/amazing-feature`)
9. Open a Pull Request

### Development Setup

```bash
# Clone the repository
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher

# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install dependencies
pip install -e ".[dev,test]"

# Run tests
pytest

# Run linting
black src/ tests/
isort src/ tests/
flake8 src/ tests/
mypy src/
```

### Coding Standards

#### Python Style
- Follow PEP 8
- Use Black for formatting (line length: 88)
- Use isort for import sorting
- Add type hints for all functions
- Document all public APIs

#### Commit Messages
Follow conventional commits format:
- `feat:` - New feature
- `fix:` - Bug fix
- `docs:` - Documentation changes
- `style:` - Formatting, missing semicolons, etc.
- `refactor:` - Code restructuring
- `test:` - Adding tests
- `chore:` - Maintenance tasks

#### Clean as You Code
For alpha software, we follow "Clean as You Code" principles:
- New code must meet quality standards
- Existing code can be improved incrementally
- Focus on the files you're modifying
- Leave the codebase better than you found it

### Testing Guidelines

1. Write tests for all new functionality
2. Maintain or improve test coverage
3. Use descriptive test names
4. Test edge cases and error conditions
5. Run the full test suite before submitting

### Documentation

- Update docstrings for modified functions
- Update README.md if adding features
- Add examples for new functionality
- Keep documentation in sync with code

## Priority Areas

Given our alpha status, we especially welcome contributions in:

1. **Test Coverage** (currently 11%, target 70%)
   - Unit tests for existing functionality
   - Integration tests for CLI commands
   - Edge case testing

2. **Security Fixes** (69 known vulnerabilities)
   - Replace pickle with JSON serialization
   - Update cryptographic functions
   - Input validation improvements

3. **Core Functionality**
   - Fix empty theorem statement issues
   - Improve Lean parser reliability
   - Enhance error handling

4. **Code Quality**
   - Reduce linting violations (currently 3,625)
   - Add type hints
   - Refactor complex functions

## Review Process

1. All PRs require at least one review
2. CI checks must pass (working tests only for alpha)
3. New code must meet quality standards
4. Existing code improvements are encouraged but not required

## Release Process

1. Releases are currently alpha versions (0.0.x)
2. We use semantic versioning
3. Release notes acknowledge alpha status and limitations
4. PyPI releases are marked as pre-release

## Getting Help

- Open a discussion for questions
- Check existing documentation
- Review closed issues for solutions
- Tag maintainers for complex issues

## Recognition

Contributors will be recognized in:
- Release notes
- Contributors file
- Project documentation

Thank you for helping improve Proof Sketcher!
