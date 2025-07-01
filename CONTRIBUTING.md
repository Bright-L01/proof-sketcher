# Contributing to Proof Sketcher

We welcome contributions to Proof Sketcher! This guide will help you get started with contributing to the project.

## > Ways to Contribute

- **Bug Reports**: Found a bug? Let us know!
- **Feature Requests**: Have an idea for improvement? Share it!
- **Code Contributions**: Fix bugs, add features, improve documentation
- **Documentation**: Help improve our guides and examples
- **Testing**: Write tests, test on different platforms
- **Examples**: Create examples for different mathematical areas

## =€ Quick Start for Contributors

### 1. Fork and Clone

```bash
# Fork the repository on GitHub, then clone your fork
git clone https://github.com/YOUR_USERNAME/proof-sketcher.git
cd proof-sketcher

# Add upstream remote
git remote add upstream https://github.com/Bright-L01/proof-sketcher.git
```

### 2. Set Up Development Environment

```bash
# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install in development mode with all dependencies
pip install -e ".[dev]"

# Install pre-commit hooks
pre-commit install
```

### 3. Verify Setup

```bash
# Run tests to ensure everything works
pytest

# Check code formatting
black --check src/ tests/
ruff check src/ tests/

# Verify CLI works
python -m proof_sketcher --version
```

## =Ý Development Workflow

### Branch Strategy

- **main**: Production-ready code
- **develop**: Integration branch for new features
- **feature/**: New features (`feature/add-latex-export`)
- **fix/**: Bug fixes (`fix/parsing-unicode`)
- **docs/**: Documentation improvements

### Making Changes

1. **Create a feature branch**:
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes**:
   - Write clean, documented code
   - Follow existing code style
   - Add tests for new functionality

3. **Test your changes**:
   ```bash
   # Run full test suite
   pytest
   
   # Run specific tests
   pytest tests/test_parser.py -v
   
   # Check coverage
   pytest --cov=proof_sketcher --cov-report=html
   ```

4. **Format code**:
   ```bash
   # Auto-format code
   black src/ tests/
   
   # Fix import order
   isort src/ tests/
   
   # Check linting
   ruff check src/ tests/
   ```

5. **Commit changes**:
   ```bash
   git add .
   git commit -m "feat: add LaTeX export functionality"
   ```

6. **Push and create PR**:
   ```bash
   git push origin feature/your-feature-name
   # Create pull request on GitHub
   ```

## >ê Testing Guidelines

### Running Tests

```bash
# Run all tests
pytest

# Run with coverage
pytest --cov=proof_sketcher --cov-report=term-missing

# Run specific test file
pytest tests/test_parser.py

# Run tests matching pattern
pytest -k "test_parse"

# Run with verbose output
pytest -v

# Run integration tests
pytest tests/integration/
```

### Writing Tests

#### Unit Tests

```python
# tests/test_my_feature.py
import pytest
from proof_sketcher.my_module import MyClass

class TestMyClass:
    """Test suite for MyClass."""
    
    @pytest.fixture
    def sample_data(self):
        """Create sample test data."""
        return {"key": "value"}
    
    def test_my_method_success(self, sample_data):
        """Test successful operation."""
        instance = MyClass()
        result = instance.my_method(sample_data)
        
        assert result is not None
        assert result.success is True
    
    def test_my_method_error_handling(self):
        """Test error handling."""
        instance = MyClass()
        
        with pytest.raises(ValueError):
            instance.my_method(None)
```

#### Integration Tests

```python
# tests/integration/test_end_to_end.py
import tempfile
from pathlib import Path
import pytest

from proof_sketcher import LeanParser, AIGenerator

class TestEndToEnd:
    """End-to-end integration tests."""
    
    def test_parse_and_generate_pipeline(self, sample_lean_file):
        """Test complete pipeline from parsing to generation."""
        # Parse Lean file
        parser = LeanParser()
        result = parser.parse_file(sample_lean_file)
        
        assert len(result.theorems) > 0
        
        # Generate explanations (mock Claude for testing)
        with patch('subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Generated explanation"
            )
            
            generator = AIGenerator()
            response = generator.generate_proof_sketch(result.theorems[0])
            
            assert response.success
```

### Test Coverage Requirements

- **Minimum coverage**: 95% for new code
- **Critical modules**: 98%+ coverage required
- **Integration tests**: Cover main user workflows
- **Edge cases**: Test error conditions and boundary cases

### Running Coverage

```bash
# Generate coverage report
pytest --cov=proof_sketcher --cov-report=html

# View report
open htmlcov/index.html

# Check specific module coverage
pytest --cov=proof_sketcher.parser --cov-report=term-missing
```

## =Ú Code Style Guide

### Python Code Style

We follow [PEP 8](https://pep8.org/) with some specific conventions:

#### Formatting

```python
# Use Black for automatic formatting
black src/ tests/

# Line length: 88 characters (Black default)
# String quotes: Double quotes preferred
# Import sorting: isort
```

#### Naming Conventions

```python
# Variables and functions: snake_case
def parse_lean_file(file_path: Path) -> ParseResult:
    theorem_count = 0
    return ParseResult(theorems=theorems)

# Classes: PascalCase
class TheoremParser:
    def __init__(self):
        self.config = ParserConfig()

# Constants: UPPER_SNAKE_CASE
DEFAULT_TIMEOUT = 30
MAX_FILE_SIZE = 1024 * 1024

# Private methods: leading underscore
def _extract_theorem_info(self, text: str) -> TheoremInfo:
    pass
```

#### Type Hints

```python
from typing import List, Optional, Union, Dict, Any
from pathlib import Path

def process_theorems(
    theorems: List[TheoremInfo],
    config: Optional[GenerationConfig] = None,
    output_dir: Path = Path("output")
) -> Dict[str, GenerationResponse]:
    """Process multiple theorems with optional configuration.
    
    Args:
        theorems: List of theorems to process
        config: Optional generation configuration
        output_dir: Directory for output files
        
    Returns:
        Dictionary mapping theorem names to responses
        
    Raises:
        ParserError: If theorem parsing fails
        GeneratorError: If generation fails
    """
    pass
```

#### Documentation

```python
class TheoremProcessor:
    """Processes Lean theorems into natural language explanations.
    
    This class handles the complete pipeline from parsing Lean files
    to generating natural language explanations and exporting to
    various formats.
    
    Attributes:
        config: Configuration for processing
        parser: Lean file parser instance
        generator: Natural language generator
        
    Example:
        >>> processor = TheoremProcessor()
        >>> result = processor.process_file("theorems.lean")
        >>> print(f"Processed {len(result.theorems)} theorems")
    """
    
    def __init__(self, config: Optional[ProcessorConfig] = None):
        """Initialize the processor.
        
        Args:
            config: Optional configuration. Uses defaults if None.
        """
        self.config = config or ProcessorConfig()
    
    def process_file(self, file_path: Path) -> ProcessingResult:
        """Process a single Lean file.
        
        Args:
            file_path: Path to the Lean file to process
            
        Returns:
            ProcessingResult containing theorems and any errors
            
        Raises:
            FileNotFoundError: If the file doesn't exist
            ParserError: If parsing fails
        """
        pass
```

### Error Handling

```python
# Custom exceptions
class ProofSketcherError(Exception):
    """Base exception for Proof Sketcher."""
    pass

class ParserError(ProofSketcherError):
    """Raised when Lean file parsing fails."""
    pass

class GeneratorError(ProofSketcherError):
    """Raised when explanation generation fails."""
    pass

# Error handling patterns
def parse_theorem(text: str) -> TheoremInfo:
    """Parse theorem from text."""
    try:
        # Parsing logic here
        return TheoremInfo(...)
    except ValueError as e:
        raise ParserError(f"Invalid theorem syntax: {e}") from e
    except Exception as e:
        logger.error(f"Unexpected error parsing theorem: {e}")
        raise ParserError(f"Failed to parse theorem: {e}") from e
```

### Logging

```python
import logging

# Use module-level loggers
logger = logging.getLogger(__name__)

def process_file(file_path: Path) -> ProcessingResult:
    """Process a Lean file."""
    logger.info(f"Processing file: {file_path}")
    
    try:
        result = parse_file(file_path)
        logger.debug(f"Found {len(result.theorems)} theorems")
        return result
    except Exception as e:
        logger.error(f"Failed to process {file_path}: {e}")
        raise
```

## <× Architecture Guidelines

### Module Structure

```
src/proof_sketcher/
   __init__.py          # Public API exports
   cli.py               # Command line interface
   core/                # Core utilities
      config.py        # Configuration management
      exceptions.py    # Custom exceptions
      utils.py         # Utility functions
   parser/              # Lean file parsing
      lean_parser.py   # Main parser
      models.py        # Data models
   generator/           # Natural language generation
      ai_generator.py  # AI-powered generation
      models.py        # Generation models
      prompts.py       # Prompt templates
   animator/            # Mathematical animations
      manim_mcp.py     # Manim MCP client
      models.py        # Animation models
   exporter/            # Output format exporters
       html.py          # HTML export
       markdown.py      # Markdown export
       pdf.py           # PDF export
```

### Design Principles

1. **Separation of Concerns**: Each module has a single responsibility
2. **Dependency Injection**: Use configuration objects for dependencies
3. **Error Handling**: Graceful error handling with informative messages
4. **Testability**: Write testable code with clear interfaces
5. **Extensibility**: Design for easy addition of new features

### Adding New Features

#### 1. New Export Format

```python
# src/proof_sketcher/exporter/my_format.py
from pathlib import Path
from typing import Dict, Any

from .base import BaseExporter
from ..generator.models import ProofSketch

class MyFormatExporter(BaseExporter):
    """Export proof sketches to my custom format."""
    
    def __init__(self, config: ExportConfig):
        super().__init__(config)
        self.format_name = "my_format"
    
    def export_sketch(
        self, 
        sketch: ProofSketch, 
        output_path: Path
    ) -> ExportResult:
        """Export a single proof sketch."""
        try:
            # Format-specific export logic
            content = self._format_sketch(sketch)
            
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(content)
            
            return ExportResult(
                success=True,
                output_path=output_path,
                format=self.format_name
            )
        except Exception as e:
            return ExportResult(
                success=False,
                error=str(e),
                format=self.format_name
            )
    
    def _format_sketch(self, sketch: ProofSketch) -> str:
        """Convert sketch to my format."""
        # Implementation details
        pass
```

#### 2. New Parser Features

```python
# src/proof_sketcher/parser/enhanced_parser.py
from typing import List, Optional
from pathlib import Path

from .lean_parser import LeanParser
from .models import TheoremInfo, ParseResult

class EnhancedLeanParser(LeanParser):
    """Enhanced parser with additional features."""
    
    def __init__(self, config: ParserConfig):
        super().__init__(config)
        self.extract_proofs = config.extract_proofs
    
    def parse_file(self, file_path: Path) -> ParseResult:
        """Parse with enhanced features."""
        # Call parent parser
        result = super().parse_file(file_path)
        
        # Add enhancements
        if self.extract_proofs:
            result = self._enhance_with_proofs(result)
        
        return result
    
    def _enhance_with_proofs(self, result: ParseResult) -> ParseResult:
        """Add proof extraction."""
        # Enhancement logic
        pass
```

## =Ö Documentation Guidelines

### Code Documentation

- **Docstrings**: Use Google-style docstrings
- **Type hints**: Required for all public APIs
- **Comments**: Explain why, not what
- **Examples**: Include usage examples in docstrings

### User Documentation

- **Clear structure**: Use headings and sections
- **Code examples**: Show working examples
- **Screenshots**: Visual aids for CLI output
- **Troubleshooting**: Common issues and solutions

### Documentation Updates

When adding features, update:

1. **API Documentation**: For code changes
2. **User Guide**: For new functionality
3. **README**: For major features
4. **CHANGELOG**: For all changes

## = Pull Request Process

### Before Submitting

- [ ] Code follows style guidelines
- [ ] Tests added for new functionality
- [ ] All tests pass
- [ ] Documentation updated
- [ ] CHANGELOG updated

### PR Template

```markdown
## Description
Brief description of changes

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Documentation update
- [ ] Performance improvement
- [ ] Refactoring

## Testing
- [ ] Added unit tests
- [ ] Added integration tests
- [ ] Manual testing performed

## Documentation
- [ ] Updated user documentation
- [ ] Updated API documentation
- [ ] Updated README (if needed)

## Checklist
- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] Tests pass locally
- [ ] Documentation updated
```

### Review Process

1. **Automated checks**: CI/CD pipeline runs tests
2. **Code review**: Maintainer reviews code
3. **Testing**: Feature testing in different environments
4. **Documentation**: Check documentation completeness
5. **Merge**: After approval and all checks pass

## =Ê Performance Guidelines

### Optimization Principles

1. **Profile first**: Measure before optimizing
2. **Cache wisely**: Use caching for expensive operations
3. **Async when appropriate**: Use async for I/O operations
4. **Resource limits**: Respect memory and CPU limits

### Performance Testing

```python
import time
import pytest
from proof_sketcher.parser import LeanParser

class TestPerformance:
    """Performance tests for critical paths."""
    
    def test_parser_performance(self, large_lean_file):
        """Test parser performance on large files."""
        parser = LeanParser()
        
        start_time = time.time()
        result = parser.parse_file(large_lean_file)
        end_time = time.time()
        
        # Performance assertions
        assert (end_time - start_time) < 5.0  # Under 5 seconds
        assert len(result.theorems) > 0
    
    @pytest.mark.performance
    def test_generation_throughput(self, sample_theorems):
        """Test generation throughput."""
        # Implementation
        pass
```

## = Bug Reports

### Good Bug Report Template

```markdown
**Describe the bug**
Clear description of what the bug is.

**To Reproduce**
Steps to reproduce:
1. Go to '...'
2. Click on '....'
3. Scroll down to '....'
4. See error

**Expected behavior**
What you expected to happen.

**Actual behavior**
What actually happened.

**Environment**
- OS: [e.g. Ubuntu 20.04]
- Python version: [e.g. 3.9.7]
- Proof Sketcher version: [e.g. 0.1.0]
- Claude CLI version: [e.g. 1.2.3]

**Additional context**
Any other context about the problem.

**Files**
Minimal Lean file that reproduces the issue.
```

## <¯ Feature Requests

### Feature Request Template

```markdown
**Is your feature request related to a problem?**
Clear description of what the problem is.

**Describe the solution you'd like**
Clear description of what you want to happen.

**Describe alternatives you've considered**
Alternative solutions you've considered.

**Additional context**
Any other context or screenshots.

**Implementation ideas**
If you have ideas about implementation.
```

## <Æ Recognition

### Contributors

All contributors are recognized in:
- CONTRIBUTORS.md file
- Release notes
- GitHub contributors section

### Hall of Fame

Special recognition for:
- Major feature contributors
- Long-term maintainers
- Outstanding bug reporters
- Documentation improvements

## =Þ Getting Help

### Development Questions

- **GitHub Discussions**: For general questions
- **GitHub Issues**: For bugs and feature requests
- **Code Review**: During pull request process

### Communication

- Be respectful and constructive
- Follow the code of conduct
- Help others when you can
- Share knowledge and learnings

## =Ä License

By contributing, you agree that your contributions will be licensed under the MIT License.

---

Thank you for contributing to Proof Sketcher! <‰