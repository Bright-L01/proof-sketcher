# Development Guide

This guide covers the development setup and practices for Proof Sketcher.

## Development Setup

### 1. Clone the Repository

```bash
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
```

### 2. Create Virtual Environment

```bash
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
```

### 3. Install Development Dependencies

```bash
pip install -e ".[dev]"
pre-commit install
```

## Project Structure

```
proof-sketcher/
├── src/proof_sketcher/     # Main package
│   ├── parser/            # Lean file parsing
│   ├── generator/         # Natural language generation
│   ├── animator/          # Animation generation
│   ├── exporter/          # Multi-format export
│   └── cli.py            # Command-line interface
├── tests/                 # Test suite
├── examples/              # Example Lean files
├── templates/             # Export templates
└── docs/                  # Documentation
```

## Testing

### Run All Tests

```bash
pytest
```

### Run Specific Test Categories

```bash
# Unit tests only
pytest -m unit

# Integration tests
pytest -m integration

# Test with coverage
pytest --cov=proof_sketcher --cov-report=html
```

### Test Individual Modules

```bash
# Test parser
pytest tests/test_parser.py -v

# Test generator
pytest tests/test_generator.py -v

# Test CLI
pytest tests/test_cli.py -v
```

## Code Quality

### Formatting

```bash
# Format code
black src/ tests/

# Check formatting
black --check src/ tests/
```

### Linting

```bash
# Run linter
ruff check src/ tests/

# Fix auto-fixable issues
ruff check --fix src/ tests/
```

### Type Checking

```bash
mypy src/
```

## Adding Features

### 1. Parser Enhancement

To add support for new Lean constructs:

1. Update `src/proof_sketcher/parser/models.py` with new fields
2. Enhance regex patterns in `lean_parser.py`
3. Update Lean extractor in `ExtractTheorem.lean`
4. Add tests in `tests/test_parser.py`

### 2. New Export Format

To add a new export format:

1. Create exporter in `src/proof_sketcher/exporter/`
2. Inherit from `BaseExporter`
3. Implement `export()` method
4. Add templates in `templates/your_format/`
5. Update CLI in `cli.py`
6. Add tests

### 3. Animation Styles

To add new animation styles:

1. Update `AnimationStyle` enum in `animator/models.py`
2. Add style configuration in `scene_builder.py`
3. Update color schemes and transitions
4. Test with example theorems

## Debugging

### Enable Debug Logging

```bash
# Via environment variable
export PROOF_SKETCHER_DEBUG=1

# Via CLI
proof-sketcher --debug prove theorem.lean
```

### Common Issues

1. **Import Errors**: Ensure you're in the virtual environment
2. **Lean Not Found**: Check `lean --version` works
3. **Test Failures**: Run `pytest -xvs` for detailed output

## Contributing Workflow

1. **Create Feature Branch**

   ```bash
   git checkout -b feature/your-feature
   ```

2. **Make Changes**
   - Write code
   - Add tests
   - Update documentation

3. **Run Tests**

   ```bash
   pytest
   black src/ tests/
   ruff check src/ tests/
   ```

4. **Commit Changes**

   ```bash
   git add .
   git commit -m "feat: add your feature"
   ```

5. **Push and Create PR**

   ```bash
   git push origin feature/your-feature
   # Create PR on GitHub
   ```

## Release Process

1. **Update Version**
   - Update `__version__` in `src/proof_sketcher/__init__.py`
   - Update version in `setup.py`

2. **Update Changelog**
   - Add release notes in `CHANGELOG.md`

3. **Create Tag**

   ```bash
   git tag -a v0.2.0 -m "Release version 0.2.0"
   git push origin v0.2.0
   ```

4. **Build and Upload**

   ```bash
   python -m build
   twine upload dist/*
   ```

## Architecture Decisions

### Why Python?

- Wide adoption in scientific computing
- Rich ecosystem (Jupyter, matplotlib, etc.)
- Easy integration with AI tools
- Lower barrier to contribution

### Why Subprocess for Claude?

- No API key management for users
- Leverages Claude Code CLI
- Consistent with user's Claude setup
- Cost-effective for users

### Why MCP for Manim?

- Clean separation of concerns
- Language-agnostic protocol
- Enables remote rendering
- Future-proof architecture

## Performance Optimization

### Caching Strategy

- Cache Claude responses by theorem hash
- Cache animations by configuration
- Use TTL to prevent stale data
- Implement size limits

### Parallel Processing

- Parse multiple files concurrently
- Batch API requests when possible
- Use asyncio for I/O operations
- Profile before optimizing

## Future Enhancements

1. **LSP Integration**: Real-time preview in editors
2. **Web Interface**: Browser-based theorem exploration
3. **Collaboration**: Multi-user annotation support
4. **Advanced Animations**: 3D visualizations, interactive proofs
5. **LLM Flexibility**: Support for other language models
