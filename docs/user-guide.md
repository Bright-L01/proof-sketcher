# Proof Sketcher User Guide

**⚠️ Alpha Software Warning**: This guide documents alpha software with significant limitations. See [Known Issues](../README.md#-known-issues) before proceeding.

## Installation

### System Requirements

- **Operating System**: Linux, macOS, or Windows 10+
- **Python**: 3.10 or higher
- **Memory**: 4GB RAM minimum
- **Storage**: 1GB free space

### Step-by-Step Installation

#### 1. Install Python

Check your Python version:
```bash
python --version  # Should be 3.10+
```

#### 2. Clone and Install

```bash
git clone https://github.com/yourusername/proof-sketcher
cd proof-sketcher
pip install -e .
```

#### 3. Verify Installation

```bash
python -m proof_sketcher --version
python -m proof_sketcher --help
```

## Basic Usage

### Your First Documentation Generation

1. **Create a simple Lean file:**

```lean
-- hello.lean
theorem hello_world : 1 + 1 = 2 := by simp
```

2. **Generate documentation (offline mode):**

```bash
python -m proof_sketcher prove hello.lean --offline --format markdown
```

3. **View the output:**

```bash
ls output/
cat output/hello_world.md
```

**⚠️ Expected Result**: You'll get a basic template with generic content, not specific explanations of your theorem.

## Understanding Current Output

Each generated page currently contains:

- **Theorem Name**: Extracted from file
- **Generic Template**: Standard explanation template
- **Basic Structure**: HTML/Markdown formatting
- **Empty Statements**: ⚠️ Often missing actual theorem content

**What's Missing (Known Issues):**
- Actual theorem statements are often empty
- AI-generated explanations (offline mode only)
- Meaningful mathematical content
- Working animations

## Available Commands

### List Theorems

```bash
# Attempt to list theorems (may show limited info)
python -m proof_sketcher list-theorems file.lean
```

**⚠️ Current Limitation**: May not extract theorem information correctly.

### Generate Documentation

```bash
# Basic generation (offline mode recommended)
python -m proof_sketcher prove file.lean --offline

# Specify format
python -m proof_sketcher prove file.lean --offline --format html
python -m proof_sketcher prove file.lean --offline --format markdown
```

### Batch Processing

```bash
# Process multiple files (experimental)
python -m proof_sketcher batch ./lean-files/ --offline
```

**⚠️ Performance Warning**: Currently slow (30+ seconds per theorem).

## Configuration

### Basic Configuration

Create `.proof-sketcher.yaml`:

```yaml
# Recommended settings for current version
generation:
  offline_mode: true  # REQUIRED - AI integration not functional
  timeout_seconds: 120  # Increase for slow processing

export:
  formats: ["html", "markdown"]
  output_dir: "output"
  
# Debugging (recommended)
debug: true
verbose_logging: true
```

### Command-Line Options

```bash
# Verbose output for debugging
python -m proof_sketcher prove file.lean --verbose --debug

# Specify output directory
python -m proof_sketcher prove file.lean --output ./docs/

# Multiple formats
python -m proof_sketcher prove file.lean --format all
```

## Current Limitations

### What Doesn't Work

1. **AI Integration**: Claude API integration is incomplete
   - Offline mode is the only working option
   - No real AI-generated explanations

2. **Lean Parsing**: Limited theorem extraction
   - Often produces empty theorem statements
   - Lean extractor build fails
   - Falls back to basic text parsing

3. **Animations**: Manim integration is broken
   - No working animations
   - Animation requests fail

4. **Content Quality**: Generic template output
   - Not theorem-specific
   - No meaningful mathematical explanations

### Performance Issues

- **Slow Processing**: 30+ seconds for simple theorems
- **Memory Usage**: Potentially high for large files
- **Error Recovery**: Limited error handling

## Troubleshooting

### Common Issues

#### "Empty theorem statements in output"

**Cause**: Lean parser not extracting content properly

**Workaround**: 
- This is a known critical issue
- No current fix available
- Output will be generic templates only

#### "Build failed" or "Lean extractor errors"

**Cause**: Lean extractor build system is broken

**Workaround**:
- System automatically falls back to basic parsing
- Reduced functionality is expected

#### "Failed to generate explanation"

**Cause**: AI integration not functional

**Solution**:
- Always use `--offline` flag
- Expect template-based output only

#### "Processing is very slow"

**Cause**: Performance issues in current implementation

**Workaround**:
- Process one file at a time
- Use `--timeout` to prevent hanging
- Expect 30+ seconds per theorem

### Debug Mode

```bash
# Enable comprehensive debugging
python -m proof_sketcher prove file.lean \
  --verbose \
  --debug \
  --offline
```

### Getting Help

1. **Check Known Issues**: See README.md
2. **Review Logs**: Enable verbose mode for detailed output
3. **Create Issues**: Report problems with full debug output

## Development and Contributing

### Current Development Status

This software is in **alpha development** with:

- 11% test coverage (target: 70%+)
- 69 security vulnerabilities
- 3,625 code quality violations
- Limited core functionality

### How to Contribute

**High Priority Areas**:

1. **Security Fixes**
   - Fix pickle deserialization vulnerabilities
   - Address XSS issues in template system
   - Update vulnerable dependencies

2. **Core Functionality**
   - Implement proper Lean theorem parsing
   - Fix empty statement generation
   - Improve Lean extractor build system

3. **Test Coverage**
   - Fix broken test modules
   - Expand from 11% to 70%+ coverage
   - Add integration tests

4. **Code Quality**
   - Fix 3,625 linting violations
   - Implement proper formatting
   - Add type annotations

### Development Setup

```bash
git clone https://github.com/yourusername/proof-sketcher
cd proof-sketcher
pip install -e ".[dev]"

# Run working tests only
pytest tests/test_core_utils.py tests/unit/test_coverage_boost.py

# Check current issues
flake8 src/proof_sketcher/ | head -20
```

## Best Practices (Current Limitations)

### For Testing

1. **Use Offline Mode**: Always include `--offline` flag
2. **Simple Files**: Test with basic theorems only
3. **Expect Templates**: Don't expect meaningful content
4. **Debug Output**: Use verbose mode to understand failures

### For Development

1. **Security Awareness**: Don't use in production environments
2. **Limited Functionality**: Focus on basic CLI testing
3. **Report Issues**: Document problems for future fixes

## Future Roadmap

### Phase 4: Production Preparation (Next 4-6 weeks)

1. **Week 1**: Security vulnerability fixes
2. **Week 2**: Core parsing functionality
3. **Week 3**: Code quality improvements
4. **Week 4**: Test coverage expansion

### Success Criteria

- Zero high/critical security vulnerabilities
- Functional theorem parsing with actual content
- 70%+ test coverage
- <100 linting violations (from 3,625)

## Disclaimer

**This is experimental alpha software.**

- **Not production ready**
- **Contains security vulnerabilities**
- **Limited functionality**
- **Use at your own risk**

Only use in development environments for testing and contribution purposes.

---

**Last Updated**: 2025-07-08  
**Status**: Alpha Development  
**Recommended Use**: Development and testing only