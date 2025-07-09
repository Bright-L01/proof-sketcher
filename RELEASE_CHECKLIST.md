# Alpha Release Checklist (v0.0.1a1)

## ⚠️ WARNING: This is an ALPHA release - NOT for production use

### Pre-release Verification

#### Code Quality
- [ ] All tests passing (currently ~38% coverage - NOT the claimed 60%)
- [ ] No critical security vulnerabilities (run `bandit -r src/`)
- [ ] Linting passes for core modules
- [ ] Type checking passes for typed modules

#### Documentation
- [x] README.md updated with honest alpha warnings
- [x] KNOWN_ISSUES.md is comprehensive and honest
- [x] Alpha warnings integrated in all outputs
- [ ] Changelog prepared for alpha release

#### Version Check
- [x] Version set to 0.0.1a1 in src/proof_sketcher/__init__.py
- [x] Version set to 0.0.1a1 in pyproject.toml
- [x] Development Status set to "2 - Pre-Alpha"

### Build Process

#### Clean Previous Builds
```bash
rm -rf dist/
rm -rf build/
rm -rf *.egg-info
rm -rf src/*.egg-info
```

#### Build Package
```bash
# Ensure build tools are up to date
pip install --upgrade build twine

# Build both wheel and source distribution
python -m build
```

#### Verify Build
```bash
# Check package contents
tar -tzf dist/*.tar.gz | head -20

# Check that key files are included
tar -tzf dist/*.tar.gz | grep -E "(README|LICENSE|pyproject.toml)"

# Check package metadata
twine check dist/*
```

### Local Testing

#### Test Installation
```bash
# Create clean test environment
python -m venv test_env
source test_env/bin/activate  # On Windows: test_env\Scripts\activate

# Install from wheel
pip install dist/*.whl

# Verify version
proof-sketcher --version  # Should show 0.0.1a1

# Verify alpha warning appears
proof-sketcher --help  # Should show alpha warning banner
```

#### Basic Functionality Test
```bash
# Create simple test file
echo 'theorem test : True := trivial' > test.lean

# Test basic command (should work)
proof-sketcher prove test.lean --offline

# Verify output has alpha warnings
cat output/*.md | grep -i "alpha"
```

#### Uninstall Test Package
```bash
pip uninstall proof-sketcher
deactivate
rm -rf test_env
```

### TestPyPI Upload

#### Pre-upload Checks
- [ ] Confirm version is 0.0.1a1 (NOT 0.1.0 or 1.0.0)
- [ ] Confirm this is going to TestPyPI (NOT real PyPI)
- [ ] Have TestPyPI credentials ready

#### Upload to TestPyPI
```bash
# Upload to TestPyPI ONLY (note the -r testpypi flag)
twine upload -r testpypi dist/*

# If you don't have TestPyPI configured:
# twine upload --repository-url https://test.pypi.org/legacy/ dist/*
```

#### Test from TestPyPI
```bash
# Create new test environment
python -m venv testpypi_env
source testpypi_env/bin/activate

# Install from TestPyPI
pip install -i https://test.pypi.org/simple/ proof-sketcher==0.0.1a1

# May need to install dependencies from regular PyPI
pip install click pydantic rich jinja2 PyYAML

# Verify it works
proof-sketcher --version
proof-sketcher --help  # Check alpha warning

# Test basic functionality
echo 'theorem simple : 1 + 1 = 2 := rfl' > simple.lean
proof-sketcher prove simple.lean --offline
```

### Post-release Tasks

#### Git Tasks
```bash
# Tag the release
git tag -a v0.0.1a1 -m "Alpha release - NOT production ready"
git push origin v0.0.1a1
```

#### GitHub Release
```bash
# Create GitHub release (mark as pre-release)
gh release create v0.0.1a1 --prerelease \
  --title "v0.0.1-alpha1 - Experimental Release" \
  --notes "⚠️ ALPHA SOFTWARE - NOT FOR PRODUCTION USE

This is an experimental alpha release for testing purposes only.

## What Works (Sometimes)
- Basic Lean theorem parsing (simple syntax only)
- Static diagram generation (when matplotlib works)
- HTML/Markdown export (with alpha warnings)
- Offline mode for basic usage

## What Doesn't Work
- Complex Lean parsing (most real theorems fail)
- Animation generation (Manim integration fragile)
- Memory efficiency (loads entire files)
- Error handling (limited)

## Known Issues
See KNOWN_ISSUES.md for comprehensive list.

## Installation (Testing Only)
\`\`\`bash
pip install -i https://test.pypi.org/simple/ proof-sketcher==0.0.1a1
\`\`\`

**DO NOT USE IN PRODUCTION**"
```

### Communication

#### Announcement Template
```
🚧 Proof Sketcher v0.0.1-alpha1 Released (Testing Only) 🚧

We've released our first alpha version to TestPyPI for brave testers!

⚠️ WARNING: This is experimental software with many limitations
- Only handles basic Lean syntax
- Many features incomplete or broken
- Not suitable for real use

If you want to help test:
pip install -i https://test.pypi.org/simple/ proof-sketcher==0.0.1a1

Please report issues (there will be many) at:
https://github.com/yourusername/proof-sketcher/issues

See KNOWN_ISSUES.md for what's broken.
```

### Rollback Plan

If critical issues found:
1. Delete release from TestPyPI (if possible)
2. Delete GitHub release
3. Delete git tag: `git tag -d v0.0.1a1; git push origin :v0.0.1a1`
4. Fix issues and release as v0.0.1a2

## Critical Reminders

- **DO NOT** upload to real PyPI
- **DO NOT** claim this is production ready
- **DO NOT** hide known limitations
- **DO** encourage issue reports
- **DO** set expectations appropriately

## Brutal Honesty Check

Before releasing, confirm:
- [ ] Test coverage is actually ~38%, not 60%
- [ ] Many features don't work as described
- [ ] Export system has duplication issues
- [ ] Parser only handles basic syntax
- [ ] Memory usage is inefficient
- [ ] This is truly alpha quality

If you can't check all boxes honestly, DO NOT RELEASE.