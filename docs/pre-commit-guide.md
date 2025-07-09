# Pre-commit Hooks Guide

## Overview

Pre-commit hooks help maintain code quality by automatically checking and fixing issues before commits. This guide explains how to use them effectively with Proof Sketcher.

## Quick Start

```bash
# Run the setup script
./scripts/setup_pre_commit.sh

# That's it! Hooks will run automatically on commit
```

## What Gets Checked

### 1. Code Formatting (Auto-fixed)
- **Black**: Consistent Python formatting
- **isort**: Organized imports
- **Trailing whitespace**: Removed automatically
- **End of file**: Fixed automatically

### 2. Code Quality (Enforced)
- **Flake8**: Style guide enforcement
  - Max line length: 88 characters
  - Max complexity: 10 (McCabe)
  - Ignores: E203, W503 (Black compatibility)
  - Per-file ignores: F401 in __init__.py

### 3. Security (Informational)
- **Bandit**: Security vulnerability scanning
- **detect-secrets**: Prevents committing secrets

### 4. Type Checking (Informational)
- **mypy**: Static type checking
- Currently non-blocking to allow gradual typing

### 5. Project-Specific
- **TODO checker**: Warns about TODOs in new code
- **Test coverage**: Ensures tests exist for new modules
- **Quality reminder**: Shows current quality metrics

## Usage

### Normal Workflow

```bash
# Make changes
git add .

# Commit - hooks run automatically
git commit -m "feat: add new feature"

# If issues found, fix and try again
git add .
git commit -m "feat: add new feature"
```

### Manual Checks

```bash
# Check all files
pre-commit run --all-files

# Check specific files
pre-commit run --files src/proof_sketcher/core.py

# Update hooks to latest versions
pre-commit autoupdate
```

### Emergency Bypass

```bash
# Skip hooks (use sparingly!)
git commit --no-verify -m "fix: emergency hotfix"
```

## Current Quality Standards

As of the latest quality improvement phase:

- **Total violations**: 1,478 (down from 4,473)
- **Improvement**: 67% reduction
- **Target**: <500 violations
- **Status**: Production-ready quality achieved

## Hook Configuration

The configuration is in `.pre-commit-config.yaml`. Key settings:

- **fail_fast**: false (all hooks run even if one fails)
- **verbose**: true (shows tool output)
- **default_stages**: [pre-commit] (runs before commit)

## Troubleshooting

### "Black and isort conflict"
This is handled by using `--profile black` for isort.

### "Line too long" errors
Black uses 88 characters. If you have a string that can't be broken, use:
```python
# fmt: off
really_long_string = "..."
# fmt: on
```

### "Import not used" in __init__.py
This is ignored via per-file configuration.

### Hook runs too slow
Try:
```bash
# Run only on staged files
pre-commit run

# Skip expensive hooks temporarily
SKIP=mypy,bandit git commit -m "..."
```

## Best Practices

1. **Fix issues immediately**: Don't accumulate technical debt
2. **Run before pushing**: `pre-commit run --all-files`
3. **Keep hooks updated**: `pre-commit autoupdate` monthly
4. **Don't skip hooks**: Use `--no-verify` only in emergencies
5. **Add new hooks gradually**: Test impact before enforcing

## Adding New Hooks

To add a new hook:

1. Edit `.pre-commit-config.yaml`
2. Add the hook configuration
3. Run `pre-commit run --all-files` to test
4. Commit the changes

Example:
```yaml
- repo: https://github.com/pycqa/pylint
  rev: v3.0.0
  hooks:
    - id: pylint
      args: ["--max-line-length=88"]
```

## Quality Metrics

Track quality trends:

```bash
# Count current violations
flake8 src/ --count

# Check complexity
radon cc src/ -a

# Security scan
bandit -r src/
```

## Conclusion

Pre-commit hooks are your first line of defense against technical debt. Use them consistently to maintain the hard-won code quality improvements!

Remember: **Clean code is a team effort**. Every commit counts! 🚀