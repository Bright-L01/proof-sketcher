#\!/bin/bash
# CI/CD Setup Script for Proof Sketcher
# Configures pre-commit hooks and CI/CD environment

set -e

echo "======================================"
echo "Proof Sketcher CI/CD Setup"
echo "Alpha Software - Version 0.0.1"
echo "======================================"
echo ""
echo "⚠️  WARNING: This is ALPHA software with:"
echo "   - 11% test coverage"
echo "   - 69 security vulnerabilities"
echo "   - 3,625 code quality issues"
echo ""
echo "This setup will help prevent adding MORE technical debt."
echo ""

# Check Python version
echo "Checking Python version..."
python_version=$(python3 --version 2>&1 | awk '{print $2}')
echo "Found Python $python_version"

# Install pre-commit
echo ""
echo "Installing pre-commit hooks..."
pip install pre-commit || {
    echo "❌ Failed to install pre-commit"
    echo "Try: pip install --user pre-commit"
    exit 1
}

# Install hooks
echo "Setting up git hooks..."
pre-commit install || {
    echo "❌ Failed to install git hooks"
    echo "Make sure you're in a git repository"
    exit 1
}

# Install commit-msg hook for conventional commits
pre-commit install --hook-type commit-msg || {
    echo "⚠️  Commit message linting not installed"
}

# Create .secrets.baseline for detect-secrets
echo ""
echo "Creating secrets baseline..."
if command -v detect-secrets &> /dev/null; then
    detect-secrets scan > .secrets.baseline || {
        echo "⚠️  Failed to create secrets baseline"
    }
else
    echo "⚠️  detect-secrets not installed, skipping baseline"
fi

# Docker setup (optional)
echo ""
echo "Docker setup (optional)..."
if command -v docker &> /dev/null; then
    echo "Docker found. Building CI/CD image..."
    docker build -t proof-sketcher:alpha . || {
        echo "⚠️  Docker build failed - manual build required"
    }
else
    echo "⚠️  Docker not found - skipping container setup"
fi

# Create local CI script
echo ""
echo "Creating local CI simulation script..."
cat > run_ci_locally.sh << 'SCRIPT'
#\!/bin/bash
# Local CI Simulation for Proof Sketcher
echo "Running local CI checks..."

# Quality metrics
echo "1. Generating quality metrics..."
coverage run -m pytest tests/unit -v || echo "Tests incomplete"
coverage report

# Security scan
echo "2. Running security scan..."
bandit -r src -ll || echo "Security issues found"

# Code quality
echo "3. Checking code quality..."
flake8 src --count --statistics || echo "Linting issues found"

# Type checking
echo "4. Type checking..."
mypy src --ignore-missing-imports || echo "Type issues found"

# Pre-commit on all files
echo "5. Running pre-commit checks..."
pre-commit run --all-files || echo "Pre-commit checks found issues"

echo "Local CI complete\!"
SCRIPT
chmod +x run_ci_locally.sh

# Summary
echo ""
echo "======================================"
echo "✅ CI/CD Setup Complete\!"
echo "======================================"
echo ""
echo "Pre-commit hooks installed:"
echo "  - Black (code formatting)"
echo "  - isort (import sorting)"
echo "  - Flake8 (linting)"
echo "  - Bandit (security)"
echo "  - MyPy (type checking)"
echo "  - Detect secrets"
echo ""
echo "Quality gates configured for NEW code:"
echo "  - All new code must be properly formatted"
echo "  - No new security vulnerabilities"
echo "  - Type hints encouraged"
echo ""
echo "Next steps:"
echo "  1. Run: ./run_ci_locally.sh"
echo "  2. Fix any issues in new code"
echo "  3. Commit with conventional format: feat:/fix:/docs:"
echo ""
echo "To skip hooks in emergency: git commit --no-verify"
echo ""
echo "Remember: Focus on 'Clean as You Code' - new code must be high quality\!"
