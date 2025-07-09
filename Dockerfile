# Dockerfile for Proof Sketcher CI/CD Environment
# Alpha software - includes all dependencies for testing and quality checks

FROM python:3.10-slim-bullseye

# Metadata
LABEL maintainer="brightliu@college.harvard.edu"
LABEL description="Proof Sketcher - Alpha Development Environment"
LABEL version="0.0.1-alpha"

# Set environment variables
ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PIP_NO_CACHE_DIR=1 \
    PIP_DISABLE_PIP_VERSION_CHECK=1 \
    DEBIAN_FRONTEND=noninteractive \
    ALPHA_SOFTWARE=true

# Install system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    # Build essentials
    build-essential \
    gcc \
    g++ \
    make \
    # Git for version control
    git \
    # Lean 4 dependencies
    curl \
    wget \
    ca-certificates \
    # LaTeX for PDF generation (optional, large)
    # texlive-base \
    # texlive-latex-extra \
    # Additional tools
    jq \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# Install Lean 4 (elan)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Create working directory
WORKDIR /app

# Copy dependency files first (better caching)
COPY requirements.txt requirements-dev.txt ./

# Install Python dependencies
RUN pip install --upgrade pip setuptools wheel && \
    pip install -r requirements.txt && \
    pip install -r requirements-dev.txt

# Install additional CI/CD tools
RUN pip install \
    # Security scanning
    bandit \
    safety \
    pip-audit \
    # Code quality
    black \
    isort \
    flake8 \
    pylint \
    mypy \
    # Testing
    pytest \
    pytest-cov \
    pytest-timeout \
    pytest-xdist \
    pytest-benchmark \
    hypothesis \
    mutmut \
    # Documentation
    sphinx \
    sphinx-rtd-theme \
    sphinx-autodoc-typehints \
    # Performance
    memory-profiler \
    line-profiler

# Copy pre-commit configuration
COPY .pre-commit-config.yaml ./

# Install pre-commit hooks
RUN git init && \
    pre-commit install --install-hooks || echo "Pre-commit hooks installation skipped"

# Copy application code
COPY . .

# Create necessary directories
RUN mkdir -p \
    /app/output \
    /app/animations \
    /app/cache \
    /app/logs \
    /app/htmlcov \
    /app/.hypothesis

# Set permissions (if running as non-root later)
RUN chmod -R 755 /app

# Health check (basic)
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD python -c "import proof_sketcher; print('OK')" || exit 1

# Default command (can be overridden)
CMD ["python", "-m", "proof_sketcher", "--help"]

# Development/Testing Commands:
# docker build -t proof-sketcher:alpha .
# docker run -it proof-sketcher:alpha pytest
# docker run -it proof-sketcher:alpha black --check src
# docker run -it proof-sketcher:alpha bandit -r src
# docker run -it proof-sketcher:alpha python -m proof_sketcher prove examples/simple.lean

# CI/CD Usage:
# docker run --rm -v $(pwd):/app proof-sketcher:alpha pytest --cov=src
# docker run --rm -v $(pwd):/app proof-sketcher:alpha flake8 src
# docker run --rm -v $(pwd):/app proof-sketcher:alpha mypy src

# Volume mounts for development:
# -v $(pwd)/src:/app/src
# -v $(pwd)/tests:/app/tests
# -v $(pwd)/output:/app/output

# Environment variables for CI:
# -e CI=true
# -e GITHUB_TOKEN=$GITHUB_TOKEN
# -e SONAR_TOKEN=$SONAR_TOKEN
EOF < /dev/null