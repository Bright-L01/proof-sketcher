# Installation Guide

This guide covers all installation methods for Proof Sketcher, from simple pip install to development setup.

## Quick Installation

### Prerequisites

- **Python 3.10+** (Python 3.12 recommended)
- **Lean 4** (4.0.0 or later)

### Install from PyPI

```bash
pip install proof-sketcher
```

### Verify Installation

```bash
proof-sketcher --version
proof-sketcher config show
```

## Detailed Installation

### 1. Install Python

#### macOS
```bash
# Using Homebrew
brew install python@3.12

# Or using pyenv
pyenv install 3.12.0
pyenv global 3.12.0
```

#### Ubuntu/Debian
```bash
sudo apt update
sudo apt install python3.12 python3.12-pip python3.12-venv
```

#### Windows
Download Python 3.12 from [python.org](https://python.org) or use winget:
```powershell
winget install Python.Python.3.12
```

### 2. Install Lean 4

#### Using elan (Recommended)
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
source ~/.elan/env
```

#### Verify Lean Installation
```bash
lean --version
lake --version
```

### 3. Install Proof Sketcher

#### Option A: From PyPI (Stable)
```bash
pip install proof-sketcher
```

#### Option B: From Source (Latest)
```bash
git clone https://github.com/YOUR_USERNAME/proof-sketcher.git
cd proof-sketcher
pip install -e ".[dev]"
```

#### Option C: Using pipx (Isolated)
```bash
pipx install proof-sketcher
```

### 4. Optional Dependencies

#### For Animation Support
```bash
# Install Manim dependencies
pip install manim

# Install video codecs (Ubuntu)
sudo apt install ffmpeg

# Install video codecs (macOS)
brew install ffmpeg
```

#### For Development
```bash
pip install proof-sketcher[dev]
```

## Virtual Environment Setup

### Using venv
```bash
python -m venv proof-sketcher-env
source proof-sketcher-env/bin/activate  # Linux/macOS
# or
proof-sketcher-env\Scripts\activate  # Windows

pip install proof-sketcher
```

### Using conda
```bash
conda create -n proof-sketcher python=3.12
conda activate proof-sketcher
pip install proof-sketcher
```

## Configuration

### First-time Setup
```bash
# Create configuration file
proof-sketcher config init

# Edit configuration
proof-sketcher config edit

# Verify setup
proof-sketcher config validate
```

### Configuration Locations
- **Global**: `~/.proof-sketcher/config.yaml`
- **Project**: `./.proof-sketcher.yaml`
- **Environment**: `PROOF_SKETCHER_*` variables

## Troubleshooting

### Common Issues

#### "command not found: proof-sketcher"
```bash
# Check if pip installed to user directory
pip show proof-sketcher

# Add to PATH if needed
export PATH="$HOME/.local/bin:$PATH"
```

#### "Lean executable not found"
```bash
# Check Lean installation
which lean
lean --version

# Reinstall Lean if needed
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
```

#### Permission errors on macOS/Linux
```bash
# Use --user flag
pip install --user proof-sketcher

# Or fix permissions
sudo chown -R $(whoami) /usr/local/lib/python3.12/site-packages
```

#### Import errors
```bash
# Check Python version
python --version

# Upgrade pip
pip install --upgrade pip

# Reinstall package
pip uninstall proof-sketcher
pip install proof-sketcher
```

### Getting Help

1. Check the [troubleshooting guide](troubleshooting.md)
2. Search existing [issues](https://github.com/YOUR_USERNAME/proof-sketcher/issues)
3. Create a new issue with:
   - Operating system and version
   - Python version (`python --version`)
   - Lean version (`lean --version`)
   - Complete error message

## Docker Installation

### Using Docker
```dockerfile
FROM python:3.12-slim

# Install Lean 4
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
ENV PATH="/root/.elan/bin:$PATH"

# Install Proof Sketcher
RUN pip install proof-sketcher

WORKDIR /workspace
```

Build and run:
```bash
docker build -t proof-sketcher .
docker run -v $(pwd):/workspace proof-sketcher proof-sketcher --help
```

## Next Steps

After installation:
1. Follow the [Quick Start Guide](../QUICKSTART_GUIDE.md)
2. Try the [examples](examples.md)
3. Read the [User Guide](USER_GUIDE.md)
4. Configure [integrations](configuration.md#integrations)