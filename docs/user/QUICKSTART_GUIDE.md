# Quick Start Guide

Get up and running with Proof Sketcher in 5 minutes.

## Prerequisites Check

Before starting, ensure you have:

1. **Python 3.9+**

   ```bash
   python --version  # Should be 3.9 or higher
   ```

2. **Claude Code CLI** (required for explanations)

   ```bash
   # Install Claude CLI if not already installed
   curl -fsSL https://claude.ai/install.sh | sh

   # Verify installation
   claude --version
   ```

## Installation

```bash
# Clone the repository
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher

# Install in development mode
pip install -e .

# Verify installation
python -m proof_sketcher --version
```

## Your First Proof Explanation

Let's start with a simple example:

### Step 1: Explore Available Examples

```bash
# List theorems in our simple examples file
python -m proof_sketcher list-theorems examples/classical/simple_examples.lean
```

You should see output like:

```
                  Theorems in simple_examples.lean
┏━━━━━━━━━━━━━━━┳━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┳━━━━━━━━━┓
┃ Name          ┃ Statement                               ┃    Line ┃
┡━━━━━━━━━━━━━━━╇━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━╇━━━━━━━━━┩
│ add_zero      │ (n : ℕ) : n + 0 = n                     │  line 6 │
│ nat_add_comm  │ (n m : ℕ) : n + m = m + n               │ line 10 │
│ real_add_zero │ (x : ℝ) : x + 0 = x                     │ line 18 │
└───────────────┴─────────────────────────────────────────┴─────────┘
```

### Step 2: Generate Your First Explanation

```bash
# Create output directory
mkdir -p output/quickstart

# Generate explanation for addition commutativity
python -m proof_sketcher prove examples/classical/simple_examples.lean \
  --theorem nat_add_comm \
  --format markdown \
  --output output/quickstart
```

### Step 3: View the Results

```bash
# See what was generated
ls output/quickstart/

# View the explanation
cat output/quickstart/nat_add_comm.md
```

**Note:** If Claude CLI is not configured, you'll see parsing success but generation might fail. That's normal - the core system is working!

## Next Steps

### Explore More Examples

```bash
# Group theory theorems
python -m proof_sketcher list-theorems examples/classical/group_theory.lean

# Try generating explanations for different mathematical areas
python -m proof_sketcher prove examples/classical/group_theory.lean \
  --theorem unique_identity \
  --format html \
  --output output/group_theory
```

### Try Different Output Formats

```bash
# Generate all formats
python -m proof_sketcher prove examples/classical/simple_examples.lean \
  --theorem add_zero \
  --format all \
  --output output/all_formats

# Check what was created
ls output/all_formats/
```

### Use Configuration

```bash
# Create a config file
cat > quickstart-config.yaml << EOF
generator:
  model: claude-3-5-sonnet-20241022
  temperature: 0.5
  verbosity: concise

export:
  output_dir: output/configured

cache:
  enabled: true
  ttl_hours: 48
EOF

# Use your configuration
python -m proof_sketcher prove examples/classical/simple_examples.lean \
  --config quickstart-config.yaml \
  --format markdown
```

## Common Commands

### List all available commands

```bash
python -m proof_sketcher --help
```

### Get help for specific commands

```bash
python -m proof_sketcher prove --help
python -m proof_sketcher cache --help
```

### Process multiple theorems

```bash
python -m proof_sketcher prove examples/classical/simple_examples.lean \
  --theorem add_zero \
  --theorem nat_add_comm \
  --format markdown \
  --output output/multiple
```

### Check cache status

```bash
python -m proof_sketcher cache status
```

## Troubleshooting

### Command not found

```bash
# Make sure you're in the project directory
pwd
# Should show: /path/to/proof-sketcher

# Try with full path
python -m proof_sketcher --version
```

### No theorems found

```bash
# Check if Lean file is valid
python -m proof_sketcher list-theorems examples/classical/simple_examples.lean

# If empty, check the file exists
ls examples/classical/simple_examples.lean
```

### Claude command fails

This is expected if Claude CLI isn't properly configured. The parsing and theorem extraction still work!

## What's Next?

- **Read the full README**: [README.md](../README.md)
- **Explore examples**: Browse the `examples/` directory
- **Learn configuration**: [Configuration Guide](configuration.md)
- **Contribute**: [Contributing Guidelines](../CONTRIBUTING.md)

## Getting Help

- **GitHub Issues**: Report problems or ask questions
- **Discussions**: Join the community discussions
- **Documentation**: Browse the full documentation in `docs/`

Happy theorem explaining! 🎓✨
