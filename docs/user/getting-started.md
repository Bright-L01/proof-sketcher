# Getting Started with Proof Sketcher

This guide will help you get up and running with Proof Sketcher quickly.

## Prerequisites

- Python 3.9 or higher
- pip (Python package manager)
- Basic familiarity with command line
- (Optional) Lean 4 for creating your own theorems

## Installation

### From PyPI (Recommended)

```bash
pip install proof-sketcher
```

### From Source

```bash
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
pip install -e .
```

### Development Installation

```bash
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
pip install -e ".[dev,test]"
```

## Verify Installation

```bash
proof-sketcher --version
proof-sketcher --help
```

## Your First Proof Explanation

### 1. Create a Simple Lean File

Create `example.lean`:

```lean
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ n ih => simp [ih]

theorem add_zero (n : Nat) : n + 0 = n := by
  simp
```

### 2. List Available Theorems

```bash
proof-sketcher list-theorems example.lean
```

Output:

```
Found 2 theorems:
1. add_comm - Commutativity of addition
2. add_zero - Adding zero
```

### 3. Generate Explanation

```bash
proof-sketcher prove example.lean --theorem add_comm
```

This generates an HTML file with a natural language explanation of the proof.

### 4. Export to Different Formats

```bash
# Markdown format
proof-sketcher prove example.lean --theorem add_comm --format markdown

# Specify output file
proof-sketcher prove example.lean --theorem add_comm --output my_proof.html

# Generate all formats
proof-sketcher prove example.lean --theorem add_comm --format all
```

## Common Use Cases

### Batch Processing

Process multiple files at once:

```bash
proof-sketcher batch *.lean --output-dir proofs/
```

### Working with Mathlib

```bash
# List theorems from Mathlib file
proof-sketcher list-theorems path/to/mathlib/file.lean

# Generate explanation for specific theorem
proof-sketcher prove mathlib/file.lean --theorem theorem_name
```

### Configuration

Create `.proof-sketcher.yaml`:

```yaml
parser:
  timeout: 30
  max_depth: 10

generator:
  style: educational
  verbosity: high

exporter:
  theme: light
  include_source: true
```

## Troubleshooting

### Common Issues

1. **"No theorems found"**
   - Ensure your Lean file has valid theorem declarations
   - Check file path is correct

2. **"Parser timeout"**
   - Increase timeout in configuration
   - Simplify complex theorems

3. **"Empty output"**
   - This is a known alpha limitation
   - Try simpler theorems

### Debug Mode

Enable verbose logging:

```bash
proof-sketcher prove file.lean --verbose
```

## Next Steps

- Read the [User Guide](user-guide/index.md) for advanced features
- Check [CLI Reference](cli-reference.md) for all commands
- Review [examples/](../examples/) directory
- Join our [community discussions](https://github.com/Bright-L01/proof-sketcher/discussions)

## Known Limitations

As alpha software, be aware of:

- Limited theorem parsing capability
- Basic template-based explanations
- No AI integration yet
- Some commands may not work as expected

See [ALPHA_STATUS.md](../ALPHA_STATUS.md) for full details.
