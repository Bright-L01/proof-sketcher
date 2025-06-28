# Proof Sketcher Quick Start Guide

## 🚀 Getting Started in 5 Minutes

### 1. Installation

```bash
# Clone the repository
git clone https://github.com/your-org/proof-sketcher
cd proof-sketcher

# Install in development mode
pip install -e .
```

### 2. Run the Demo

```bash
# See Proof Sketcher in action
python demo.py
```

### 3. Try with Your Own Files

Even without Lean installed, you can parse basic theorem structure:

```bash
# Parse a Lean file
proof-sketcher prove examples/lean_project/ProofSketcherExamples/Nat.lean
```

## 📋 Full Setup (Recommended)

### Prerequisites

1. **Install Lean 4**
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   source $HOME/.elan/env
   ```

2. **Install Claude Code CLI**
   ```bash
   # Requires Node.js
   npm install -g @anthropic-ai/claude-code
   claude auth login
   ```

3. **Verify Installation**
   ```bash
   lean --version
   lake --version
   claude --version
   ```

### Test Full Functionality

```bash
# With Lean installed, you get full theorem extraction
proof-sketcher prove examples/lean_project/ProofSketcherExamples/List.lean

# Generate natural language explanation (requires Claude Code CLI)
proof-sketcher prove examples/basic.lean --explain

# Create animation (requires MCP server)
proof-sketcher prove examples/basic.lean --animate
```

## 🎯 Example Workflow

### 1. Create a Lean File

```lean
-- MyTheorem.lean
theorem my_theorem (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  exact ⟨h.2, h.1⟩
```

### 2. Generate Explanation

```bash
proof-sketcher prove MyTheorem.lean --format markdown
```

### 3. View Output

The tool generates:
- Natural language explanation of the theorem
- Step-by-step proof breakdown
- Mathematical context and insights

## 🔧 Configuration

Create `.proof-sketcher.yaml` for custom settings:

```yaml
generator:
  explanation_type: tutorial  # concise, detailed, or tutorial
  
animator:
  quality: 1080p
  style: modern
  
export:
  output_dir: ./proofs/
```

## 📚 Next Steps

1. **Explore Examples**: Check out the `examples/` directory
2. **Read Documentation**: See `docs/` for detailed guides
3. **Join Community**: Report issues and share feedback

## 🆘 Troubleshooting

### "Lean not found"
- Ensure Lean is installed and in your PATH
- Or use the regex fallback mode (automatic)

### "Claude command not found"
- Install Claude Code CLI: `npm install -g @anthropic-ai/claude-code`
- Run `claude auth login` to authenticate

### "Parse errors"
- Check that your Lean file has valid syntax
- Ensure you're using Lean 4 (not Lean 3)

## 🎉 Success!

You're ready to transform formal proofs into beautiful explanations!