# User Guide

Complete guide to using Proof Sketcher for transforming Lean 4 theorems into natural language explanations.

## Table of Contents

1. [Getting Started](#getting-started)
2. [Understanding the Workflow](#understanding-the-workflow) 
3. [Command Line Interface](#command-line-interface)
4. [Configuration](#configuration)
5. [Working with Different Mathematical Areas](#working-with-different-mathematical-areas)
6. [Output Formats](#output-formats)
7. [Python API](#python-api)
8. [Best Practices](#best-practices)
9. [Troubleshooting](#troubleshooting)

## Getting Started

### Installation Prerequisites

Proof Sketcher requires several components:

1. **Python 3.9+**: Core runtime
2. **Claude Code CLI**: For natural language generation
3. **Lean 4**: For parsing new Lean files (optional)
4. **Node.js**: For Manim animations (optional)

```bash
# Check Python version
python --version

# Install Claude CLI
curl -fsSL https://claude.ai/install.sh | sh

# Verify Claude installation
claude --version
```

### Basic Installation

```bash
# Clone and install
git clone https://github.com/Bright-L01/proof-sketcher.git
cd proof-sketcher
pip install -e .

# Verify installation
python -m proof_sketcher --version
```

## Understanding the Workflow

Proof Sketcher follows this pipeline:

```
Lean File → Parse Theorems → Generate Explanations → Export Formats
     ↓            ↓                    ↓                  ↓
  *.lean      TheoremInfo        Natural Language      HTML/PDF/MD
```

### 1. Parsing Phase
- Extracts theorem statements, proofs, and dependencies
- Handles Lean syntax and mathlib imports
- Creates structured representation

### 2. Generation Phase  
- Uses Claude AI to create natural language explanations
- Generates different explanation styles (concise, detailed, tutorial)
- Incorporates mathematical context and intuition

### 3. Export Phase
- Converts explanations to various formats
- Adds mathematical notation rendering
- Creates navigation and cross-references

## Command Line Interface

### Core Commands

#### `list-theorems`: Explore Lean Files

```bash
# List all theorems in a file
python -m proof_sketcher list-theorems file.lean

# Get detailed information
python -m proof_sketcher list-theorems file.lean --verbose

# Filter by pattern
python -m proof_sketcher list-theorems file.lean --pattern "*comm*"
```

#### `prove`: Generate Explanations

```bash
# Basic usage
python -m proof_sketcher prove file.lean

# Specific theorem
python -m proof_sketcher prove file.lean --theorem theorem_name

# Custom output
python -m proof_sketcher prove file.lean \
  --format markdown \
  --output docs/ \
  --theorem add_comm
```

#### `cache`: Manage Caching

```bash
# Check cache status
python -m proof_sketcher cache status

# Clear cache
python -m proof_sketcher cache clear

# List cached items
python -m proof_sketcher cache list

# Clear specific pattern
python -m proof_sketcher cache clear --pattern "group_theory*"
```

#### `config`: Configuration Management

```bash
# Show current configuration
python -m proof_sketcher config show

# Validate configuration file
python -m proof_sketcher config validate config.yaml

# Generate sample configuration
python -m proof_sketcher config init
```

### Command Options

#### Global Options
- `--verbose, -v`: Enable detailed logging
- `--config, -c`: Specify configuration file
- `--help`: Show help information

#### Prove Command Options
- `--theorem, -t`: Process specific theorems only
- `--format, -f`: Output format (html, markdown, pdf, jupyter, all)
- `--output, -o`: Output directory
- `--animate`: Generate animations (requires Manim MCP)

## Configuration

### Configuration File Structure

Create `.proof-sketcher.yaml`:

```yaml
# Natural Language Generation
generator:
  model: claude-3-5-sonnet-20241022
  temperature: 0.7
  max_tokens: 4000
  verbosity: detailed  # concise, detailed, tutorial
  cache_responses: true
  cache_ttl_hours: 24

# Parser Settings
parser:
  lean_executable: lean
  lake_executable: lake
  timeout: 30
  extract_dependencies: true
  extract_docstrings: true

# Animation Configuration
animator:
  quality: high  # low, medium, high, ultra
  fps: 60
  style: modern  # classic, modern, minimal, educational
  background_color: "#1a1a1a"
  text_color: "#ffffff"
  accent_color: "#3498db"
  math_font: "Computer Modern"

# Export Settings
export:
  output_dir: docs/
  html_theme: doc-gen4
  pdf_engine: pdflatex
  include_source: true
  include_dependencies: true

# Caching
cache:
  enabled: true
  directory: ~/.proof-sketcher/cache
  max_size_mb: 500
  cleanup_interval_hours: 24
```

### Environment Variables

```bash
# Debug mode
export PROOF_SKETCHER_DEBUG=true

# Override specific settings
export PROOF_SKETCHER_GENERATOR_MODEL=claude-3-opus
export PROOF_SKETCHER_CACHE_ENABLED=false
export PROOF_SKETCHER_OUTPUT_DIR=/custom/output
```

### Configuration Hierarchy

1. Command line arguments (highest priority)
2. Environment variables
3. Configuration file
4. Default values (lowest priority)

## Working with Different Mathematical Areas

### Group Theory

```bash
# Explore group theory theorems
python -m proof_sketcher list-theorems examples/classical/group_theory.lean

# Generate explanations for group properties
python -m proof_sketcher prove examples/classical/group_theory.lean \
  --theorem unique_identity \
  --format markdown \
  --output docs/group_theory
```

**Common group theory theorems:**
- Identity uniqueness
- Inverse uniqueness  
- Cancellation laws
- Subgroup properties
- Homomorphism theorems

### Real Analysis

```bash
# Process real analysis theorems
python -m proof_sketcher prove examples/classical/real_analysis.lean \
  --theorem supremum_property \
  --format html \
  --output docs/analysis
```

**Typical real analysis concepts:**
- Completeness properties
- Limit theorems
- Continuity and differentiability
- Integration theory
- Metric space properties

### Topology

```bash
# Generate topology explanations
python -m proof_sketcher prove examples/classical/topology.lean \
  --theorem hausdorff_separation \
  --format pdf \
  --output docs/topology
```

**Key topological concepts:**
- Open and closed sets
- Compactness and connectedness
- Separation axioms
- Continuous functions
- Homeomorphisms

### Creating Custom Examples

Create your own Lean file:

```lean
-- my_theorems.lean
import Mathlib.Data.Nat.Basic

theorem my_theorem (n : ℕ) : n + 0 = n := by
  simp

theorem another_theorem (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b
```

Then process it:

```bash
python -m proof_sketcher prove my_theorems.lean --format all
```

## Output Formats

### HTML Format

**Features:**
- Interactive navigation
- Syntax highlighting
- Mathematical notation rendering
- Cross-references and links
- Mobile-responsive design

**Usage:**
```bash
python -m proof_sketcher prove file.lean --format html
```

**Customization:**
```yaml
export:
  html_theme: doc-gen4  # doc-gen4, minimal, academic
  include_toc: true
  include_search: true
  syntax_highlighting: true
```

### Markdown Format

**Features:**
- GitHub-flavored markdown
- KaTeX/MathJax support
- Collapsible sections
- Code blocks with syntax highlighting

**Usage:**
```bash
python -m proof_sketcher prove file.lean --format markdown
```

**Example output:**
```markdown
# Theorem: nat_add_comm

## Statement
For all natural numbers n and m: n + m = m + n

## Intuitive Explanation
This fundamental theorem establishes that addition of natural numbers...

## Proof Strategy
The proof proceeds by induction on n:
1. **Base case**: When n = 0...
2. **Inductive step**: Assume P(n), prove P(n+1)...
```

### PDF Format

**Features:**
- Professional LaTeX formatting
- Custom document classes
- Bibliography support
- Hyperlinked references

**Usage:**
```bash
python -m proof_sketcher prove file.lean --format pdf
```

**Requirements:**
- LaTeX distribution (TeX Live, MiKTeX)
- Required packages: amsmath, amsthm, hyperref

### Jupyter Notebook Format

**Features:**
- Interactive code cells
- Rich media output
- Educational widgets
- Exportable to various formats

**Usage:**
```bash
python -m proof_sketcher prove file.lean --format jupyter
```

**Running notebooks:**
```bash
jupyter lab output/theorem_name.ipynb
```

## Python API

### Basic Usage

```python
from proof_sketcher import LeanParser, AIGenerator, ProofSketcherConfig

# Load configuration
config = ProofSketcherConfig.load("config.yaml")

# Parse Lean file
parser = LeanParser(config.parser)
result = parser.parse_file("theorems.lean")

print(f"Found {len(result.theorems)} theorems")
for theorem in result.theorems:
    print(f"- {theorem.name}: {theorem.statement}")
```

### Advanced API Usage

```python
from proof_sketcher.generator import AIGenerator, GenerationConfig
from proof_sketcher.generator.models import GenerationType
from proof_sketcher.exporter import MarkdownExporter, HTMLExporter

# Custom generation configuration
gen_config = GenerationConfig(
    model="claude-3-5-sonnet-20241022",
    temperature=0.5,
    verbosity="tutorial",
    cache_responses=True
)

# Initialize generator
generator = AIGenerator(default_config=gen_config)

# Generate different types of explanations
for theorem in result.theorems:
    # Proof sketch
    sketch = generator.generate_proof_sketch(theorem)
    
    # ELI5 explanation
    eli5 = generator.generate_eli5_explanation(theorem)
    
    # Tactic explanation
    tactics = generator.generate_tactic_explanation(theorem)
    
    print(f"Theorem: {theorem.name}")
    print(f"Sketch: {sketch.introduction}")
    print(f"ELI5: {eli5}")
    print("---")
```

### Async Animation Generation

```python
import asyncio
from proof_sketcher.animator import ManimAnimator, AnimationConfig

async def generate_animations():
    # Configure animation
    anim_config = AnimationConfig(
        quality="high",
        style="modern",
        fps=60
    )
    
    # Initialize animator
    animator = ManimAnimator(config=anim_config)
    
    # Generate animation for proof sketch
    animation_response = await animator.animate_proof(sketch)
    
    if animation_response.success:
        print(f"Animation saved to: {animation_response.video_path}")
        print(f"Duration: {animation_response.duration} seconds")
    else:
        print(f"Animation failed: {animation_response.error}")

# Run async function
asyncio.run(generate_animations())
```

### Batch Processing

```python
from pathlib import Path
from proof_sketcher.core.batch import BatchProcessor

# Set up batch processing
processor = BatchProcessor(config)

# Find all Lean files
lean_files = list(Path("src").glob("**/*.lean"))

# Process in parallel
results = processor.process_files(
    lean_files,
    output_dir="output/batch",
    format="markdown",
    parallel=True,
    max_workers=4
)

# Summary
for file_path, result in results.items():
    if result.success:
        print(f"✓ {file_path}: {result.theorem_count} theorems")
    else:
        print(f"✗ {file_path}: {result.error}")
```

## Best Practices

### File Organization

```
project/
├── lean_files/
│   ├── basic/
│   └── advanced/
├── output/
│   ├── html/
│   ├── markdown/
│   └── pdf/
├── config/
│   ├── development.yaml
│   └── production.yaml
└── scripts/
    └── generate_docs.sh
```

### Configuration Management

```bash
# Development configuration
cat > config/development.yaml << EOF
generator:
  verbosity: detailed
  cache_responses: true
  
export:
  output_dir: output/dev
  include_source: true
  
debug: true
EOF

# Production configuration  
cat > config/production.yaml << EOF
generator:
  verbosity: concise
  cache_responses: true
  cache_ttl_hours: 48
  
export:
  output_dir: docs/
  include_source: false
  
performance:
  parallel_processing: true
  max_workers: 8
EOF
```

### Automation Scripts

```bash
#!/bin/bash
# scripts/generate_docs.sh

set -e

echo "Generating documentation for all theorem files..."

# Process each mathematical area
for area in group_theory real_analysis topology; do
    echo "Processing $area..."
    
    python -m proof_sketcher prove "src/${area}/" \
        --config config/production.yaml \
        --format all \
        --output "docs/${area}" \
        --verbose
        
    echo "✓ Completed $area"
done

echo "Building combined index..."
python scripts/build_index.py docs/

echo "Documentation generation complete!"
```

### Performance Optimization

1. **Use caching effectively**:
   ```yaml
   cache:
     enabled: true
     ttl_hours: 48  # Cache for 2 days
     max_size_mb: 1000  # 1GB cache limit
   ```

2. **Batch processing**:
   ```bash
   # Process multiple files together
   python -m proof_sketcher prove src/*.lean --format markdown
   ```

3. **Incremental updates**:
   ```bash
   # Only process changed files
   find src/ -name "*.lean" -newer last_run.timestamp \
     -exec python -m proof_sketcher prove {} \;
   ```

## Troubleshooting

### Common Issues

#### 1. "No theorems found in file"

**Cause**: File parsing failed or no valid theorem syntax

**Solutions**:
```bash
# Check Lean syntax
lean --check your_file.lean

# Verify file structure
python -m proof_sketcher list-theorems your_file.lean --verbose

# Check imports
head -10 your_file.lean  # Should show import statements
```

#### 2. "Claude command failed"

**Cause**: Claude CLI not installed or configured

**Solutions**:
```bash
# Reinstall Claude CLI
curl -fsSL https://claude.ai/install.sh | sh

# Check PATH
which claude

# Test Claude directly
claude --help
```

#### 3. "Animation generation failed"

**Cause**: Manim MCP server not available

**Solutions**:
```bash
# Install Manim MCP server
npm install -g @manim-mcp/server

# Start server manually
manim-mcp-server --port 3000

# Test connection
curl http://localhost:3000/health
```

#### 4. "Permission denied" errors

**Cause**: Output directory permissions

**Solutions**:
```bash
# Check permissions
ls -la output/

# Create with proper permissions
mkdir -p output/docs
chmod 755 output/docs

# Use different output directory
python -m proof_sketcher prove file.lean --output ~/Documents/proofs
```

### Debug Mode

```bash
# Enable comprehensive debugging
export PROOF_SKETCHER_DEBUG=true
export PROOF_SKETCHER_LOG_LEVEL=DEBUG

python -m proof_sketcher prove file.lean --verbose
```

### Log Analysis

```bash
# Check log files
tail -f ~/.proof-sketcher/logs/proof_sketcher.log

# Search for specific errors
grep -i "error\|failed" ~/.proof-sketcher/logs/proof_sketcher.log

# Monitor performance
grep -i "timing\|duration" ~/.proof-sketcher/logs/proof_sketcher.log
```

## Getting Help

- **Documentation**: Browse the `docs/` directory
- **Examples**: Check `examples/` for working code
- **Issues**: Report bugs on GitHub Issues
- **Discussions**: Join community discussions
- **API Reference**: See `docs/api/` for detailed API docs

## What's Next?

- Explore the [API Documentation](api.md) for advanced usage
- Check out [Configuration Guide](configuration.md) for detailed settings
- Read [Contributing Guidelines](../CONTRIBUTING.md) to contribute
- Browse [Examples](../examples/) for inspiration