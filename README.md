# Proof Sketcher

**Version**: 0.1.0-mvp
**Status**: Minimal Viable Product - Basic functionality restored

## What It Actually Does

Proof Sketcher parses Lean 4 files and generates natural language explanations of theorems using template-based generation. No AI required, no animations, just simple explanations.

**Working Features:**

- ✅ Parse Lean files to extract theorems
- ✅ Generate basic explanations (offline/template-based)
- ✅ Export to Markdown format
- ✅ Simple command-line interface

**Not Working Yet:**

- ❌ AI-powered explanations (offline only)
- ❌ Visualizations or diagrams
- ❌ doc-gen4 integration
- ❌ HTML/PDF export
- ❌ Advanced parsing features

## Installation

```bash
# Clone repository
git clone https://github.com/yourusername/proof-sketcher.git
cd proof-sketcher

# Install in development mode
pip install -e .
```

## Quick Start

### Test the Pipeline

```bash
# Run the integration test to verify everything works
python test_mvp_pipeline.py
```

### Basic Usage

```python
from proof_sketcher.parser import LeanParser
from proof_sketcher.generator import AIGenerator
from proof_sketcher.exporter import MarkdownExporter

# Parse Lean file
parser = LeanParser()
result = parser.parse_file("example.lean")

# Generate explanation
generator = AIGenerator()  # Uses offline mode
sketch = generator.generate_offline(result.theorems[0])

# Export to markdown
exporter = MarkdownExporter()
content = exporter.export(sketch, "output.md")
```

## Example Output

Input theorem:

```lean
theorem add_zero (n : Nat) : n + 0 = n := by simp
```

Generated explanation:

```markdown
# Theorem: add_zero

## Statement
`n + 0 = n`

## Explanation
This theorem establishes an equality relationship between mathematical
expressions. It involves establishing an equality between mathematical
expressions.

## Proof Steps
### Step 1: Set up the proof context
We begin by introducing the mathematical objects we need to work with.

### Step 2: Simplify the expression
The result follows directly from simplification rules.

## Conclusion
This completes the proof of add_zero. The proof is straightforward,
requiring only a few logical steps.
```

## Current Architecture

After removing 8,000+ lines of animation code:

```
src/proof_sketcher/
├── parser/
│   ├── simple_parser.py    # Basic theorem extraction
│   └── models.py           # Data models
├── generator/
│   ├── simple_generator.py # Template-based generation
│   └── offline.py          # Offline templates
└── exporter/
    └── simple_markdown.py  # Basic markdown export
```

## Limitations

1. **Parser**: Simple regex-based, may miss complex theorems
2. **Generator**: Template-only, repetitive explanations
3. **Export**: Basic markdown, no fancy formatting
4. **Scale**: Not optimized for large projects

## Roadmap to Recovery

### Phase 8: Expand Export Formats (Next)

- [ ] Add basic HTML export
- [ ] Improve markdown formatting
- [ ] Add batch processing

### Phase 9: Better Generation

- [ ] Integrate Claude API (optional)
- [ ] Improve templates
- [ ] Add mathematical context

### Phase 10: Real Parser

- [ ] Use Lean's actual AST
- [ ] Handle complex proofs
- [ ] Extract more metadata

### Phase 11: doc-gen4 Integration

- [ ] Parse doc-gen4 output
- [ ] Inject explanations
- [ ] Generate enhanced docs

## Why This Rewrite?

We removed 8,000+ lines of broken animation code and started over with the simplest thing that could work. This MVP proves the core concept: we can parse Lean, generate explanations, and export them. Everything else builds on this foundation.

## Contributing

This is a fresh start. The codebase is minimal and focused. Before adding features:

1. Run `test_mvp_pipeline.py` - it must pass
2. Keep it simple - no complex features yet
3. Document what actually works - no aspirations

## License

MIT License - See LICENSE file

---

**Contact**: <brightliu@college.harvard.edu>
**Note**: This is a complete rewrite. Previous versions with animation support have been deprecated.
