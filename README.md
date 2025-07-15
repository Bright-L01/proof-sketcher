# Proof Sketcher

**Version**: 0.1.1-actual-mvp
**Status**: Functional MVP - Core pipeline working

## What It Actually Does

Proof Sketcher parses Lean 4 files and generates natural language explanations of theorems using template-based generation. Now with modern HTML export and MathJax 4.0 support.

**Working Features:**

- ✅ Parse Lean files to extract theorems and lemmas
- ✅ Generate explanations (offline/template-based)
- ✅ Export to Markdown format
- ✅ Export to HTML with MathJax 4.0 support
- ✅ Batch processing for multiple files
- ✅ Auto-generated index files
- ✅ Mathematical notation rendering

**Not Working Yet:**

- ❌ AI-powered explanations (offline only)
- ❌ doc-gen4 integration
- ❌ PDF export
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
from proof_sketcher.exporter import MarkdownExporter, HTMLExporter

# Parse Lean file
parser = LeanParser()
result = parser.parse_file("example.lean")

# Generate explanation
generator = AIGenerator()  # Uses offline mode
sketch = generator.generate_offline(result.theorems[0])

# Export to markdown
markdown_exporter = MarkdownExporter()
markdown_content = markdown_exporter.export(sketch, "output.md")

# Export to HTML with MathJax
html_exporter = HTMLExporter()
html_content = html_exporter.export(sketch, "output.html")
```

### Batch Processing

```python
from proof_sketcher.parser import LeanParser
from proof_sketcher.generator import AIGenerator
from proof_sketcher.exporter import BatchExporter

# Parse multiple theorems
parser = LeanParser()
result = parser.parse_file("theorems.lean")

# Batch export to multiple formats
batch_exporter = BatchExporter()
files = batch_exporter.export_from_theorems(
    result.theorems,
    generator=AIGenerator(),
    formats=["markdown", "html"],
    create_index=True
)
# Creates: markdown/*.md, html/*.html, README.md, index.html
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

Clean MVP architecture with modern export capabilities:

```
src/proof_sketcher/
├── parser/
│   ├── simple_parser.py    # Lean theorem extraction (multiline support)
│   └── models.py           # Pydantic data models
├── generator/
│   ├── simple_generator.py # Template-based generation  
│   └── offline.py          # Offline templates with context
└── exporter/
    ├── simple_markdown.py  # Markdown export
    ├── simple_html.py      # HTML export with MathJax 4.0
    └── batch_processor.py  # Batch export with indexing
```

## Limitations

1. **Parser**: Simple regex-based, may miss complex theorems
2. **Generator**: Template-only, repetitive explanations
3. **Export**: Basic markdown, no fancy formatting
4. **Scale**: Not optimized for large projects

## Roadmap to Full Features

### Phase 8: Enhanced Export ✅ (Completed)

- ✅ Add HTML export with MathJax 4.0
- ✅ Improve markdown formatting
- ✅ Add batch processing with indexing

### Phase 9: Better Generation (Next)

- [ ] Integrate Claude API (optional)
- [ ] Improve templates with mathematical context
- [ ] Add difficulty assessment
- [ ] Better prerequisite detection

### Phase 10: Real Parser

- [ ] Use Lean's actual AST via LSP
- [ ] Handle complex proofs with tactics
- [ ] Extract more metadata (dependencies, imports)

### Phase 11: doc-gen4 Integration

- [ ] Parse doc-gen4 output
- [ ] Inject explanations into existing docs
- [ ] Generate enhanced documentation

## Why This Rewrite?

We removed 8,000+ lines of broken animation code and started over with the simplest thing that could work. This MVP proves the core concept works and provides a solid foundation for future features. The current implementation handles real Lean syntax patterns and provides modern export formats.

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
