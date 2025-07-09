# Proof Sketcher (Alpha)

⚠️ **ALPHA SOFTWARE - NOT PRODUCTION READY** ⚠️

**Current version**: 0.0.1-alpha1  
**Test coverage**: ~38% (improved but still limited)  
**Known issues**: See [KNOWN_ISSUES.md](KNOWN_ISSUES.md)

## What It Actually Does (Updated Reality)

Proof Sketcher is an experimental tool that attempts to generate documentation for simple Lean 4 theorems. After recent development work, some features now work better, but significant limitations remain.

### What Currently Works ✅

- ✅ **Animation System**: 3-tier fallback (Manim → matplotlib → placeholder)
- ✅ **Export System**: HTML, Markdown, and PDF export (with caveats)
- ✅ **Basic Parsing**: Simple Lean 4 theorem syntax parsing
- ✅ **CLI Interface**: Functional command-line interface
- ✅ **Offline Mode**: Template-based explanations (no AI required)
- ✅ **Error Handling**: Graceful degradation (won't crash on animation failures)

### What Doesn't Work Yet ❌

- ❌ **Complex Lean Parsing**: Only handles the most basic theorem syntax
- ❌ **Reliable Animation**: Manim integration works only when properly installed
- ❌ **Infrastructure Issues**: Contains duplicate export systems (see below)
- ❌ **Performance**: Memory issues with large files
- ❌ **Production Features**: No caching, optimization, or proper error recovery
- ❌ **Real AI Integration**: Limited AI integration capabilities

## Critical Infrastructure Issues (Honest Assessment)

### Export System Duplication
**Problem**: The codebase contains **TWO separate export systems**:

1. **`src/proof_sketcher/exporter/`** - Comprehensive system with:
   - Full template management
   - Doc-gen4 compatibility  
   - Asset optimization
   - Advanced features

2. **`src/proof_sketcher/export/`** - Simplified system with:
   - Basic HTML/Markdown/PDF export
   - Simple templates
   - Limited features

**Impact**: This duplication causes confusion and wastes development effort.

**Current Status**: Both systems work but should be consolidated.

### Model Changes
**Recent Change**: Added `file_path`, `start_line`, `end_line` to `TheoremInfo` model to support export functionality.

**Impact**: This may affect existing code that uses `TheoremInfo` objects.

## Installation (Alpha Testing Only)

**Requirements:**
- Python 3.8+
- Optional: Lean 4 installation
- Optional: Manim for animations (may not work)
- Optional: LaTeX for PDF export

```bash
# Clone repository (not on PyPI)
git clone https://github.com/yourusername/proof-sketcher.git
cd proof-sketcher

# Install in development mode
pip install -e .

# Install optional dependencies (may fail)
pip install manim matplotlib jinja2
```

## Basic Usage (What Actually Works)

```bash
# Simple theorem (likely to work)
proof-sketcher prove simple.lean --offline

# Specify output format
proof-sketcher prove simple.lean --format html --output ./docs/

# Test animation system (falls back gracefully)
proof-sketcher prove simple.lean --format html
```

### Example That Should Work

Create `simple.lean`:
```lean
theorem add_zero (n : ℕ) : n + 0 = n := by
  rw [Nat.add_zero]
```

Run:
```bash
proof-sketcher prove simple.lean --offline --format html
```

**Expected result**: HTML file with static diagram visualization.

## Current Capabilities (Realistic Assessment)

### Animation System
- **Manim detection**: Automatically checks if Manim is available
- **Graceful fallback**: Animation → Static diagram → Placeholder file
- **Never fails**: Always produces some visualization
- **Timeout protection**: Won't hang indefinitely

### Export System
- **HTML**: Professional templates with MathJax support
- **Markdown**: GitHub-compatible with media embedding
- **PDF**: LaTeX-based (requires LaTeX installation)
- **Templates**: Basic template system with CSS styling

### Parser
- **Basic theorems**: Handles simple theorem statements
- **Limited syntax**: Fails on complex mathlib constructs
- **No tactics**: Limited tactic support
- **Small files**: Works best with simple examples

## Known Issues (Critical)

### High Priority
1. **Export system duplication**: Two separate systems need consolidation
2. **Parser limitations**: Only handles basic Lean syntax
3. **Memory usage**: No streaming, loads entire files
4. **Animation reliability**: Manim integration fragile
5. **Limited testing**: Many edge cases untested

### Infrastructure Issues
- **Code duplication**: Export vs exporter modules
- **Inconsistent APIs**: Different interfaces for similar functionality
- **Limited documentation**: Many modules undocumented
- **Technical debt**: Multiple architectural patterns mixed

### Limitations
- **Complex Lean code**: Most real theorems will fail to parse
- **Performance**: Slow processing, high memory usage
- **Error messages**: Poor user feedback on failures
- **Configuration**: Limited customization options

## What Will Probably Fail

- Theorems with complex tactics
- Large Lean files (>500 lines)
- Advanced mathlib constructs
- Batch processing large numbers of files
- PDF export (if LaTeX not properly configured)

## Workarounds

- **Use simple theorems**: Stick to basic syntax
- **Small files**: Keep under 100 lines
- **Offline mode**: Avoid API dependencies
- **HTML/Markdown**: Avoid PDF export unless needed
- **Restart frequently**: If memory usage grows

## Development Status

**Current phase**: Alpha development with working basic features

**Recent progress:**
- ✅ Animation system implemented with fallback
- ✅ Export system functional (though duplicated)
- ✅ Basic end-to-end pipeline working
- ✅ Test coverage improved to ~38%

**Next priorities:**
1. Consolidate export systems
2. Improve parser for more Lean syntax
3. Add proper error handling
4. Optimize memory usage
5. Create user documentation

## Contributing (Areas That Need Help)

### Critical Issues
1. **Consolidate export systems**: Merge duplicate functionality
2. **Parser improvements**: Support more Lean syntax
3. **Performance optimization**: Reduce memory usage
4. **Error handling**: Better user feedback
5. **Documentation**: User guides and examples

### Infrastructure
- **Testing**: Increase coverage beyond 38%
- **Code quality**: Address remaining linting issues
- **Architecture**: Resolve design inconsistencies
- **Performance**: Add benchmarking and optimization

## Architecture Status

### Recent Improvements
- ✅ Animation system with proper fallback chain
- ✅ Export templates and styling
- ✅ Basic error handling in key components
- ✅ Test coverage for new features

### Remaining Issues
- ⚠️ Export system duplication (needs consolidation)
- ⚠️ Limited parser capabilities
- ⚠️ No proper logging strategy
- ⚠️ Mixed architectural patterns
- ⚠️ Hardcoded configuration

## Testing

```bash
# Run all tests
pytest

# Run specific test suites
pytest tests/test_animation.py      # Animation system tests
pytest tests/test_exporters.py     # Export system tests  
pytest tests/test_end_to_end.py    # End-to-end pipeline tests

# Current status: 35+ new tests added for Phase 3 features
```

## Support and Expectations

**Support**: Limited - this is alpha software  
**Bug reports**: Welcome but may not be addressed quickly  
**Production use**: **Absolutely not recommended**  
**Learning tool**: Good for understanding the problem space  

## Roadmap (Realistic)

- **Alpha 2**: Consolidate export systems, improve parser
- **Alpha 3**: Performance optimization, better error handling  
- **Beta 1**: Stable for simple use cases
- **1.0**: Maybe, if development continues

## License

MIT License - Use at your own risk.

## Honest Disclaimer

This software:
- ✅ Works for simple examples
- ✅ Has reasonable test coverage for new features
- ✅ Won't crash on animation failures
- ❌ Can't handle complex Lean code
- ❌ Has architecture issues (duplicate systems)
- ❌ Uses too much memory
- ❌ Is not ready for real use

**Use for**: Learning, experimentation, testing basic concepts  
**Don't use for**: Anything important, production systems, complex Lean projects

---

**Last Updated**: 2025-07-09  
**Development Status**: Alpha - Core features work but limited scope  
**Recommendation**: Useful for simple examples, not ready for real work