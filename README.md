# Proof Sketcher (Alpha) - Post-Pivot

⚠️ **ALPHA SOFTWARE - MAJOR REFACTORING IN PROGRESS** ⚠️

**Current version**: 0.0.1-alpha2-dev
**Status**: Emergency refactoring after removing 8,000+ lines of animation code
**New Direction**: Will become a doc-gen4 enhancer, not a competitor

## Major Architecture Change (July 2025)

We've made a brutal but necessary decision: **remove all animation functionality** and pivot to enhancing doc-gen4 rather than competing with it.

### What We Removed 🗑️

- ❌ **6,470 lines** of animation code (Manim integration)
- ❌ **567 lines** of duplicate export system
- ❌ **~1,000 lines** of animation tests
- ❌ **Total: ~8,000 lines** of complex, fragile code

### Why This Change?

1. **Manim added 80% complexity for 20% value** - It worked ~20% of the time
2. **doc-gen4 already exists** - Why compete when we can enhance?
3. **Technical debt was killing us** - 60+ type errors, duplicate systems
4. **Wrong problem** - Users need better explanations, not buggy animations

## New Vision: doc-gen4 Enhancer

### What Proof Sketcher Will Become

A focused tool that:

1. **Integrates with doc-gen4** output
2. **Adds natural language explanations** to Lean documentation
3. **Provides simple static diagrams** (matplotlib only)
4. **Enhances readability** for newcomers to Lean

### Current State (Honest)

- ✅ Basic Lean parsing still works
- ✅ Export to HTML/Markdown still works
- ✅ Static diagram generation possible
- ❌ 60+ type errors need fixing
- ❌ Architecture needs complete overhaul
- ❌ Not ready for any real use

## Installation (Development Only)

```bash
# Clone repository
git clone https://github.com/yourusername/proof-sketcher.git
cd proof-sketcher

# Install in development mode
pip install -e .
```

## Basic Usage (Limited Functionality)

```bash
# Parse simple theorem
proof-sketcher prove simple.lean --offline --format markdown

# List theorems in file
proof-sketcher list-theorems file.lean
```

## Roadmap

### Phase 1: Cleanup (Current)

- [x] Remove animation system
- [x] Remove duplicate export system
- [ ] Fix all type errors
- [ ] Achieve 60% test coverage

### Phase 2: doc-gen4 Integration

- [ ] Research doc-gen4 API
- [ ] Build adapter layer
- [ ] Parse doc-gen4 output
- [ ] Inject explanations

### Phase 3: Rebuild

- [ ] Clean architecture
- [ ] Natural language generation via Claude
- [ ] Simple static diagrams only
- [ ] Export enhanced documentation

## For Developers

### Current Issues

1. **Type Safety**: 60+ mypy errors need fixing
2. **Test Coverage**: Only 24% (need 60%+)
3. **Architecture**: Needs complete redesign
4. **Dependencies**: Many can be removed

### How to Help

1. **Don't add features** - We're removing, not adding
2. **Fix type errors** - Run `mypy src/`
3. **Add tests** - Focus on core functionality
4. **Document honestly** - No false claims

## Why This Will Work Better

1. **Focused Scope**: Do one thing well
2. **Build on Success**: doc-gen4 handles the hard parts
3. **Real Value**: Natural language explanations help newcomers
4. **Maintainable**: Smaller, cleaner codebase

## Honest Timeline

- **Week 1**: Fix type errors, achieve 60% coverage
- **Week 2**: Research and prototype doc-gen4 integration
- **Week 3**: Rebuild with clean architecture
- **Week 4**: Beta release as doc-gen4 enhancer

## The Bottom Line

Proof Sketcher tried to do too much. We're cutting scope dramatically to deliver something actually useful. No more animations, no more competing with doc-gen4, just simple enhancements to make Lean documentation more accessible.

If you want animations, use Manim directly. If you want Lean documentation, use doc-gen4. If you want natural language explanations added to your Lean docs, wait for our beta.

---

**Contact**: <brightliu@college.harvard.edu>
**License**: MIT
**Status**: Under heavy refactoring - expect breaking changes
