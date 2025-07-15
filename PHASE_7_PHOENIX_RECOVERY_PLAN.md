# Phase 7: Project Phoenix - Complete Recovery Plan

## 🔥 Rising from the Ashes

**Date**: July 15, 2025
**Project State**: Critical but Salvageable
**Recovery Method**: Brutal Simplification

## 📊 Executive Summary

After analyzing 1000+ lines of code, reading industry best practices, and examining successful projects, the verdict is clear:

**The Problem**: Too much complexity, too little verification
**The Solution**: Delete 80%, fix 20%, prove it works
**Time Required**: 7 days to working MVP

## 🎯 Core Recovery Strategy

### The One Rule
**"Nothing new until ONE path works end-to-end"**

### The MVP Path
```
Lean File → Parse → Generate (Offline) → Export Markdown
```

That's it. Everything else is noise until this works.

## 📋 Day-by-Day Execution Plan

### Day 1-2: The Great Purge
**Goal**: Reduce project to essential files only

**Delete List**:
```bash
# Reports and documentation (keep only essential)
rm PHASE_*.md
rm *_REPORT.md
rm *_SUMMARY.md
rm MILESTONE_*.md
rm TESTING_*.md
rm PRODUCTION_*.md
rm TECHNICAL_DEBT.md
rm CODE_QUALITY_*.md
rm PROJECT_*.md
rm SECURITY_*.md
rm RELEASE_*.md
rm KNOWN_ISSUES.md
rm EMERGENCY_*.md
rm PIVOT_*.md
rm DOCGEN4_*.md
rm ALPHA_*.md
rm PARSER_*.md

# Test scripts and experiments
rm *test*.py  # except tests/ directory
rm demo_*.py
rm benchmark*.py
rm verify*.py
rm execute_*.py
rm diagnose_*.py
rm cleanup_*.py
rm find_*.py
rm check_*.py
rm run_*.py
rm phase*.py
rm emergency_*.py
rm comprehensive_*.py
rm minimal_working_example.py  # Will recreate

# Temporary files and outputs
rm *.png
rm -rf animations/
rm -rf demo_*/
rm -rf output/
rm -rf htmlcov/
rm -rf temp/
rm -rf dist/
rm -rf benchmark_results/
rm -rf performance_results/

# Duplicates (keep only the main ones)
rm src/proof_sketcher/generator/ai_generator_fixed.py
rm src/proof_sketcher/cli/commands/batch_new.py
rm src/proof_sketcher/parser/mathlib_notation_optimized.py

# Lists and temporary text files
rm *.txt
rm *.json  # except package files
```

**Keep List**:
- Core source in `src/`
- Essential configs (`pyproject.toml`, `.gitignore`, etc.)
- `README.md` (will rewrite)
- `LICENSE`, `CODE_OF_CONDUCT.md`
- `tests/` directory (will clean up)
- `examples/` directory (will simplify)
- `docs/` directory (will update)

### Day 3: Fix Core Path
**Goal**: Make the basic pipeline work

1. **Fix Parser** (`src/proof_sketcher/parser/lean_parser.py`)
   - Ensure `parse_file()` returns `ParseResult` with theorems
   - Handle basic theorem extraction
   - Remove complex optimization code

2. **Fix Generator** (`src/proof_sketcher/generator/ai_generator.py`)
   - Ensure offline mode works
   - Generate simple explanations
   - Remove animation references

3. **Fix Exporter** (`src/proof_sketcher/exporter/markdown.py`)
   - Export basic markdown
   - Remove complex formatting
   - Ensure file writes correctly

### Day 4: Create Single Integration Test
**Goal**: Prove the pipeline works

Create `test_mvp_pipeline.py`:
```python
def test_minimal_pipeline():
    # 1. Create simple Lean file
    # 2. Parse it
    # 3. Generate offline explanation
    # 4. Export to markdown
    # 5. Verify output exists and contains expected content
```

### Day 5: Update Documentation
**Goal**: Make docs match reality

1. **Rewrite README.md**
   - What it ACTUALLY does (not aspirations)
   - How to ACTUALLY use it
   - What ACTUALLY works

2. **Create QUICKSTART.md**
   - One working example
   - Step-by-step instructions
   - Expected output

### Day 6: Validate with Real Files
**Goal**: Ensure it works with actual Lean code

Test with 5 real Lean files:
1. Simple theorem (addition)
2. Theorem with tactics
3. Theorem with imports
4. Mathlib theorem
5. Complex proof

Document results honestly.

### Day 7: Package and Plan Next Phase
**Goal**: Clean release and future roadmap

1. **Final Cleanup**
   - Remove any remaining cruft
   - Ensure all tests pass
   - Update version to 0.1.0-mvp

2. **Create Roadmap**
   - Phase 8: Add HTML export
   - Phase 9: Improve generation
   - Phase 10: Add caching
   - Phase 11: doc-gen4 integration

## 🎯 Success Criteria

### Week 1 Deliverables
- [ ] < 100 total files in project
- [ ] Parser works with real Lean files
- [ ] Generator creates basic explanations
- [ ] Exporter produces valid markdown
- [ ] One integration test passes
- [ ] README reflects reality
- [ ] 5 working examples

### What Success Looks Like
```bash
$ proof-sketcher prove examples/simple.lean --offline
Parsing examples/simple.lean... ✓
Generating explanation... ✓
Exporting to markdown... ✓
Output: output/simple.md

$ cat output/simple.md
# Theorem: add_zero

**Statement**: For any natural number n, n + 0 = n

**Explanation**: This theorem states that adding zero to any natural
number leaves it unchanged. This is a fundamental property of addition
and serves as one of the defining characteristics of zero as the
additive identity.

**Proof**: The proof uses simplification (simp tactic) which applies
the definition of addition on natural numbers.
```

## 🚫 What We're NOT Doing

1. **No Feature Creep**
   - No animations
   - No complex visualizations
   - No multiple formats (yet)
   - No optimization (yet)
   - No doc-gen4 (yet)

2. **No Perfectionism**
   - Basic is fine
   - Working is better than perfect
   - Simple explanations are enough
   - Markdown only for now

3. **No Scope Expansion**
   - One input format (Lean files)
   - One processing path (parse → generate → export)
   - One output format (Markdown)
   - One test that proves it works

## 📊 Risk Mitigation

### High Risk Areas
1. **Parser might be fundamentally broken**
   - Mitigation: Use subprocess to call lean directly
   - Fallback: Parse file text with regex

2. **Generator might have hidden dependencies**
   - Mitigation: Use purely offline generation
   - Fallback: Template-based generation

3. **Too much coupling between components**
   - Mitigation: Test each component in isolation first
   - Fallback: Rewrite minimal versions

### Contingency Plans
- If parser can't be fixed in 1 day: Write minimal parser
- If generator is too complex: Use template system
- If nothing works: Start fresh with 100-line prototype

## 🏁 Final Notes

### Why This Will Work
1. **Focused Scope**: One path, no distractions
2. **Brutal Simplicity**: Delete first, add later
3. **Proof-Driven**: Nothing assumed, everything verified
4. **Industry Wisdom**: Following "broken window" theory

### Why Previous Attempts Failed
1. **Too Ambitious**: Animations + NLP + Multiple formats
2. **No Verification**: Assumed things worked
3. **Documentation Drift**: Docs didn't match code
4. **Complexity Spiral**: Added features before basics worked

### The Phoenix Principle
Like the mythical phoenix, this project must burn away everything non-essential to be reborn. What emerges will be simpler, focused, and actually functional.

## ✅ Commitment

This plan represents 7 days of focused work to create:
- One working pipeline
- One verified test
- One honest README
- Five working examples

No more, no less. Everything else comes after we prove the core works.

**Let's begin the resurrection.**
