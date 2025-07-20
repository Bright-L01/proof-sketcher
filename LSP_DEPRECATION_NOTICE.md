# LSP Integration Deprecation Notice

## Summary

The LSP (Language Server Protocol) integration in proof-sketcher has been **deprecated and disabled** due to critical performance and functionality issues.

## Issues Identified

1. **Zero Theorem Extraction**: The LSP client extracts 0 theorems from any Lean file, making it completely non-functional for its intended purpose.

2. **Performance**: The LSP client is approximately **1000x slower** than the simple regex-based parser, with no benefits to show for the performance cost.

3. **Broken Implementation**: The LSP communication appears to be fundamentally broken, with no working implementation achieved despite the complex codebase.

## Changes Made

1. **Default Parser Changed**: `LeanParser` now defaults to `SimpleLeanParser` instead of `HybridLeanParser`

2. **Deprecation Warnings Added**: All LSP-related classes now emit deprecation warnings when instantiated:
   - `LeanLSPClient`
   - `HybridLeanParser`
   - `SemanticTheoremInfo`

3. **Configuration Updated**: The `use_lsp` flag in `ParserConfig` is forced to `False` with a warning if set to `True`

4. **Tests Marked as Deprecated**: LSP-related tests are marked as deprecated or skipped

5. **Documentation Updated**: Module docstrings clearly indicate the deprecation status

## Recommendation

**Always use `SimpleLeanParser` for all parsing needs.** It is:
- Fast and efficient
- Fully functional
- Well-tested
- Extracts theorems correctly

## Code Examples

### Before (Deprecated)
```python
from proof_sketcher.parser import LeanParser  # Was HybridLeanParser
parser = LeanParser()  # Would try to use LSP
```

### After (Recommended)
```python
from proof_sketcher.parser import SimpleLeanParser
parser = SimpleLeanParser()  # Direct, fast, working parser
```

Or use the updated default:
```python
from proof_sketcher.parser import LeanParser  # Now SimpleLeanParser
parser = LeanParser()  # Uses SimpleLeanParser directly
```

## Future Considerations

The LSP code is kept in the codebase for historical reference and potential future fixes. If a working LSP implementation is achieved in the future, it could be re-enabled after thorough testing proves it can:

1. Successfully extract theorems
2. Provide meaningful semantic analysis
3. Perform at acceptable speeds
4. Add value beyond the simple parser

Until then, the simple parser remains the only supported parsing method.

## Performance Comparison

| Metric | Simple Parser | LSP Parser |
|--------|--------------|------------|
| Speed | ~10ms per file | ~10,000ms per file |
| Theorems Extracted | All theorems | 0 theorems |
| Reliability | High | Non-functional |
| Dependencies | None | Lean 4 LSP server |
| Status | Fully Working | Broken |
