# Known Issues (v0.0.1-alpha1)

This document provides a brutally honest assessment of known issues, limitations, and workarounds for Proof Sketcher alpha.

## 🔥 Critical Issues

### 1. Export System Duplication
**Severity**: High  
**Impact**: Architecture confusion, development inefficiency

**Description**: The codebase contains two separate export systems:
- `src/proof_sketcher/exporter/` - Comprehensive system with advanced features
- `src/proof_sketcher/export/` - Simple system created during development

**Problems**:
- Different APIs for similar functionality
- Duplicated effort and maintenance burden
- Confusion about which system to use/extend
- Inconsistent output quality between systems

**Workaround**: Use the simple `export` system for basic needs, `exporter` for advanced features.

**Fix Timeline**: Alpha 2 (consolidation required)

### 2. Parser Limitations
**Severity**: High  
**Impact**: Most real Lean code fails to parse

**Description**: Parser only handles the most basic Lean theorem syntax.

**What Fails**:
- Complex mathlib theorems
- Advanced tactics (beyond basic `rw`, `simp`)
- Mutual recursive definitions
- Complex type signatures
- Most real-world Lean code

**Example of What Breaks**:
```lean
-- This will likely fail
theorem complex_theorem (α : Type*) [Fintype α] (f : α → ℕ) :
  ∃ x y, x ≠ y ∧ f x = f y := by
  by_contra h
  -- Complex proof here
```

**Workaround**: Use only simple, basic theorems like:
```lean
-- This might work
theorem simple : 1 + 1 = 2 := rfl
```

**Fix Timeline**: Ongoing - requires significant parser rewrite

### 3. Memory Usage Issues
**Severity**: High  
**Impact**: System becomes unusable with larger files

**Description**: 
- Entire files loaded into memory (no streaming)
- No proper cleanup of intermediate objects
- Memory usage grows during batch processing
- May crash on files >1000 lines

**Symptoms**:
- Slow processing after multiple files
- High memory usage in activity monitor
- Eventual crashes on large batches

**Workaround**: 
- Restart application between large operations
- Process files individually rather than in batches
- Keep Lean files under 100 lines

**Fix Timeline**: Alpha 3 (requires streaming implementation)

## ⚠️ Major Issues

### 4. Animation System Fragility
**Severity**: Medium-High  
**Impact**: Animations often fail, but system degrades gracefully

**Description**: Manim integration is fragile and environment-dependent.

**Common Failures**:
- Manim not installed or misconfigured
- LaTeX not available for math rendering
- Platform-specific Manim issues
- Timeout failures on complex animations

**Success Rate**: ~20% (animation), ~95% (static fallback)

**Workaround**: System automatically falls back to static diagrams. No user action needed.

**Fix Timeline**: Alpha 2 (improved Manim detection and installation)

### 5. Limited Error Handling
**Severity**: Medium  
**Impact**: Poor user experience when things go wrong

**Description**: Error messages are often unhelpful or missing.

**Problems**:
- Cryptic error messages
- No recovery suggestions
- Silent failures in some cases
- Stack traces exposed to users

**Example Bad Error**:
```
AttributeError: 'TheoremInfo' object has no attribute 'file_path'
```

**Workaround**: Check logs for more details, restart if stuck.

**Fix Timeline**: Alpha 2 (comprehensive error handling rewrite)

### 6. Performance Issues
**Severity**: Medium  
**Impact**: Slow processing times

**Current Performance**:
- Simple theorem: 5-15 seconds
- Complex parsing: 30+ seconds  
- Batch processing: Linear scaling (no optimization)

**Bottlenecks**:
- No caching of parsed results
- Inefficient file I/O
- Repeated template compilation
- No parallel processing

**Workaround**: Process files individually, avoid batch operations.

**Fix Timeline**: Alpha 3 (performance optimization phase)

## 🐛 Medium Issues

### 7. PDF Export Dependencies
**Severity**: Medium  
**Impact**: PDF export fails without LaTeX

**Description**: PDF export requires full LaTeX installation.

**Problems**:
- Complex installation requirements
- Platform-specific LaTeX issues
- Large dependency footprint
- Poor error messages when LaTeX missing

**Workaround**: Use HTML or Markdown export instead.

**Fix Timeline**: Alpha 2 (consider HTML-to-PDF alternative)

### 8. Template System Limitations
**Severity**: Medium  
**Impact**: Limited customization options

**Description**: Templates are hardcoded with limited customization.

**Limitations**:
- No user-customizable templates
- Limited theme options
- Hardcoded CSS styling
- No plugin system

**Workaround**: Modify CSS files directly (not recommended).

**Fix Timeline**: Beta 1 (proper template system)

### 9. Configuration Management
**Severity**: Medium  
**Impact**: Limited user control over behavior

**Description**: Configuration options are scattered and inconsistent.

**Problems**:
- No central configuration file
- Command-line options incomplete
- Some settings hardcoded
- No environment variable support

**Workaround**: Use command-line flags for available options.

**Fix Timeline**: Alpha 2 (unified configuration system)

## 🔧 Minor Issues

### 10. Test Coverage Gaps
**Severity**: Low-Medium  
**Impact**: Potential bugs in untested code paths

**Current Coverage**: ~38% (improved from 11%)

**Gaps**:
- Edge cases in parser
- Error handling paths
- Large file processing
- Concurrent operations

**Workaround**: Use cautiously, report any unexpected behavior.

**Fix Timeline**: Ongoing (target 70% by Beta 1)

### 11. Documentation Gaps
**Severity**: Low  
**Impact**: Harder to use and extend

**Missing Documentation**:
- User guide for advanced features
- API reference for developers
- Deployment instructions
- Integration examples

**Workaround**: Read source code, check tests for examples.

**Fix Timeline**: Alpha 2 (comprehensive documentation)

### 12. Logging Inconsistencies
**Severity**: Low  
**Impact**: Difficult debugging

**Problems**:
- Inconsistent log levels
- No structured logging
- Poor log message formatting
- No log rotation

**Workaround**: Use `--verbose` flag for more details.

**Fix Timeline**: Alpha 2 (structured logging system)

## 🚫 Not Yet Implemented

### Planned Features (Not Working)
- **Real AI Integration**: Only basic template generation works
- **Batch Processing**: Exists but unreliable
- **Caching System**: Basic implementation, not production-ready
- **Plugin System**: Not implemented
- **Web Interface**: Command-line only
- **Database Storage**: File-based only

### Missing Production Features
- **Monitoring**: No metrics or health checks
- **Deployment**: No production deployment support
- **Security**: Basic input validation only
- **Scalability**: Single-threaded, no clustering
- **Backup/Recovery**: No data persistence strategy

## 🔄 Workarounds Summary

### For Users
1. **Keep files simple**: Use basic Lean syntax only
2. **Stay small**: Files under 100 lines work best
3. **Use offline mode**: Avoid API dependencies
4. **Prefer HTML/Markdown**: Avoid PDF export
5. **Restart frequently**: If memory usage grows

### For Developers
1. **Use simple export system**: Avoid the complex exporter module
2. **Test incrementally**: Don't rely on comprehensive test suite
3. **Check logs**: Error messages often in logs, not user output
4. **Fork carefully**: Architecture may change significantly

## 🎯 Priority Fix Order

### Alpha 2 (Next Release)
1. Consolidate export systems
2. Improve error handling and messages  
3. Add basic caching for performance
4. Create proper configuration system

### Alpha 3 (Performance Focus)
1. Implement streaming for large files
2. Add parallel processing
3. Optimize memory usage
4. Add benchmarking and monitoring

### Beta 1 (Stability Focus)
1. Comprehensive test coverage (70%+)
2. Production-ready error handling
3. User documentation and guides
4. Template customization system

## 📞 Reporting Issues

### Before Reporting
1. Check this document for known issues
2. Try with a simple example first
3. Check if it's a configuration problem
4. Look at application logs

### What to Include
1. **System information**: OS, Python version, dependencies
2. **Minimal reproduction**: Smallest example that fails
3. **Full error output**: Including stack traces
4. **Expected vs actual behavior**
5. **Workarounds tried**

### Where to Report
- GitHub Issues: [Project Repository](https://github.com/yourusername/proof-sketcher/issues)
- Include label: `alpha-feedback`

## ⚖️ Risk Assessment

### Use This Software If:
- You're experimenting with simple Lean theorems
- You understand it's alpha software
- You can work around limitations
- You want to contribute to development

### Don't Use This Software If:
- You need reliable, production-ready tools
- You're working with complex Lean projects
- You can't tolerate frequent issues
- You need comprehensive documentation

---

**Last Updated**: 2025-07-09  
**Document Version**: 1.0  
**Software Version**: 0.0.1-alpha1  

**Remember**: This is alpha software. If it works, that's great. If it doesn't, that's expected. Report issues to help improve the next version.