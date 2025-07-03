# Performance Benchmarks

This directory contains performance benchmarks for Proof Sketcher to evaluate performance characteristics with files of various sizes and complexity.

## Benchmark Suite

### Test Categories

1. **Tiny** (3 theorems) - Basic functionality test
2. **Small** (10 theorems) - Small file performance
3. **Medium Small** (25 theorems) - Moderate file performance
4. **Medium** (50 theorems) - Medium file performance  
5. **Medium Large** (100 theorems) - Large-ish file performance
6. **Large** (200 theorems) - Large file performance
7. **Extra Large** (400 theorems) - Very large file performance

### Metrics Measured

- **Parse Time**: Time to parse Lean file and extract theorems
- **Generation Time**: Time to generate proof sketches (offline mode)
- **Export Time**: Time to export to HTML format
- **Total Processing Time**: End-to-end processing time
- **Memory Usage**: Peak and average memory consumption
- **Throughput**: Theorems processed per second
- **Cache Effectiveness**: Cache hits vs misses
- **Scaling Factors**: How performance scales with file size

### Performance Characteristics

The benchmarks test several important performance aspects:

1. **Linear Scaling**: Does performance scale linearly with file size?
2. **Memory Efficiency**: How much memory is required per theorem?
3. **Cache Effectiveness**: Does caching improve performance for repeated operations?
4. **Error Handling**: How does the system perform when encountering errors?
5. **Resource Limits**: What are the practical limits for large files?

## Running Benchmarks

### Quick Benchmark
```bash
python benchmarks/performance_benchmarks.py --quick
```

### Full Benchmark Suite
```bash
python benchmarks/performance_benchmarks.py --include-large
```

### Save Results to File
```bash
python benchmarks/performance_benchmarks.py --output benchmark_results.json
```

## Expected Performance Targets

Based on system capabilities and complexity:

### Processing Speed
- **Target**: 5-50 theorems/second (depending on complexity)
- **Minimum**: 1 theorem/second for complex theorems
- **Optimal**: 20+ theorems/second for simple theorems

### Memory Usage
- **Target**: < 50MB peak memory for 100 theorems
- **Maximum**: < 500MB for 1000+ theorems
- **Efficiency**: < 1MB per theorem on average

### Scaling Characteristics
- **Linear Time**: Processing time should scale linearly with theorem count
- **Sublinear Memory**: Memory should scale sublinearly due to caching
- **Efficiency Loss**: < 10% efficiency degradation per 100 theorems

## Benchmark Results Analysis

### Performance Trends to Monitor

1. **Parsing Performance**
   - Should be fast and consistent
   - Memory usage should be minimal
   - Errors should be gracefully handled

2. **Generation Performance**
   - Offline mode should be very fast
   - Cache hits should improve performance significantly
   - Memory usage should be reasonable

3. **Export Performance**
   - HTML export should be fast
   - File I/O should not be a bottleneck
   - Template rendering should be efficient

### Warning Signs

- **Exponential Time Growth**: Processing time growing faster than linearly
- **Memory Leaks**: Memory usage not releasing after processing
- **High Error Rates**: Frequent failures on valid input
- **Poor Cache Utilization**: Low cache hit rates
- **Disk I/O Bottlenecks**: Slow file operations

## System Requirements

### Minimum Requirements
- Python 3.9+
- 4GB RAM
- 1GB free disk space
- Modern multi-core CPU

### Recommended for Large Files
- Python 3.11+
- 16GB RAM
- 10GB free disk space
- High-performance SSD
- Multi-core CPU (8+ cores)

## Interpreting Results

### Good Performance Indicators
✅ Consistent processing rates across file sizes
✅ Linear time scaling with theorem count
✅ High cache hit rates for repeated operations
✅ Low memory usage per theorem
✅ No errors on valid input

### Performance Issues
⚠️ Exponential time growth with file size
⚠️ High memory usage (>10MB per theorem)
⚠️ Low processing rates (<1 theorem/second)
⚠️ Frequent errors or failures
⚠️ Poor scaling characteristics

## Contributing

When adding new benchmarks:

1. Follow the existing naming convention
2. Include both success and error scenarios
3. Document expected performance characteristics
4. Add appropriate test data generators
5. Ensure benchmarks are deterministic
6. Include memory and time measurements

## Historical Performance Data

Track performance over time to identify regressions:

- Baseline performance established
- Monitor performance changes with each release
- Identify performance regressions early
- Validate performance improvements