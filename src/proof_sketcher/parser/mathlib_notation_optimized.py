"""
Optimized Mathlib notation handler - Milestone 3.2.1

This module provides an optimized version of the notation handler with:
- String interning for memory efficiency
- Fast-path conversions for common patterns
- Batch processing capabilities
- Compiled regex optimization
- Result caching
- Memory-efficient symbol storage
"""

import functools
import logging
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple

from .mathlib_notation import MathlibNotationHandler, NotationMapping


class OptimizedMathlibNotationHandler(MathlibNotationHandler):
    """Optimized version of the Mathlib notation handler."""

    def __init__(self, enable_caching: bool = True, cache_size: int = 10000):
        """Initialize optimized notation handler.

        Args:
            enable_caching: Whether to enable LRU caching
            cache_size: Maximum cache size
        """
        super().__init__()
        self.enable_caching = enable_caching
        self.cache_size = cache_size

        # String interning for memory efficiency
        self.interned_symbols = {}
        self.interned_latex = {}
        self.interned_html = {}

        # Fast-path lookups for common patterns
        self.fast_patterns = self._build_fast_patterns()

        # Optimized regex compilation
        self._compile_optimized_patterns()

        # Performance metrics
        self.conversion_count = 0
        self.cache_hits = 0
        self.fast_path_hits = 0

    def _intern_string(self, s: str, cache: Dict[str, str]) -> str:
        """Intern string to save memory."""
        if s not in cache:
            cache[s] = sys.intern(s) if len(s) < 100 else s
        return cache[s]

    def _build_fast_patterns(self) -> Dict[str, str]:
        """Build fast-path patterns for common conversions."""
        # Most frequently used mathematical symbols
        common_patterns = {
            "∈": r"\in",
            "∀": r"\forall",
            "∃": r"\exists",
            "→": r"\to",
            "↔": r"\if",
            "∧": r"\land",
            "∨": r"\lor",
            "¬": r"\neg",
            "⊆": r"\subseteq",
            "∪": r"\cup",
            "∩": r"\cap",
            "∅": r"\emptyset",
            "ℕ": r"\mathbb{N}",
            "ℝ": r"\mathbb{R}",
            "ℤ": r"\mathbb{Z}",
            "ℚ": r"\mathbb{Q}",
            "ℂ": r"\mathbb{C}",
            "≤": r"\le",
            "≥": r"\ge",
            "≠": r"\ne",
            "≈": r"\approx",
            "≡": r"\equiv",
            "∼": r"\sim",
            "≅": r"\cong",
            "∑": r"\sum",
            "∏": r"\prod",
            "∫": r"\int",
            "∂": r"\partial",
            "∇": r"\nabla",
            "∞": r"\infty",
        }

        return {
            self._intern_string(k, self.interned_symbols): self._intern_string(
                v, self.interned_latex
            )
            for k, v in common_patterns.items()
        }

    def _compile_optimized_patterns(self):
        """Compile optimized regex patterns."""
        # Create optimized symbol pattern with fast-path symbols first
        fast_symbols = list(self.fast_patterns.keys())
        other_symbols = [s for s in self.lean_to_latex.keys() if s not in fast_symbols]

        # Sort by length (longest first) within each group
        fast_symbols.sort(key=len, reverse=True)
        other_symbols.sort(key=len, reverse=True)

        # Combine with fast symbols first for better performance
        all_symbols = fast_symbols + other_symbols
        escaped_symbols = [re.escape(symbol) for symbol in all_symbols]

        # Compile optimized pattern
        self.optimized_symbol_pattern = re.compile(
            "|".join(escaped_symbols), re.UNICODE
        )

        # Pre-compile common compound patterns
        self.compound_patterns = [
            (
                re.compile(r"∀\s*([a-zA-Z][a-zA-Z0-9]*)\s*∈\s*([ℕℝℤℚℂ])"),
                r"\\forall \1 \\in \2",
            ),
            (
                re.compile(r"∃\s*([a-zA-Z][a-zA-Z0-9]*)\s*∈\s*([ℕℝℤℚℂ])"),
                r"\\exists \1 \\in \2",
            ),
            (re.compile(r"([A-Z])\s*⊆\s*([A-Z])"), r"\1 \\subseteq \2"),
            (re.compile(r"([A-Z])\s*∪\s*([A-Z])"), r"\1 \\cup \2"),
            (re.compile(r"([A-Z])\s*∩\s*([A-Z])"), r"\1 \\cap \2"),
        ]

    @functools.lru_cache(maxsize=10000)
    def convert_to_latex_cached(self, lean_notation: str) -> str:
        """Cached version of LaTeX conversion."""
        return self._convert_to_latex_impl(lean_notation)

    @functools.lru_cache(maxsize=5000)
    def convert_to_html_cached(self, lean_notation: str) -> str:
        """Cached version of HTML conversion."""
        return self._convert_to_html_impl(lean_notation)

    def convert_to_latex(self, lean_notation: str) -> str:
        """Optimized LaTeX conversion with caching and fast paths."""
        if not lean_notation:
            return ""

        self.conversion_count += 1

        # Use cached version if caching is enabled
        if self.enable_caching:
            self.cache_hits += 1
            return self.convert_to_latex_cached(lean_notation)
        else:
            return self._convert_to_latex_impl(lean_notation)

    def _convert_to_latex_impl(self, lean_notation: str) -> str:
        """Implementation of LaTeX conversion with optimizations."""
        result = lean_notation

        # Fast path for single symbols
        if len(result) == 1 and result in self.fast_patterns:
            self.fast_path_hits += 1
            return self.fast_patterns[result]

        # Fast path for simple expressions (no spaces, single symbol)
        if len(result) <= 3 and " " not in result:
            for symbol in self.fast_patterns:
                if symbol in result:
                    result = result.replace(symbol, self.fast_patterns[symbol])
                    self.fast_path_hits += 1
                    return result

        # Apply compound patterns first (more specific)
        for pattern, replacement in self.compound_patterns:
            result = pattern.sub(replacement, result)

        # Handle type class constraints first
        result = self._handle_type_classes_latex(result)

        # Handle dependent types
        result = self._handle_dependent_types_latex(result)

        # Apply symbol replacements with optimized pattern
        result = self.optimized_symbol_pattern.sub(
            lambda m: self.lean_to_latex.get(m.group(0), m.group(0)), result
        )

        # Handle function types
        result = self._handle_function_types_latex(result)

        # Handle Greek letters
        result = self._handle_greek_letters_latex(result)

        # Handle namespace qualification
        result = self._handle_namespaces_latex(result)

        # Clean up spacing
        result = self._clean_latex_spacing(result)

        return result

    def convert_to_html(self, lean_notation: str) -> str:
        """Optimized HTML conversion."""
        if not lean_notation:
            return ""

        self.conversion_count += 1

        if self.enable_caching:
            self.cache_hits += 1
            return self.convert_to_html_cached(lean_notation)
        else:
            return self._convert_to_html_impl(lean_notation)

    def _convert_to_html_impl(self, lean_notation: str) -> str:
        """Implementation of HTML conversion with optimizations."""
        result = lean_notation

        # Fast path for single symbols
        if len(result) == 1 and result in self.lean_to_html:
            self.fast_path_hits += 1
            return self.lean_to_html[result]

        # Replace mathematical symbols with HTML entities
        result = self.optimized_symbol_pattern.sub(
            lambda m: self.lean_to_html.get(m.group(0), m.group(0)), result
        )

        # Handle type classes for HTML
        result = self._handle_type_classes_html(result)

        # Handle Greek letters for HTML
        result = self._handle_greek_letters_html(result)

        # Escape remaining special characters
        result = result.replace("<", "&lt;").replace(">", "&gt;")

        return result

    def batch_convert_to_latex(self, expressions: List[str]) -> List[str]:
        """Batch convert multiple expressions to LaTeX for better performance."""
        if not expressions:
            return []

        # Pre-sort expressions by length for better cache locality
        indexed_expressions = [(i, expr) for i, expr in enumerate(expressions)]
        indexed_expressions.sort(key=lambda x: len(x[1]))

        # Process in batches
        results = [None] * len(expressions)

        for i, expr in indexed_expressions:
            results[i] = self.convert_to_latex(expr)

        return results

    def batch_convert_to_html(self, expressions: List[str]) -> List[str]:
        """Batch convert multiple expressions to HTML."""
        if not expressions:
            return []

        # Pre-sort for cache locality
        indexed_expressions = [(i, expr) for i, expr in enumerate(expressions)]
        indexed_expressions.sort(key=lambda x: len(x[1]))

        results = [None] * len(expressions)

        for i, expr in indexed_expressions:
            results[i] = self.convert_to_html(expr)

        return results

    def get_notation_table_optimized(self, text: str) -> List[Dict[str, str]]:
        """Optimized notation table generation."""
        # Use set for faster membership testing
        found_symbols = set()

        # Use optimized pattern to find all symbols at once
        for match in self.optimized_symbol_pattern.finditer(text):
            symbol = match.group(0)
            found_symbols.add(symbol)

        # Build notation table
        notation_table = []
        for symbol in found_symbols:
            if symbol in self.lean_to_latex:
                notation_table.append(
                    {
                        "symbol": symbol,
                        "latex": self.lean_to_latex[symbol],
                        "html": self.lean_to_html.get(symbol, symbol),
                        "description": self.symbol_descriptions.get(
                            symbol, f"Symbol: {symbol}"
                        ),
                    }
                )

        # Sort by symbol for consistent output
        return sorted(notation_table, key=lambda x: x["symbol"])

    def detect_mathematical_areas_optimized(self, text: str) -> List[str]:
        """Optimized mathematical area detection."""
        # Use compiled pattern for faster symbol detection
        found_symbols = set()
        for match in self.optimized_symbol_pattern.finditer(text):
            found_symbols.add(match.group(0))

        # Group symbols by category for faster processing
        areas_found = set()

        # Create category lookup for O(1) access
        symbol_to_category = {}
        for mapping in self.all_mappings:
            symbol_to_category[mapping.lean_symbol] = mapping.category

        # Detect areas based on found symbols
        for symbol in found_symbols:
            category = symbol_to_category.get(symbol)
            if category:
                areas_found.add(category)

        # Map categories to mathematical areas
        area_map = {
            "set_theory": "Set Theory",
            "logic": "Mathematical Logic",
            "algebra": "Abstract Algebra",
            "order": "Order Theory",
            "numbers": "Number Theory",
            "analysis": "Mathematical Analysis",
            "category": "Category Theory",
        }

        return [area_map.get(area, area.title()) for area in areas_found]

    def optimize_for_large_dataset(self, expected_size: int):
        """Optimize handler for processing large datasets."""
        if expected_size > 10000:
            # Increase cache sizes for large datasets
            self.convert_to_latex_cached = functools.lru_cache(maxsize=20000)(
                self._convert_to_latex_impl
            )
            self.convert_to_html_cached = functools.lru_cache(maxsize=10000)(
                self._convert_to_html_impl
            )

        # Pre-compile more aggressive optimizations
        if expected_size > 50000:
            # Create lookup tables for ultra-fast symbol replacement
            self._create_lookup_tables()

    def _create_lookup_tables(self):
        """Create fast lookup tables for large-scale processing."""
        # Create translation tables for str.translate (fastest Python string operation)
        self.latex_translation_table = str.maketrans(
            {symbol: latex for symbol, latex in self.fast_patterns.items()}
        )

        # Create HTML translation table
        html_fast_patterns = {
            symbol: self.lean_to_html.get(symbol, symbol)
            for symbol in self.fast_patterns.keys()
            if symbol in self.lean_to_html
        }
        self.html_translation_table = str.maketrans(html_fast_patterns)

    def get_performance_stats(self) -> Dict[str, any]:
        """Get performance statistics."""
        total_conversions = self.conversion_count
        cache_hit_rate = (
            (self.cache_hits / total_conversions) * 100 if total_conversions > 0 else 0
        )
        fast_path_rate = (
            (self.fast_path_hits / total_conversions) * 100
            if total_conversions > 0
            else 0
        )

        return {
            "total_conversions": total_conversions,
            "cache_hits": self.cache_hits,
            "cache_hit_rate_percent": cache_hit_rate,
            "fast_path_hits": self.fast_path_hits,
            "fast_path_rate_percent": fast_path_rate,
            "latex_cache_size": (
                self.convert_to_latex_cached.cache_info().currsize
                if self.enable_caching
                else 0
            ),
            "html_cache_size": (
                self.convert_to_html_cached.cache_info().currsize
                if self.enable_caching
                else 0
            ),
            "memory_efficiency": {
                "interned_symbols": len(self.interned_symbols),
                "interned_latex": len(self.interned_latex),
                "interned_html": len(self.interned_html),
            },
        }

    def clear_caches(self):
        """Clear all caches to free memory."""
        if self.enable_caching:
            self.convert_to_latex_cached.cache_clear()
            self.convert_to_html_cached.cache_clear()

        # Reset performance counters
        self.conversion_count = 0
        self.cache_hits = 0
        self.fast_path_hits = 0

    def benchmark_performance(
        self, test_expressions: List[str], iterations: int = 1
    ) -> Dict[str, float]:
        """Benchmark handler performance."""
        import time

        # Clear caches for fair comparison
        self.clear_caches()

        # Warm up
        for expr in test_expressions[:10]:
            self.convert_to_latex(expr)
            self.convert_to_html(expr)

        # Benchmark LaTeX conversion
        start_time = time.time()
        for _ in range(iterations):
            for expr in test_expressions:
                self.convert_to_latex(expr)
        latex_time = time.time() - start_time

        # Benchmark HTML conversion
        start_time = time.time()
        for _ in range(iterations):
            for expr in test_expressions:
                self.convert_to_html(expr)
        html_time = time.time() - start_time

        # Benchmark batch operations
        start_time = time.time()
        for _ in range(iterations):
            self.batch_convert_to_latex(test_expressions)
        batch_latex_time = time.time() - start_time

        total_ops = len(test_expressions) * iterations

        return {
            "latex_time_seconds": latex_time,
            "html_time_seconds": html_time,
            "batch_latex_time_seconds": batch_latex_time,
            "latex_throughput_ops_per_second": (
                total_ops / latex_time if latex_time > 0 else 0
            ),
            "html_throughput_ops_per_second": (
                total_ops / html_time if html_time > 0 else 0
            ),
            "batch_throughput_ops_per_second": (
                total_ops / batch_latex_time if batch_latex_time > 0 else 0
            ),
            "performance_stats": self.get_performance_stats(),
        }


# Factory function for creating optimized handler
def create_optimized_handler(
    enable_caching: bool = True,
    cache_size: int = 10000,
    expected_dataset_size: int = 1000,
) -> OptimizedMathlibNotationHandler:
    """Create optimized notation handler with appropriate settings.

    Args:
        enable_caching: Whether to enable LRU caching
        cache_size: Maximum cache size
        expected_dataset_size: Expected size of dataset for optimization

    Returns:
        Optimized notation handler instance
    """
    handler = OptimizedMathlibNotationHandler(enable_caching, cache_size)

    if expected_dataset_size > 1000:
        handler.optimize_for_large_dataset(expected_dataset_size)

    return handler
