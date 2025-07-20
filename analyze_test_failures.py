#!/usr/bin/env python3
"""Analyze test failures and categorize them."""

from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path


def parse_test_output(file_path):
    """Parse pytest output and categorize failures."""
    with open(file_path, "r") as f:
        content = f.read()

    # Find all test results
    test_pattern = re.compile(r"(tests/[^\s]+::[^\s]+)\s+(PASSED|FAILED|ERROR|SKIPPED)")
    results = test_pattern.findall(content)

    # Categorize by result type
    categorized = defaultdict(list)
    for test_path, result in results:
        categorized[result].append(test_path)

    # Further categorize failures by test module
    failure_categories = defaultdict(list)
    for test_path in categorized["FAILED"] + categorized["ERROR"]:
        # Extract module path
        module_path = test_path.split("::")[0]
        module_name = Path(module_path).stem
        failure_categories[module_name].append(test_path)

    return categorized, failure_categories


def analyze_error_patterns(file_path):
    """Extract common error patterns from test output."""
    with open(file_path, "r") as f:
        content = f.read()

    # Common error patterns
    patterns = {
        "Import Error": r"ImportError:|ModuleNotFoundError:",
        "Attribute Error": r"AttributeError:",
        "Type Error": r"TypeError:",
        "Value Error": r"ValueError:",
        "Key Error": r"KeyError:",
        "File Not Found": r"FileNotFoundError:",
        "Assertion Error": r"AssertionError:",
        "Not Implemented": r"NotImplementedError:",
        "Config Error": r"ConfigError:|config",
        "Missing Field": r"missing.*field|field.*missing",
        "Unexpected Argument": r"unexpected.*argument|got an unexpected",
        "Mock/Patch Error": r"patch|mock|MagicMock",
    }

    error_counts = defaultdict(int)
    error_examples = defaultdict(list)

    # Split content into individual test outputs
    test_blocks = re.split(r"={10,} FAILURES ={10,}|_{10,} ERROR", content)

    for block in test_blocks:
        for error_type, pattern in patterns.items():
            if re.search(pattern, block, re.IGNORECASE):
                error_counts[error_type] += 1
                # Extract first line of error for example
                lines = block.strip().split("\n")
                for line in lines:
                    if re.search(pattern, line, re.IGNORECASE):
                        error_examples[error_type].append(line.strip())
                        break

    return error_counts, error_examples


def main():
    """Main analysis function."""
    # Parse test results
    categorized, failure_categories = parse_test_output("test_output.txt")
    error_counts, error_examples = analyze_error_patterns("test_output.txt")

    # Print summary
    print("=== TEST RESULTS SUMMARY ===")
    print(f"Total tests: {sum(len(v) for v in categorized.values())}")
    for result_type, tests in categorized.items():
        print(f"{result_type}: {len(tests)}")

    print("\n=== FAILURE CATEGORIES BY MODULE ===")
    for module, tests in sorted(
        failure_categories.items(), key=lambda x: len(x[1]), reverse=True
    ):
        print(f"\n{module}: {len(tests)} failures")
        for test in tests[:3]:  # Show first 3 examples
            print(f"  - {test}")
        if len(tests) > 3:
            print(f"  ... and {len(tests) - 3} more")

    print("\n=== ERROR PATTERN ANALYSIS ===")
    for error_type, count in sorted(
        error_counts.items(), key=lambda x: x[1], reverse=True
    ):
        if count > 0:
            print(f"\n{error_type}: {count} occurrences")
            # Show unique examples
            unique_examples = list(set(error_examples[error_type]))[:2]
            for example in unique_examples:
                print(f"  Example: {example[:100]}...")


if __name__ == "__main__":
    main()
