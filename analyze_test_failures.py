#!/usr/bin/env python3
"""Comprehensive test failure analysis for proof-sketcher."""

from __future__ import annotations

import re
import subprocess
from collections import defaultdict
from typing import Dict, List, Tuple


def run_tests_with_output() -> str:
    """Run all tests and capture output."""
    cmd = ["python", "-m", "pytest", "tests/", "--tb=short", "-v", "--no-header"]
    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.stdout + result.stderr


def categorize_failures(output: str) -> Dict[str, List[str]]:
    """Categorize test failures by error type."""
    categories = defaultdict(list)

    # Parse test results
    lines = output.split("\n")
    current_test = None
    current_error = []

    for line in lines:
        # New test failure
        if "FAILED" in line or "ERROR" in line:
            if current_test and current_error:
                error_type = classify_error("\n".join(current_error))
                categories[error_type].append(current_test)
            current_test = line.strip()
            current_error = []
        # Collect error details
        elif current_test and (
            line.startswith("E   ")
            or line.startswith(">")
            or "Error" in line
            or "assert" in line
        ):
            current_error.append(line)

    # Don't forget the last one
    if current_test and current_error:
        error_type = classify_error("\n".join(current_error))
        categories[error_type].append(current_test)

    return dict(categories)


def classify_error(error_text: str) -> str:
    """Classify error based on error message."""
    if "ValidationError" in error_text or "Field required" in error_text:
        return "Pydantic Validation Error"
    elif "AttributeError" in error_text and "does not have the attribute" in error_text:
        return "Missing Attribute/Import Error"
    elif "NameError" in error_text:
        return "Undefined Name Error"
    elif "TypeError" in error_text and "takes no arguments" in error_text:
        return "Constructor Argument Error"
    elif "FileNotFoundError" in error_text:
        return "File Not Found Error"
    elif "assert" in error_text and "exit_code" in error_text:
        return "CLI Exit Code Error"
    elif "ModuleNotFoundError" in error_text:
        return "Module Import Error"
    elif "KeyError" in error_text:
        return "Dictionary Key Error"
    elif "ValueError" in error_text:
        return "Value Error"
    else:
        return "Other Error"


def get_test_stats(output: str) -> Tuple[int, int, int, int]:
    """Extract test statistics from pytest output."""
    # Look for summary line like "198 failed, 79 passed, 7 skipped, 8 errors"
    summary_pattern = r"(\d+) failed.*?(\d+) passed.*?(\d+) skipped.*?(\d+) error"
    match = re.search(summary_pattern, output)
    if match:
        return tuple(map(int, match.groups()))

    # Alternative pattern
    alt_pattern = r"(\d+) failed.*?(\d+) passed"
    match = re.search(alt_pattern, output)
    if match:
        failed, passed = map(int, match.groups())
        return (failed, passed, 0, 0)

    return (0, 0, 0, 0)


def analyze_test_modules(output: str) -> Dict[str, int]:
    """Count failures by test module."""
    module_failures = defaultdict(int)

    for line in output.split("\n"):
        if "FAILED" in line or "ERROR" in line:
            # Extract module name
            match = re.search(r"tests/(\w+)/test_(\w+)\.py", line)
            if match:
                module_type, module_name = match.groups()
                module_failures[f"{module_type}/{module_name}"] += 1

    return dict(module_failures)


def print_analysis(
    categories: Dict[str, List[str]],
    stats: Tuple[int, int, int, int],
    module_failures: Dict[str, int],
):
    """Print analysis results."""
    failed, passed, skipped, errors = stats
    total = failed + passed + skipped + errors
    pass_rate = (passed / total * 100) if total > 0 else 0

    print("=" * 80)
    print("TEST FAILURE ANALYSIS REPORT")
    print("=" * 80)
    print()

    print(f"Overall Statistics:")
    print(f"  Total Tests: {total}")
    print(f"  Passed: {passed} ({passed/total*100:.1f}%)")
    print(f"  Failed: {failed} ({failed/total*100:.1f}%)")
    print(f"  Errors: {errors}")
    print(f"  Skipped: {skipped}")
    print(f"  Current Pass Rate: {pass_rate:.1f}%")
    print(f"  Gap to 80%: {80 - pass_rate:.1f}%")
    print()

    print("Failures by Category:")
    sorted_categories = sorted(
        categories.items(), key=lambda x: len(x[1]), reverse=True
    )
    for category, tests in sorted_categories:
        print(f"\n{category} ({len(tests)} failures):")
        for test in tests[:3]:  # Show first 3 examples
            print(f"  - {test}")
        if len(tests) > 3:
            print(f"  ... and {len(tests) - 3} more")

    print("\n" + "=" * 80)
    print("Failures by Module:")
    sorted_modules = sorted(module_failures.items(), key=lambda x: x[1], reverse=True)
    for module, count in sorted_modules[:10]:  # Top 10 modules
        print(f"  {module}: {count} failures")

    print("\n" + "=" * 80)
    print("RECOMMENDED FIX PRIORITY:")
    print()

    # Calculate impact of fixing each category
    fixes_needed = int((0.8 * total) - passed)
    print(f"Need to fix {fixes_needed} tests to reach 80% pass rate")
    print()

    priority = 1
    for category, tests in sorted_categories:
        if len(tests) > 0:
            print(f"{priority}. Fix {category} ({len(tests)} tests)")
            print(f"   Impact: Would increase pass rate by {len(tests)/total*100:.1f}%")
            priority += 1


if __name__ == "__main__":
    print("Running test analysis...")
    output = run_tests_with_output()

    categories = categorize_failures(output)
    stats = get_test_stats(output)
    module_failures = analyze_test_modules(output)

    print_analysis(categories, stats, module_failures)
