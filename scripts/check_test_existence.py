# \!/usr/bin/env python3
"""
Check if test files exist for new Python modules.
Used by pre-commit hooks to encourage test-driven development.
Alpha software: Currently informational only.
"""

import os
import sys
from pathlib import Path


def find_test_file(module_path: Path) -> Path | None:
    """Find the corresponding test file for a module."""
    # Convert src path to test path
    parts = module_path.parts
    if "src" not in parts:
        return None

    src_index = parts.index("src")
    test_parts = list(parts[:src_index]) + ["tests"] + list(parts[src_index + 1 :])

    # Replace module.py with test_module.py
    if test_parts[-1].endswith(".py") and not test_parts[-1].startswith("test_"):
        test_parts[-1] = "test_" + test_parts[-1]

    test_path = Path(*test_parts)

    # Check multiple possible locations
    possible_paths = [
        test_path,
        test_path.parent / "unit" / test_path.name,
        test_path.parent / "integration" / test_path.name,
        test_path.parent.parent / "unit" / test_path.name,
        test_path.parent.parent / "integration" / test_path.name,
    ]

    for path in possible_paths:
        if path.exists():
            return path

    return None


def main():
    """Check test existence for provided files."""
    if len(sys.argv) < 2:
        print("No files to check")
        return 0

    missing_tests = []

    for file_path in sys.argv[1:]:
        module_path = Path(file_path)

        # Skip non-Python files
        if not module_path.suffix == ".py":
            continue

        # Skip __init__.py files
        if module_path.name == "__init__.py":
            continue

        # Skip test files themselves
        if "test" in module_path.parts or module_path.name.startswith("test_"):
            continue

        test_file = find_test_file(module_path)

        if test_file is None:
            missing_tests.append(module_path)
            print(f"⚠️  No test file found for: {module_path}")
            print(
                f"   Consider creating: tests/{module_path.stem}/test_{module_path.name}"
            )
        else:
            print(f"✅ Test file exists: {test_file}")

    if missing_tests:
        print("\n" + "=" * 60)
        print("⚠️  REMINDER: This is ALPHA software with 11% test coverage.")
        print("   New code should have tests to improve quality\!")
        print("   Missing test files:")
        for module in missing_tests:
            print(f"   - {module}")
        print("=" * 60)
        # Don't fail in alpha - just warn
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
