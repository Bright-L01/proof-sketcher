#!/usr/bin/env python3
"""
Automated code quality improvement tool for Proof Sketcher.
Fixes common quality issues systematically and safely.
"""

import argparse
import ast
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import autopep8


class QualityFixer:
    """Automated code quality fixes with safety checks."""

    def __init__(self, dry_run: bool = False):
        """Initialize quality fixer.

        Args:
            dry_run: If True, only show what would be changed
        """
        self.dry_run = dry_run
        self.changes_made = 0
        self.files_processed = 0

    def fix_file(self, file_path: Path) -> bool:
        """Fix common quality issues in a single file.

        Args:
            file_path: Path to Python file to fix

        Returns:
            True if file was modified
        """
        if not file_path.exists() or file_path.suffix != ".py":
            return False

        print(f"Processing: {file_path}")

        try:
            original_content = file_path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            print(f"  ⚠️  Skipping {file_path} - encoding issues")
            return False

        # Apply fixes in order of safety
        fixed_content = original_content
        changes = 0

        # 1. Fix basic formatting issues (safest)
        new_content, count = self._fix_whitespace_issues(fixed_content)
        fixed_content, changes = new_content, changes + count

        # 2. Fix line length issues
        new_content, count = self._fix_line_length(fixed_content)
        fixed_content, changes = new_content, changes + count

        # 3. Remove unused imports (moderate risk)
        new_content, count = self._remove_unused_imports(fixed_content)
        fixed_content, changes = new_content, changes + count

        # 4. Fix f-string issues (low risk)
        new_content, count = self._fix_fstring_issues(fixed_content)
        fixed_content, changes = new_content, changes + count

        # 5. Fix bare except clauses (moderate risk)
        new_content, count = self._fix_bare_except(fixed_content)
        fixed_content, changes = new_content, changes + count

        # 6. Apply autopep8 formatting
        if changes > 0:
            fixed_content = autopep8.fix_code(
                fixed_content,
                options={
                    "max_line_length": 88,
                    "aggressive": 1,  # Conservative aggression
                    "experimental": False,
                },
            )

        # Check if we should apply changes
        if fixed_content != original_content:
            if self.dry_run:
                print(f"  🔍 Would fix {changes} issues in {file_path}")
                self._show_diff_summary(original_content, fixed_content)
            else:
                # Validate the fixed code can be parsed
                try:
                    ast.parse(fixed_content)
                except SyntaxError as e:
                    print(f"  ❌ Syntax error after fixes: {e}")
                    return False

                file_path.write_text(fixed_content, encoding="utf-8")
                print(f"  ✅ Fixed {changes} issues")
                self.changes_made += changes

            self.files_processed += 1
            return True

        return False

    def _fix_whitespace_issues(self, content: str) -> Tuple[str, int]:
        """Fix whitespace-related issues."""
        changes = 0
        lines = content.splitlines()
        fixed_lines = []

        for line in lines:
            original_line = line

            # Remove trailing whitespace
            line = line.rstrip()
            if line != original_line:
                changes += 1

            fixed_lines.append(line)

        # Ensure file ends with newline
        fixed_content = "\n".join(fixed_lines)
        if not content.endswith("\n") and fixed_content:
            fixed_content += "\n"
            changes += 1

        return fixed_content, changes

    def _fix_line_length(self, content: str) -> Tuple[str, int]:
        """Fix basic line length issues where safe."""
        changes = 0
        lines = content.splitlines()
        fixed_lines = []

        for line in lines:
            if len(line) > 88:  # Use 88 char limit like black
                # Only fix simple cases - long import lines and comments
                if line.strip().startswith("#") and len(line) > 100:
                    # Split long comments
                    words = line.split()
                    if len(words) > 3:
                        indent = len(line) - len(line.lstrip())
                        prefix = " " * indent + "# "

                        current_line = prefix
                        for word in words[1:]:  # Skip the '#'
                            if len(current_line + " " + word) > 88:
                                fixed_lines.append(current_line.rstrip())
                                current_line = prefix + word
                                changes += 1
                            else:
                                current_line += " " + word
                        fixed_lines.append(current_line.rstrip())
                        continue

                elif "import" in line and "," in line:
                    # Split long import lines
                    if line.strip().startswith("from") and "import" in line:
                        parts = line.split("import", 1)
                        if len(parts) == 2:
                            imports = [imp.strip() for imp in parts[1].split(",")]
                            if len(imports) > 1:
                                fixed_lines.append(parts[0] + "import (")
                                for imp in imports:
                                    fixed_lines.append(f"    {imp.strip()},")
                                fixed_lines.append(")")
                                changes += 1
                                continue

            fixed_lines.append(line)

        return "\n".join(fixed_lines) + "\n", changes

    def _remove_unused_imports(self, content: str) -> Tuple[str, int]:
        """Remove obviously unused imports (conservative approach)."""
        changes = 0

        try:
            tree = ast.parse(content)
        except SyntaxError:
            return content, 0

        # Find imports and their usage
        imports = []
        used_names = set()

        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    imports.append((node, alias.name, alias.asname))
            elif isinstance(node, ast.ImportFrom):
                for alias in node.names:
                    imports.append((node, alias.name, alias.asname))
            elif isinstance(node, ast.Name):
                used_names.add(node.id)

        # Remove unused imports (very conservative)
        lines = content.splitlines()
        lines_to_remove = set()

        for node, name, asname in imports:
            check_name = asname if asname else name

            # Only remove if obviously unused and safe
            if (
                check_name not in used_names
                and check_name
                in ["typing.Optional"]  # Only remove specific safe imports
                and hasattr(node, "lineno")
            ):
                lines_to_remove.add(node.lineno - 1)
                changes += 1

        if lines_to_remove:
            fixed_lines = [
                line for i, line in enumerate(lines) if i not in lines_to_remove
            ]
            return "\n".join(fixed_lines) + "\n", changes

        return content, changes

    def _fix_fstring_issues(self, content: str) -> Tuple[str, int]:
        """Fix f-strings missing placeholders."""
        changes = 0

        # Find f-strings without placeholders
        pattern = r'f["\']([^"\']*)["\']'

        def replace_fstring(match):
            nonlocal changes
            string_content = match.group(1)
            if "{" not in string_content:
                changes += 1
                # Remove f prefix
                quote = match.group(0)[1]  # Get quote type
                return quote + string_content + quote
            return match.group(0)

        fixed_content = re.sub(pattern, replace_fstring, content)
        return fixed_content, changes

    def _fix_bare_except(self, content: str) -> Tuple[str, int]:
        """Fix bare except clauses."""
        changes = 0

        # Replace bare except with Exception
        def replace_except(match):
            nonlocal changes
            changes += 1
            return "except Exception:"

        pattern = r"\bexcept\s*:"
        fixed_content = re.sub(pattern, replace_except, content)

        return fixed_content, changes

    def _show_diff_summary(self, original: str, fixed: str):
        """Show a summary of what would change."""
        orig_lines = original.splitlines()
        fixed_lines = fixed.splitlines()

        print(f"    Original lines: {len(orig_lines)}")
        print(f"    Fixed lines: {len(fixed_lines)}")

        # Count specific improvements
        orig_trailing = sum(1 for line in orig_lines if line.endswith(" "))
        fixed_trailing = sum(1 for line in fixed_lines if line.endswith(" "))
        print(f"    Trailing whitespace: {orig_trailing} → {fixed_trailing}")

        orig_long = sum(1 for line in orig_lines if len(line) > 88)
        fixed_long = sum(1 for line in fixed_lines if len(line) > 88)
        print(f"    Long lines (>88): {orig_long} → {fixed_long}")

    def fix_directory(self, directory: Path, recursive: bool = True) -> Dict[str, int]:
        """Fix all Python files in a directory.

        Args:
            directory: Directory to process
            recursive: Whether to process subdirectories

        Returns:
            Summary of changes made
        """
        pattern = "**/*.py" if recursive else "*.py"
        python_files = list(directory.glob(pattern))

        print(f"Found {len(python_files)} Python files to process")

        for file_path in python_files:
            # Skip certain files/directories
            if any(
                skip in str(file_path)
                for skip in [
                    "__pycache__",
                    ".git",
                    ".venv",
                    "venv",
                    ".mypy_cache",
                    ".pytest_cache",
                ]
            ):
                continue

            self.fix_file(file_path)

        return {
            "files_processed": self.files_processed,
            "changes_made": self.changes_made,
        }


def main():
    """Main entry point for quality fixer."""
    parser = argparse.ArgumentParser(
        description="Fix code quality issues in Proof Sketcher"
    )
    parser.add_argument("path", type=Path, help="File or directory to process")
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be changed without making changes",
    )
    parser.add_argument(
        "--module", help="Specific module to fix (e.g., 'parser', 'generator')"
    )

    args = parser.parse_args()

    if not args.path.exists():
        print(f"❌ Path does not exist: {args.path}")
        sys.exit(1)

    fixer = QualityFixer(dry_run=args.dry_run)

    if args.path.is_file():
        if fixer.fix_file(args.path):
            print("✅ File processed successfully")
        else:
            print("⚠️  No changes needed")
    else:
        # Process directory
        target_dir = args.path
        if args.module:
            target_dir = args.path / args.module
            if not target_dir.exists():
                print(f"❌ Module directory not found: {target_dir}")
                sys.exit(1)

        summary = fixer.fix_directory(target_dir)

        print(f"\n📊 Summary:")
        print(f"   Files processed: {summary['files_processed']}")
        print(f"   Total changes: {summary['changes_made']}")

        if args.dry_run:
            print("   (Dry run - no files were modified)")
        else:
            print("   ✅ All fixes applied")


if __name__ == "__main__":
    main()
