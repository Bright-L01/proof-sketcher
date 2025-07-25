#!/usr/bin/env python3
"""Script to check if test files exist for new modules."""

import sys
import os
from pathlib import Path

def check_test_existence(source_files):
    """Check if corresponding test files exist for source files."""
    missing_tests = []
    
    for src_file in source_files:
        # Convert source file path to test file path
        src_path = Path(src_file)
        
        # Skip if not a Python file
        if src_path.suffix != '.py':
            continue
            
        # Skip if already a test file
        if 'test_' in src_path.name:
            continue
            
        # Create expected test file path
        test_path = Path('tests') / 'unit' / f"test_{src_path.stem}.py"
        
        if not test_path.exists():
            missing_tests.append(src_file)
    
    return missing_tests

if __name__ == "__main__":
    # Get files from command line arguments
    source_files = sys.argv[1:] if len(sys.argv) > 1 else []
    
    missing = check_test_existence(source_files)
    
    if missing:
        print("Missing test files for:")
        for file in missing:
            print(f"  - {file}")
        sys.exit(1)
    else:
        print("All source files have corresponding tests")
        sys.exit(0)