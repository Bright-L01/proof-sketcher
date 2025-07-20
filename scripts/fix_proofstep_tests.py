#!/usr/bin/env python3
"""Fix ProofStep validation errors in tests by adding required fields."""

import re
from pathlib import Path


def fix_proofstep_in_file(file_path: Path) -> bool:
    """Fix ProofStep instantiations in a test file."""
    content = file_path.read_text()
    original_content = content
    
    # Pattern to find ProofStep instantiations
    # This will match ProofStep(...) with various arguments
    pattern = r'ProofStep\s*\(\s*([^)]+)\s*\)'
    
    def fix_proofstep(match):
        args = match.group(1)
        
        # Check if it already has the required fields
        if all(field in args for field in ['intuitive_explanation', 'conceptual_explanation', 
                                           'bridging_explanation', 'formal_explanation']):
            return match.group(0)
        
        # Parse existing arguments
        lines = args.split('\n')
        indent = '    '
        if lines[0].strip():
            # Single line or first line has content
            new_args = [lines[0]]
        else:
            new_args = []
            
        # Add default values for missing required fields
        required_fields = {
            'intuitive_explanation': '"Test intuitive explanation"',
            'conceptual_explanation': '"Test conceptual explanation"',
            'bridging_explanation': '"Test bridging explanation"',
            'formal_explanation': '"Test formal explanation"'
        }
        
        # Check which fields are missing
        for field, default in required_fields.items():
            if f'{field}=' not in args and f'"{field}"' not in args:
                new_args.append(f'{indent}{field}={default},')
        
        # Add remaining original args
        for line in lines[1:]:
            if line.strip():
                new_args.append(line)
        
        # Reconstruct the ProofStep call
        if len(new_args) == 1:
            return f'ProofStep({new_args[0]})'
        else:
            args_str = '\n'.join(new_args)
            return f'ProofStep(\n{args_str}\n)'
    
    # Replace all ProofStep instantiations
    content = re.sub(pattern, fix_proofstep, content, flags=re.DOTALL)
    
    if content != original_content:
        file_path.write_text(content)
        return True
    return False


def main():
    """Fix ProofStep issues in all test files."""
    test_dir = Path('tests')
    fixed_files = []
    
    for test_file in test_dir.rglob('test_*.py'):
        if fix_proofstep_in_file(test_file):
            fixed_files.append(test_file)
    
    print(f"Fixed {len(fixed_files)} test files:")
    for file in fixed_files:
        print(f"  - {file}")


if __name__ == '__main__':
    main()