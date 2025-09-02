#!/usr/bin/env python3
"""
Verus Code Line Counter

This script counts lines of code in Verus files, categorizing them into:
- Rust code: Regular Rust implementation code
- Spec code: Specifications (requires, ensures, open spec, closed spec, etc.)
- Proof code: Code inside proof blocks and ghost operations

Usage: python3 verus_line_counter.py <file_path> [--verbose]
"""

import re
import sys
from typing import Tuple, List
from dataclasses import dataclass

@dataclass
class LineCount:
    rust: int = 0
    spec: int = 0
    proof: int = 0
    total: int = 0
    blank: int = 0
    comment: int = 0

def classify_line(line: str, in_proof_block: bool, brace_depth: int) -> Tuple[str, bool, int]:
    """
    Classify a line as 'rust', 'spec', 'proof', 'blank', or 'comment'.
    Returns (classification, new_in_proof_block, new_brace_depth)
    """
    stripped = line.strip()
    
    # Handle blank lines
    if not stripped:
        return 'blank', in_proof_block, brace_depth
    
    # Handle comments (but not doc comments which might contain specs)
    if stripped.startswith('//') and not stripped.startswith('///'):
        return 'comment', in_proof_block, brace_depth
    
    # Track brace depth for proof blocks
    open_braces = stripped.count('{')
    close_braces = stripped.count('}')
    new_brace_depth = brace_depth + open_braces - close_braces
    
    # Check for proof block start
    if 'proof {' in stripped:
        return 'proof', True, new_brace_depth
    
    # If we're in a proof block
    if in_proof_block:
        # Check if we're exiting the proof block
        if brace_depth > 0 and new_brace_depth <= 0:
            return 'proof', False, 0
        return 'proof', True, new_brace_depth
    
    # Spec keywords and patterns
    spec_patterns = [
        r'\b(requires|ensures|invariant|invariant_except_break)\b',
        r'\b(open\s+spec|closed\s+spec)\b',
        r'\b(decreases)\b',
        r'#\[trigger\]',
        r'forall\|.*\|',
        r'exists\|.*\|',
        r'match.*==>',
        r'&&& ',  # Verus conjunction in specs
        r'\|\|\| ',  # Verus disjunction in specs
    ]
    
    # Check for spec patterns
    for pattern in spec_patterns:
        if re.search(pattern, stripped):
            return 'spec', in_proof_block, new_brace_depth
    
    # Check for ghost operations
    ghost_patterns = [
        r'\bghost\b',
        r'\btracked\b',
        r'Tracked\(',
        r'Ghost\(',
        r'@\.',  # Ghost dereference
    ]
    
    for pattern in ghost_patterns:
        if re.search(pattern, stripped):
            # Could be spec or proof depending on context
            # If it's a simple declaration with ghost/tracked, it's likely spec
            if re.match(r'^\s*(pub\s+)?(ghost|tracked)\s+\w+:', stripped):
                return 'spec', in_proof_block, new_brace_depth
            # Otherwise, it's likely proof code
            return 'proof', in_proof_block, new_brace_depth
    
    # Default to Rust code
    return 'rust', in_proof_block, new_brace_depth

def count_lines(file_path: str, verbose: bool = False) -> LineCount:
    """Count lines in a Verus file."""
    counts = LineCount()
    in_proof_block = False
    brace_depth = 0
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"Error reading file {file_path}: {e}")
        return counts
    
    counts.total = len(lines)
    
    for i, line in enumerate(lines, 1):
        classification, in_proof_block, brace_depth = classify_line(
            line, in_proof_block, brace_depth
        )
        
        if classification == 'rust':
            counts.rust += 1
        elif classification == 'spec':
            counts.spec += 1
        elif classification == 'proof':
            counts.proof += 1
        elif classification == 'blank':
            counts.blank += 1
        elif classification == 'comment':
            counts.comment += 1
        
        if verbose:
            print(f"{i:3d}: {classification:7s} | {line.rstrip()}")
    
    return counts

def print_summary(file_path: str, counts: LineCount):
    """Print a summary of line counts."""
    print(f"\nLine count summary for {file_path}:")
    print(f"{'Category':<12} {'Lines':<8} {'Percentage':<10}")
    print("-" * 32)
    
    code_total = counts.rust + counts.spec + counts.proof
    
    if code_total > 0:
        print(f"{'Rust code':<12} {counts.rust:<8} {counts.rust/code_total*100:>6.1f}%")
        print(f"{'Spec code':<12} {counts.spec:<8} {counts.spec/code_total*100:>6.1f}%")
        print(f"{'Proof code':<12} {counts.proof:<8} {counts.proof/code_total*100:>6.1f}%")
        print("-" * 32)
        print(f"{'Code total':<12} {code_total:<8} {'100.0%':<10}")
    
    print(f"{'Comments':<12} {counts.comment:<8}")
    print(f"{'Blank lines':<12} {counts.blank:<8}")
    print(f"{'Total lines':<12} {counts.total:<8}")

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 verus_line_counter.py <file_path> [--verbose]")
        sys.exit(1)
    
    file_path = sys.argv[1]
    verbose = '--verbose' in sys.argv
    
    counts = count_lines(file_path, verbose)
    print_summary(file_path, counts)

if __name__ == '__main__':
    main()