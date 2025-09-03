#!/usr/bin/env python3
"""
Verus Code Line Counter v2

This script counts lines of code in Verus files, categorizing them into:
- Rust code: Regular Rust implementation code
- Spec code: Specifications (requires, ensures, open spec, closed spec, etc.)
- Proof code: Code inside proof blocks and ghost operations

Usage: python3 verus_line_counter_v2.py <file_path> [--verbose]
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

class VerusLineClassifier:
    def __init__(self):
        self.reset_state()
    
    def reset_state(self):
        self.in_proof_block = False
        self.proof_brace_depth = 0
        self.in_spec_fn = False
        self.spec_fn_brace_depth = 0
        self.in_proof_fn = False
        self.proof_fn_brace_depth = 0
        self.in_regular_fn = False
        self.regular_fn_brace_depth = 0
        self.in_requires_ensures = False
        self.last_fn_type = None  # 'spec', 'proof', 'regular'
        
    def reset_function_state(self):
        """Reset function-related state when we detect a new top-level construct"""
        self.in_requires_ensures = False
        self.last_fn_type = None
        
    def classify_line(self, line: str) -> str:
        """Classify a single line of Verus code."""
        stripped = line.strip()
        
        # Handle blank lines
        if not stripped:
            return 'blank'
        
        # Handle comments (but not doc comments)
        if stripped.startswith('//') and not stripped.startswith('///'):
            return 'comment'
        
        # Reset function state at major boundaries to prevent state bleeding
        if re.search(r'^\s*(impl|struct|enum|mod|use)\b', stripped):
            self.reset_function_state()
        
        # Count braces for depth tracking
        open_braces = stripped.count('{')
        close_braces = stripped.count('}')
        
        # Handle proof blocks
        if 'proof {' in stripped:
            self.in_proof_block = True
            # Count braces properly: start with the opening brace from 'proof {'
            # then add any additional braces on the same line
            self.proof_brace_depth = 1 + (open_braces - 1) - close_braces
            if self.proof_brace_depth <= 0:
                # Proof block opens and closes on same line
                self.in_proof_block = False
                self.proof_brace_depth = 0
            return 'proof'
        
        if self.in_proof_block:
            self.proof_brace_depth += open_braces - close_braces
            if self.proof_brace_depth <= 0:
                self.in_proof_block = False
                self.proof_brace_depth = 0
                # This line ends the proof block, so it's still proof
                # But subsequent lines will not be in proof context
                return 'proof'
            return 'proof'
        
        # Handle proof function definitions
        if re.search(r'\bproof\s+fn\b', stripped):
            self.in_proof_fn = True
            self.proof_fn_brace_depth = max(1, open_braces)  # Start at 1 if no braces yet
            self.last_fn_type = 'proof'
            return 'proof'
        
        if self.in_proof_fn:
            self.proof_fn_brace_depth += open_braces - close_braces
            if self.proof_fn_brace_depth <= 0:
                self.in_proof_fn = False
                self.proof_fn_brace_depth = 0
                self.last_fn_type = None
            return 'proof'
        
        # Handle spec function definitions
        if re.search(r'\b(open\s+spec|closed\s+spec)\s+fn\b', stripped):
            self.in_spec_fn = True
            self.spec_fn_brace_depth = max(1, open_braces)  # Start at 1 if no braces yet
            self.last_fn_type = 'spec'
            return 'spec'
        
        # Handle spec fn (different pattern)
        if re.search(r'\bspec\s+fn\b', stripped):
            self.in_spec_fn = True  
            self.spec_fn_brace_depth = max(1, open_braces)  # Start at 1 if no braces yet
            self.last_fn_type = 'spec'
            return 'spec'
        
        if self.in_spec_fn:
            self.spec_fn_brace_depth += open_braces - close_braces
            if self.spec_fn_brace_depth <= 0:
                self.in_spec_fn = False
                self.spec_fn_brace_depth = 0
                self.last_fn_type = None
            return 'spec'
        
        # Handle requires/ensures blocks - context depends on function type - must come before regular fn body
        if re.search(r'^\s*(requires|ensures)\s*$', stripped) or \
           (re.search(r'\b(requires|ensures)\b', stripped) and not '{' in stripped):
            self.in_requires_ensures = True
            # proof fn contracts are proof, spec fn contracts are spec, regular fn contracts are spec
            if self.last_fn_type == 'proof':
                return 'proof'
            else:
                return 'spec'
        
        if self.in_requires_ensures:
            # Exit requires/ensures when we hit opening brace
            if '{' in stripped:
                self.in_requires_ensures = False
                # Fall through to other logic to handle the brace line
            else:
                # Continue in requires/ensures mode for continuation lines
                # This includes indented lines and lines that are part of the contract
                if self.last_fn_type == 'proof':
                    return 'proof'
                else:
                    return 'spec'
        
        # Handle regular function definitions (to set context) - must come before ghost pattern check
        if re.search(r'\bfn\s+\w+', stripped) and not re.search(r'\b(spec|proof)\s+fn\b', stripped):
            self.in_regular_fn = True
            self.regular_fn_brace_depth = max(1, open_braces)
            self.last_fn_type = 'regular'
            return 'rust'  # Function signature is rust code
        
        # Handle regular function body
        if self.in_regular_fn:
            self.regular_fn_brace_depth += open_braces - close_braces
            if self.regular_fn_brace_depth <= 0:
                self.in_regular_fn = False
                self.regular_fn_brace_depth = 0
                self.last_fn_type = None
                return 'rust'
            
            # Inside regular function body, check for special constructs
            # Loop invariants are proof code
            if re.search(r'\binvariant\b', stripped):
                return 'proof'
            
            # Everything else in regular function body is rust (including Tracked operations)
            return 'rust'
        
        # Direct spec patterns (higher priority than ghost patterns)
        spec_patterns = [
            r'\b(invariant|invariant_except_break|decreases)\b',
            r'#\[trigger\]',
            r'forall\|.*\|',
            r'exists\|.*\|',
            r'match.*==>',
            r'&&& ',  # Verus conjunction
            r'\|\|\| ',  # Verus disjunction
        ]
        
        for pattern in spec_patterns:
            if re.search(pattern, stripped):
                # Special case: if we're in regular function body, even spec patterns might be rust
                # (e.g., function calls that happen to contain these patterns)
                if self.in_regular_fn and re.search(r'\w+\(.*\)', stripped):
                    # This looks like a function call, not a spec
                    break
                return 'spec'
        
        # Ghost/tracked operations
        ghost_patterns = [
            r'\bghost\b',
            r'\btracked\b',
            r'Tracked\(',
            r'Ghost\(',
            r'@\.',  # Ghost dereference
        ]
        
        for pattern in ghost_patterns:
            if re.search(pattern, stripped):
                # Simple ghost/tracked declarations are spec
                if re.match(r'^\s*(pub\s+)?(ghost|tracked)\s+\w+:', stripped):
                    return 'spec'
                # If we're in a regular function, ghost operations are rust
                if self.in_regular_fn:
                    return 'rust'
                # In other contexts, ghost operations are typically proof
                return 'proof'
        
        # Final fallback: if this looks like function body code, classify as rust
        if re.search(r'^\s+\w+\(.*\)', stripped):  # Indented function call
            return 'rust'
        
        # Default to Rust code
        return 'rust'

def count_lines(file_path: str, verbose: bool = False) -> LineCount:
    """Count lines in a Verus file."""
    counts = LineCount()
    classifier = VerusLineClassifier()
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"Error reading file {file_path}: {e}")
        return counts
    
    counts.total = len(lines)
    
    for i, line in enumerate(lines, 1):
        classification = classifier.classify_line(line)
        
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
        print("Usage: python3 verus_line_counter_v2.py <file_path> [--verbose]")
        sys.exit(1)
    
    file_path = sys.argv[1]
    verbose = '--verbose' in sys.argv
    
    counts = count_lines(file_path, verbose)
    print_summary(file_path, counts)

if __name__ == '__main__':
    main()