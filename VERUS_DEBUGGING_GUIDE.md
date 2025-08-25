# Verus Debugging Guide: Lessons from Timer Multiplexer Verification

## Context: Verus-Tock Project

This guide documents successful debugging strategies for formal verification in the Verus-Tock project, specifically from resolving tracked resource borrowing and sequence length preservation issues in `capsules/core/src/virtualizers/new_virtual_alarm.rs`.

**Project Background:**
- Verus formal verification for Rust embedded systems (Tock OS)
- Timer multiplexer architecture: MuxAlarm coordinates multiple VirtualMuxAlarm instances
- Complex tracked resource management with linear typing
- Iterator-to-sequence correspondence verification

## Core Debugging Philosophy

### 1. **Assumption Validation is Critical**
> "The important part of debugging is to validate assumptions. I do not think the sequence length changes, but verus clearly does not know that."

- **Never assume your intuition is wrong** - often the logic is correct but Verus needs help understanding it
- **Use experimental assertions systematically** to validate what you think should be true
- **Refinements over rewrites** - add postconditions to help Verus understand what functions preserve

### 2. **Systematic Exploratory Debugging**
> "Use assertions to search for where Verus gets confused and add refinements on loops or functions or whatever is needed to satisfy verus. This is an exploratory process without a clear path."

**The Winning Strategy:**
```rust
// Add systematic experimental assertions throughout the algorithm
proof {
    assert(original_old_len == perms.virtual_alarm_states_seq@.len());
}

// After every significant operation:
some_function_call();
proof {
    assert(original_old_len == perms.virtual_alarm_states_seq@.len()); // Does this break it?
}
```

**Why This Works:**
- Pinpoints the **exact** operation causing issues
- Validates your assumptions step by step
- Reveals where Verus loses context vs. actual logical errors

## Tracked Resource Management Patterns

### 1. **The Resource Borrowing Pattern**
```rust
// WRONG: Multiple tracked_unwrap() calls consume the resource
let iterator1 = ListIteratorV::new(list, &Tracked(perms.virtual_alarms_state.tracked_unwrap().get()));
let iterator2 = iterator1.next(&Tracked(perms.virtual_alarms_state.tracked_unwrap().get())); // FAILS!

// RIGHT: Extract once, share properly
let tracked ghost_state = perms.virtual_alarms_state.tracked_unwrap().get();
let exec_ghost_ref = Tracked(ghost_state);
let iterator = ListIteratorV::new(list, &exec_ghost_ref);
let next = iterator.next(&exec_ghost_ref); // Works!

proof {
    // Reconstruct for proofs
    perms.virtual_alarms_state = Some(exec_ghost_ref);
}
```

### 2. **Proof Context Preservation**
```rust
// WRONG: old(perms) becomes invalid after structural modifications
let tracked ghost_state = perms.virtual_alarms_state.tracked_unwrap().get();
proof {
    perms.virtual_alarms_state = Some(Tracked(ghost_state));
    // old(perms).field@.len() relationships now broken!
    assert(old(perms).virtual_alarm_states_seq@.len() == perms.virtual_alarm_states_seq@.len()); // FAILS
}

// RIGHT: Capture relationships BEFORE any modifications
let ghost original_old_len = old(perms).virtual_alarm_states_seq@.len();
let ghost original_seq_len = perms.virtual_alarm_states_seq@.len();

proof {
    assert(original_seq_len == original_old_len); // Establish baseline
}

let tracked ghost_state = perms.virtual_alarms_state.tracked_unwrap().get();
proof {
    perms.virtual_alarms_state = Some(Tracked(ghost_state));
    assert(original_old_len == perms.virtual_alarm_states_seq@.len()); // Now works!
}
```

## Iterator Debugging Techniques

### 1. **Understanding Iterator Contracts**
From `list_i.rs` iterator postconditions:
```rust
// When iterator.next() returns Some(_):
// - old(iterator).index@ + 1 < ghost_state@.cells.len()
// - iterator.index@ == old(iterator).index@ + 1

// Key insight: Use the OLD index for sequence access, not the new index
let ghost old_index = index; // Capture before iterator.next()
match iterator.next(&ghost_state) {
    Some(cur) => {
        // cur corresponds to element at old_index, not current iterator.index@
        let tracked virtual_perms = perms.virtual_alarm_states_seq.borrow().tracked_borrow(old_index);
    }
}
```

### 2. **Iterator/Sequence Length Relationships**
```rust
// Critical relationship from mux_alarm_wf:
// cells.len() == virtual_alarm_states_seq@.len() + 1

// Iterator operates on cells (N+1 elements)
// Sequence has N elements  
// Loop invariant must account for this:
loop 
    invariant
        0 <= index <= original_old_len,  // Iterator can visit N+1 positions
        perms.virtual_alarm_states_seq@.len() == original_old_len,
        perms.virtual_alarms_state@.unwrap()@.cells.len() == original_old_len + 1,
```

## Function Refinement Strategies

### 1. **Adding Critical Postconditions**
The breakthrough came from identifying that external function calls needed explicit postconditions:

```rust
// BEFORE: disarm() had no sequence length guarantee
pub fn disarm(&self, Tracked(perms): Tracked<&mut MuxAlarmPerms>)
    requires
        self.mux_alarm_wf(old(perms)),
    ensures
        self.mux_alarm_wf((perms)),
        // Missing: sequence length preservation!

// AFTER: Explicit refinement
pub fn disarm(&self, Tracked(perms): Tracked<&mut MuxAlarmPerms>)  
    requires
        self.mux_alarm_wf(old(perms)),
    ensures
        self.mux_alarm_wf((perms)),
        // REFINEMENT: disarm() preserves sequence length
        perms.virtual_alarm_states_seq@.len() == old(perms).virtual_alarm_states_seq@.len(),
```

### 2. **Identifying Which Functions Need Refinement**
Use exploratory assertions around function calls:
```rust
proof {
    assert(property_should_be_preserved);
}
function_call();
proof {
    assert(property_should_be_preserved); // Does the function break this?
}
```

When the second assertion fails, you've found your target for adding postconditions.

## Verus-Specific Insights

### 1. **Memory Safety is Conditional on Verification**
From `/home/mod/Documents/github/verus-tock/verus/source/docs/guide/src/memory-safety.md`:
- Unlike Rust's unsafe/safe distinction, Verus has no staggered correctness notion
- If verification fails, all bets are off - memory safety is not guaranteed
- This makes complete verification critical, not optional

### 2. **Ghost vs Tracked Variables**
```rust
let tracked mut index : int = 0int; // WRONG: tracked for proof-mode arithmetic
let ghost mut index : int = 0int;   // RIGHT: ghost for proof variables
```

### 3. **Spec vs Proof vs Exec Modes**
```rust
// Exec mode: actual runtime execution
let exec_value = some_function();

// Proof mode: verification logic
proof {
    ghost_variable = ghost_variable + 1;
    assert(some_property);
}

// Spec mode: specifications and postconditions
ensures
    result.property == expected_value
```

## Debugging Tools and Commands

### 1. **Incremental Verification**
```bash
make  # Run verification
```
- Look for "X verified, Y errors" counts
- Improvement in verified count indicates progress
- Focus on first failing assertion - fix cascade issues

### 2. **Error Analysis Priority**
1. **Assertion failures**: Direct logical issues
2. **Precondition failures**: Function contract violations  
3. **Type errors**: Mode mismatches (spec/proof/exec)
4. **Loop invariant failures**: Invariant strengthening needed

### 3. **Iterator Debugging Pattern**
```rust
// Add systematic assertions in loops:
loop
    invariant
        property1,
        property2,
        // Add: property_being_debugged,
{
    // Add before operations:
    proof { assert(property_being_debugged); }
    
    operation();
    
    // Add after operations: 
    proof { assert(property_being_debugged); }
}
```

## Repository-Specific Context

### File Structure
- `capsules/core/src/virtualizers/new_virtual_alarm.rs` - Main timer multiplexer
- `kernel/src/collections/list_i.rs` - Verified linked list with iterator support
- `verification_docs/` - Verus examples and patterns
- `TRACKED_RESOURCE_BORROWING_ISSUE.md` - Issue documentation

### Key Architectural Patterns
- **Timer Multiplexing**: Single hardware timer → multiple virtual timers
- **Linear Resource Management**: Tracked types for memory safety
- **Iterator Correspondence**: Linking iterator state to sequence indices

### Build and Test
```bash
make                    # Full verification
make first_time        # Initial build with dependencies
```

## Success Metrics

**This debugging session achieved:**
- ✅ 91 → 92 verified functions (+1)
- ✅ 3 → 2 verification errors (-1)  
- ✅ Core sequence length preservation issue resolved
- ✅ Tracked resource borrowing patterns established
- ✅ Zero assume statements eliminated in target area

## Final Wisdom

1. **Trust your intuition about correctness** - the algorithm is usually right
2. **Use systematic experimental assertions** to find where Verus gets confused
3. **Add refinements (postconditions) rather than rewriting logic**
4. **Capture proof relationships before structural modifications**
5. **Understand iterator contracts deeply** - they're often the source of bounds issues
6. **Function refinements are often the key** - external calls need explicit guarantees

The most powerful realization: **Verification failures don't mean your code is wrong - they often mean Verus needs help understanding what your code preserves.**