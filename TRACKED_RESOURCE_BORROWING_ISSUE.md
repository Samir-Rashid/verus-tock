# Tracked Resource Borrowing and Proof Context Issue

## Problem Summary

Working on timer multiplexer verification in `capsules/core/src/virtualizers/new_virtual_alarm.rs`. Successfully identified and partially fixed a tracked resource consumption issue, but encountering proof context problems with sequence length preservation.

## Root Cause Identified

**Issue**: `tracked_unwrap()` consumption in iterator usage pattern
```rust
// PROBLEMATIC - consumes resource on first call
let iterator = ListIteratorV::new(list, &Tracked(perms.virtual_alarms_state.tracked_unwrap().get()));
// Later calls fail because resource is consumed
match iterator.next(&Tracked(perms.virtual_alarms_state.tracked_unwrap().get())) { ... }
```

**Technical Details**: 
- `tracked_unwrap()` moves value out of `Option<Tracked<T>>`, consuming the resource
- Multiple calls to `tracked_unwrap()` fail because field becomes `None` after first use
- Algorithm needs same resource across multiple iterator operations in single function

## Solution Implemented

**Pattern**: Extract once, create exec-accessible wrapper, reconstruct for proofs
```rust
let tracked ghost_state = perms.virtual_alarms_state.tracked_unwrap().get();
let exec_ghost_ref = Tracked(ghost_state);

let mut iterator = ListIteratorV::new(self.virtual_alarms.as_ref().unwrap(), &exec_ghost_ref);

proof {
    perms.virtual_alarms_state = Some(exec_ghost_ref);
}

// Later uses throughout function
match iterator.next(&exec_ghost_ref) { ... }
```

**Status**: ✅ Exec code now works - iterator validation passes, no consumption errors

## Remaining Issue

**Proof Context Problem**: Sequence length preservation assertion fails
```rust
// This assertion now fails after resource reconstruction
assert(old(perms).virtual_alarm_states_seq@.len() == perms.virtual_alarm_states_seq@.len());
```

**Expected Behavior**: The algorithm only reads sequences, never modifies them. This property should be preserved through resource extraction/reconstruction.

## Questions for Verus Community

1. **Resource Identity**: Does `tracked_unwrap().get()` followed by `Some(Tracked(...))` reconstruction preserve all proof properties of the original resource?

2. **Old State Access**: How should `old(perms)` relationships be maintained when the `perms` parameter structure is modified in proof blocks during function execution?

3. **Proof Context Preservation**: What's the correct pattern for maintaining proof invariants across resource extraction/reconstruction boundaries?

4. **Alternative Patterns**: Is there a better approach for sharing tracked resources across multiple function calls within the same function scope?

## Context

- **Function**: `alarm(&'a self, Tracked(perms): Tracked<&mut MuxAlarmPerms>)`
- **Resource**: `perms.virtual_alarms_state: Option<Tracked<GhostState<VirtualMuxAlarm>>>`
- **Usage**: Multiple `ListIteratorV` operations requiring same tracked resource
- **Goal**: Eliminate `assume` statements by proving sequence length preservation

## Code Location

File: `/home/mod/Documents/github/verus-tock/capsules/core/src/virtualizers/new_virtual_alarm.rs`
Lines: ~814-830 (resource extraction), ~1226 (failing assertion)

## Verification Status

- **Before**: 93 verified, assume statements used
- **Current**: 91 verified, 3 errors (exec issues fixed, proof context issues remain)
- **Target**: Full verification without assume statements