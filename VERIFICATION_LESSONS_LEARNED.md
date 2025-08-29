# Verus Verification Lessons Learned: tracked_borrow ID Correspondence

## Summary

I investigated verification failures in `new_virtual_alarm.rs` related to tracked_borrow ID correspondence, created a minimal reproducer, and discovered key insights about Verus proof strategies.

## What I Initially Misunderstood

### ❌ **Wrong Assumption: Fundamental Verus Limitation**
- **What I thought**: `tracked_borrow` doesn't establish ID correspondence between borrowed elements and sequence elements
- **Reality**: `tracked_borrow` DOES establish this via its postcondition `*ret === self[i]` + structural equality implying ID equality

### ❌ **Wrong Assumption: Simple Minimal Reproducer**  
- **What I tried**: Creating a minimal test with arbitrary parameters
- **Reality**: The issue wasn't in `tracked_borrow` itself, but in missing preconditions in calling contexts

### ❌ **Wrong Approach: Focusing on tracked_borrow Implementation**
- **What I did**: Spent time trying to understand tracked_borrow internals
- **Better approach**: Should have examined the calling context and preconditions first

## What I Actually Learned

### ✅ **Key Discovery: Structural Equality Works**
```rust
// This DOES work in Verus:
let tracked borrowed_ref = seq.borrow().tracked_borrow(index);
assert(*borrowed_ref === seq@[index]); // tracked_borrow postcondition 
assert(borrowed_ref.field.id() === seq@[index].field.id()); // follows from structural equality
```

### ✅ **Root Cause: Missing Preconditions**
The real issue was that proof functions were being called without establishing the necessary relationship:
```rust
pub proof fn establish_tracked_borrow_correspondence(
    virtual_perms: &VirtualMuxAlarmPerms,
    seq: &MuxAlarmPerms,
    index: int,
) 
    requires
        // MISSING: This precondition was not specified!
        *virtual_perms === seq.virtual_alarm_states_seq@[index],
```

### ✅ **Verus Design Insight: Postconditions vs Preconditions**
- `tracked_borrow` provides the postcondition `*ret === self[i]`
- But proof functions must be called with preconditions that establish this relationship
- The gap was in **propagating** the tracked_borrow guarantee to the proof function

## Debugging Strategies That Worked

### 🔧 **ProofPlumber Methodology**
1. **Comment out failing assertions** to isolate the issue
2. **Test incremental steps** (content equality → field equality → ID equality)
3. **Create minimal reproducers** to understand the core mechanism
4. **Work backwards** from failing assertions to identify missing context

### 🔧 **Effective Debugging Pattern**
```rust
proof {
    // Step 1: Test what tracked_borrow guarantees
    assert(*virtual_perms === seq@[index]);
    
    // Step 2: Test if structural equality implies field equality  
    assert(virtual_perms.field === seq@[index].field);
    
    // Step 3: Test if field equality implies ID equality
    assert(virtual_perms.field.id() === seq@[index].field.id());
}
```

### 🔧 **Context Investigation Strategy**
- Don't just look at the failing function
- **Trace back to the call site** where `tracked_borrow` actually happens
- Verify that the relationship is being **propagated through all intermediate functions**

## Strategies for Solving Faster Next Time

### 🚀 **Start with Call Site Analysis**
1. **Find where `tracked_borrow` is called** (line 991 in this case)
2. **Trace the flow** from tracked_borrow → intermediate functions → failing assertion
3. **Identify where the relationship gets lost**

### 🚀 **Minimal Reproducer Strategy**
- Create reproducers that **match the exact calling pattern** 
- Don't oversimplify - include the **intermediate function calls**
- Test the **full chain** not just the core mechanism

### 🚀 **Documentation Reading Priority**
1. **Function signatures first**: `tracked_borrow(tracked &self, i: int) -> tracked ret : &A`
2. **Postconditions**: `ensures *ret === self[i]`  
3. **Real usage examples** from verified codebases (verus-mimalloc was invaluable)

## Relevant Documentation & Code

### 📚 **Most Helpful References**
- **Verus tracked_borrow signature**: `/verus/source/vstd/seq.rs` - showed the exact postcondition
- **Real usage examples**: `/verification_docs/verified-memory-allocator/verus-mimalloc/types.rs`
- **Variable modes documentation**: `/verus/source/docs/guide/src/reference-var-modes.md`

### 📚 **Code Patterns That Helped**
```rust
// Pattern from verus-mimalloc/types.rs:
segment.main.borrow(Tracked(&local.segments.tracked_borrow(self.segment_id@).main))
```
This showed me the real `seq.borrow().tracked_borrow(index)` pattern.

### 📚 **Key Verus Facts**
- **tracked_borrow postcondition**: `*ret === self[i]` (guarantees structural equality)
- **Structural equality of tracked types**: DOES imply field ID equality 
- **Mode requirements**: `tracked_borrow` works in exec context with `seq.borrow().tracked_borrow(i)`

## What the Fix Should Be

### 🎯 **Correct Approach**
Instead of removing assumes, **add the missing precondition**:

```rust
pub proof fn establish_tracked_borrow_correspondence(
    virtual_perms: &VirtualMuxAlarmPerms,  
    perms: &MuxAlarmPerms,
    index: int,
)
    requires
        self.mux_alarm_wf(perms),
        0 <= index < perms.virtual_alarm_states_seq@.len(),
        // ADD THIS: Establish that virtual_perms came from tracked_borrow
        *virtual_perms === perms.virtual_alarm_states_seq@[index],
    ensures
        virtual_perms.armed_perm.id() === perms.virtual_alarm_states_seq@[index].armed_perm.id(),
```

### 🎯 **Call Site Changes**
Update all call sites to provide this precondition, e.g.:
```rust
let tracked virtual_perms = perms.virtual_alarm_states_seq.borrow().tracked_borrow(sequence_index);
proof {
    // Now we can call the proof function with the established relationship
    self.establish_tracked_borrow_correspondence(virtual_perms, perms, sequence_index);
}
```

## Mental Models That Changed

### 🧠 **Before: Bottom-Up Debugging**  
"The verification primitive must be broken, let me understand the implementation"

### 🧠 **After: Top-Down Context Analysis**
"The primitive works, let me trace how the context flows from where it's established to where it's needed"

### 🧠 **Before: Assume = Language Limitation**
"If there's an assume, it's probably a fundamental language limitation"

### 🧠 **After: Assume = Missing Context**  
"If there's an assume, it's probably missing preconditions or context propagation"

## Key Insight for Verus Verification

**Verus verification often fails not because the fundamental mechanisms don't work, but because the logical relationships aren't being properly established and propagated through the proof context.**

The fix is usually adding the right preconditions/invariants rather than working around language limitations.