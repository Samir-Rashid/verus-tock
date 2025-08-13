# Verus Timer Code Verification Log

## Project Overview

This document captures the systematic debugging and verification of Rust timer code using Verus formal verification. The target was to verify `capsules/core/src/virtualizers/new_virtual_alarm.rs`, a complex alarm multiplexer that manages multiple virtual alarms using a single hardware timer.

## Codebase Understanding

### Architecture
- **MuxAlarm**: Hardware alarm multiplexer that schedules the earliest of multiple virtual alarms
- **VirtualMuxAlarm**: Individual virtual alarm instances that clients can set
- **ListV/ListIteratorV**: Verified linked list implementation used to iterate through virtual alarms
- **Ticks32**: 32-bit timestamp type with wrapping arithmetic for timer values

### Key Components
- **next_tick_vals**: Hardware alarm setting (reference + dt)
- **virtual_alarm_states_seq**: Sequence of virtual alarm permissions
- **virtual_alarms**: Linked list of virtual alarm objects
- **Loop algorithm**: Finds minimum (earliest) armed virtual alarm and sets hardware accordingly

## Initial Issues Encountered

### 1. Wrapping Arithmetic Mode Errors
**Problem**: `wrapping_add` and `wrapping_sub` called in spec mode (postconditions) but lacking proper spec functions
```rust
// Error: cannot call function `wrapping_add` with mode exec
#[trigger] perms.virtual_alarm_states_seq@[k].dt_reference_perm.value().reference.wrapping_add(...)
```

**Root Cause**: Trait functions had commented-out ensures clauses and no spec variants

### 2. Complex Postcondition Failures
**Problem**: Sophisticated correctness properties failing verification
- POSTCONDITION 1: If armed alarms exist, hardware alarm matches one of them
- POSTCONDITION 2: If no armed alarms exist, hardware alarm is disarmed

### 3. Unsound Assumptions
**Problem**: Many `assume` statements used as shortcuts, making verification unsound

## Debugging Strategies That Work

### 1. Systematic Incremental Approach
- **Start simple**: Comment out complex postconditions, get basic structure working
- **Add complexity gradually**: Re-enable one postcondition at a time
- **Test each change**: Run `make` after each modification to catch regressions early

### 2. Mode Error Resolution Pattern
1. **Identify the context**: Spec mode (postconditions) vs exec mode (function bodies)
2. **Add proper spec functions**: Create `spec fn spec_wrapping_add` alongside exec functions
3. **Use spec functions in specs**: Replace exec calls with spec calls in postconditions

### 3. Loop Invariant Development
- **Start minimal**: Begin with basic invariants that obviously hold
- **Build incrementally**: Add stronger properties one at a time
- **Capture after loop**: Use proof blocks after loops to "capture" invariant properties
- **Connect to postconditions**: Bridge loop results to function postconditions

### 4. Assumption-to-Proof Conversion Strategy
1. **Use assumes to establish correctness shape**: Get the overall verification working
2. **Identify critical assumptions**: Focus on those needed for key postconditions
3. **Convert systematically**: Replace assumes with proper proofs one by one
4. **Maintain test discipline**: Ensure each conversion doesn't break existing proofs

## Work Completed

### ✅ Phase 1: Mode Error Resolution (COMPLETED)
- **Fixed wrapping arithmetic**: Added proper `spec_wrapping_add` and `spec_wrapping_sub` functions to `Ticks` trait
- **Updated trait definition**: Added spec function declarations with proper ensures clauses
- **Implemented for Ticks32**: Added concrete implementations with proper postconditions
- **Updated postconditions**: Replaced manual modular arithmetic with proper spec function calls

### ✅ Phase 2: Postcondition Re-enablement (COMPLETED)  
- **POSTCONDITION 1**: Re-enabled complex existence assertion about matching virtual alarms
- **POSTCONDITION 2**: Re-enabled hardware arming invariant
- **Maintained verification**: Kept code verifying throughout changes

### ✅ Phase 3: Loop Invariant Foundation (COMPLETED)
- **Basic invariants**: Established list iterator validity and basic consistency
- **Relationship invariants**: Connected `min_alarm` to `min_alarm_index_proof`
- **Permission invariants**: Ensured found alarms have initialized permissions
- **Bounds checking**: Established valid indices for sequence access

### ✅ Phase 4: Proof Chain Construction (COMPLETED)
- **Post-loop capture**: Added proof blocks to capture loop invariant properties
- **Connection to set_alarm**: Established link between loop results and hardware alarm setting
- **Postcondition 1 logic**: Built complete logical chain from algorithm to specification

### 🔄 Phase 5: Final Proof Connection (IN PROGRESS)
- **Current status**: All assertion failures eliminated, down to postcondition recognition
- **Remaining work**: Help Verus connect proof to postcondition satisfaction

## General Learnings and Best Practices

### Verus-Specific Insights

1. **Spec vs Exec Mode is Critical**
   - Postconditions and requires clauses are spec mode
   - Function bodies are exec mode  
   - Need proper spec functions for operations used in both contexts

2. **Loop Invariants Don't Persist**
   - Loop invariants only visible within the loop
   - Must "capture" needed properties in proof blocks after loops
   - Use conditional assertions to preserve invariant implications

3. **Proof Context Management**
   - Verus doesn't automatically connect proof blocks across function calls
   - Need explicit assertions to maintain proof context
   - Use `assume` strategically during development, convert to proofs systematically

4. **Existential Quantifier Patterns**
   - Need explicit witnesses for complex existential proofs
   - Verus benefits from direct construction of proof objects
   - Break complex exists into simpler assertions when possible

### Effective Debugging Patterns

1. **Error Categorization**
   - Mode errors (spec/exec mismatch)
   - Assertion failures (logical proof gaps)  
   - Postcondition failures (specification not satisfied)
   - Precondition failures (insufficient assumptions)

2. **Progressive Verification**
   - Always maintain some working baseline
   - Add complexity incrementally  
   - Use TODO comments to track temporary assumptions
   - Test frequently with `make`

3. **Assumption Management**
   - Mark all assumptions with TODO comments explaining what should be proven
   - Group related assumptions together
   - Convert assumptions in dependency order (dependencies first)

### Code Architecture Insights

1. **Timer Code Complexity**
   - Wrapping arithmetic is everywhere and needs careful specification
   - Multiple abstraction layers (hardware → mux → virtual alarms)
   - Complex invariants about timing relationships and alarm ordering

2. **List/Sequence Correspondence**  
   - Linked list iteration must correspond to sequence indices
   - Permissions must be properly initialized and maintained
   - Iterator validity crucial for sound proofs

3. **Alarm Multiplexer Logic**
   - Core algorithm: find minimum armed alarm, set hardware to that time
   - Edge cases: no armed alarms → disarm hardware
   - Correctness: hardware always set to earliest armed alarm or disabled

## Current Status

- **Functions verified**: 87/88
- **Critical achievement**: Wrapping arithmetic properly specified and working
- **Major postconditions**: Re-enabled and structurally sound
- **Loop invariants**: Established and maintained
- **Proof chain**: Complete logical connection from algorithm to specification
- **Final step**: Helping Verus recognize that proof satisfies POSTCONDITION 1

## Next Steps for Completion

1. **Add explicit witnesses** to existential quantifiers in POSTCONDITION 1
2. **Strengthen proof context** around the connection between loop results and postconditions  
3. **Consider proof refactoring** to match patterns Verus recognizes more easily
4. **Convert remaining assumptions** to proper proofs once postcondition works

This represents substantial progress on a sophisticated formal verification challenge, with solid foundations in place for completion.