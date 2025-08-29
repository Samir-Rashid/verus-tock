use vstd::prelude::*;
use vstd::cell::*;

verus! {

// EXACT tracked struct from source
pub tracked struct VirtualMuxAlarmPerms {
    pub tracked armed_perm: PointsTo<bool>,
}

// Minimal reproducer: Test tracked_borrow in exec context (like the source)
fn test_tracked_borrow_id_correspondence_in_exec_context(
    seq: &mut Tracked<Seq<VirtualMuxAlarmPerms>>
)
    requires 
        old(seq)@.len() > 0,
        old(seq)@[0].armed_perm.is_init(),
    ensures
        seq@ == old(seq)@,
{
    let ghost index = 0;
    
    // EXACT LINE 991 from new_virtual_alarm.rs pattern:
    let tracked virtual_perms = seq.borrow().tracked_borrow(index);
    
    proof {
        // tracked_borrow postcondition guarantees: *virtual_perms === seq@[index]
        assert(*virtual_perms === seq@[index]);
        
        // The question: Does structural equality of tracked types imply ID equality?
        // This is the exact assertion that fails and requires assume() in line 560:
        assert(virtual_perms.armed_perm.id() === seq@[index].armed_perm.id());
    }
}

// Test to isolate if the issue is specific to tracked_borrow or general to structural equality
pub proof fn test_structural_equality_implies_id_equality(
    a: &VirtualMuxAlarmPerms,
    b: &VirtualMuxAlarmPerms,
)
    requires 
        *a === *b,
        a.armed_perm.is_init(),
        b.armed_perm.is_init(),
{
    // This should fail if structural equality doesn't imply ID equality for tracked types
    assert(a.armed_perm.id() === b.armed_perm.id());
}

fn main() {
    // The minimal reproducer actually verifies successfully!
    // This means tracked_borrow DOES establish the ID correspondence via structural equality.
    // The issue in the source code must be more complex - possibly involving:
    // 1. Multiple layers of borrowing/references
    // 2. Different contexts where structural equality doesn't hold
    // 3. Or the assumes are unnecessarily conservative
}

} // verus!