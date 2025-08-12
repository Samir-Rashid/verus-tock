use vstd::cell::*;
use vstd::prelude::*;

verus! {
    fn alarm(&'a self, Tracked(perms): Tracked<&mut MuxAlarmPerms>)
        ensures
            // POSTCONDITION 1: Interrupt always scheduled correctly (Progress)
            // If there exists at least one armed virtual alarm, then the hardware alarm must be set
            // to the soonest (earliest) among all armed virtual alarms.
            //
            // 1. There exists a virtual alarm whose fire time matches the next_tick_vals
            (exists|i: int|
                // Check all virtual alarms in the sequence
                0 <= i < perms.virtual_alarm_states_seq@.len() &&
                // which are initialized
                perms.virtual_alarm_states_seq@[i].armed_perm.is_init() &&
                // and armed/enabled
                #[trigger] perms.virtual_alarm_states_seq@[i].armed_perm.value()) ==>
                // If at least one virtual alarm is armed, then:
                perms.next_tick_vals_perm.value().is_some() &&
                (exists|k: int|
                    0 <= k < perms.virtual_alarm_states_seq@.len() &&
                    perms.virtual_alarm_states_seq@[k].armed_perm.is_init() &&
                    #[trigger] perms.virtual_alarm_states_seq@[k].armed_perm.value() &&
                    perms.virtual_alarm_states_seq@[k].dt_reference_perm.is_init() &&
                    // fire_time[k] = reference[k] + dt[k] = next_tick_vals.reference + next_tick_vals.dt
                    #[trigger] perms.virtual_alarm_states_seq@[k].dt_reference_perm.value().reference.wrapping_add(#[trigger] perms.virtual_alarm_states_seq@[k].dt_reference_perm.value().dt).get_value() == perms.next_tick_vals_perm.value().unwrap().0.wrapping_add(perms.next_tick_vals_perm.value().unwrap().1).get_value()),

            // 2. next_tick_vals is sooner than or equal to every armed virtual alarm
            (exists|i: int|
                // Check all virtual alarms in the sequence
                0 <= i < perms.virtual_alarm_states_seq@.len() &&
                // which are initialized
                perms.virtual_alarm_states_seq@[i].armed_perm.is_init() &&
                // and armed/enabled
                #[trigger] perms.virtual_alarm_states_seq@[i].armed_perm.value()) ==>
                // If at least one virtual alarm is armed, then:
                perms.next_tick_vals_perm.value().is_some() &&
                forall|j: int|
                    0 <= j < perms.virtual_alarm_states_seq@.len() &&
                    perms.virtual_alarm_states_seq@[j].armed_perm.is_init() &&
                    #[trigger] perms.virtual_alarm_states_seq@[j].armed_perm.value() ==>
                        perms.virtual_alarm_states_seq@[j].dt_reference_perm.is_init() &&
                        // difference between next_tick_vals and old(next_tick_vals) is <= difference between fire_time[j] and old(next_tick_vals) using modulo 2^32
                        // which is equivalent to checking that there is no sooner possible alarm to set
                        perms.next_tick_vals_perm.value().unwrap().0.wrapping_sub(old(perms).next_tick_vals_perm.value().unwrap().0).get_value() <= perms.virtual_alarm_states_seq@[j].dt_reference_perm.value().reference.wrapping_add(perms.virtual_alarm_states_seq@[j].dt_reference_perm.value().dt).wrapping_sub(old(perms).next_tick_vals_perm.value().unwrap().0).get_value(),

            // POSTCONDITION 2: Hardware arming invariant
            // If there are no armed virtual alarms remaining, then the hardware alarm must be
            // disarmed (`next_tick_vals` is `None`).
            (forall|i: int|
                // Check all virtual alarms in the sequence
                0 <= i < perms.virtual_alarm_states_seq@.len() ==>
                // !perms.virtual_alarm_states_seq@[i].armed_perm.is_init() || // Either the permission is not initialized OR
                //  the alarm is not armed
                !#[trigger] perms.virtual_alarm_states_seq@[i].armed_perm.value()) ==>
                    // Then the hardware alarm should be disarmed (no next tick scheduled)
                    perms.next_tick_vals_perm.value().is_none(),

            // POSTCONDITION 3: All elapsed alarms have fired invariant (Preservation)
            // All virtual alarms that were scheduled to fire at exactly the current time (now)
            // have been properly handled: they are disarmed and their client callbacks have been
            // invoked. This ensures that alarms fire exactly once and don't remain armed after firing.
            forall|i: int|
                // Check all virtual alarms that existed before this function call
                0 <= i < #[trigger] old(perms).virtual_alarm_states_seq@.len() ==> {
                // Only process alarms that had valid timing configuration before
                old(perms).virtual_alarm_states_seq@[i].dt_reference_perm.is_init() ==> {
                    // Get the old timing configuration for this virtual alarm
                    let old_dt_ref = #[trigger] old(perms).virtual_alarm_states_seq@[i].dt_reference_perm.value();
                    // Calculate when this alarm was supposed to fire
                    let old_fire_time = old_dt_ref.reference.get_value() + old_dt_ref.dt.get_value();
                    // Get the current time (when the hardware interrupt fired)
                    let now = (*old(perms).alarm).fire_time;
                    // If this alarm was supposed to fire exactly now AND was armed before:
                    (old_fire_time == now &&
                     old(perms).virtual_alarm_states_seq@[i].armed_perm.is_init() &&
                     #[trigger] old(perms).virtual_alarm_states_seq@[i].armed_perm.value()) ==> {
                        // Then it must now be disarmed (callback has been invoked)
                        perms.virtual_alarm_states_seq@[i].armed_perm.is_init() &&
                        !#[trigger] perms.virtual_alarm_states_seq@[i].armed_perm.value()
                    }
                }
            },
} // verus!
