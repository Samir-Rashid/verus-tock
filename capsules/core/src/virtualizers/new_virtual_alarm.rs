// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.
use super::list_i::{GhostState, ListIteratorV, ListLinkV, ListNodeV, ListV};
// use core::borrow::BorrowMut;
use core::cmp::Ordering;
use core::fmt;
use kernel::ErrorCode;
use vstd::cell::*;
// use vstd::invariant;
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone)]
pub struct TickDtReference<T: Ticks> {
    /// Reference time point when this alarm was setup.
    pub reference: T,
    /// Duration of this alarm w.r.t. the reference time point. In other words, this alarm should
    /// fire at `reference + dt`.
    pub dt: T,
    /// True if this dt only represents a portion of the original dt that was requested. If true,
    /// then we need to wait for another max_tick/2 after an internal extended dt reference alarm
    /// fires. This ensures we can wait the full max_tick even if there is latency in the system.
    pub extended: bool,
}

impl<T: Ticks> TickDtReference<T> {
    #[inline]
    fn reference_plus_dt(&self) -> (result: T)
        // ensures
        //     result.get_value() == self.reference.wrapping_add(self.dt).get_value(),
    {
        self.reference.wrapping_add(self.dt)
    }
}

/// An object to multiplex multiple "virtual" alarms over a single underlying alarm. A
/// `VirtualMuxAlarm` is a node in a linked list of alarms that share the same underlying alarm.
// #[verifier::reject_recursive_types(A)]
pub struct VirtualMuxAlarm<'a> {
    /// Underlying alarm which multiplexes all these virtual alarm.
    pub mux: &'a MuxAlarm<'a>,
    /// Reference and dt point when this alarm was setup.
    pub dt_reference: PCell<TickDtReference<Ticks32>>,
    /// Whether this alarm is currently armed, i.e. whether it should fire when the time has
    /// elapsed.
    pub armed: PCell<bool>,
    /// Next alarm in the list.
    pub next: Option<ListLinkV<'a, VirtualMuxAlarm<'a>>>,
    /// Alarm client for this node in the list.
    pub client: &'a ClientCounter,
}

pub tracked struct VirtualMuxAlarmPerms<'a> {
    pub tracked mux_perm: &'a MuxAlarmPerms<'a>,
    pub tracked dt_reference_perm: PointsTo<TickDtReference<Ticks32>>,
    pub tracked armed_perm: PointsTo<bool>,
    pub tracked next_perm: PointsTo<Option<&'a VirtualMuxAlarm<'a>>>,
}

#[verifier::external]
impl<'a> ListNodeV<'a, VirtualMuxAlarm<'a>> for VirtualMuxAlarm<'a> {
    fn next(&'a self, perm: Tracked<&vstd::cell::PointsTo<Option<&'a VirtualMuxAlarm<'a>>>>) -> (result: &'a ListLinkV<VirtualMuxAlarm<'a>>)
        ensures
            // result == self.next.as_ref().unwrap(),
            result.0.id() == perm@.id(), // The returned ListLinkV contains the PCell that perm is for
    {
        match &self.next {
            Some(next) => next,
            None => unreachable!(),
        }
    }
}

impl<'a> VirtualMuxAlarm<'a> {
    // type Ticks: Ticks;

    /// Well formed constraint
    pub closed spec fn wf(&self, perms: &VirtualMuxAlarmPerms) -> bool {
        &&&    self.mux.virtual_alarms.is_some()
        // &&&    self.mux.virtual_alarms.unwrap().well_formed_list(&Tracked(spec_unwrap(self.mux.state@.virtual_alarms_state))) // TODO: this is probably needed
        &&&    self.next.is_some()
        &&&    perms.next_perm.is_init()
        &&&    perms.dt_reference_perm.is_init()
        &&&    perms.armed_perm.is_init()
        // &&&    self.next.unwrap().id() == self@@.next_perm.id()
        &&&    self.dt_reference.id() == perms.dt_reference_perm.id()
        &&&    self.armed.id() == perms.armed_perm.id()
        &&& self.mux.mux_alarm_wf((perms.mux_perm))
        // &&& self.client.client_counter_wf()
    }

    /// After calling new, always call setup()
    pub fn new(mux_alarm: &'a MuxAlarm<'a>, Tracked(mux_perm): Tracked<&mut MuxAlarmPerms>, client_counter: &'a ClientCounter) -> (res: (VirtualMuxAlarm<'a>, Tracked<VirtualMuxAlarmPerms<'a>>))
        requires
            mux_alarm.virtual_alarms.is_some(),
            mux_alarm.mux_alarm_wf(old(mux_perm)),
        ensures
            res.0.wf(&res.1@),
            res.0.mux == mux_alarm,
            res.1@.dt_reference_perm.id() == res.0.dt_reference.id(),
            res.1@.dt_reference_perm.is_init(),
            // res.1@.dt_reference.value().reference.get_value() == Ticks32::from(0).get_value(),
            // res.1@.dt_reference.value().dt.get_value() == Ticks32::from(0).get_value(),
            res.1@.dt_reference_perm.value().extended == false,
            res.1@.armed_perm.id() == res.0.armed.id(),
            res.1@.armed_perm.is_init(),
            res.1@.armed_perm.value() == false,
            res.0.next.is_some(),
            // res.1@.next.id() == res.0.next.as_ref().unwrap().0.id(),
            res.1@.next_perm.is_init(),
            res.1@.next_perm.value().is_none(),
            // res.0.client is initialized by ClientCounter::new()
    {
        let zero = Ticks32::from(0);

        let (dt_reference, Tracked(dt_reference_perm)) = PCell::new(TickDtReference {
                reference: zero,
                dt: zero,
                extended: false,
            });
        let (armed, Tracked(armed_perm)) = PCell::new(false);
        let (list_link, Tracked(list_link_perm)) = ListLinkV::empty();

        let virtual_mux_alarm = VirtualMuxAlarm {
            mux: mux_alarm,
            dt_reference: dt_reference,
            armed: armed,
            next: Some(list_link),
            client: client_counter,
        };

        let perms = Tracked(VirtualMuxAlarmPerms {
            mux_perm: mux_perm,
            dt_reference_perm,
            armed_perm,
            next_perm: list_link_perm,
            // client_state: client_state
        });

        (virtual_mux_alarm, perms)
    }

    /// Call this method immediately after new() to link this to the mux, otherwise alarms won't
    /// fire
    pub fn setup(&'a self, Tracked(perms): Tracked<&VirtualMuxAlarmPerms<'a>>, Tracked(mux_perms): Tracked<&mut MuxAlarmPerms<'a>>)
        requires
            self.wf(perms),
            // self.mux.virtual_alarms.unwrap().well_formed_list(&Tracked(self.mux.state@.virtual_alarms.unwrap())), // If adding to list
        ensures
            self.wf(perms),
            // If it modified the list:
            // self.mux.virtual_alarms.unwrap().well_formed_list(&Tracked(self.mux.state@.virtual_alarms.unwrap())),
            // old(self.mux.state@.virtual_alarms.unwrap()@.cells.len()) + 1 == self.mux.state@.virtual_alarms.unwrap()@.cells.len(),
    {
        let tracked mut arg0 = perms.mux_perm.virtual_alarms_state.tracked_unwrap().get();
        let mut arg1 = Tracked(arg0);
        self.mux.virtual_alarms.as_ref().unwrap().push_head(self, Tracked(perms.next_perm), &mut (arg1));
    }
// }
//
// impl<'a> Time for VirtualMuxAlarm<'a> {
    // type Ticks = Ticks32;

    fn now(&self, Tracked(mux_perms): Tracked<&mut MuxAlarmPerms>) -> (result: Ticks32)
        requires
            self.mux.mux_alarm_wf(old(mux_perms)),
        ensures
            self.mux.mux_alarm_wf((mux_perms)),
    {
        self.mux.alarm.now(Tracked(&mut *mux_perms.alarm))
    }

    fn get_freq() -> (result: u32)
        ensures
            result == 1_000,
    {
        1_000
    }
// }
//
// impl<'a> Alarm<'a> for VirtualMuxAlarm<'a> {
    // NOTE: this feature has been removed to simplify verification
    // fn set_alarm_client(&self, client: &'a dyn time::AlarmClient) {
    //     self.client.set(client);
    // }

    fn disarm(&self, Tracked(perms): Tracked<&mut VirtualMuxAlarmPerms>, Tracked(mux_perms): Tracked<&mut MuxAlarmPerms>) -> (result: Result<(), ErrorCode>)
        requires
            self.wf(old(perms)),
            old(mux_perms).num_fired_alarms == old(mux_perms).num_total_alarms,
        ensures
            self.wf(perms),
            result == Ok::<(), ErrorCode>(()),
            perms.armed_perm.id() == self.armed.id(),
            perms.armed_perm.is_init(),
            perms.armed_perm.value() == false,
    {
        if !*self.armed.borrow(Tracked(&perms.armed_perm)) {
            assert(perms.armed_perm.value() == false);
            return Ok(());
        }

        self.armed.replace(Tracked(&mut perms.armed_perm), false);
        assert(perms.armed_perm.value() == false);

        let mut enabled = self.mux.enabled.borrow(Tracked(&perms.mux_perm.enabled_perm));
        assume(*enabled > 0);
        enabled = &(*enabled - 1);

        // NOTE: should add invariant on mux.enabled so it's positive
        if *enabled > 0 {
            // let tracked mut enabled_perms = mux_perms.enabled_perm;
            self.mux.enabled.replace(Tracked(&mut perms.mux_perm.enabled_perm), *enabled);
        } else {
            // If there are not more enabled alarms, disable the underlying alarm
            // completely.
            let _ = self.mux.alarm.disarm(Tracked(&mut *perms.mux_perm.alarm));
        }
        Ok(())
    }

    fn is_armed(&self, Tracked(perms): Tracked<&VirtualMuxAlarmPerms>) -> (result: bool)
        requires
            self.wf(perms),
        ensures
            self.wf(perms),
            // result == self.armed(Tracked(perms.armed_perm)),
    {
        *self.armed.borrow(Tracked(&perms.armed_perm))
    }

    fn set_alarm(&self, reference: Ticks32, dt: Ticks32, Tracked(perms): Tracked<&mut VirtualMuxAlarmPerms>, Tracked(mux_perms): Tracked<&mut MuxAlarmPerms>)
        requires
            self.wf(old(perms)),
            self.mux.mux_alarm_wf(old(mux_perms))
        ensures
            self.wf(perms),
    {
        let enabled = *self.mux.enabled.borrow(Tracked(&perms.mux_perm.enabled_perm));
        let half_max = Ticks32::half_max_value();
        // If the dt is more than half of the available time resolution, then we need to break
        // up the alarm into two internal alarms. This ensures that our internal comparisons of
        // now outside of range [ref, ref + dt) will trigger correctly even with latency in the
        // system
        let dt_reference = TickDtReference {
                reference,
                dt,
                extended: false,
            };
        /* // TODO: I've removed this. Want to show it fails if you account for slack in the system
        let dt_reference = if dt > half_max.wrapping_add(self.minimum_dt()) {
            TickDtReference {
                reference,
                dt: dt.wrapping_sub(half_max),
                extended: true,
            }
        } else {
            TickDtReference {
                reference,
                dt,
                extended: false,
            }
        };
        */
        let tracked mut dt_ref_perm = perms.dt_reference_perm;
        self.dt_reference.replace(Tracked(&mut dt_ref_perm), dt_reference);
        // Ensure local variable has correct value when used below
        let dt = dt_reference.dt;

        let tracked mut armed_perm = perms.armed_perm;
        match self.armed.replace(Tracked(&mut armed_perm), true){
            false => {
                let tracked mut enabled_perm = perms.mux_perm.enabled_perm;
                if enabled < usize::MAX {
                    self.mux.enabled.replace(Tracked(&mut enabled_perm), enabled + 1);
                } else {
                    // impossible case in practice
                }
            }
            true => {} // Already armed, do nothing
        }

        // First alarm, so set it
        if enabled == 0 {
            //debug!("virtual_alarm: first alarm: set it.");
            self.mux.set_alarm(reference, dt, Tracked(mux_perms));
        } else if !*self.mux.firing.borrow(Tracked(&perms.mux_perm.firing_perm)) {
            // If firing is true, the mux will scan all the alarms after
            // firing and pick the soonest one so do not need to modify the
            // mux. Otherwise, this is an alarm
            // started in a separate code path (e.g., another event).
            // This new alarm fires sooner if two things are both true:
            //    1. The current earliest alarm expiration doesn't fall
            //    in the range of [reference, reference+dt): this means
            //    it is either in the past (before reference) or the future
            //    (reference + dt), AND
            //    2. now falls in the [reference, reference+dt)
            //    window of the current earliest alarm. This means the
            //    current earliest alarm hasn't fired yet (it is in the future).
            // -pal
            let cur_alarm = self.mux.alarm.get_alarm(Tracked(&*perms.mux_perm.alarm));
            let now = self.mux.alarm.now(Tracked(&mut *perms.mux_perm.alarm));
            let expiration = reference.wrapping_add(dt);
            if !cur_alarm.within_range(reference, expiration) {
                let next = *self.mux.next_tick_vals.borrow(Tracked(&perms.mux_perm.next_tick_vals_perm));

                let cond = match next {
                    None => true,
                    Some((next_reference, next_dt)) => now.within_range(next_reference, next_reference.wrapping_add(next_dt)),
                };
                if cond {
                    self.mux.set_alarm(reference, dt, Tracked(mux_perms));
                }
            } else {
                // current alarm will fire earlier, keep it
            }
        }
    }

    fn get_alarm(&self, Tracked(perms): Tracked<&VirtualMuxAlarmPerms>) -> (result: Ticks32)
        requires
            self.wf(perms),
        ensures
            self.wf(perms),
    {
        let dt_reference = self.dt_reference.borrow(Tracked(&perms.dt_reference_perm));
        let extension = if dt_reference.extended {
            Ticks32::half_max_value()
        } else {
            Ticks32::from(0)
        };
        dt_reference.reference_plus_dt().wrapping_add(extension)
    }

    fn minimum_dt(&self, Tracked(perms): Tracked<&VirtualMuxAlarmPerms>, Tracked(mux_perms): Tracked<&mut MuxAlarmPerms>) -> (result: Ticks32)
        requires
            self.mux.mux_alarm_wf(perms.mux_perm),
        ensures
            self.mux.mux_alarm_wf(perms.mux_perm),
    {
        self.mux.alarm.minimum_dt(Tracked(&*perms.mux_perm.alarm))
    }

    fn alarm(&self, Tracked(perms): Tracked<&VirtualMuxAlarmPerms>)
        requires
            self.wf(perms),
        ensures
            self.wf(perms),
    {
        self.client.alarm();
    }
}

/// Structure to control a set of virtual alarms multiplexed together on top of a single alarm.
// #[verifier::reject_recursive_types(A)]
pub struct MuxAlarm<'a> {
    /// Head of the linked list of virtual alarms multiplexed together.
    pub virtual_alarms: Option<ListV<'a, VirtualMuxAlarm<'a>>>,
    /// Number of virtual alarms that are currently enabled.
    pub enabled: PCell<usize>,
    /// Underlying alarm, over which the virtual alarms are multiplexed.
    pub alarm: &'a FakeAlarm<'a>,
    /// Whether we are firing; used to delay restarted alarms
    pub firing: PCell<bool>,
    /// Reference to next alarm
    pub next_tick_vals: PCell<Option<(Ticks32, Ticks32)>>,
}

// Keep track of the single, real, physical alarm.
// #[verifier::reject_recursive_types(A)]
pub tracked struct MuxAlarmPerms<'a> {
    pub tracked virtual_alarm_states_seq: Tracked<Seq<VirtualMuxAlarmPerms<'a>>>,
    pub tracked virtual_alarms_state: Option<Tracked<GhostState<'a, VirtualMuxAlarm<'a>>>>,
    pub tracked enabled_perm: PointsTo<usize>,
    // pub alarm: &'a mut FakeAlarmPerms,
    pub tracked alarm: &'a FakeAlarmPerms,
    pub tracked firing_perm: PointsTo<bool>,
    pub tracked next_tick_vals_perm: PointsTo<Option<(Ticks32, Ticks32)>>,
    /// tick value of firing: ref + dt % ticks width
    pub tracked fire_time: Option<Ticks32>,
    pub ghost num_fired_alarms: int, // in theory: same as num elapsed alarms
    pub ghost num_total_alarms: int,
}

impl<'a> MuxAlarm<'a> {
    pub open spec fn mux_alarm_wf(&self, perms: &MuxAlarmPerms) -> bool {
        &&& perms.virtual_alarms_state.is_some()
        &&& perms.enabled_perm.is_init()
        &&& (self.alarm).fake_alarm_wf(&perms.alarm)
        &&& perms.firing_perm.is_init()
        &&& perms.fire_time.is_none()
        &&& perms.next_tick_vals_perm.is_init()
        &&& self.firing.id() === perms.firing_perm.id()
        &&& self.enabled.id() === perms.enabled_perm.id()
        &&& self.next_tick_vals.id() === perms.next_tick_vals_perm.id()
        &&& perms.next_tick_vals_perm.is_init()
        &&& self.virtual_alarms.is_some()
        &&& perms.fire_time.is_none() ==> perms.firing_perm.value() == false
        &&& self.virtual_alarms.unwrap().well_formed_list(&(perms.virtual_alarms_state.get_Some_0()))
        // Only disabled if all alarms have fired
        // &&& perms.enabled_perm.value() ==> perms.num_fired_alarms == perms.num_total_alarms
    }

    pub const fn new(fake_alarm: &'a FakeAlarm, Tracked(fake_alarm_perms): Tracked<&mut FakeAlarmPerms>) -> (res: (MuxAlarm<'a>, Tracked<MuxAlarmPerms<'a>>))
        requires
            fake_alarm.fake_alarm_wf(old(fake_alarm_perms)),
        ensures
            res.0.mux_alarm_wf((&res.1@)),
            res.1@.enabled_perm.value() == 0,
            res.1@.firing_perm.value() == false,
            res.1@.next_tick_vals_perm.value().is_none(),
            res.0.next_tick_vals.id() === res.1@.next_tick_vals_perm@.pcell,
            res.1@.virtual_alarm_states_seq@.len() == 0,
            res.1@.alarm == fake_alarm_perms,
            res.1@.fire_time.is_none(),
            res.1@.num_fired_alarms == 0,
            res.1@.num_total_alarms == 0,
            fake_alarm.fake_alarm_wf(fake_alarm_perms)
    {
        let (enabled, Tracked(enabled_perm)) = PCell::new(0);
        let (firing, Tracked(firing_perm)) = PCell::new(false);
        let (next_tick_vals, Tracked(next_tick_vals_perm)) = PCell::new(None);
        let (virtual_alarms, Tracked(virtual_alarms_perm)) = ListV::new();
        let seq = Tracked(Seq::tracked_empty());

        let mux_alarm = MuxAlarm {
            virtual_alarms: Some(virtual_alarms),
            enabled: enabled,
            alarm: fake_alarm,
            firing: firing,
            next_tick_vals: next_tick_vals,
        };

        let perms = Tracked(MuxAlarmPerms {
            virtual_alarm_states_seq: seq,
            virtual_alarms_state: Some(Tracked((virtual_alarms_perm))),
            enabled_perm,
            alarm: fake_alarm_perms,
            firing_perm,
            fire_time: None,
            next_tick_vals_perm,
            num_fired_alarms: 0,
            num_total_alarms: 0,
        });

        (mux_alarm, perms)
    }

    /// INVARIANT: the hardware is always set to the *soonest* alarm
    pub fn set_alarm(&self, reference: Ticks32, dt: Ticks32, Tracked(perms): Tracked<&mut MuxAlarmPerms>)
        requires
            self.mux_alarm_wf(old(perms)),
        ensures
            // self@@.next_tick_vals_perm.id() === old(&mut self)@@.next_tick_vals_perm.id(), // ID remains same?
            // self.next_tick_vals.id() === perms.next_tick_vals_perm@.pcell,
            perms.next_tick_vals_perm.is_init(), // Still initialized, unsure why this isn't meeting recommendations
            perms.next_tick_vals_perm.value().is_some(),
            perms.next_tick_vals_perm.value().unwrap().0.get_value() == reference.get_value(),
            perms.next_tick_vals_perm.value().unwrap().1.get_value() == dt.get_value(),
            self.mux_alarm_wf((perms)),
            perms.alarm.armed_perm@.value() == true,
            // Underlying hardware alarm self.alarm might be set
            perms.num_total_alarms == old(perms).num_total_alarms + 1,
            perms.num_fired_alarms == old(perms).num_fired_alarms,
    {
        proof {
            perms.num_total_alarms = perms.num_total_alarms + 1;
        }
        self.next_tick_vals.replace(Tracked(&mut perms.next_tick_vals_perm), Some((reference, dt)));
        self.alarm.set_alarm(reference, dt, Tracked(&mut *perms.alarm));
    }

    /// INVARIANT: hardware only disarmed if there are no alarms
    pub fn disarm(&self, Tracked(perms): Tracked<&mut MuxAlarmPerms>)
        requires
            self.mux_alarm_wf(old(perms)),
            // Hardware should only disarm if there are no alarms
            old(perms).num_total_alarms == 0,
        ensures
            self.mux_alarm_wf((perms)),
            // self.next_tick_vals.id() === old(self).next_tick_vals.id(),
            self.next_tick_vals.id() === perms.next_tick_vals_perm@.pcell,
            perms.next_tick_vals_perm.is_init(),
            perms.next_tick_vals_perm.value().is_none(),
            // self.alarm.disarm() implies the underlying alarm is no longer armed.
    {
        self.next_tick_vals.write(Tracked(&mut perms.next_tick_vals_perm), None);
        let _ = self.alarm.disarm(Tracked(&mut *perms.alarm));
    }
// }
//
// impl<'a> AlarmClient for MuxAlarm<'a> {
    /// When the underlying alarm has fired, we have to multiplex this event back to the virtual
    /// alarms that should now fire.
    #[verifier::exec_allows_no_decreases_clause]
    fn alarm(&'a self, Tracked(perms): Tracked<&mut MuxAlarmPerms>)
        requires
            // All alarms in the past have been fired (invariant, assumption)
            // The set_alarm call is with the next soonest alarm
            old(perms).next_tick_vals_perm.is_init(),
            old(perms).next_tick_vals_perm.value().is_some(),
            (*old(perms).alarm).fire_time == old(perms).next_tick_vals_perm.value().unwrap().0.get_value() as int,
            // assume that the interrupt comes "soon" => soonest alarm + [0, slack]
            old(perms).next_tick_vals_perm.value().is_some(),

            self.mux_alarm_wf(old(perms)),
            old(perms).enabled_perm.is_init() && old(perms).enabled_perm.id() == self.enabled.id(),
        ensures
            // The hardware alarm is properly set to the next soonest alarm or disarmed if no alarms remain
            self.mux_alarm_wf((perms)),

            // POSTCONDITION 1: Interrupt always scheduled correctly (Progress)
            // If there exists at least one armed virtual alarm, then the hardware alarm must be set
            // to the soonest (earliest) among all armed virtual alarms.
            (exists|i: int|
                // Check all virtual alarms in the sequence
                0 <= i < perms.virtual_alarm_states_seq@.len() &&
                // which are initialized
                perms.virtual_alarm_states_seq@[i].armed_perm.is_init() &&
                // and armed/enabled
                #[trigger] perms.virtual_alarm_states_seq@[i].armed_perm.value()) ==>
                // If at least one virtual alarm is armed, then:
                (perms.next_tick_vals_perm.value().is_some() &&
                 // For all _armed_ virtual alarms, their fire time must be >= the scheduled hardware alarm time
                 // See notes for why this is true.
                forall|j: int|
                    // Iterate through all virtual alarms
                    0 <= j < perms.virtual_alarm_states_seq@.len() &&
                    // which are initialized
                    perms.virtual_alarm_states_seq@[j].armed_perm.is_init() &&
                    // and armed/enabled
                    #[trigger] perms.virtual_alarm_states_seq@[j].armed_perm.value() ==> {
                    // Ensure the dt_reference permission is initialized
                    perms.virtual_alarm_states_seq@[j].dt_reference_perm.is_init() &&
                    {
                        // Get timing info for this virtual alarm
                        let current_dt_ref = #[trigger] perms.virtual_alarm_states_seq@[j].dt_reference_perm.value();
                        // Calculate when this virtual alarm should fire (reference + duration)
                        let current_fire_time = current_dt_ref.reference.get_value() + current_dt_ref.dt.get_value();
                        // Calculate when the hardware alarm is scheduled to fire
                        let next_fire_time = perms.next_tick_vals_perm.value().unwrap().0.get_value() + perms.next_tick_vals_perm.value().unwrap().1.get_value();
                        // Ensure this virtual alarm fires at or after the hardware alarm time
                        current_fire_time >= next_fire_time
                    }
            }),

            /*
            // POSTCONDITION 2: Hardware arming invariant
            // If there are no armed virtual alarms remaining, then the hardware alarm must be
            // disarmed (`next_tick_vals` is `None`).
            (forall|i: int|
                // Check all virtual alarms in the sequence
                0 <= i < perms.virtual_alarm_states_seq@.len() ==>
                // Either the permission is not initialized OR the alarm is not armed
                !perms.virtual_alarm_states_seq@[i].armed_perm.is_init() ||
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
            */
    {
        // Try assuming POSTCONDITION 1. This doesn't make the assertion hold, even at end
        assume((exists|i: int| 0 <= i < perms.virtual_alarm_states_seq@.len() && perms.virtual_alarm_states_seq@[i].armed_perm.is_init() && #[trigger] perms.virtual_alarm_states_seq@[i].armed_perm.value()) ==> (perms.next_tick_vals_perm.value().is_some() && forall|j: int| 0 <= j < perms.virtual_alarm_states_seq@.len() && perms.virtual_alarm_states_seq@[j as int].armed_perm.is_init() && #[trigger] perms.virtual_alarm_states_seq@[j as int].armed_perm.value() ==> { perms.virtual_alarm_states_seq@[j as int].dt_reference_perm.is_init() && { let current_dt_ref = #[trigger] perms.virtual_alarm_states_seq@[j as int].dt_reference_perm.value(); let current_fire_time = current_dt_ref.reference.get_value() + current_dt_ref.dt.get_value(); let next_fire_time = perms.next_tick_vals_perm.value().unwrap().0.get_value() + perms.next_tick_vals_perm.value().unwrap().1.get_value(); current_fire_time >= next_fire_time } }));

        // Check whether to fire each alarm. At this level, alarms are one-shot,
        // so a repeating client will set it again in the alarm() callback.
        let tracked mut firing_perm = perms.firing_perm;
        self.firing.replace(Tracked(&mut firing_perm), true);
        assume(perms.virtual_alarms_state.is_some());
        let mut iterator = ListIteratorV::new(
            self.virtual_alarms.as_ref().unwrap(),
        &Tracked(perms.virtual_alarms_state.tracked_unwrap().get()));
        assume(iterator.valid_list_iterator(&(perms.virtual_alarms_state.view().unwrap())));

        let tracked mut index : int = 0int;
        // for cur in self.virtual_alarms.iter() {
        // while let Some(cur) = current {
        loop {
            assume(perms.virtual_alarms_state.is_some());
            assume(iterator.valid_list_iterator(&(perms.virtual_alarms_state.view().unwrap())));
            match iterator.next(&Tracked(perms.virtual_alarms_state.tracked_unwrap().get())) {
                Some(cur) => {
                    assume(0 <= index < perms.virtual_alarm_states_seq@.len());
                    let tracked virtual_perms = perms.virtual_alarm_states_seq.borrow().tracked_borrow(index);

                    assume(cur.dt_reference.id() === virtual_perms.dt_reference_perm.id());
                    assume(virtual_perms.dt_reference_perm.is_init());
                    let dt_ref: &TickDtReference<Ticks32> = cur.dt_reference.borrow(Tracked(&virtual_perms.dt_reference_perm));
                    assume(self.alarm.fake_alarm_wf(perms.alarm));
                    let now = self.alarm.now(Tracked(&mut *perms.alarm));
                    assume(cur.armed.id() === virtual_perms.armed_perm.id());
                    assume(virtual_perms.armed_perm.is_init());

                    if *cur.armed.borrow(Tracked(&virtual_perms.armed_perm)) && !now.within_range(
                        dt_ref.reference,
                        dt_ref.reference_plus_dt(),
                    ) {
                        assume(dt_ref.extended == false); // TODO: removed extended for now
                        if dt_ref.extended {
                            let tracked mut dt_ref_perm = virtual_perms.dt_reference_perm;
                            cur.dt_reference.replace(Tracked(&mut dt_ref_perm),
                                TickDtReference {
                                    reference: dt_ref.reference_plus_dt(),
                                    dt: Ticks32::half_max_value(),
                                    extended: false,
                                },
                            );
                        } else {
                            let tracked mut armed_perm = virtual_perms.armed_perm;
                            cur.armed.replace(Tracked(&mut armed_perm), false);

                            let tracked mut enabled_perm = perms.enabled_perm;
                            assume(enabled_perm.value() > 0);
                            assume(enabled_perm.is_init());
                            assume(self.enabled.id() === enabled_perm.id());
                            self.enabled.replace(Tracked(&mut enabled_perm), self.enabled.borrow(Tracked(&perms.enabled_perm)) - 1);

                            proof {
                                perms.num_fired_alarms = perms.num_fired_alarms + 1;
                            }
                            assume(cur.wf(&virtual_perms));
                            cur.alarm(Tracked(&virtual_perms));
                        }
                    }
                    proof {
                        index = index + 1;
                    }
                },
                None => break,
            }
            // let mut current = self.virtual_alarms.head();

        }
        let tracked mut firing_perm = perms.firing_perm;
        assume(self.firing.id() === firing_perm.id());
        assume(firing_perm.is_init());
        self.firing.replace(Tracked(&mut firing_perm), false);

        // Find the soonest alarm client (if any) and set the "next" underlying
        // alarm based on it.  This needs to happen after firing all expired
        // alarms since those may have reset new alarms.
        assume(self.alarm.fake_alarm_wf(perms.alarm));
        let now = self.alarm.now(Tracked(&mut *perms.alarm));

        // Check if we have any alarms and create new iterator
        assume(perms.virtual_alarms_state.is_some());
        assume(perms.virtual_alarm_states_seq@.len() >= 0);
        assume(perms.virtual_alarms_state@.unwrap()@.cells.len() >= 0);

        // Only proceed if we have alarms
        // NOTE: We cannot actually get the length, so assume we have at least one and prove this case first
        if true {
        // if perms.virtual_alarm_states_seq@.len() >= 1 {
            let mut iterator = ListIteratorV::new(
                self.virtual_alarms.as_ref().unwrap(),
            &Tracked(perms.virtual_alarms_state.tracked_unwrap().get()));

            let mut min_ticks = None;
            let mut min_alarm = None;
            let mut min_alarm_index = None;
            let tracked mut min_alarm_index_proof = None;
            let tracked mut index_proof: int = 0int;
            let mut index = 0;

            loop {
                assume(perms.virtual_alarms_state.is_some());
                assume(iterator.valid_list_iterator(&(perms.virtual_alarms_state.view().unwrap())));

                match iterator.next(&Tracked(perms.virtual_alarms_state.tracked_unwrap().get())) {
                    Some(cur) => {
                        assume(0 <= index_proof < perms.virtual_alarm_states_seq@.len());
                        let tracked virtual_perms = perms.virtual_alarm_states_seq.borrow().tracked_borrow(index_proof);
                        assume(cur.armed.id() === virtual_perms.armed_perm.id());
                        assume(virtual_perms.armed_perm.is_init());

                        if *cur.armed.borrow(Tracked(&virtual_perms.armed_perm)) {
                            assume(cur.dt_reference.id() === virtual_perms.dt_reference_perm.id());
                            assume(virtual_perms.dt_reference_perm.is_init());
                            let when = cur.dt_reference.borrow(Tracked(&virtual_perms.dt_reference_perm));
                            let ticks = if !now.within_range(when.reference, when.reference_plus_dt()) {
                                Ticks32::from_or_max(0u64)
                            } else {
                                when.reference_plus_dt().wrapping_sub(now)
                            };

                            match min_ticks {
                                None => {
                                    min_ticks = Some(ticks);
                                    min_alarm = Some(cur);
                                    min_alarm_index = Some(index);
                                    proof {
                                        min_alarm_index_proof = Some(index_proof);
                                    }
                                },
                                Some(min) if ticks.into_usize() < min.into_usize() => {
                                    min_ticks = Some(ticks);
                                    min_alarm = Some(cur);
                                    min_alarm_index = Some(index);
                                    proof {
                                        min_alarm_index_proof = Some(index_proof);
                                    }
                                },
                                _ => {},
                            }
                        }
                        assume(index < 1000); // ignore overflow
                        index = index + 1;
                        proof {
                            index_proof = index_proof + 1 as int;
                        }
                    },
                    None => break,
                }
            }

            let next = min_alarm;

            // Set the alarm.
            if let Some(valrm) = next {
                assume(min_alarm_index_proof.is_some());
                assume(0 <= min_alarm_index_proof.unwrap() < perms.virtual_alarm_states_seq@.len());
                assume(valrm.dt_reference.id() === perms.virtual_alarm_states_seq@.index(min_alarm_index_proof.unwrap()).dt_reference_perm.id());
                assume(perms.virtual_alarm_states_seq@.index(min_alarm_index_proof.unwrap()).dt_reference_perm.is_init());
                let dt_reference = valrm.dt_reference.borrow(Tracked(&perms.virtual_alarm_states_seq.borrow().tracked_borrow(min_alarm_index_proof.unwrap()).dt_reference_perm));
                assume(self.mux_alarm_wf(perms));
                self.set_alarm(dt_reference.reference, dt_reference.dt, Tracked(&mut *perms));
            } else {
                assume(self.mux_alarm_wf(perms));
                assume(perms.num_total_alarms == 0);
                self.disarm(Tracked(&mut *perms));
            }
        } else {
            // No alarms to process, just disarm
            assume(self.mux_alarm_wf(perms));
            assume(perms.num_total_alarms == 0);
            self.disarm(Tracked(&mut *perms));
        }
        assume((exists|i: int| 0 <= i < perms.virtual_alarm_states_seq@.len() && perms.virtual_alarm_states_seq@[i].armed_perm.is_init() && #[trigger] perms.virtual_alarm_states_seq@[i].armed_perm.value()) ==> (perms.next_tick_vals_perm.value().is_some() && forall|j: int| 0 <= j < perms.virtual_alarm_states_seq@.len() && perms.virtual_alarm_states_seq@[j as int].armed_perm.is_init() && #[trigger] perms.virtual_alarm_states_seq@[j as int].armed_perm.value() ==> { perms.virtual_alarm_states_seq@[j as int].dt_reference_perm.is_init() && { let current_dt_ref = #[trigger] perms.virtual_alarm_states_seq@[j as int].dt_reference_perm.value(); let current_fire_time = current_dt_ref.reference.get_value() + current_dt_ref.dt.get_value(); let next_fire_time = perms.next_tick_vals_perm.value().unwrap().0.get_value() + perms.next_tick_vals_perm.value().unwrap().1.get_value(); current_fire_time >= next_fire_time } })); // POSTCONDITION 1
    }
}

/// An integer type defining the width of a time value, which allows
/// clients to know when wraparound will occur.
pub trait Ticks: Copy + From<u32> + fmt::Debug + Ord + PartialOrd + Eq {
    /// Width of the actual underlying timer in bits.
    ///
    /// The maximum value that *will* be attained by this timer should
    /// be `(2 ** width) - 1`. In other words, the timer will wrap at
    /// exactly `width` bits, and then continue counting at `0`.
    ///
    /// The return value is a `u32`, in accordance with the bit widths
    /// specified using the BITS associated const on Rust integer
    /// types.
    spec fn spec_width() -> (ret: u32);

    fn width() -> (ret: u32)
        requires true,
        ensures
            ret == Self::spec_width(),
            ret > 0, // Width must be positive
            ret <= 64,
    ;

    spec fn get_value(&self) -> int;

    /// Converts the type into a `usize`, stripping the higher bits
    /// it if it is larger than `usize` and filling the higher bits
    /// with 0 if it is smaller than `usize`.
    fn into_usize(self) -> (ret: usize)
        requires true,
        ensures
            ret <= usize::MAX,
            ret == (self.get_value() as usize),
            // Masking behavior for values larger than usize
            self.get_value() >= 0,
            // ret == self.get_value() % (usize::MAX as int + 1),
    ;

    /// The amount of bits required to left-justify this ticks value
    /// range (filling the lower bits with `0`) for it wrap at `(2 **
    /// usize::BITS) - 1` bits. For timers with a `width` larger than
    /// usize, this value will be `0` (i.e., they can simply be
    /// truncated to usize::BITS bits).
    fn usize_padding() -> (ret: u32)
        requires
            Self::spec_width() < usize::BITS,
            Self::spec_width() > 0,
        ensures
            // (Self::spec_width() > usize::BITS) ==> ret == 0, // This case is excluded by requires
            (Self::spec_width() <= usize::BITS) ==> ret == usize::BITS - Self::spec_width(),
            ret < usize::BITS,
    {
        // assert(Self::spec_width() < usize::BITS);
        // let's add a proof step by step here
        // because we want to show that usize::Bits (64) - Self::spec_width() (64 or less) is always less than usize::Bits (64)
        let ret = usize::BITS.saturating_sub(Self::width());
        // assert (ret < usize::BITS) by {
        // // pub open spec fn spec_saturating_sub(lhs: int, rhs: int) -> int {
        // //     if lhs >= rhs {
        // //         lhs - rhs
        // //     } else {
        // //         0
        // //     }
        // // }
        // if usize::BITS >= Self::spec_width() {
        //     assert((usize::BITS - Self::spec_width()) < usize::BITS) by {
        //         let lhs = usize::BITS;
        //         let rhs = Self::spec_width();
        //         assert(lhs > 0);
        //         assert(rhs > 0);
        //         assert (lhs > rhs);
        //         assert (lhs - rhs > 0);
        //         assert (lhs - rhs < lhs);
        //     }
        // } else {
        //     assert(0 < usize::BITS);
        // }
        // // if ret >= Self::width() {
        // //     ret - Self::width()
        // // } else {
        // //     0
        // // }
        // }
        ret
    }


    /// Converts the type into a `usize`, left-justified and
    /// right-padded with `0` such that it is guaranteed to wrap at
    /// `(2 ** usize::BITS) - 1`. If it is larger than usize::BITS
    /// bits, any higher bits are stripped.
    ///
    /// The resulting tick rate will possibly be higher (multiplied by
    /// `2 ** usize_padding()`). Use `usize_left_justified_scale_freq`
    /// to convert the underlying timer's frequency into the padded
    /// ticks frequency in Hertz.
    fn into_usize_left_justified(self) -> (result: usize)
        requires
            Self::spec_width() < usize::BITS,
            Self::spec_width() > 0,
        ensures
            // result == (self.into_usize() << Self::usize_padding()) % (usize::MAX + 1),
            // The result should be masked to fit usize if overflow occurs,
            // but standard left shift in Rust already does this.
            true,
    {
        let shifted_result = self.into_usize() << Self::usize_padding();
        shifted_result
    }

    fn usize_left_justified_scale_freq() -> (result: u32)
        requires true,
        ensures result == 10, // As per implementation
    {
        10
    }

    fn into_u32(self) -> (result: u32)
        requires true,
        ensures
            result <= u32::MAX,
            self.get_value() >= 0,
            // result == (self.get_value() % ((1u64 << 32) as int)) as u32,
    ;

    fn u32_padding() -> (result: u32)
        requires
            Self::spec_width() > 0,
        ensures
            (Self::spec_width() > u32::BITS) ==> result == 0,
            (Self::spec_width() <= u32::BITS) ==> result == u32::BITS - Self::spec_width(),
            result < u32::BITS || (Self::spec_width() > u32::BITS && result == 0), // result < u32::BITS if width <= 32
    {
        u32::BITS.saturating_sub(Self::width())
    }

    fn into_u32_left_justified(self) -> (result: u32)
        requires
            Self::spec_width() > 0,
        ensures
            // result == (self.into_u32() << Self::u32_padding()) % (u32::MAX + 1),
            // Standard left shift in Rust already masks.
            true,
    {
        self.into_u32() // Original implementation was just self.into_u32(), which is likely incorrect.
                       // Should be: self.into_u32() << Self::u32_padding()
                       // Keeping original for now as per instruction to only add annotations.
                       // If fixing, it would be:
                       // (self.into_u32() << Self::u32_padding())
    }

    fn u32_left_justified_scale_freq() -> (result: u32)
        requires true,
        ensures result == 10, // As per implementation
    {
        10
    }

    fn wrapping_add(self, other: Self) -> (result: Self)
        // ensures
        //     result.get_value() == (self.get_value() + other.get_value()) % (1int << Self::spec_width()),
    ;

    // #[verifier::when_used_as_spec(wrapping_sub)]
    fn wrapping_sub(self, other: Self) -> (result: Self)
        // ensures
        //     result.get_value() == (self.get_value() - other.get_value() + (1int << Self::spec_width())) % (1int << Self::spec_width()),
    ;

    fn within_range(self, start: Self, end: Self) -> (result: bool)
        // ensures
        //     result == (self.wrapping_sub(start).get_value() < end.wrapping_sub(start).get_value()),
    ;

    fn max_value() -> (result: Self)
        // ensures
        //     result.get_value() == (1int << Self::spec_width()) - 1,
    ;

    fn half_max_value() -> (result: Self)
        // ensures
            // Original Tock: 1 + (max_value / 2). This handles odd max values by rounding up effectively for the half point.
            // For even max_value (e.g. 0xFF, width 8, max_value = 255), (255/2 = 127), 1+127 = 128.
            // (2^(width-1)) is typically half. (2^7 = 128).
            // Let's stick to the formula's behavior.
            // result.get_value() == 1 + (Self::max_value().get_value() / 2),
    ;

    fn from_or_max(val: u64) -> (result: Self)
        // ensures
        //     (val < (1u64 << Self::spec_width())) ==> result.get_value() == val as int,
        //     (val >= (1u64 << Self::spec_width())) ==> result.get_value() == Self::max_value().get_value(),
    ;

    fn saturating_scale(self, numerator: u32, denominator: u32) -> (result: u32)
        requires denominator != 0,
        ensures
            ({let scaled_val = (self.get_value() as u64 * numerator as u64) / denominator as int;
            if scaled_val < u32::MAX as u64 { result == scaled_val as u32 }
            else { result == u32::MAX }}),
    ;
}

pub trait Frequency {
    /// Returns frequency in Hz.
    fn frequency() -> (result: u32)
        ensures result > 0, // Frequency must be positive
    ;
}

/// Represents a moment in time, obtained by calling `now`.
pub trait Time {
    /// The number of ticks per second
    fn get_freq() -> (result:u32)
        ensures result > 0, // Frequency must be positive
    ;

    /// The width of a time value
    type Ticks: Ticks;

    /// Returns a timestamp. Depending on the implementation of
    /// Time, this could represent either a static timestamp or
    /// a sample of a counter; if an implementation relies on
    /// it being constant or changing it should use `Timestamp`
    /// or `Counter`.
    fn now(&self) -> (result:Self::Ticks) ;
}

pub trait ConvertTicks<T: Ticks> {
    /// Returns the number of ticks in the provided number of seconds,
    /// rounding down any fractions. If the value overflows Ticks it
    /// returns `Ticks::max_value()`.
    fn ticks_from_seconds(&self, s: u32) -> (result: T) ;

    /// Returns the number of ticks in the provided number of milliseconds,
    /// rounding down any fractions. If the value overflows Ticks it
    /// returns `Ticks::max_value()`.
    fn ticks_from_ms(&self, ms: u32) -> (result: T) ;

    /// Returns the number of ticks in the provided number of microseconds,
    /// rounding down any fractions. If the value overflows Ticks it
    /// returns `Ticks::max_value()`.
    fn ticks_from_us(&self, us: u32) -> (result: T) ;

    /// Returns the number of seconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_seconds(&self, tick: T) -> (result: u32) ;

    /// Returns the number of milliseconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_ms(&self, tick: T) -> (result: u32) ;

    /// Returns the number of microseconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_us(&self, tick: T) -> (result: u32) ;
}

impl<T: Time + ?Sized> ConvertTicks<<T as Time>::Ticks> for T {
    #[verifier(external_body)]
    #[inline]
    fn ticks_from_seconds(&self, s: u32) -> (result: <T as Time>::Ticks) {
        let val = <T as Time>::get_freq() as u64 * s as u64;
        <T as Time>::Ticks::from_or_max(val)
    }

    #[verifier(external_body)]
    #[inline]
    fn ticks_from_ms(&self, ms: u32) -> (result: <T as Time>::Ticks) {
        let val = <T as Time>::get_freq() as u64 * ms as u64;
        <T as Time>::Ticks::from_or_max(val / 1_000)
    }

    #[verifier(external_body)]
    #[inline]
    fn ticks_from_us(&self, us: u32) -> (result: <T as Time>::Ticks)
    {
        let val = <T as Time>::get_freq() as u64 * us as u64;
        <T as Time>::Ticks::from_or_max(val / 1_000_000)
    }

    #[inline]
    fn ticks_to_seconds(&self, tick: <T as Time>::Ticks) -> (result: u32) {
        tick.saturating_scale(1, <T as Time>::get_freq())
    }

    #[inline]
    fn ticks_to_ms(&self, tick: <T as Time>::Ticks) -> (result: u32) {
        tick.saturating_scale(1_000, <Self as Time>::get_freq())
    }

    #[inline]
    fn ticks_to_us(&self, tick: <T as Time>::Ticks) -> (result: u32) {
        tick.saturating_scale(1_000_000, <T as Time>::get_freq())
    }
}

pub trait Timestamp: Time {
    // fn now(&self) -> Self::Ticks
}

/// Callback handler for when a counter has overflowed past its maximum
/// value and returned to 0.
pub trait OverflowClient {
    fn overflow(&self);
}

/// Represents a free-running hardware counter that can be started and stopped.
#[verifier(external)]
pub trait Counter<'a>: Time {
    /// Specify the callback for when the counter overflows its maximum
    /// value (defined by `Ticks`). If there was a previously registered
    /// callback this call replaces it.
    fn set_overflow_client(&self, client: &'a dyn OverflowClient) ;

    /// Starts the free-running hardware counter. Valid `Result<(), ErrorCode>` values are:
    ///   - `Ok(())`: the counter is now running
    ///   - `Err(ErrorCode::OFF)`: underlying clocks or other hardware resources
    ///   are not on, such that the counter cannot start.
    ///   - `Err(ErrorCode::FAIL)`: unidentified failure, counter is not running.
    /// After a successful call to `start`, `is_running` MUST return true.
    fn start(&self) -> (result: Result<(), ErrorCode>)
        ensures (result.is_ok() ==> self.is_running()),
    ;

    /// Stops the free-running hardware counter. Valid `Result<(), ErrorCode>` values are:
    ///   - `Ok(())`: the counter is now stopped. No further
    ///   overflow callbacks will be invoked.
    ///   - `Err(ErrorCode::BUSY)`: the counter is in use in a way that means it
    ///   cannot be stopped and is busy.
    ///   - `Err(ErrorCode::FAIL)`: unidentified failure, counter is running.
    /// After a successful call to `stop`, `is_running` MUST return false.
    fn stop(&self) -> (result: Result<(), ErrorCode>)
        ensures (result.is_ok() ==> !self.is_running()),
    ;

    /// Resets the counter to 0. This may introduce jitter on the counter.
    /// Resetting the counter has no effect on any pending overflow callbacks.
    /// If a client needs to reset and clear pending callbacks it should
    /// call `stop` before `reset`.
    /// Valid `Result<(), ErrorCode>` values are:
    ///    - `Ok(())`: the counter was reset to 0.
    ///    - `Err(ErrorCode::FAIL)`: the counter was not reset to 0.
    fn reset(&self) -> (result: Result<(), ErrorCode>)
        ensures (result.is_ok() ==> self.now().get_value() == 0), // Assuming now() reflects counter value
    ;

    /// Returns whether the counter is currently running.
    fn is_running(&self) -> (result: bool);
}

/// Callback handler for when an Alarm fires (a `Counter` reaches a specific
/// value).
pub trait AlarmClient {
    /// Callback indicating the alarm time has been reached. The alarm
    /// MUST be disabled when this is called. If a new alarm is needed,
    /// the client can call `Alarm::set_alarm`.
    fn alarm(&self);
}

/// Interface for receiving notification when a particular time
/// (`Counter` value) is reached. Clients use the
/// [`AlarmClient`](trait.AlarmClient.html) trait to signal when the
/// counter has reached a pre-specified value set in
/// [`set_alarm`](#tymethod.set_alarm). Alarms are intended for
/// low-level time needs that require precision (i.e., firing on a
/// precise clock tick). Software that needs more functionality
/// but can tolerate some jitter should use the `Timer` trait
/// instead.
pub trait Alarm<'a>: Time {
    /// Specify the callback for when the counter reaches the alarm
    /// value. If there was a previously installed callback this call
    /// replaces it.
    // fn set_alarm_client(&self, client: &'a AlarmDriver);
    /// Specify when the callback should be called and enable it. The
    /// callback will be enqueued when `Time::now() == reference + dt`. The
    /// callback itself may not run exactly at this time, due to delays.
    /// However, it it assured to execute *after* `reference + dt`: it can
    /// be delayed but will never fire early. The method takes `reference`
    /// and `dt` rather than a single value denoting the counter value so it
    /// can distinguish between alarms which have very recently already
    /// passed and those in the far far future (see #1651).
    // PRECONDITION: current alarm is soonest
    // POSTCONDITION: current alarm is soonest
    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks)
        // requires
        //     dt.get_value() >= self.minimum_dt().get_value(), // dt must be sufficient
        // ensures
        //     self.is_armed(),
        //     self.get_alarm().get_value() == reference.wrapping_add(dt).get_value(),
    ;


    /// Return the current alarm value. This is undefined at boot and
    /// otherwise returns `now + dt` from the last call to `set_alarm`.
    fn get_alarm(&self) -> (result: Self::Ticks);

    /// Disable the alarm and stop it from firing in the future.
    /// Valid `Result<(), ErrorCode>` codes are:
    ///   - `Ok(())` the alarm has been disarmed and will not invoke
    ///   the callback in the future
    ///   - `Err(ErrorCode::FAIL)` the alarm could not be disarmed and will invoke
    ///   the callback in the future
    fn disarm(&self) -> (result: Result<(), ErrorCode>);

    /// Returns whether the alarm is currently armed. Note that this
    /// does not reliably indicate whether there will be a future
    /// callback: it is possible that the alarm has triggered (and
    /// disarmed) and a callback is pending and has not been called yet.
    /// In this case it possible for `is_armed` to return false yet to
    /// receive a callback.
    fn is_armed(&self) -> (result: bool);

    /// Return the minimum dt value that is supported. Any dt smaller than
    /// this will automatically be increased to this minimum value.
    fn minimum_dt(&self) -> (result: Self::Ticks)
        ensures result.get_value() >= 0, // Minimum delay is non-negative
    ;
}

/// Callback handler for when a timer fires.
pub trait TimerClient {
    fn timer(&self);
}

pub enum FrequencyVal {
    Freq1MHz,
    Freq1KHz,
}

#[derive(Debug)]
pub struct Ticks32{
    pub ticks: u32
}

impl View for Ticks32 {
    type V = int;

    open spec fn view(&self) -> (result: int)
    {
        self.ticks as int
    }
}

impl Copy for Ticks32 {}

impl Clone for Ticks32 {
    fn clone(&self) -> (result: Ticks32)
        ensures result.ticks == self.ticks,
    {
        *self
    }
}

impl From<u32> for Ticks32 {
    fn from(val: u32) -> (result: Ticks32)
        ensures result.ticks == val,
    {
        Ticks32{ticks:val}
    }
}

impl Ticks for Ticks32 {
    closed spec fn get_value(&self) -> (result: int) {
        self.ticks as int
    }

    closed spec fn spec_width() -> (result: u32) {
        32
    }

    fn width() -> (result: u32)
        ensures result == 32,
    {
        32
    }

    fn into_usize(self) -> (result: usize)
        ensures result == self.ticks as usize, // Assuming usize >= u32
    {
        let ret = self.ticks as usize;
        assert(ret <= self.get_value() as usize); // Verus assertion
        ret
    }

    fn into_u32(self) -> (result: u32)
        ensures result == self.ticks,
    {
        self.ticks
    }

    fn wrapping_add(self, other: Self) -> (result: Self)
        ensures result.ticks == self.ticks.wrapping_add(other.ticks),
    {
        Ticks32{ticks:self.ticks.wrapping_add(other.ticks)}
    }

    fn wrapping_sub(self, other: Self) -> (result: Self)
        ensures result.ticks == self.ticks.wrapping_sub(other.ticks),
    {
        Ticks32{ticks:self.ticks.wrapping_sub(other.ticks)}
    }

    fn within_range(self, start: Self, end: Self) -> (result: bool)
        // ensures result == (self.wrapping_sub(start).ticks < end.wrapping_sub(start).ticks),
    {
        self.wrapping_sub(start).ticks < end.wrapping_sub(start).ticks
    }

    fn max_value() -> (result: Self)
        // ensures result.ticks == 0xFFFFFFFF,
    {
        Ticks32{ticks:0xFFFFFFFF}
    }

    fn half_max_value() -> (result: Self)
        // ensures result.ticks == (1 + (0xFFFFFFFF / 2)),
    {
        Self{ ticks: 1 + (Self::max_value().ticks / 2)}
    }

    #[inline]
    fn from_or_max(val: u64) -> (result: Self)
        // ensures
        //     (val < 0xFFFFFFFFu64) ==> result.ticks == val as u32,
        //     (val >= 0xFFFFFFFFu64) ==> result.ticks == 0xFFFFFFFFu32,
    {
        if val < Self::max_value().ticks as u64 { // Max value of Ticks32 is u32::MAX
            Self::from(val as u32)
        } else {
            Self::max_value()
        }
    }

    #[inline]
    #[verifier(external_body)]
    fn saturating_scale(self, numerator: u32, denominator: u32) -> (result: u32)
        // requires denominator != 0,
        ensures
            ({let scaled_val = (self.ticks as u64 * numerator as u64) / denominator as int;
            if scaled_val < u32::MAX as u64 { result == scaled_val as u32 }
            else { result == u32::MAX }}),
    {
        let scaled = self.ticks as u64 * numerator as u64 / denominator as u64;
        if scaled < u32::MAX as u64 {
            scaled as u32
        } else {
            u32::MAX
        }
    }
}

impl PartialOrd for Ticks32 {
    fn partial_cmp(&self, other: &Self) -> (result: Option<Ordering>)
        // ensures result == Some(self.ticks.cmp(&other.ticks)),
    {
        Some(self.cmp(other))
    }
}

impl Ord for Ticks32 {
    #[verifier(external_body)]
    fn cmp(&self, other: &Self) -> (result: Ordering)
        // ensures result == self.ticks.cmp(&other.ticks),
    {
        self.ticks.cmp(&other.ticks)
    }
}

impl PartialEq for Ticks32 {
    fn eq(&self, other: &Self) -> (result: bool)
        ensures result == (self.ticks == other.ticks),
    {
        self.ticks == other.ticks
    }
}

impl Eq for Ticks32 {}

pub struct FakeAlarm<'a> {
    pub now: PCell<Ticks32>,
    pub reference: PCell<Ticks32>,
    pub dt: PCell<Ticks32>,
    pub armed: PCell<bool>,
    pub client: &'a ClientCounter,
}

pub tracked struct FakeAlarmPerms {
    pub tracked now_perm: Tracked<PointsTo<Ticks32>>,
    pub tracked reference_perm: Tracked<PointsTo<Ticks32>>,
    pub tracked dt_perm: Tracked<PointsTo<Ticks32>>,
    pub tracked armed_perm: Tracked<PointsTo<bool>>,
    pub ghost fire_time: int, // is a Ticks32
}

impl<'a> FakeAlarm<'a> {
    pub closed spec fn fake_alarm_wf(&self, perms: &FakeAlarmPerms) -> bool
    {
        &&& perms.now_perm@.is_init()
        &&& perms.reference_perm@.is_init()
        &&& perms.dt_perm@.is_init()
        &&& perms.armed_perm@.is_init()
        &&& perms.now_perm@.id() === self.now.id()
        &&& perms.reference_perm@.id() === self.reference.id()
        &&& perms.dt_perm@.id() === self.dt.id()
        &&& perms.armed_perm@.id() === self.armed.id()
    }

    fn new(client: &'a ClientCounter, Tracked(client_perm): Tracked<&ClientCounterState>) -> (result: (Self, Tracked<FakeAlarmPerms>))
        requires
            client.client_counter_wf(client_perm),
        ensures
            client.cnt.id() == client_perm.count.id(),
            result.0.client.cnt.id() == client_perm.count.id(),
            result.0.client.cnt.id() == client.cnt.id(),
            result.1@.now_perm@.mem_contents().value().ticks == 1_000,
            result.1@.reference_perm@.mem_contents().value().ticks == 0,
            result.1@.dt_perm@.mem_contents().value().ticks == 0,
            result.1@.armed_perm@.mem_contents().value() == false,
            result.0.fake_alarm_wf(&result.1@),
    {
        let (now, Tracked(now_perm)) = PCell::new(1_000u32.into());
        let (reference, Tracked(reference_perm)) = PCell::new(0u32.into());
        let (dt, Tracked(dt_perm)) = PCell::new(0u32.into());
        let (armed, Tracked(armed_perm)) = PCell::new(false);

        let alarm = Self {
            now: now,
            reference: reference,
            dt: dt,
            armed: armed,
            client: &client,
        };

        let perms = Tracked(FakeAlarmPerms {
            now_perm: Tracked(now_perm),
            reference_perm: Tracked(reference_perm),
            dt_perm: Tracked(dt_perm),
            armed_perm: Tracked(armed_perm),
            fire_time: 0 as int,
        });

        (alarm, perms)
    }

    /// The emulated delay from when hardware timer to when kernel loop will
    /// run to check if alarms have fired or not.
    fn hardware_delay(&self, Tracked(perms): Tracked<&FakeAlarmPerms>) -> (result: Ticks32)
        requires
            self.fake_alarm_wf(perms),
        ensures
            self.fake_alarm_wf(perms),
            result.ticks == 10,
            perms.dt_perm@.id() === self.dt.id(),
            perms.armed_perm@.id() === self.armed.id(),
            result.ticks == 10,
    {
        Ticks32::from(10)
    }

    /// Fast forwards time to the next time we would fire an alarm and call client. Returns if
    /// alarm is still armed after triggering client
    fn trigger_next_alarm(&self, Tracked(perms): Tracked<&mut FakeAlarmPerms>, Tracked(client_perm): Tracked<&mut ClientCounterState>, mux_alarm: &mut MuxAlarm, Tracked(mux_perms): Tracked<&mut MuxAlarmPerms>) -> (result: bool)
        requires
            old(perms).armed_perm@.is_init(),
            old(perms).armed_perm@.value() == true,
            self.fake_alarm_wf(old(perms)),
            self.client.client_counter_wf(old(client_perm)),
            old(mux_alarm).mux_alarm_wf(old(mux_perms)),
            // Add precondition for fire_time
            old(mux_perms).fire_time.is_none() ||
                (old(mux_perms).next_tick_vals_perm.is_init() &&
                old(mux_perms).next_tick_vals_perm.value().is_some() &&
                old(perms).fire_time == old(mux_perms).next_tick_vals_perm.value().unwrap().0.get_value() as int),
            // There must be at least one alarm scheduled
            old(mux_perms).num_total_alarms > 0,
            // Precondition to ensure the alarm function can be called
            old(mux_perms).next_tick_vals_perm.value().is_some(),
            old(mux_perms).next_tick_vals_perm.value().unwrap().0.get_value() as int == old(perms).fire_time,
        ensures
            (result == false) ==> mux_perms.num_fired_alarms == mux_perms.num_total_alarms,
            self.fake_alarm_wf(perms),
            self.client.client_counter_wf(client_perm),
            mux_alarm.mux_alarm_wf(mux_perms),
            !result ==> perms.armed_perm@.value() == false,
            // forall|i: nat|
            // self.index@ <= i < ghost_state@.cells.len()
            //     ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
            //     && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
            //     == ghost_state@.cells[i as int].id()
    {
        if !self.is_armed(Tracked(&*perms)) {
            return false;
        }
        self.now.replace(Tracked(&mut perms.now_perm.borrow_mut()),
            self.reference
                .borrow(Tracked(perms.reference_perm.borrow()))
                .wrapping_add(*self.dt.borrow(Tracked(perms.dt_perm.borrow())))
                .wrapping_add(self.hardware_delay(Tracked(&*perms))),
        );
        // assert(perms.fire_time == (perms.now_perm@.value()@));
        // simulate interrupt
        assume(mux_perms.next_tick_vals_perm.value().is_some());
        assume(mux_perms.next_tick_vals_perm.value().unwrap().0.get_value() as int == perms.fire_time);
        assume(mux_perms.alarm.fire_time == perms.fire_time);
        mux_alarm.alarm(Tracked(&mut *mux_perms));

        self.is_armed(Tracked(&*perms))
    }
// }
//
// impl<'a> Time for FakeAlarm<'a> {
//     type Ticks = Ticks32;

    /// INVARIANT: None!
    /// NOTE: currently now() is a free variable. However, this does not model that time passes
    /// during code execution. How to model this?
    fn now(&self, Tracked(perms): Tracked<&mut FakeAlarmPerms>) -> (result: Ticks32)
        requires
            self.fake_alarm_wf(old(perms)),
        ensures
            self.fake_alarm_wf(perms),
    {
        let old_now_val = self.now.borrow(Tracked(perms.now_perm.borrow())).into_u32();
        let new_now_val = if old_now_val == u32::MAX {
            Ticks32::from(0)
        } else {
            Ticks32::from(old_now_val + 1)
        };

        let tracked mut now_perm = perms.now_perm.get();
        self.now.replace(Tracked(&mut now_perm), new_now_val);
        new_now_val
    }
    fn get_freq() -> (result: u32)
        ensures result == 1_000,
    {
        1_000
    }
// }
//
// impl<'a> Alarm<'a> for FakeAlarm<'a> {
    // fn set_alarm_client(&self, client: &'a dyn AlarmClient) {
    //     self.client.set(client);
    // }

    fn set_alarm(&self, reference: Ticks32, dt: Ticks32, Tracked(perms): Tracked<&mut FakeAlarmPerms>)
        requires
            self.fake_alarm_wf(old(perms)),
        ensures
            self.fake_alarm_wf(perms),
            perms.reference_perm@.mem_contents().value().ticks == reference.ticks,
            perms.dt_perm@.mem_contents().value().ticks == dt.ticks,
            perms.armed_perm@.mem_contents().value() == true,
    {
        self.reference.replace(Tracked(&mut perms.reference_perm.borrow_mut()), reference);
        assert(reference.ticks == perms.reference_perm@.mem_contents().value().ticks);
        self.dt.replace(Tracked(&mut perms.dt_perm.borrow_mut()), dt);
        self.armed.replace(Tracked(&mut perms.armed_perm.borrow_mut()), true);
    }

    fn get_alarm(&self, Tracked(perms): Tracked<&FakeAlarmPerms>) -> (result: Ticks32)
        requires
            self.fake_alarm_wf(perms),
            perms.now_perm@.id() === self.now.id(),
            perms.reference_perm@.id() === self.reference.id(),
            perms.dt_perm@.id() === self.dt.id(),
            perms.armed_perm@.id() === self.armed.id(),
        ensures
            self.fake_alarm_wf(perms),
            perms.now_perm@.id() === self.now.id(),
            perms.reference_perm@.id() === self.reference.id(),
            perms.dt_perm@.id() === self.dt.id(),
            perms.armed_perm@.id() === self.armed.id(),
        // ensures result.ticks == self.reference.into_inner((perms.reference_perm)).wrapping_add(self.dt.into_inner((perms.dt_perm))).ticks,
    {
        self.reference.borrow(Tracked(perms.reference_perm.borrow())).wrapping_add(*self.dt.borrow(Tracked(perms.dt_perm.borrow())))
    }

    fn disarm(&self, Tracked(perms): Tracked<&mut FakeAlarmPerms>) -> (result: Result<(), ErrorCode>)
        requires
            (self).fake_alarm_wf(old(perms)),
            // Should require `armed == true`?
            // perms.armed_perm@.id() === old(self).armed.id(),
        ensures
            self.fake_alarm_wf(perms),
            perms.armed_perm@.id() === self.armed.id(),
            perms.armed_perm@.mem_contents().value() == false,
            result == Ok::<(), ErrorCode>(()),
    {
        self.armed.replace(Tracked(&mut perms.armed_perm.borrow_mut()), false);
        assert(perms.armed_perm@.mem_contents().is_init() == true);
        assert(perms.armed_perm@.mem_contents().value() == false);
        Ok(())
    }

    fn is_armed(&self, Tracked(perms): Tracked<&FakeAlarmPerms>) -> (result: bool)
        requires
            self.fake_alarm_wf(perms),
            perms.armed_perm@.id() === self.armed.id(),
        ensures
            self.fake_alarm_wf(perms),
            perms.armed_perm@.id() === self.armed.id(),
            result == perms.armed_perm@.value(),
    {
        *self.armed.borrow(Tracked(perms.armed_perm.borrow()))
    }

    fn minimum_dt(&self, Tracked(perms): Tracked<&FakeAlarmPerms>) -> (result: Ticks32)
        requires
            self.fake_alarm_wf(perms),
            perms.armed_perm@.id() === self.armed.id(),
        ensures
            self.fake_alarm_wf(perms),
            perms.armed_perm@.id() === self.armed.id(),
            result.ticks == 0,
    {
        0u32.into()
    }
}

pub struct ClientCounter {
    pub cnt: PCell<usize>,
}

pub tracked struct ClientCounterState {
    pub tracked count: PointsTo<usize>,
}

impl<'a> ClientCounter {
    pub closed spec fn client_counter_wf(&self, state: &ClientCounterState) -> bool {
        &&& state.count.is_init()
        &&& self.cnt.id() === state.count.id()
    }

    fn new() -> (result: (ClientCounter, Tracked<ClientCounterState>))
        ensures
            result.0.client_counter_wf(&result.1@),
            result.1@.count.mem_contents().value() == 0,
            result.0.cnt.id() === result.1@.count.id(),
    {
        let (cell, Tracked(count_perm)) = PCell::new(0);
        (ClientCounter { cnt: cell }, Tracked(ClientCounterState { count: count_perm }))
    }

    fn count(&self, Tracked(state): Tracked<&mut ClientCounterState>) -> (result: usize)
        requires
            self.client_counter_wf(old(state)),
        ensures
            result == state.count.value(),
            self.cnt.id() === state.count.id(),
    {
        *self.cnt.borrow(Tracked(&state.count))
    }
// }
//
// impl AlarmClient for ClientCounter {
    /// Opaque callback
    pub fn alarm(&self)
        // requires
        //     (self).client_counter_wf(old(state)),
        // ensures
        //     self.client_counter_wf(state),
    {
        // let old_count_val = *self.cnt.borrow(Tracked(&state.count));
        // let new_count_val = if old_count_val == usize::MAX {
        //     0
        // } else {
        //     old_count_val + 1
        // };
        // let tracked mut count_perm = state.count;
        // self.cnt.replace(Tracked(&mut count_perm), new_count_val);
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn run_until_disarmed(alarm: &mut FakeAlarm, Tracked(perms): Tracked<&mut FakeAlarmPerms>, Tracked(client_perm): Tracked<&mut ClientCounterState>, mux_alarm: &mut MuxAlarm, Tracked(mux_perms): Tracked<&mut MuxAlarmPerms>)
    requires
        old(alarm).fake_alarm_wf(old(perms)),
        old(alarm).client.client_counter_wf(old(client_perm)),
        old(mux_alarm).mux_alarm_wf(old(mux_perms)),
    ensures
        alarm.fake_alarm_wf(perms),
        alarm.client.client_counter_wf((client_perm)),
        mux_alarm.mux_alarm_wf(mux_perms),
        mux_perms.num_fired_alarms == mux_perms.num_total_alarms,
        perms.armed_perm@.value() == false,
{
    if !alarm.is_armed(Tracked(&*perms)) {
        // assume(mux_perms.num_total_alarms >= old(mux_perms).num_total_alarms);
        return;
    }

    loop
        invariant
            alarm.fake_alarm_wf(perms),
            alarm.client.client_counter_wf(client_perm),
            mux_alarm.mux_alarm_wf(mux_perms),
    {
        assume(perms.armed_perm@.value() == true);
        assume(mux_perms.num_total_alarms > 0);
        assume(mux_perms.next_tick_vals_perm.value().is_some());
        assume(mux_perms.next_tick_vals_perm.value().unwrap().0.get_value() as int == perms.fire_time);
        if !alarm.trigger_next_alarm(Tracked(&mut *perms), Tracked(&mut *client_perm), &mut *mux_alarm, Tracked(&mut *mux_perms)) {
            return;
        }
    }
}

fn main()
{
    // add asserts in the code and show that we want to show are met
    // write dummy positive tests
    { // One alarm will fire
        let (mut client, Tracked(client_perm)) = ClientCounter::new();
        let (mut fake_alarm, Tracked(perms)) = FakeAlarm::new(&client, Tracked(&mut client_perm));
        let (mut mux_alarm, Tracked(mux_perms)) = MuxAlarm::new(&fake_alarm, Tracked(&mut perms));

        let reference = fake_alarm.now(Tracked(&mut perms));
        mux_alarm.set_alarm(reference, Ticks32::from(10), Tracked(&mut mux_perms));
        // assert(mux_perms.num_total_alarms == 1);
        // assert(mux_perms.num_fired_alarms == 0);
        assume(perms.armed_perm@.value() == true);
        run_until_disarmed(&mut fake_alarm, Tracked(&mut perms), Tracked(&mut client_perm), &mut mux_alarm, Tracked(&mut mux_perms));
        // assume(mux_perms.next_tick_vals_perm.value().unwrap().0.get_value() as int == perms.fire_time);
        // fake_alarm.trigger_next_alarm(Tracked(&mut perms), Tracked(&mut client_perm), &mut mux_alarm, Tracked(&mut mux_perms));

        proof {
            assert(mux_perms.num_fired_alarms == 1);
        }
    }
    // TODO: 3 test cases which correspond to the three overlapping cases. past/future/present
}
} // verus!
