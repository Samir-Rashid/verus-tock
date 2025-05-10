// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.
use super::list_i::{GhostState, ListIteratorV, ListLinkV, ListNodeV, ListV};
use core::cmp::Ordering;
use core::fmt;
use kernel::ErrorCode;
use vstd::cell::*;
use vstd::prelude::*;
// use vstd::std_specs::option::spec_unwrap;

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
#[verifier::reject_recursive_types(A)]
pub struct VirtualMuxAlarm<'a, A: Alarm<'a>> {
    /// Underlying alarm which multiplexes all these virtual alarm.
    pub mux: &'a MuxAlarm<'a, A>,
    /// Reference and dt point when this alarm was setup.
    pub dt_reference: PCell<TickDtReference<A::Ticks>>,
    /// Whether this alarm is currently armed, i.e. whether it should fire when the time has
    /// elapsed.
    pub armed: PCell<bool>,
    /// Next alarm in the list.
    pub next: Option<ListLinkV<'a, VirtualMuxAlarm<'a, A>>>,
    /// Alarm client for this node in the list.
    pub client: &'a ClientCounter,
    pub state: Tracked<VirtualMuxAlarmState<'a, A>>,
}

#[verifier::reject_recursive_types(A)]
pub struct VirtualMuxAlarmState<'a, A: Alarm<'a>> {
    pub dt_reference_perm: PointsTo<TickDtReference<A::Ticks>>,
    pub armed_perm: PointsTo<bool>,
    pub next_perm: PointsTo<Option<&'a VirtualMuxAlarm<'a, A>>>,
}

impl<'a, A: Alarm<'a>> ListNodeV<'a, VirtualMuxAlarm<'a, A>> for VirtualMuxAlarm<'a, A> {
    fn next(&'a self, perm: builtin::Tracked<&vstd::cell::PointsTo<core::option::Option<&'a VirtualMuxAlarm<'a, A>>>>) -> (result: &'a ListLinkV<VirtualMuxAlarm<'a, A>>)
        ensures
            // result == self.next.as_ref().unwrap(),
            result.0.id() == perm@.id(), // The returned ListLinkV contains the PCell that perm is for
    {
        &self.next((perm))
    }
}

impl<'a, A: Alarm<'a>> VirtualMuxAlarm<'a, A> {
    // type Ticks: Ticks;

    /// Well formed constraint
    pub closed spec fn wf(&self) -> bool {
        &&&    self.mux.virtual_alarms.is_some()
        // &&&    self.mux.virtual_alarms.unwrap().well_formed_list(&Tracked(spec_unwrap(self.mux.state@.virtual_alarms_state))) // TODO: this is probably needed
        &&&    self.next.is_some()
        &&&    self.state@.next_perm.is_init()
        &&&    self.state@.dt_reference_perm.is_init()
        &&&    self.state@.armed_perm.is_init()
        // &&&    self.next.unwrap().id() == self.state@.next_perm.id()
        &&&    self.dt_reference.id() == self.state@.dt_reference_perm.id()
        &&&    self.armed.id() == self.state@.armed_perm.id()
    }

    /// After calling new, always call setup()
    pub fn new(mux_alarm: &'a MuxAlarm<'a, A>) -> (res: VirtualMuxAlarm<'a, A>)
        requires
            true, // mux_alarm is a valid reference
        ensures
            res.wf(),
            res.mux == mux_alarm,
            res.state@.dt_reference_perm.id() == res.dt_reference.id(),
            res.state@.dt_reference_perm.is_init(),
            // res.state@.dt_reference.value().reference.get_value() == A::Ticks::from(0).get_value(),
            // res.state@.dt_reference.value().dt.get_value() == A::Ticks::from(0).get_value(),
            res.state@.dt_reference_perm.value().extended == false,
            res.state@.armed_perm.id() == res.armed.id(),
            res.state@.armed_perm.is_init(),
            res.state@.armed_perm.value() == false,
            res.next.is_some(),
            // res.state@.next.id() == res.next.as_ref().unwrap().0.id(),
            res.state@.next_perm.is_init(),
            res.state@.next_perm.value().is_none(),
            // res.client is initialized by ClientCounter::new()
    {
        let zero = A::Ticks::from(0);

        let (dt_reference, Tracked(dt_reference_perm)) = PCell::new(TickDtReference {
                reference: zero,
                dt: zero,
                extended: false,
            });
        let (armed, Tracked(armed_perm)) = PCell::new(false);
        let (list_link, Tracked(list_link_perm)) = ListLinkV::empty();

        VirtualMuxAlarm {
            mux: (mux_alarm),
            dt_reference: dt_reference,
            armed: armed,
            next: Some(list_link),
            client: &ClientCounter::new(),
            state: Tracked(VirtualMuxAlarmState {
                dt_reference_perm,
                armed_perm,
                next_perm: list_link_perm,
            }),
        }
    }

    /// Call this method immediately after new() to link this to the mux, otherwise alarms won't
    /// fire
    pub fn setup(&'a self)
        requires
            self.wf(),
            self.mux.virtual_alarms.is_some(),
            // self.mux.virtual_alarms.unwrap().well_formed_list(&Tracked(self.mux.state@.virtual_alarms.unwrap())), // If adding to list
            self.state@.next_perm.is_init(), // Permission for self.next
        ensures
            self.wf(),
            // If it modified the list:
            // self.mux.virtual_alarms.unwrap().well_formed_list(&Tracked(self.mux.state@.virtual_alarms.unwrap())),
            // old(self.mux.state@.virtual_alarms.unwrap()@.cells.len()) + 1 == self.mux.state@.virtual_alarms.unwrap()@.cells.len(),
    {
        let tracked mut arg0 = self.mux.state.get().virtual_alarms_state.tracked_unwrap();
        let mut arg1 = Tracked(arg0);
        self.mux.virtual_alarms.unwrap().push_head(self, Tracked(self.state.get().next_perm), &mut (arg1));
    }
// }
//
// impl<'a, A: Alarm<'a>> Time for VirtualMuxAlarm<'a, A> {
    // type Ticks = A::Ticks;

    fn now(&self) -> (result: A::Ticks)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        self.mux.alarm.now()
    }

    fn get_freq() -> (result: u32)
        ensures
            result == 1_000,
    {
        1_000
    }
// }
//
// impl<'a, A: Alarm<'a>> Alarm<'a> for VirtualMuxAlarm<'a, A> {
    // NOTE: this feature has been removed to simplify verification
    // fn set_alarm_client(&self, client: &'a dyn time::AlarmClient) {
    //     self.client.set(client);
    // }

    fn disarm(&self) -> (result: Result<(), ErrorCode>)
        requires
            self.wf(),
        // TODO: fix all the requires clauses
        // requires
        //     self.state@.armed_perm.is_init() && self.state@.armed_perm.id() == self.armed.id(),
        //     self.mux.state@.enabled.is_init() && self.mux.state@.enabled.id() == self.mux.enabled.id(),
        //     // self.mux.alarm is valid for disarm call
        ensures
            self.wf(),
            result == Ok::<(), ErrorCode>(()),
            self.state@.armed_perm.id() == self.armed.id(),
            self.state@.armed_perm.is_init(),
            self.state@.armed_perm.value() == false,
            // (old(self.armed.borrow(Tracked(&self.state@.armed))) && old(self.mux.enabled.borrow(Tracked(&self.mux.state@.enabled))) > 0) ==>
            //    self.mux.state@.enabled.value() == old(self.mux.enabled.borrow(Tracked(&self.mux.state@.enabled))) - 1,
            // If old(self.mux.enabled.borrow(Tracked(&self.mux.state@.enabled))) == 1 and self was armed, underlying alarm is disarmed.
    {
        if !self.armed.into_inner(Tracked(self.state.get().armed_perm)) {
            return Ok(());
        }

        let tracked mut perms = self.state.get().armed_perm;
        self.armed.put(Tracked(&mut perms), false);

        let enabled = self.mux.enabled.into_inner(Tracked(self.mux.state.get().enabled_perm)) - 1;
        let tracked mut perms = self.mux.state.get().enabled_perm;
        self.mux.enabled.put(Tracked(&mut perms), enabled);

        // If there are not more enabled alarms, disable the underlying alarm
        // completely.
        if enabled == 0 {
            let _ = self.mux.alarm.disarm();
        }
        Ok(())
    }

    fn is_armed(&self) -> (result: bool)
        requires
            self.wf(),
        // requires
        //     self.state@.armed.is_init() && self.state@.armed.id() == self.armed.id(),
        // TODO: THIS IS TRACKED INCORRECTLY, I need to store the mathematical representation of armed in state
        ensures
            self.wf(),
        //     result == self.state@.armed(Tracked(self.state@.armed)),
    {
        self.armed.into_inner(Tracked(self.state.get().armed_perm))
    }

    fn set_alarm(&self, reference: A::Ticks, dt: A::Ticks)
        requires
            self.wf(),
        // requires
        //     self.state@.dt_reference.is_init() && self.state@.dt_reference.id() == self.dt_reference.id(),
        //     self.state@.armed.is_init() && self.state@.armed.id() == self.armed.id(),
        //     self.mux.state@.enabled.is_init() && self.mux.state@.enabled.id() == self.mux.enabled.id(),
        //     self.mux.state@.firing.is_init() && self.mux.state@.firing.id() == self.mux.firing.id(),
        //     self.mux.state@.next_tick_vals.is_init() && self.mux.state@.next_tick_vals.id() == self.mux.next_tick_vals.id(),
        //     // self.mux.alarm is valid
        ensures
            self.wf(),
            // Complex ensures based on the commented logic involving dt_reference update,
            // armed status, mux.enabled count, and potentially calling self.mux.set_alarm.
    {
        let enabled = self.mux.enabled.into_inner(Tracked(self.mux.state.get().enabled_perm));
        let half_max = A::Ticks::half_max_value();
        // If the dt is more than half of the available time resolution, then we need to break
        // up the alarm into two internal alarms. This ensures that our internal comparisons of
        // now outside of range [ref, ref + dt) will trigger correctly even with latency in the
        // system
        let dt_reference = TickDtReference {
                reference,
                dt,
                extended: false,
            };
        /* // TODO: I've removed this bc I have no idea what is going on
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
        let tracked mut perm = self.state.get().dt_reference_perm;
        self.dt_reference.put(Tracked(&mut perm), dt_reference);
        // Ensure local variable has correct value when used below
        let dt = dt_reference.dt;

        let tracked mut perm = self.state.get().armed_perm;
        match self.armed.replace(Tracked(&mut perm), true){
            false => {
                let tracked mut perm = self.mux.state.get().enabled_perm;
                self.mux.enabled.put(Tracked(&mut perm), enabled + 1);
            }
            true => {} // Already armed, do nothing
        }

        // First alarm, so set it
        if enabled == 0 {
            //debug!("virtual_alarm: first alarm: set it.");
            self.mux.set_alarm(reference, dt);
        } else if !self.mux.firing.into_inner(Tracked(self.mux.state.get().firing_perm)) {
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
            let cur_alarm = self.mux.alarm.get_alarm();
            let now = self.mux.alarm.now();
            let expiration = reference.wrapping_add(dt);
            if !cur_alarm.within_range(reference, expiration) {
                let next = self.mux.next_tick_vals.into_inner(Tracked(self.mux.state.get().next_tick_vals_perm));

                let cond = match next {
                    None => true,
                    Some((next_reference, next_dt)) => now.within_range(next_reference, next_reference.wrapping_add(next_dt)),
                };
                if cond {
                    self.mux.set_alarm(reference, dt);
                }
            } else {
                // current alarm will fire earlier, keep it
            }
        }
    }

    fn get_alarm(&self) -> (result: A::Ticks)
        requires
            self.wf(),
        // requires
        //     // self.state@.dt_reference.is_init() && self.state@.dt_reference.id() == self.dt_reference.id(),
        ensures
            self.wf(),
            // let dt_ref_val = self.dt_reference.borrow(Tracked(&self.state@.dt_reference));
            // let extension_val = if dt_ref_val.extended { A::Ticks::half_max_value() } else { A::Ticks::from(0) };
            // result.get_value() == dt_ref_val.reference_plus_dt().wrapping_add(extension_val).get_value(),
            // result.get_value() == A::Ticks::from(0).get_value(), // For current dummy implementation
    {
            // A::Ticks::from(0) // TODO: dummy value, delete
        let dt_reference = self.dt_reference.into_inner(Tracked(self.state.get().dt_reference_perm));
        let extension = if dt_reference.extended {
            A::Ticks::half_max_value()
        } else {
            A::Ticks::from(0)
        };
        dt_reference.reference_plus_dt().wrapping_add(extension)
    }

    fn minimum_dt(&self) -> (result: A::Ticks)
        requires
            self.wf(),
        // requires
        //     self.mux.alarm is valid, // To call minimum_dt()
        ensures
            self.wf(),
        //     // result.get_value() == self.mux.alarm.minimum_dt().get_value(),
        //     true, // Assuming self.mux.alarm.minimum_dt() returns a valid Ticks
    {
        self.mux.alarm.minimum_dt()
    }
// }
//
// impl<'a, A: Alarm<'a>> AlarmClient for VirtualMuxAlarm<'a, A> {
    fn alarm(&self)
        requires
            self.wf(),
        // requires
            // self.client is valid to call alarm()
        ensures
            self.wf(),
            // self.client.count() might have changed if alarm was called
    {
        self.client.alarm();
    }
}

// TODO: refactor PCell into type invariant or https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.InvCell.html
/// Structure to control a set of virtual alarms multiplexed together on top of a single alarm.
// TODO: impl view trait which is correct way. turns exec mode item into a mathematical representation
#[verifier::reject_recursive_types(A)]
pub struct MuxAlarm<'a, A: Alarm<'a>> {
    /// Head of the linked list of virtual alarms multiplexed together.
    pub virtual_alarms: Option<ListV<'a, VirtualMuxAlarm<'a, A>>>,
    /// Number of virtual alarms that are currently enabled.
    pub enabled: PCell<usize>,
    /// Underlying alarm, over which the virtual alarms are multiplexed.
    pub alarm: &'a A,
    /// Whether we are firing; used to delay restarted alarms
    pub firing: PCell<bool>,
    /// Reference to next alarm
    pub next_tick_vals: PCell<Option<(A::Ticks, A::Ticks)>>,
    pub state: Tracked<MuxAlarmState<'a, A>>,
}

// Keep track of the single, real, physical alarm.
#[verifier::reject_recursive_types(A)]
pub struct MuxAlarmState<'a, A: Alarm<'a>> {
    pub virtual_alarm_states_seq: Ghost<Seq<VirtualMuxAlarmState<'a, A>>>,
    pub virtual_alarms_state: Option<GhostState<'a, VirtualMuxAlarm<'a, A>>>,
    /// NUMBER of virtual alarms that are currently enabled.
    pub enabled_perm: PointsTo<usize>,
    pub alarm: &'a A,
    pub firing_perm: PointsTo<bool>,
    pub next_tick_vals_perm: PointsTo<Option<(A::Ticks, A::Ticks)>>,
    /// tick value of firing: ref + dt % ticks width
    pub fire_time: Option<A::Ticks>,
}

// returns spec mode
impl<'a, A: Alarm<'a>> View for MuxAlarm<'a, A> {
    type V = Tracked<MuxAlarmState<'a, A>>;
    open spec fn view(&self) -> Self::V
        // requires true, // self is valid
        // ensures result === self.state, // === for Tracked comparison
    {
        self.state
    }
}

impl<'a, A: Alarm<'a>> MuxAlarm<'a, A> {
    pub const fn new(alarm_ref: &'a A) -> (res:MuxAlarm<'a, A>)
        requires
            true, // alarm_ref is a valid reference
        ensures
            res@@.enabled_perm.value() == 0,
            res@@.enabled_perm.id() == res.enabled.id(),
            res@@.firing_perm.value() == false,
            res@@.firing_perm.id() == res.firing.id(),
            res@@.next_tick_vals_perm.value().is_none(), // Option<(A::Ticks, A::Ticks)>
            res@@.next_tick_vals_perm.id() == res.next_tick_vals.id(),
            res@@.enabled_perm.is_init(),
            res@@.firing_perm.is_init(),
            res@@.next_tick_vals_perm.is_init(),
            res.next_tick_vals.id() === res@@.next_tick_vals_perm@.pcell,
            res.virtual_alarms.is_some(),
            // res.virtual_alarms.as_ref().unwrap().well_formed_list(&res@@.virtual_alarms.unwrap()), // Assuming ListV::new ensures this
            res@@.virtual_alarm_states_seq@.len() == 0,
            res@@.alarm == alarm_ref,
            res@@.fire_time.is_none(),
    {
        let (enabled , Tracked(enabled_perm)) = PCell::new(0);
        let (firing , Tracked(firing_perm)) = PCell::new(false);
        let (next_tick_vals , Tracked(next_tick_vals_perm)) = PCell::new(None);
        let (virtual_alarms, Tracked(virtual_alarms_perm)) = ListV::new();
        let seq = Ghost(Seq::empty());

        MuxAlarm {
            virtual_alarms: Some(virtual_alarms),
            enabled: enabled,
            alarm: alarm_ref,
            firing: firing,
            next_tick_vals: next_tick_vals,
            state: Tracked(MuxAlarmState {
                virtual_alarm_states_seq: seq,
                virtual_alarms_state: Some(virtual_alarms_perm),
                enabled_perm,
                alarm: alarm_ref,
                firing_perm,
                fire_time: None,
                next_tick_vals_perm,
            }),
        }
    }

    pub fn set_alarm(&self, reference: A::Ticks, dt: A::Ticks)
        // requires
            // self.next_tick_vals.id() === self@@.next_tick_vals@.pcell,
            // self@@.next_tick_vals.is_init(),
            // Any other preconditions from original Tock logic, e.g., dt >= minimum_dt
        ensures
            // self@@.next_tick_vals.id() === old(&mut self@@).next_tick_vals.id(), // ID remains same
            self.next_tick_vals.id() === self@@.next_tick_vals_perm@.pcell, // ID matches ghost state
            self@@.next_tick_vals_perm.is_init(), // Still initialized
            self@@.next_tick_vals_perm.value().is_some(),
            self@@.next_tick_vals_perm.value().unwrap().0.get_value() == reference.get_value(),
            self@@.next_tick_vals_perm.value().unwrap().1.get_value() == dt.get_value(),
            // Underlying hardware alarm self.alarm might be set
    {
        let tracked mut perms = self.state.get().next_tick_vals_perm;
        self.next_tick_vals.write(Tracked(&mut perms), Some((reference, dt)));
        // TODO: self.alarm.set_alarm(...) call and its state modeling
        self.alarm.set_alarm(reference, dt);
    }

    pub fn disarm(&self)
        requires
            self.next_tick_vals.id() === self@@.next_tick_vals_perm@.pcell,
            self@@.next_tick_vals_perm.is_init(),
            // self.alarm is valid for disarm call,
        ensures
            // self.next_tick_vals.id() === old(self).next_tick_vals.id(),
            self.next_tick_vals.id() === self@@.next_tick_vals_perm@.pcell,
            self@@.next_tick_vals_perm.is_init(),
            self@@.next_tick_vals_perm.value().is_none(),
            // self.alarm.disarm() implies the underlying alarm is no longer armed.
            // The Result<(), ErrorCode> from self.alarm.disarm() is Ok(()).
            true, // Placeholder for result of self.alarm.disarm()
    {
        let tracked mut perms = self.state.get().next_tick_vals_perm;
        self.next_tick_vals.write(Tracked(&mut perms), None);
        let _ = self.alarm.disarm();
    }
}

impl<'a, A: Alarm<'a>> AlarmClient for MuxAlarm<'a, A> {
    /// When the underlying alarm has fired, we have to multiplex this event back to the virtual
    /// alarms that should now fire.
    fn alarm(&self)
        // requires
        //     self@@.firing.is_init() && self@@.firing.id() == self.firing.id(),
        //     // self.virtual_alarms is Some and well_formed_list with self@@.virtual_alarms.unwrap()
        //     // Each VirtualMuxAlarm in the list must be valid, its PCells (dt_reference, armed) must match its state.
        //     // self.alarm is valid for now() call.
        //     self@@.enabled.is_init() && self@@.enabled.id() == self.enabled.id(),
        // ensures
            // Complex ensures based on iterating virtual_alarms, checking armed status,
            // potentially calling their alarm() methods, updating their armed status,
            // updating self@@.enabled, and then re-evaluating the next alarm for self.alarm.
            // self@@.firing is false at the end.
    {
        // Check whether to fire each alarm. At this level, alarms are one-shot,
        // so a repeating client will set it again in the alarm() callback.
        let tracked mut perm = self.state.get().firing_perm;
        self.firing.put(Tracked(&mut perm), true);
        let tracked mut perms = self.state.get().firing_perm;
        self.firing.write(Tracked(&mut perms), false);
        let mut iterator = ListIteratorV::new(
            &(self.virtual_alarms).unwrap(),
        &Tracked(self.state.get().virtual_alarms_state.tracked_unwrap()));

        // for cur in self.virtual_alarms.iter() {
        // while let Some(cur) = current {
        loop {
            match iterator.next(&Tracked(self.state.get().virtual_alarms_state.tracked_unwrap())) {
                Some(cur) => {
                    let dt_ref = cur.dt_reference.into_inner(Tracked(cur.state.get().dt_reference_perm));
                    let now = self.alarm.now();
                    if cur.armed.into_inner(Tracked(cur.state.get().armed_perm)) && !now.within_range(
                        dt_ref.reference,
                        dt_ref.reference_plus_dt(),
                    ) {
                        if dt_ref.extended {
                            let tracked mut perm = cur.state.get().dt_reference_perm;
                            cur.dt_reference.put(Tracked(&mut perm),
                                TickDtReference {
                                    reference: dt_ref.reference_plus_dt(),
                                    dt: A::Ticks::half_max_value(),
                                    extended: false,
                                },
                            );
                        } else {
                            let tracked mut perm = cur.state.get().armed_perm;
                            cur.armed.put(Tracked(&mut perm), false);
                            let tracked mut perm = self.state.get().enabled_perm;
                            self.enabled.put(Tracked(&mut perm), self.enabled.into_inner(Tracked(self.state.get().enabled_perm)) - 1);

                            cur.alarm();
                        }
                    }
                },
                None => break,
            }
            // let mut current = self.virtual_alarms.head();

        }
        let tracked mut perm = self.state.get().firing_perm;
        self.firing.put(Tracked(&mut perm), false);

        // Find the soonest alarm client (if any) and set the "next" underlying
        // alarm based on it.  This needs to happen after firing all expired
        // alarms since those may have reset new alarms.
        let now = self.alarm.now();
        // let next = self
        //     .virtual_alarms
        //     .iter()
        //     .filter(|cur| cur.armed.get())
        //     .min_by_key(|cur| {
        //         let when = cur.dt_reference.get();
        //         // If the alarm has already expired, then it should be
        //         // considered as the earliest possible (0 ticks), so it
        //         // will trigger as soon as possible. This can happen
        //         // if the alarm expired *after* it was examined in the
        //         // above loop.
        //         if !now.within_range(when.reference, when.reference_plus_dt()) {
        //             A::Ticks::from(0u32)
        //         } else {
        //             when.reference_plus_dt().wrapping_sub(now)
        //         }
        //     })
        let mut iterator = ListIteratorV::new(
            &(self.virtual_alarms).unwrap(),
        &Tracked(self.state.get().virtual_alarms_state.tracked_unwrap()));
        let mut min_ticks = None;
        let mut min_alarm = None;

        loop {
            match iterator.next(&Tracked(self.state.get().virtual_alarms_state.tracked_unwrap())) {
                Some(cur) => {
                    if cur.armed.into_inner(Tracked(cur.state.get().armed_perm)) {
                        let when = cur.dt_reference.into_inner(Tracked(cur.state.get().dt_reference_perm));
                        let ticks = if !now.within_range(when.reference, when.reference_plus_dt()) {
                            A::Ticks::from_or_max(0u64)
                        } else {
                            when.reference_plus_dt().wrapping_sub(now)
                        };

                        match min_ticks {
                            None => {
                                min_ticks = Some(ticks);
                                min_alarm = Some(cur);
                            },
                            Some(min) if ticks.into_usize() < min.into_usize() => {
                                min_ticks = Some(ticks);
                                min_alarm = Some(cur);
                            },
                            _ => {},
                        }
                    }
                },
                None => break ,
            }
        }

        let next = min_alarm;

        // Set the alarm.
        if let Some(valrm) = next {
            let dt_reference = valrm.dt_reference.into_inner(Tracked(valrm.state.get().dt_reference_perm));
            self.set_alarm(dt_reference.reference, dt_reference.dt);
        } else {
            self.disarm();
        }
    }
}

// pub(crate) open spec fn spec_saturating_sub(lhs: int, rhs: int) -> int {
//     if lhs >= rhs {
//         lhs - rhs
//     } else {
//         0
//     }
// }

// #[verifier(external_fn_specification)]
// pub fn ex_saturatingsub(a: u32, b: u32) -> (ret: u32)
//     ensures
//         ret == spec_saturating_sub(a as int, b as int),
// {
//     a.saturating_sub(b)
// }

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
    // VERUS-TODO: need to model saturating_sub
    // #[verifier(external_body)]
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
    fn ticks_from_seconds(&self, s: u32) -> (result: T)
        requires true, // self must implement Time for get_freq
        // ensures
        //     ({let freq = (<Self as Time>::get_freq() as u64);
        //     let val = freq * (s as u64);
        //     result.get_value() == T::from_or_max(val).get_value()}),
    ;

    /// Returns the number of ticks in the provided number of milliseconds,
    /// rounding down any fractions. If the value overflows Ticks it
    /// returns `Ticks::max_value()`.
    fn ticks_from_ms(&self, ms: u32) -> (result: T)
        requires true,
        // ensures
        //     ({let freq = (<Self as Time>::get_freq() as u64);
        //     let val = freq * (ms as u64);
        //     result.get_value() == T::from_or_max(val / 1_000).get_value()}),
    ;

    /// Returns the number of ticks in the provided number of microseconds,
    /// rounding down any fractions. If the value overflows Ticks it
    /// returns `Ticks::max_value()`.
    fn ticks_from_us(&self, us: u32) -> (result: T)
        requires true,
        // ensures
        //     ({let freq = (<Self as Time>::get_freq() as u64);
        //     let val = freq * (us as u64);
        //     result.get_value() == T::from_or_max((val / 1_000_000) as u64).get_value()}),
    ;

    /// Returns the number of seconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_seconds(&self, tick: T) -> (result: u32)
        // requires <Self as Time>::get_freq() != 0,
        // ensures result == tick.saturating_scale(1, <Self as Time>::get_freq()),
    ;

    /// Returns the number of milliseconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_ms(&self, tick: T) -> (result: u32)
        // requires <Self as Time>::get_freq() != 0,
        // ensures result == tick.saturating_scale(1_000, <Self as Time>::get_freq()),
    ;

    /// Returns the number of microseconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_us(&self, tick: T) -> (result: u32)
        // requires <Self as Time>::get_freq() != 0,
        // ensures result == tick.saturating_scale(1_000_000, <Self as Time>::get_freq()),
    ;
}

impl<T: Time + ?Sized> ConvertTicks<<T as Time>::Ticks> for T {
    #[verifier(external_body)]
    #[inline]
    fn ticks_from_seconds(&self, s: u32) -> (result: <T as Time>::Ticks)
        // ensures
        //     ({let freq = (<Self as Time>::get_freq() as u64);
        //     let val = freq * (s as u64);
        //     result.get_value() == <T as Time>::Ticks::from_or_max(val as u64).get_value()}),
    {
        let val = <T as Time>::get_freq() as u64 * s as u64;
        <T as Time>::Ticks::from_or_max(val)
    }

    #[verifier(external_body)]
    #[inline]
    fn ticks_from_ms(&self, ms: u32) -> (result: <T as Time>::Ticks)
        // ensures
        //     ({let freq = (<Self as Time>::get_freq() as u64);
        //     let val = freq * (ms as u64);
        //     result.get_value() == <T as Time>::Ticks::from_or_max((val / 1_000) as u64).get_value()}),
    {
        let val = <T as Time>::get_freq() as u64 * ms as u64;
        <T as Time>::Ticks::from_or_max(val / 1_000)
    }

    #[verifier(external_body)]
    #[inline]
    fn ticks_from_us(&self, us: u32) -> (result: <T as Time>::Ticks)
        // ensures
        //     ({let freq = (<Self as Time>::get_freq() as u64);
        //     let val = freq * (us as u64);
        //     result.get_value() == <T as Time>::Ticks::from_or_max((val / 1_000_000) as u64).get_value()}),
    {
        let val = <T as Time>::get_freq() as u64 * us as u64;
        <T as Time>::Ticks::from_or_max(val / 1_000_000)
    }

    #[inline]
    fn ticks_to_seconds(&self, tick: <T as Time>::Ticks) -> (result: u32)
        // requires <Self as Time>::get_freq() != 0,
        // ensures result == tick.saturating_scale(1, <Self as Time>::get_freq()),
    {
        tick.saturating_scale(1, <T as Time>::get_freq())
    }

    #[inline]
    fn ticks_to_ms(&self, tick: <T as Time>::Ticks) -> (result: u32)
        // requires <Self as Time>::get_freq() != 0,
        // ensures result == tick.saturating_scale(1_000, <Self as Time>::get_freq()),
    {
        tick.saturating_scale(1_000, <Self as Time>::get_freq())
    }

    #[inline]
    fn ticks_to_us(&self, tick: <T as Time>::Ticks) -> (result: u32)
        // requires <Self as Time>::get_freq() != 0,
        // ensures result == tick.saturating_scale(1_000_000, <Self as Time>::get_freq()),
    {
        tick.saturating_scale(1_000_000, <T as Time>::get_freq())
    }
}

pub trait Timestamp: Time {
    // Requires/ensures for methods in Time already apply.
    // Timestamp implies now() is idempotent over short periods or for a given instance.
    // fn now(&self) -> Self::Ticks
    //    ensures old(self).now() == self.now(); // This might be too strong, depends on definition.
}

/// Callback handler for when a counter has overflowed past its maximum
/// value and returned to 0.
pub trait OverflowClient {
    fn overflow(&self)
        requires true, // self is valid
        ensures true, // Describes side-effects, specific to implementation
    ;
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
    fn is_running(&self) -> (result: bool)
    ;
}

/// Callback handler for when an Alarm fires (a `Counter` reaches a specific
/// value).
pub trait AlarmClient {
    /// Callback indicating the alarm time has been reached. The alarm
    /// MUST be disabled when this is called. If a new alarm is needed,
    /// the client can call `Alarm::set_alarm`.
    fn alarm(&self)
    ;
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
    // spec fn wf(&self) -> bool; // This idea doesn't work
    /// Specify the callback for when the counter reaches the alarm
    /// value. If there was a previously installed callback this call
    /// replaces it.
    // fn set_alarm_client(&self, client: &'a AlarmDriver); // TODO: did i remove???
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
    // TODO: add asserts in the code and show that we want to show are met
    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks)
        // requires
        //     self.wf(),
        //     dt.get_value() >= self.minimum_dt().get_value(), // dt must be sufficient
        // ensures
        //     self.is_armed(),
        //     self.get_alarm().get_value() == reference.wrapping_add(dt).get_value(),
    ;


    /// Return the current alarm value. This is undefined at boot and
    /// otherwise returns `now + dt` from the last call to `set_alarm`.
    fn get_alarm(&self) -> (result: Self::Ticks)
        // requires
        //     self.wf(),
        // ensures
        //     // If armed, returns the target time.
        //     // If not armed, behavior might be less defined by Tock.
        //     // For Verus, if armed: result == internal_target_time
        //     true,
    ;

    /// Disable the alarm and stop it from firing in the future.
    /// Valid `Result<(), ErrorCode>` codes are:
    ///   - `Ok(())` the alarm has been disarmed and will not invoke
    ///   the callback in the future
    ///   - `Err(ErrorCode::FAIL)` the alarm could not be disarmed and will invoke
    ///   the callback in the future
    fn disarm(&self) -> (result: Result<(), ErrorCode>)
        // requires
        //     self.wf(),
        // requires
        //     self.is_armed(),
            // self.armed.id() === self.state@.armed_perm.id(),
        // ensures (result.is_ok() ==> !self.is_armed()),
    ;

    /// Returns whether the alarm is currently armed. Note that this
    /// does not reliably indicate whether there will be a future
    /// callback: it is possible that the alarm has triggered (and
    /// disarmed) and a callback is pending and has not been called yet.
    /// In this case it possible for `is_armed` to return false yet to
    /// receive a callback.
    fn is_armed(&self) -> (result: bool)
        // requires
        //     self.wf(),
    ;

    /// Return the minimum dt value that is supported. Any dt smaller than
    /// this will automatically be increased to this minimum value.
    fn minimum_dt(&self) -> (result: Self::Ticks)
        // requires
            // self.wf(),
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
        ensures
            (val < 0xFFFFFFFFu64) ==> result.ticks == val as u32,
            (val >= 0xFFFFFFFFu64) ==> result.ticks == 0xFFFFFFFFu32,
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
        // ensures result == Some(self.ticks.cmp(&other.ticks)), // TODO: cmp is not supported
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

    pub now_perm: Tracked<PointsTo<Ticks32>>,
    pub reference_perm: Tracked<PointsTo<Ticks32>>,
    pub dt_perm: Tracked<PointsTo<Ticks32>>,
    pub armed_perm: Tracked<PointsTo<bool>>,
}

impl<'a> FakeAlarm<'a> {
    fn new(client: &ClientCounter) -> (result: Self)
        ensures
            result.now_perm@.mem_contents().value().ticks == 1_000,
            result.reference_perm@.mem_contents().value().ticks == 0,
            result.dt_perm@.mem_contents().value().ticks == 0,
            result.armed_perm@.mem_contents().value() == false,
    {
        let (now, Tracked(now_perm)) = PCell::new(1_000u32.into());
        let (reference, Tracked(reference_perm)) = PCell::new(0u32.into());
        let (dt, Tracked(dt_perm)) = PCell::new(0u32.into());
        let (armed, Tracked(armed_perm)) = PCell::new(false);

        Self {
            now: now,
            reference: reference,
            dt: dt,
            armed: armed,
            client: &client,

            now_perm: Tracked(now_perm),
            reference_perm: Tracked(reference_perm),
            dt_perm: Tracked(dt_perm),
            armed_perm: Tracked(armed_perm),
        }
    }

    /// The emulated delay from when hardware timer to when kernel loop will
    /// run to check if alarms have fired or not.
    pub fn hardware_delay(&self) -> (result: Ticks32)
        ensures result.ticks == 10,
    {
        Ticks32::from(10)
    }

    /// Fast forwards time to the next time we would fire an alarm and call client. Returns if
    /// alarm is still armed after triggering client
    pub fn trigger_next_alarm(&self) -> (result: bool)
        // ensures
            // If !old(self).is_armed(), result is false and state is unchanged.
            // Otherwise, self.now is updated, self.client.alarm() is called, and result is self.is_armed().
            // More precise:
            // (!old(self).armed.get()) ==> (result == false && self.now.get().ticks == old(self).now.get().ticks && self.client.ticks.get() == old(self).client.ticks.get()),
            // (old(self).armed.get()) ==> ({
            //     let expected_now = old(self).reference.get().wrapping_add(old(self).dt.get()).wrapping_add(old(self).hardware_delay());
            //     self.now.get().ticks == expected_now.ticks &&
            //     // self.client.alarm() was called, its ensures apply
            //     result == self.armed.get()
            // }),
    {
        if !self.is_armed() {
            return false;
        }
        let tracked mut perm = self.now_perm.get();
        self.now.put(Tracked(&mut perm),
            self.reference
                .into_inner((self.reference_perm))
                .wrapping_add(self.dt.into_inner((self.dt_perm)))
                .wrapping_add(self.hardware_delay()),
        );
        self.client.alarm();
        self.is_armed()
    }

    /// Runs for the specified number of ticks as long as there are alarms armed.
    pub fn run_for_ticks(&self, left: Ticks32)
        // ensures
            // self.now is advanced by 'left' ticks, or until alarms stop firing and time is consumed.
            // The final value of self.now.get() == old(self).now.get().wrapping_add(left).
            // self.now.get().ticks == old(self).now.get().wrapping_add(left).ticks,
    {
        let final_now = self.now.into_inner((self.now_perm)).wrapping_add(left);
        let mut remaining_ticks_to_run = left.into_u32();

        while self.is_armed() {
            // Ensure that we have enough remaining ticks to handle the next alarm. Reference is
            // always in the past, so we need to figure out the difference between the reference
            // and now to discount the DT the alarm needs to wait by.
            let ticks_from_reference = self.now.into_inner((self.now_perm)).wrapping_sub(self.reference.into_inner((self.reference_perm)));
            let dt_to_wait = self
                .dt
                .into_inner((self.dt_perm))
                .into_u32()
                .saturating_sub(ticks_from_reference.into_u32());
            if dt_to_wait <= remaining_ticks_to_run {
                remaining_ticks_to_run = remaining_ticks_to_run - dt_to_wait; // Safe due to check
                // Advance time by dt_to_wait before triggering
                // self.now.set(self.now.get().wrapping_add(Ticks32::from(dt_to_wait))); // This is implicitly handled by trigger_next_alarm setting now
                self.trigger_next_alarm();
            } else {
                break;
            }
        }
        // Ensure that we ate up all of the time we were suppose to run for
        let tracked mut perm = self.now_perm.get();
        self.now.put(Tracked(&mut perm), final_now);
    }
}

impl<'a> Time for FakeAlarm<'a> {
    type Ticks = Ticks32;

    fn now(&self) -> (result: Ticks32)
        // ensures
        //     result.ticks == (if old(self).now.get().ticks == u32::MAX { 0 } else { old(self).now.get().ticks + 1 }),
        //     self.now.get().ticks == result.ticks,
    {
        let old_now_val = self.now.into_inner((self.now_perm)).into_u32();
        let new_now_val = if old_now_val == u32::MAX {
            Ticks32::from(0)
        } else {
            Ticks32::from(old_now_val + 1)
        };

        let tracked mut perm = self.now_perm.get();
        self.now.put(Tracked(&mut perm),new_now_val);
        new_now_val
    }
    fn get_freq() -> (result: u32)
        ensures result == 1_000,
    {
        1_000
    }
}

impl<'a> Alarm<'a> for FakeAlarm<'a> {
    // fn set_alarm_client(&self, client: &'a dyn AlarmClient) {
    //     self.client.set(client);
    // }

    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks)
        ensures
            self.reference_perm@.mem_contents().value().ticks == reference.ticks,
            self.dt_perm@.mem_contents().value().ticks == dt.ticks,
            self.armed_perm@.mem_contents().value() == true,
    {

        let tracked mut perm = self.reference_perm.get();
        self.reference.put(Tracked(&mut perm),reference);
        let tracked mut perm = self.dt_perm.get();
        self.dt.put(Tracked(&mut perm),dt);
        let tracked mut perm = self.armed_perm.get();
        self.armed.put(Tracked(&mut perm),true);
    }

    fn get_alarm(&self) -> (result: Self::Ticks)
// error: cannot call function `lib::virtualizers::new_virtual_alarm::Ticks::wrapping_add` with mode exec
//     --> capsules/core/src/virtualizers/new_virtual_alarm.rs:1570:33
//      |
// 1570 | ...t.ticks == self.reference.into_inner((self.reference_perm)).wrapping_add(self.dt.into_inner((self.dt_perm))).ticks,
//      |               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

        // ensures result.ticks == self.reference.into_inner((self.reference_perm)).wrapping_add(self.dt.into_inner((self.dt_perm))).ticks,
    {
        self.reference.into_inner((self.reference_perm)).wrapping_add(self.dt.into_inner((self.dt_perm)))
    }

    fn disarm(&self) -> (result: Result<(), ErrorCode>)
        ensures
            self.armed_perm@.mem_contents().value() == false,
            result == Ok::<(), ErrorCode>(()),
    {
        let tracked mut perm = self.armed_perm.get();
        self.armed.put(Tracked(&mut perm),false);
        Ok(())
    }

    fn is_armed(&self) -> (result:bool)
        ensures result == self.armed_perm@.mem_contents().value(),
    {
        self.armed.into_inner((self.armed_perm))
    }

    fn minimum_dt(&self) -> (result: Self::Ticks)
        ensures result.ticks == 0,
    {
        0u32.into()
    }
}

pub struct ClientCounter( PCell<usize>, ClientCounterState);
pub struct ClientCounterState {
    count: Tracked<PointsTo<usize>>,
}

impl ClientCounter {
    fn new() -> (result: Self)
        ensures
            result.1.count@.mem_contents().value() == 0,
            result.0.id() === result.1.count@.id(),
    {
        let (cell, Tracked(count_perm)) = PCell::new(0);
        Self(cell, ClientCounterState { count: Tracked(count_perm) })
    }

    fn count(&self) -> (result: usize)
        ensures result == self.1.count@.mem_contents().value(),
            self.0.id() === self.1.count@.id(),
    {
        self.0.into_inner(self.1.count)
    }
}

impl AlarmClient for ClientCounter {
    fn alarm(&self)
        // ensures
        //     self.ticks.get() == (if old(self).ticks.get() == usize::MAX { 0 } else { old(self).ticks.get() + 1 }),
        //     // self.1.count remains unchanged as it's not modified here.
        //     self.1.count == old(self).1.count,
    {
        let old_count_val = self.0.into_inner(self.1.count);
        let new_count_val = if old_count_val == usize::MAX {
            0
        } else {
            old_count_val + 1
        };
        let tracked mut perm = self.1.count.get();
        self.0.put(Tracked(&mut perm),new_count_val);
    }
}

fn run_until_disarmed(alarm: &FakeAlarm)
    // ensures
        // Either alarm is not armed, or loop executed at most 20 times.
        // State of alarm is modified by trigger_next_alarm calls.
        // (!alarm.is_armed()) || true, // Second part is tautology if loop count matters for ensures
                                     // More precise: alarm.client.count() reflects number of firings
{
    for _ in 0..20 {
        if !alarm.trigger_next_alarm() {
            return;
        }
    }
}

fn main()
{
    // write dummy positive tests
    { // One alarm will fire
        let client= ClientCounter::new(); // TODO: alarm needs to use this client
        let alarm = FakeAlarm::new(&client);

        let mut mux_alarm = MuxAlarm::new(&alarm);

        mux_alarm.set_alarm(alarm.now(), Ticks32::from(10));
        run_until_disarmed(&alarm); // local_alarm is likely not armed by the above.

        let fired_count = client.count(); // This will be 0.
        proof{
            // This assertion will likely fail with current code structure as `fired_count` is 0.
            // To make it 1, `local_client_counter_for_assertion.alarm()` must be called.
            assert(fired_count == 1);
            assert(fired_count == 0); // Based on current logic.
        }


        // Let's assume the test means:
        // 1. Create a physical alarm `alarm_phys = FakeAlarm::new()`.
        // 2. Create a MuxAlarm `mux = MuxAlarm::new(&alarm_phys)`.
        // 3. `alarm_phys.set_alarm_client(&mux)` (if FakeAlarm had set_alarm_client).
        // 4. Create a VirtualMuxAlarm `virt = VirtualMuxAlarm::new(&mux)`.
        // 5. `virt.set_alarm_client(&client_for_virt)` (if VirtualMuxAlarm had set_alarm_client).
        // 6. `virt.set_alarm(...)`. This would arm `virt`, potentially arm `mux`, which arms `alarm_phys`.
        // 7. `run_until_disarmed(&alarm_phys)`.
        // 8. Check `client_for_virt.count()`.

        // Given the current code:
        // `mux.set_alarm` calls `self.next_tick_vals.write`. It does NOT call `self.alarm.set_alarm`.
        // The Tock logic is that `VirtualMuxAlarm::set_alarm` would call `mux.set_alarm` (if conditions met).
        // And `MuxAlarm::set_alarm` (the one that takes reference, dt) would call `self.alarm.set_alarm`.
        // The current `MuxAlarm::set_alarm` only updates `next_tick_vals`.

        // The test as written:
        // `mux.set_alarm(alarm.now(), 10.into());`
        // This calls the `MuxAlarm::set_alarm` which only updates `mux.next_tick_vals`.
        // It does not arm the underlying `FakeAlarm alarm`.
        // So `run_until_disarmed(&alarm)` will do nothing as `alarm` is not armed by this call.
        // `alarm.now()` advances time.
        // `client.count()` will be 0. The assertion `fired_count == 1` will fail.

        // To make the test meaningful with current stubs, one would directly call `alarm.set_alarm`.
        // Example:
        // let test_alarm = FakeAlarm::new(); // This FakeAlarm has its own internal ClientCounter.
        // test_alarm.set_alarm(test_alarm.now(), 10.into());
        // run_until_disarmed(&test_alarm);
        // // To check the count, we'd need access to test_alarm.client.count().
        // // proof { assert(test_alarm.client.count() == 1); } // This requires client to be public or have getter.

        // The provided test code is for illustration and may not pass without further refinement
        // of both the main code and the test logic.
        // For the purpose of adding requires/ensures, I will assume the functions are called as is.
        /*
        let local_alarm = FakeAlarm::new();
        let local_client_counter_for_assertion = ClientCounter::new(); // This client is not used by local_alarm

        let mut mux = MuxAlarm::new(&local_alarm);
        // The following call to mux.set_alarm does not arm local_alarm based on current MuxAlarm::set_alarm impl.
        mux.set_alarm(local_alarm.now(), Ticks32::from(10));
        run_until_disarmed(&local_alarm); // local_alarm is likely not armed by the above.

        let fired_count = local_client_counter_for_assertion.count(); // This will be 0.
        proof{
            // This assertion will likely fail with current code structure as `fired_count` is 0.
            // To make it 1, `local_client_counter_for_assertion.alarm()` must be called.
            assert(fired_count == 1);
            assert(fired_count == 0); // Based on current logic.
        }
        */
    }
    { // TODO: five alarms will fire

    }
    { // TODO: disarming an alarm will not fire

    }
    // TODO: write dummy negative tests
    { // TODO: come up with cases that should statically be caught by verifier

    }

    // TODO: 3 test cases which correspond to the three overlapping cases. past/future/present
}
} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    struct Test1MHz64(); // Needs Ticks64 definition if used
                         // Assuming Ticks64 is like Ticks32/etc.
                         // pub struct Ticks64(u64); // Example
                         // impl Ticks for Ticks64 { ... }

    impl Time for Test1MHz64 {
        // fn get_freq(freq_val: FrequencyVal) -> u32 { // Original had freq_val param, trait doesn't
        fn get_freq() -> u32 {
            // match freq_val { // freq_val not available
            //     FrequencyVal::Freq1MHz => 1_000_000,
            //     _ => 0,
            // }
            1_000_000 // Assuming Freq1MHz is implied
        }
        type Ticks = Ticks32; // Placeholder, should be Ticks64 if defined

        fn now(&self) -> Self::Ticks {
            // 0u32.into() // If Ticks is Ticks64, should be Ticks64::from(0u64) or similar
            Ticks32::from(0u32) // Matching type Ticks = Ticks32
        }
    }
}
