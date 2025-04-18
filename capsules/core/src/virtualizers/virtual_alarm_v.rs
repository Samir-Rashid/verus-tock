// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.
//! Virtualize the Alarm interface to enable multiple users of an underlying
//! alarm hardware peripheral.
use vstd::cell::*;
use vstd::prelude::*;

use kernel::hil::time::{Ticks, Time};
use kernel::utilities::cells::OptionalCell;
use kernel::ErrorCode;

use crate::alarm_v::AlarmDriver;
use crate::list_v::{GhostState, ListIteratorV, ListLinkV, ListNodeV, ListV};

verus! {

pub trait AlarmState {}
/// A trait that defines the behavior of an alarm.
pub trait Alarm<'a>: Time {
    type State: AlarmState;
    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks, state: &Tracked<Self::State>);
    fn get_alarm(&self, state: &Tracked<Self::State>) -> Self::Ticks;
    // Should the state be a trait too? Like we cannot have the
    // same state for a muxAlarm and a virtualAlarm
    fn disarm(&self, state: &mut Tracked<Self::State>) -> Result<(), ErrorCode> where Self: core::marker::Sized;
    fn is_armed(&self, state: &Tracked<Self::State>) -> bool where Self: core::marker::Sized;
    fn minimum_dt(&self, state: &Tracked<Self::State>) -> Self::Ticks;
}

#[derive(Copy, Clone)]
pub struct TickDtReference<T: Ticks> {
    /// Reference time point when this alarm was setup.
    reference: T,
    /// Duration of this alarm w.r.t. the reference time point. In other words, this alarm should
    /// fire at `reference + dt`.
    dt: T,
    /// True if this dt only represents a portion of the original dt that was requested. If true,
    /// then we need to wait for another max_tick/2 after an internal extended dt reference alarm
    /// fires. This ensures we can wait the full max_tick even if there is latency in the system.
    extended: bool,
}

// VERUS-TODO: Remove the Copy trait from T once this is fixed
// cannot move out of `self.reference` which is behind a shared reference
impl<T: Ticks + Copy + Clone> TickDtReference<T> {
    #[inline]
    fn reference_plus_dt(&self) -> T {
        self.reference.wrapping_add(self.dt)
    }

    fn get_reference(&self) -> T {
        self.reference
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct ExAlarmDriver<'a, A: Alarm<'a>>(AlarmDriver<'a, A>);

// pub struct AlarmDriver<'a, A: Alarm<'a>>
/// An object to multiplex multiple "virtual" alarms over a single underlying alarm. A
/// `VirtualMuxAlarm` is a node in a linked list of alarms that share the same underlying alarm.
#[verifier::reject_recursive_types(A)]
pub struct VirtualMuxAlarm<'a, A: Alarm<'a>> {
    /// Underlying alarm which multiplexes all these virtual alarm.
    pub mux: Option<&'a MuxAlarm<'a, A>>,
    /// Reference and dt point when this alarm was setup.
    pub dt_reference: PCell<TickDtReference<A::Ticks>>,
    /// Whether this alarm is currently armed, i.e. whether it should fire when the time has
    /// elapsed.
    pub armed: PCell<bool>,
    /// Next alarm in the list.
    pub next: Option<ListLinkV<'a, VirtualMuxAlarm<'a, A>>>,
    /// Alarm client for this node in the list.
    pub client: OptionalCell<&'a AlarmDriver<'a, A>>,
}

#[verifier::external]
impl<'a, A: Alarm<'a>> ListNodeV<'a, VirtualMuxAlarm<'a, A>> for VirtualMuxAlarm<'a, A> {
    fn next(&'a self, next_points_to: Tracked<&PointsTo<Option<&'a VirtualMuxAlarm<'a, A>>>>) -> &'a ListLinkV<'a, VirtualMuxAlarm<'a, A>> {
        match self.next {
            Some(next) => &next,
            None => unreachable!(),
        }
    }
}

#[verifier::reject_recursive_types(A)]
pub tracked struct VirtualMuxAlarmState<'a, A: Alarm<'a>> {
    //phantom: core::marker::PhantomData<A>,
    // not sure if we should put the alarm_state as part of the mux state
    pub mux_alarm_state: Tracked<MuxAlarmState<'a, A>>,
    pub tracked dt_reference_pt: PointsTo<TickDtReference<<VirtualMuxAlarm<'a, A> as kernel::hil::time::Time>::Ticks>>,
    pub tracked armed_pt: PointsTo<bool>,
}

impl<'a, A:Alarm<'a>> AlarmState for VirtualMuxAlarmState<'a, A> {}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
// VERUS-TODO: Verify the OptionnalCell type
pub struct ExOptionalCell<T>(OptionalCell<T>);

#[verifier::external_fn_specification]
pub const fn ExOptionalCellempty<T>() -> OptionalCell<T> {
    OptionalCell::empty()
}

#[verifier::external_fn_specification]
pub fn ExOptionalCellMap<T: Copy, F, R>(optcell: &OptionalCell<T>, closure: F) -> Option<R> where
    F: FnOnce(T) -> R,
 {
    optcell.map(closure)
}

impl<'a, A: Alarm<'a>> VirtualMuxAlarm<'a, A> {
    pub closed spec fn valid_state(&self, state: &Tracked<VirtualMuxAlarmState<'a, A>>) -> bool {
        &&& self.dt_reference.id() == state@.dt_reference_pt.id()
        &&& self.armed.id() == state@.armed_pt.id()
        &&& state@.dt_reference_pt.is_init()
        &&& state@.armed_pt.is_init()
    }

    /// After calling new, always call setup()
    pub fn new(mux_alarm: &'a MuxAlarm<'a, A>, mux_alarm_state: &Tracked<MuxAlarmState<'a, A>>) -> (res: (
        VirtualMuxAlarm<'a, A>,
        Tracked<VirtualMuxAlarmState<'a, A>>,
        Tracked<PointsTo<Option<&'a VirtualMuxAlarm<'a, A>>>>,
    ))
        ensures
            res.0.dt_reference.id() == res.1@.dt_reference_pt.id(),
            res.0.armed.id() == res.1@.armed_pt.id(),
            res.1@.dt_reference_pt.is_init(),
            res.1@.armed_pt.is_init(),
            res.1@.armed_pt.value() == false,
            res.0.next.unwrap().0.id() == res.2@.id(),
            res.2@.is_init(),
            res.0.mux.is_some(),
    {
        // let zero = A::Ticks::from(0);
        let zero = A::Ticks::from_or_max(0);
        let (dt_reference, Tracked(dt_reference_pt)) = PCell::new(
            TickDtReference { reference: zero, dt: zero, extended: false },
        );
        let (armed, Tracked(armed_pt)) = PCell::new(false);
        let (next, tracked_next_pt) = ListLinkV::empty();
        // let phantom = core::marker::PhantomData;
        (
            VirtualMuxAlarm {
                mux: Some(mux_alarm),
                dt_reference,
                armed,
                next: Some(next),
                client: OptionalCell::empty(),
            },
            Tracked(VirtualMuxAlarmState { mux_alarm_state: *mux_alarm_state, dt_reference_pt, armed_pt }),
            tracked_next_pt,
        )
    }

    #[verifier::external_body]
    pub fn mux(&'a self) -> &'a MuxAlarm<'a, A> {
        self.mux.unwrap()
    }

    // VERUS-TODO: Check if this one should be marked at external
    #[verifier::external]
    fn set_alarm_client(&self, client: &'a AlarmDriver<'a, A>) {
        self.client.set(client);
    }

    /// Call this method immediately after new() to link this to the mux, otherwise alarms won't
    /// fire
    #[verifier::external]
    pub fn setup(&'a self, next_pt: Tracked<PointsTo<Option<&'a VirtualMuxAlarm<'a, A>>>>, alarm_state: &mut Tracked<VirtualMuxAlarmState<'a, A>>) {
        let tracked virtual_alarms_state = alarm_state@.mux_alarm_state@.virtual_alarms_state;
        self.mux().virtual_alarms().push_head(self, next_pt, &mut Tracked(virtual_alarms_state));
        proof {
            alarm_state@.mux_alarm_state@.alarm_states_seq = alarm_state@.mux_alarm_state@.alarm_states_seq.insert(0, alarm_state@);
        }
    }
}

impl<'a, A: Alarm<'a>> Time for VirtualMuxAlarm<'a, A> {
    // type Frequency = A::Frequency;
    fn get_freq() -> u32 {
        1000
    }

    type Ticks = A::Ticks;

    fn now(&self) -> Self::Ticks {
        self.mux().alarm().now()
    }
}

impl<'a, A: Alarm<'a>> Alarm<'a> for VirtualMuxAlarm<'a, A> {
    type State = VirtualMuxAlarmState<'a, A>;

    // error: expression has mode spec, expected mode proof
    // https://github.com/verus-lang/verus/issues/1460
    fn disarm(&self, state: &mut Tracked<Self::State>) -> (res: Result<(), ErrorCode>)
    ensures
    self.valid_state(state),
    self.dt_reference.id() == state@.dt_reference_pt.id(),
    {
        if *self.armed.borrow(Tracked(&state@.armed_pt)) {
            return Ok(());
        }
        let tracked mut armed_pt_perm = state@.armed_pt;
        self.armed.replace(Tracked(&mut armed_pt_perm), false);

        // let enabled = self.mux().enabled.get() - 1;
        // VERUS-TODO: Fix the above overflow in the above line and replace it
        let enabled = self.mux().enabled.borrow(Tracked(&state@.mux_alarm_state@.enabled_pt)) - 1;
        let enabled_pt_perm = state@.mux_alarm_state@.enabled_pt;
        self.mux().enabled.replace(Tracked(&mut enabled_pt_perm), enabled);

        // If there are not more enabled alarms, disable the underlying alarm
        // completely.
        if enabled == 0 {
            let alarm_state = state@.mux_alarm_state@.alarm_state;
            let _ = self.mux().alarm().disarm(&mut alarm_state);
        }
        Ok(())
    }

    fn is_armed(&self, state: &Tracked<Self::State>) -> (res: bool)
    ensures
    self.valid_state(state),
    state@.armed_pt.value() == res,
    {
        *self.armed.borrow(Tracked(&state@.armed_pt))
    }

    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks, state: & Tracked<Self::State>) {
        let enabled = *self.mux().enabled.borrow(Tracked(&state@.mux_alarm_state@.enabled_pt));
        let half_max = Self::Ticks::half_max_value();
        // If the dt is more than half of the available time resolution, then we need to break
        // up the alarm into two internal alarms. This ensures that our internal comparisons of
        // now outside of range [ref, ref + dt) will trigger correctly even with latency in the
        // system
        // VERUS-TODO define less than and greater than for Ticks?
        // Reason, arithmetic operations are not supported on the Ticks type
        let dt_reference = if dt.into_usize() > half_max.wrapping_add(
            self.minimum_dt(&state),
        ).into_usize() {
            TickDtReference { reference, dt: dt.wrapping_sub(half_max), extended: true }
        } else {
            TickDtReference { reference, dt, extended: false }
        };
        let dt_reference_pt = state@.dt_reference_pt;
        self.dt_reference.write(Tracked(&mut dt_reference_pt), dt_reference);
        // Ensure local variable has correct value when used below
        let dt = dt_reference.dt;

        //if !*self.armed.borrow(Tracked(&state@.armed_pt)) {
            // VERUS-TODO prove that this line is not overflowing and uncomment
            // self.mux().enabled.set(enabled + 1);
            let armed_pt_perm = state@.armed_pt;
            self.armed.write(Tracked(&mut armed_pt_perm), true);
        //}
        // First alarm, so set it

        if enabled == 0 {
            //debug!("virtual_alarm: first alarm: set it.");
            let alarm_state = state@.mux_alarm_state;
            self.mux().set_alarm(reference, dt, &mut alarm_state);
        } else if *self.mux().firing.borrow(Tracked(&state@.mux_alarm_state@.firing_pt)) {
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
            let cur_alarm = self.mux().alarm().get_alarm(&state@.mux_alarm_state@.alarm_state);
            let now = self.mux().alarm().now();
            let expiration = reference.wrapping_add(dt);
            if cur_alarm.within_range(reference, expiration) {
                // VERUS-TODO: Check if it is equivalent to the previous impl
                let next = *self.mux().next_tick_vals.borrow(Tracked(&state@.mux_alarm_state@.next_tick_vals_pt)); // TODO: I am rather confused because this value is literally wrong. It's not the next soonest alarm, it's the most recently added alarm.
                let alarm_state = state@.mux_alarm_state;
                if let Some((next_reference, next_dt)) = next {
                    if now.within_range(next_reference, next_reference.wrapping_add(next_dt)) {
                        self.mux().set_alarm(reference, dt, &mut alarm_state);
                    }
                } else {
                    self.mux().set_alarm(reference, dt, &mut alarm_state);
                }
                // if next.map(|next| {
                //     let (next_reference, next_dt) = next;
                //     now.within_range(next_reference, next_reference.wrapping_add(next_dt))
                // })
                // .unwrap_or(true)
                // {
                //     self.mux().set_alarm(reference, dt);
                // }
            } else {
                // current alarm will fire earlier, keep it
            }
        }
    }

    fn get_alarm(&self, state: &Tracked<Self::State>) -> Self::Ticks {
        let dt_reference = self.dt_reference.borrow(Tracked(&state@.dt_reference_pt));
        let extension = if dt_reference.extended {
            Self::Ticks::half_max_value()
        } else {
            Self::Ticks::from_or_max(0)
        };
        dt_reference.reference_plus_dt().wrapping_add(extension)
    }

    fn minimum_dt(&self, state: &Tracked<Self::State>) -> Self::Ticks {
        self.mux().alarm().minimum_dt(&state@.mux_alarm_state@.alarm_state)
    }
}

impl<'a, A: Alarm<'a>> AlarmClient<'a, A> for VirtualMuxAlarm<'a, A> {
    // VERUS-TODO: Verify the AlarmDriver so that we don't have to trust this
    #[verifier::external_body]
    fn alarm(&self, state: &mut Tracked<MuxAlarmState<'a, A>>) {
        self.client.map(|client| client.alarm(state));
        // if  self.client.is_some() {
        //     let client = self.client.get().map(|client| client.alarm());
        // client.alarm();
        // }
    }
}

/// Structure to control a set of virtual alarms multiplexed together on top of a single alarm.
#[verifier::reject_recursive_types(A)]
// #[verifier::accept_recursive_types(A)]
pub struct MuxAlarm<'a, A: Alarm<'a>> { // TODO: define an alarm implementation, make the toy programs at the end like in linked list for what you should be able to know statically. can do things with mux alarm after alarm. all the alarms wshould be in order, num armed == num enabled.
    //
    /// Head of the linked list of virtual alarms multiplexed together.
    pub virtual_alarms: Option<ListV<'a, VirtualMuxAlarm<'a, A>>>, // TODO: why is this recursive? Find the sorted def from github summer school forall pairs
    // this is like a lazy mergesort, but the time is bounded and costs are limited per proc
    /// Number of virtual alarms that are currently enabled.
    pub enabled: PCell<usize>,
    /// Underlying alarm, over which the virtual alarms are multiplexed.
    pub alarm: Option<&'a A>,
    /// Whether we are firing; used to delay restarted alarms
    pub firing: PCell<bool>,
    /// Reference to next alarm
    pub next_tick_vals: PCell<Option<(A::Ticks, A::Ticks)>>,
}

#[verifier::reject_recursive_types(A)]
pub tracked struct MuxAlarmState<'a, A: Alarm<'a>> {
    pub alarm_state: Tracked<A::State>,
    pub ghost alarm_states_seq: Seq<VirtualMuxAlarmState<'a, A>>,
    pub tracked virtual_alarms_state: GhostState<'a, VirtualMuxAlarm<'a, A>>,
    pub tracked enabled_pt: PointsTo<usize>,
    pub tracked firing_pt: PointsTo<bool>,
    pub tracked next_tick_vals_pt: PointsTo<Option<(A::Ticks, A::Ticks)>>,
}

impl<'a, A: Alarm<'a>> MuxAlarm<'a, A> {
    pub const fn new(alarm: &'a A, alarm_state: Tracked<A::State>) -> (res: (MuxAlarm<'a, A>, Tracked<MuxAlarmState<'a, A>>))
    ensures
    res.0.enabled.id() == res.1@.enabled_pt.id(),
    res.0.firing.id() == res.1@.firing_pt.id(),
    res.0.next_tick_vals.id() == res.1@.next_tick_vals_pt.id(),
    res.1@.enabled_pt.is_init(),
    res.1@.firing_pt.is_init(),
    res.1@.next_tick_vals_pt.is_init(),
    res.1@.enabled_pt.value() == 0,
    res.1@.firing_pt.value() == false,
    res.1@.next_tick_vals_pt.value().is_none(),
    res.0.virtual_alarms.is_some(),
    res.0.alarm.is_some(),
    {
        let (virtual_alarms, Tracked(virtual_alarms_state)) = ListV::new();
        let (enabled, Tracked(enabled_pt)) = PCell::new(0);
        let (firing, Tracked(firing_pt)) = PCell::new(false);
        let (next_tick_vals, Tracked(next_tick_vals_pt)) = PCell::new(None);
        (MuxAlarm {
            virtual_alarms: Some(virtual_alarms),
            enabled,
            alarm: Some(alarm),
            firing,
            next_tick_vals,
        }, Tracked(MuxAlarmState {
            alarm_state,
            alarm_states_seq: Seq::empty(),
            virtual_alarms_state,
            enabled_pt,
            firing_pt,
            next_tick_vals_pt,
        }))
    }

    #[verifier::external_body]
    pub fn virtual_alarms(&'a self) -> &ListV<'a, VirtualMuxAlarm<'a, A>> {
        match self.virtual_alarms {
            Some(virtual_alarms) => &virtual_alarms,
            None => unreachable!(),
        }
    }

    #[verifier::external_body]
    pub fn alarm(&'a self) -> &'a A {
        self.alarm.unwrap()
    }

    pub fn set_alarm(&self, reference: A::Ticks, dt: A::Ticks, state: &mut Tracked<MuxAlarmState<'a, A>>) {
        let next_tick_vals_pt = state@.next_tick_vals_pt;
        self.next_tick_vals.write(Tracked(&mut next_tick_vals_pt), Some((reference, dt)));
        self.alarm().set_alarm(reference, dt, &mut state@.alarm_state);
    }

    pub fn disarm(&self, state: &mut Tracked<MuxAlarmState<'a, A>>) {
        let next_tick_vals_pt = state@.next_tick_vals_pt;
        self.next_tick_vals.write(Tracked(&mut next_tick_vals_pt), None);
        let alarm_state = state@.alarm_state;
        let _ = self.alarm().disarm(&mut alarm_state);
    }
}

pub trait AlarmClient<'a, A: Alarm<'a>> {
    fn alarm(&self, state: &mut Tracked<MuxAlarmState<'a, A>>);
}

impl<'a, A: Alarm<'a>> AlarmClient<'a, A> for MuxAlarm<'a, A> {
    /// When the underlying alarm has fired, we have to multiplex this event back to the virtual
    /// alarms that should now fire.
    fn alarm(&self, state: &mut Tracked<MuxAlarmState<'a, A>>) {
        // Check whether to fire each alarm. At this level, alarms are one-shot,
        // so a repeating client will set it again in the alarm() callback.
        let firing_pt = state@.firing_pt;
        self.firing.write(Tracked(&mut firing_pt), true);
        let mut iterator = ListIteratorV::new(self.virtual_alarms(), &Tracked(state@.virtual_alarms_state));
        let initial_index = iterator.index@;
        // for cur in self.virtual_alarms().iter() {
        // while let Some(cur) = current {
        loop {
            let ghost seq_index: int = 0int;
            proof {
                seq_index = iterator.index@ - initial_index;
            }
            match iterator.next(&Tracked(state@.virtual_alarms_state)) {
                Some(cur) => {
                    let cur_state = state@.alarm_states_seq.index(seq_index);
                    let dt_ref = cur.dt_reference.borrow(Tracked(&cur_state.dt_reference_pt));
                    let now = self.alarm().now();
                    if *cur.armed.borrow(Tracked(&cur_state.armed_pt)) && !now.within_range(
                        dt_ref.reference,
                        dt_ref.reference_plus_dt(),
                    ) {
                        if dt_ref.extended {
                            cur.dt_reference.write(
                                Tracked(&mut cur_state.dt_reference_pt),
                                TickDtReference {
                                    reference: dt_ref.reference_plus_dt(),
                                    dt: A::Ticks::half_max_value(),
                                    extended: false,
                                },
                            );
                        } else {
                            cur.armed.write(Tracked(&mut cur_state.armed_pt), false);
                            // VERUS-TODO uncomment the following line and prove the lack of overflow
                            // self.enabled.set(self.enabled.get() - 1);
                            cur.alarm(&mut cur_state.mux_alarm_state);
                        }
                    }
                },
                None => break,
            }
            // let mut current = self.virtual_alarms().head();

        }
        let firing_pt = state@.firing_pt;
        self.firing.write(Tracked(&mut firing_pt), false);
        // Find the soonest alarm client (if any) and set the "next" underlying
        // alarm based on it.  This needs to happen after firing all expired
        // alarms since those may have reset new alarms.
        let now = self.alarm().now();
        // let next = self
        //     .virtual_alarms()
        //     .iter()
        //     .filter(|cur| cur.armed.get())
        //     .min_by_key(|cur| {
        // TODO: this now > ref assumption does not seem sound
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
        let mut iterator = ListIteratorV::new(self.virtual_alarms(), &Tracked(state@.virtual_alarms_state));
        let mut min_ticks = None;
        let mut min_alarm = None;
        let ghost min_seq_index = 0int;

        loop {
            let ghost seq_index = 0int;
            proof {
                seq_index = iterator.index@ - initial_index;
            }
            match iterator.next(&Tracked(state@.virtual_alarms_state)) {
                Some(cur) => {
                    let cur_state = state@.alarm_states_seq.index(seq_index);
                    if *cur.armed.borrow(Tracked(&cur_state.armed_pt)) {
                        let when = cur.dt_reference.borrow(Tracked(&cur_state.dt_reference_pt));
                        let ticks = if now.within_range(when.reference, when.reference_plus_dt()) {
                            A::Ticks::from_or_max(0u64)
                        } else {
                            when.reference_plus_dt().wrapping_sub(now)
                        };

                        match min_ticks {
                            None => {
                                min_ticks = Some(ticks);
                                min_alarm = Some(cur);
                                min_seq_index = seq_index;
                            },
                            Some(min) if ticks.into_usize() < min.into_usize() => {
                                min_ticks = Some(ticks);
                                min_alarm = Some(cur);
                                min_seq_index = seq_index;
                            },
                            _ => {},
                        }
                    }
                },
                None => break,
            }
        }

        let next = min_alarm;

        // Set the alarm.
        if let Some(valrm) = next {
            let valrm_state = state@.alarm_states_seq.index(min_seq_index);
            let dt_reference = valrm.dt_reference.borrow(Tracked(&valrm_state.dt_reference_pt));
            self.set_alarm(dt_reference.reference, dt_reference.dt, state);
        } else {
            self.disarm(state);
        }
    }
}

} // verus!
