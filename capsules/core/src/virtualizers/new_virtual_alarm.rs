// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.
//! Hardware agnostic interfaces for time and timers within the Tock
//! kernel.
//!
//! These traits are designed to be able encompass the wide
//! variety of hardware counters in a general yet efficient way. They
//! abstract the frequency of a counter through the `Frequency` trait
//! and the width of a time value through the `Ticks`
//! trait. Higher-level software abstractions should generally rely on
//! standard and common implementations of these traits (e.g.. `u32`
//! ticks and 16MHz frequency).  Hardware counter implementations and
//! peripherals can represent the actual hardware units an translate
//! into these more general ones.
// use crate::ErrorCode;
use core::cmp::Ordering;
use core::fmt;
use kernel::ErrorCode;
// spec_saturating_sub
use core::cell::Cell;
use kernel::collections::list_i::{GhostState, ListIteratorV, ListLinkV, ListNodeV, ListV};
use kernel::hil::time::{ex_saturatingsub, ExErrorCode, ExOrdering};
// use kernel::hil::time::{Ticks, Time};
use kernel::utilities::cells::OptionalCell;
use vstd::cell::*;
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone)]
struct TickDtReference<T: Ticks> {
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

// TODO: refactor PCell into type invariant or https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.InvCell.html
/// Structure to control a set of virtual alarms multiplexed together on top of a single alarm.
// #[verifier::reject_recursive_types(A)]
// TODO: impl view trait which is correct way. turns exec mode item into a mathematical representation
pub struct MuxAlarm<'a, A: Alarm<'a>> {
    /// Head of the linked list of virtual alarms multiplexed together.
    // virtual_alarms: ListV<'a, VirtualMuxAlarm<'a, A>>, // TODO:
    /// Number of virtual alarms that are currently enabled.
    pub enabled: PCell<usize>, // TODO: determine why this is a cell
    /// Underlying alarm, over which the virtual alarms are multiplexed.
    pub alarm: &'a A,
    /// Whether we are firing; used to delay restarted alarms
    pub firing: PCell<bool>,
    /// Reference to next alarm
    pub next_tick_vals: PCell<Option<(A::Ticks, A::Ticks)>>,
    // "Struct fields of an exec struct must be exec mode"....... bruh
    // https://verus-lang.github.io/verus/guide/reference-var-modes.html?highlight=tracked#using-tracked-and-ghost-variables-from-a-proof-function
    // pub tracked state: MuxAlarmState<'a, A>,
    pub state: Tracked<MuxAlarmState<'a, A>>,
}

// returns spec mode
impl<'a, A: Alarm<'a>> View for MuxAlarm<'a, A> {
    type V = Tracked<MuxAlarmState<'a, A>>; // TODO: this return doesn't need to be wrapped in Tracked<>
    open spec fn view(&self) -> Self::V {
        self.state
    }
}

// Keep track of the single, real, physical alarm.
// Undocumented that Tracked functions only work in proof mode https://verus-lang.github.io/verus/verusdoc/vstd/prelude/struct.Tracked.html#method.view
// TODO: ask Eric, marking this struct as `tracked` was causing the error
pub struct MuxAlarmState<'a, A: Alarm<'a>> {
    // TODO: need virtual alarms state and virtual alarms Seq

    /// NUMBER of virtual alarms that are currently enabled.
    // pub tracked enabled: int,
    pub enabled: PointsTo<usize>,
    /// Underlying alarm, over which the virtual alarms are multiplexed.
    pub alarm: &'a A,
    /// Whether we are firing; used to delay restarted alarms
    pub firing: PointsTo<bool>,
    /// Reference to CURRENT ALARM ref and dt
    pub next_tick_vals: PointsTo<Option<(A::Ticks, A::Ticks)>>,
    /// tick value of firing: ref + dt % ticks width
    pub fire_time: Option<A::Ticks>,
}

impl<'a, A: Alarm<'a>> MuxAlarm<'a, A> {
    /*
    error: #[verifier::type_invariant]: a struct with a type invariant cannot have any fields public to the crate
    */
    // #[verifier::type_invariant]
    // spec fn type_inv(self) -> bool {
    //     true
    // // use `proof {use_type_invariant(&self);}` to get access to this invariant in proofs
    // }

    // #[exec]
    /// Variables in exec code may be exec, ghost, or tracked.
    /// However, exec function parameters and return values are always exec.
    /// In these places, the library types Ghost and Tracked are used
    /// to wrap ghost values and tracked values.
    /// Ghost and tracked expressions Ghost(expr) and Tracked(expr) create values of type Ghost<T>
    /// and Tracked<T>, where expr is treated as proof code whose value is wrapped inside Ghost or Tracked.
    /// The view x@ of a Ghost or Tracked x is the ghost or tracked value inside the Ghost or Tracked.
    pub const fn new(alarm: &'a A) -> (res:MuxAlarm<'a, A>)//(res: (MuxAlarm<'a, A>, Tracked<MuxAlarmState<'a, A>>))
        ensures
            res@@.enabled.value() == 0,
            res@@.enabled.id() == res.enabled.id(),
            res@@.firing.value() == false,
            res@@.firing.id() == res.firing.id(),
            res@@.next_tick_vals.value() == None::<(A::Ticks, A::Ticks)>,
            res@@.next_tick_vals.id() == res.next_tick_vals.id(),
            res@@.enabled.is_init(),
            res@@.firing.is_init(),
            res@@.next_tick_vals.is_init(),
            // res.state.firing.get().mem_contents().value() == false, // this field expression is disallowed because of datatype opaqueness => because this field was not pub
            res.next_tick_vals.id() === res@@.next_tick_vals@.pcell
    {
        let (enabled , Tracked(enabled_perm)) = PCell::new(0);
        let (firing , Tracked(firing_perm)) = PCell::new(false);
        let (next_tick_vals , Tracked(next_tick_vals_perm)) = PCell::new(None);
        MuxAlarm {
            // virtual_alarms: ListV::new(), // TODO:
            enabled: enabled,
            alarm,
            firing: firing,
            next_tick_vals: next_tick_vals,
            state: Tracked(MuxAlarmState {
                // virtual_alarms: ListV::new(), // TODO:
                enabled: enabled_perm,
                alarm,
                firing: firing_perm,
                fire_time: None,
                next_tick_vals: next_tick_vals_perm,
            }),
        }
    }

    // BRO ZERO PCELL USAGE EXISTS https://github.com/search?q=.write(Tracked%20path%3A*.rs&type=code
    pub fn set_alarm(&self, reference: A::Ticks, dt: A::Ticks)//, //state: &mut MuxAlarmState<'a, A>)
            // TODO: wrap requirements into "well formed" condition
        requires
            self.next_tick_vals.id() === self@@.next_tick_vals@.pcell,
            self@@.next_tick_vals.is_init(),
            // PRECONDITION: can only be sooner or if disabled
            // reference + dt < state@.fire_time@.value().unwrap_or(reference),

        ensures
            self.next_tick_vals.id() === self@@.next_tick_vals@.pcell
            // state.next_tick_vals@.value() == Some((reference, dt)),
            // self.next_tick_vals.get().is_none() ==> self.next_tick_vals.get().is_some(),
            // self.next_tick_vals.get().is_some() ==> self.next_tick_vals.get().is_none(),
            // self.enabled.get() == 0 ==> self.enabled.get() == 1,
            // self.firing.get() == false ==> self.firing.get() == true,
            // self.alarm.now() == reference + dt,
    {
        let tracked mut perms = self.state.get().next_tick_vals;
        self.next_tick_vals.write(Tracked(&mut perms), Some((reference, dt)));
    }

    pub fn disarm(&self)
        requires
            self.next_tick_vals.id() === self@@.next_tick_vals@.pcell,
            self@@.next_tick_vals.is_init(),
        ensures
            self.next_tick_vals.id() === self@@.next_tick_vals@.pcell
            // self.next_tick_vals.get().is_none(),
            // self.enabled.get() == 0,
            // self.firing.get() == false,
            // self.alarm.now() == 0,
    {
        let tracked mut perms = self.state.get().next_tick_vals;
        self.next_tick_vals.write(Tracked(&mut perms), None);
        let _ = self.alarm.disarm(); // TODO: this state modification needs to be modeled
    }
}

// TODO: empty out the impl and verify
impl<'a, A: Alarm<'a>> AlarmClient for MuxAlarm<'a, A> {
    /// When the underlying alarm has fired, we have to multiplex this event back to the virtual
    /// alarms that should now fire.
    // TODO: the buffer that we need to handle may not be bounded here? There can
    fn alarm(&self)
        // ensures
        //     self.next_tick_vals.id() === self@@.next_tick_vals@.pcell
            // self.enabled.get() == 0,
            // self.firing.get() == false,
            // self.next_tick_vals.get().is_none(),
    {
        // // Check whether to fire each alarm. At this level, alarms are one-shot,
        // // so a repeating client will set it again in the alarm() callback.
        // self.firing.set(true);
        // let mut iterator = ListIteratorV { cur: self.virtual_alarms.head() };
        // // for cur in self.virtual_alarms.iter() {
        // // while let Some(cur) = current {
        // loop {
        //     match iterator.next() {
        //         Some(cur) => {
        //             let dt_ref = cur.dt_reference.get();
        //             let now = self.alarm.now();
        //             if cur.armed.get() && !now.within_range(
        //                 dt_ref.reference,
        //                 dt_ref.reference_plus_dt(),
        //             ) {
        //                 if dt_ref.extended {
        //                     cur.dt_reference.set(
        //                         TickDtReference {
        //                             reference: dt_ref.reference_plus_dt(),
        //                             dt: A::Ticks::half_max_value(),
        //                             extended: false,
        //                         },
        //                     );
        //                 } else {
        //                     cur.armed.set(false);
        //                     // VERUS-TODO uncomment the following line and prove the lack of overflow
        //                     // self.enabled.set(self.enabled.get() - 1);
        //                     cur.alarm();
        //                 }
        //             }
        //         },
        //         None => break ,
        //     }
        //     // let mut current = self.virtual_alarms.head();

        // }
        // self.firing.set(false);
        // // Find the soonest alarm client (if any) and set the "next" underlying
        // // alarm based on it.  This needs to happen after firing all expired
        // // alarms since those may have reset new alarms.
        // let now = self.alarm.now();
        // // let next = self
        // //     .virtual_alarms
        // //     .iter()
        // //     .filter(|cur| cur.armed.get())
        // //     .min_by_key(|cur| {
        // //         let when = cur.dt_reference.get();
        // //         // If the alarm has already expired, then it should be
        // //         // considered as the earliest possible (0 ticks), so it
        // //         // will trigger as soon as possible. This can happen
        // //         // if the alarm expired *after* it was examined in the
        // //         // above loop.
        // //         if !now.within_range(when.reference, when.reference_plus_dt()) {
        // //             A::Ticks::from(0u32)
        // //         } else {
        // //             when.reference_plus_dt().wrapping_sub(now)
        // //         }
        // //     })
        // let mut iterator = ListIteratorV { cur: self.virtual_alarms.head() };
        // let mut min_ticks = None;
        // let mut min_alarm = None;

        // loop {
        //     match iterator.next() {
        //         Some(cur) => {
        //             if cur.armed.get() {
        //                 let when = cur.dt_reference.get();
        //                 let ticks = if !now.within_range(when.reference, when.reference_plus_dt()) {
        //                     A::Ticks::from_or_max(0u64)
        //                 } else {
        //                     when.reference_plus_dt().wrapping_sub(now)
        //                 };

        //                 match min_ticks {
        //                     None => {
        //                         min_ticks = Some(ticks);
        //                         min_alarm = Some(cur);
        //                     },
        //                     Some(min) if ticks.into_usize() < min.into_usize() => {
        //                         min_ticks = Some(ticks);
        //                         min_alarm = Some(cur);
        //                     },
        //                     _ => {},
        //                 }
        //             }
        //         },
        //         None => break ,
        //     }
        // }

        // let next = min_alarm;

        // // Set the alarm.
        // if let Some(valrm) = next {
        //     let dt_reference = valrm.dt_reference.get();
        //     self.set_alarm(dt_reference.reference, dt_reference.dt);
        // } else {
        //     self.disarm();
        // }
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
        ensures
            ret == Self::spec_width(),
            ret <= 64,
    ;

    spec fn get_value(&self) -> int;

    /// Converts the type into a `usize`, stripping the higher bits
    /// it if it is larger than `usize` and filling the higher bits
    /// with 0 if it is smaller than `usize`.
    fn into_usize(self) -> (ret: usize)
        ensures
            ret <= usize::MAX,
            ret == (self.get_value() as usize),  // replace by a spec
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
            (Self::spec_width() > usize::BITS) ==> ret == 0,
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
            Self::spec_width()
                > 0,
    // ensures result == result & (((1usize << usize::BITS) - 1) as usize)
    // ensures result == result & (((1usize << usize::BITS) - 1usize) as usize)
    // ensures result as int == result as int & (((1 as int) << usize::BITS as int) - 1)

    {
        // self.into_usize() << Self::usize_padding()
        let shifted_result = self.into_usize() << Self::usize_padding();
        shifted_result
    }

    /// Convert the generic [`Frequency`] argument into a frequency
    /// (Hertz) describing a left-justified ticks value as returned by
    /// [`Ticks::into_usize_left_justified`].
    fn usize_left_justified_scale_freq() -> u32 {
        10
    }

    /// Converts the type into a `u32`, stripping the higher bits
    /// it if it is larger than `u32` and filling the higher bits
    /// with 0 if it is smaller than `u32`. Included as a simple
    /// helper since Tock uses `u32` pervasively and most platforms
    /// are 32 bits.
    fn into_u32(self) -> u32;

    /// The amount of bits required to left-justify this ticks value
    /// range (filling the lower bits with `0`) for it wrap at `(2 **
    /// 32) - 1` bits. For timers with a `width` larger than 32, this
    /// value will be `0` (i.e., they can simply be truncated to
    /// 32-bits).
    ///
    /// The return value is a `u32`, in accordance with the bit widths
    /// specified using the BITS associated const on Rust integer
    /// types.
    // VERUS-TODO: need to model saturating_sub
    // #[verifier(external_body)]
    fn u32_padding() -> u32 {
        u32::BITS.saturating_sub(Self::width())
    }

    /// Converts the type into a `u32`, left-justified and
    /// right-padded with `0` such that it is guaranteed to wrap at
    /// `(2 ** 32) - 1`. If it is larger than 32-bits, any higher bits
    /// are stripped.
    ///
    /// The resulting tick rate will possibly be higher (multiplied by
    /// `2 ** u32_padding()`). Use `u32_left_justified_scale_freq` to
    /// convert the underlying timer's frequency into the padded ticks
    /// frequency in Hertz.
    fn into_u32_left_justified(self) -> u32 {
        self.into_u32()
    }

    /// Convert the generic [`Frequency`] argument into a frequency
    /// (Hertz) describing a left-justified ticks value as returned by
    /// [`Ticks::into_u32_left_justified`].
    fn u32_left_justified_scale_freq() -> u32 {
        // VERUS-TODO need to make this frequency thing cleaner
        10
    }

    /// Add two values, wrapping around on overflow using standard
    /// unsigned arithmetic.
    fn wrapping_add(self, other: Self) -> Self;

    /// Subtract two values, wrapping around on underflow using standard
    /// unsigned arithmetic.
    fn wrapping_sub(self, other: Self) -> Self;

    /// Returns whether the value is in the range of [`start, `end`) using
    /// unsigned arithmetic and considering wraparound. It returns `true`
    /// if, incrementing from `start`, the value will be reached before `end`.
    /// Put another way, it returns `(self - start) < (end - start)` in
    /// unsigned arithmetic.
    fn within_range(self, start: Self, end: Self) -> bool;

    /// Returns the maximum value of this type, which should be (2^width)-1.
    fn max_value() -> Self;

    /// Returns the half the maximum value of this type, which should be (2^width-1).
    fn half_max_value() -> Self;

    /// Converts the specified val into this type if it fits otherwise the
    /// `max_value()` is returned
    fn from_or_max(val: u64) -> Self;

    /// Scales the ticks by the specified numerator and denominator. If the resulting value would
    /// be greater than u32,`u32::MAX` is returned instead
    fn saturating_scale(self, numerator: u32, denominator: u32) -> u32;
}

/// Represents a clock's frequency in Hz, allowing code to transform
/// between computer time units and wall clock time. It is typically
/// an associated type for an implementation of the `Time` trait.
pub trait Frequency {
    /// Returns frequency in Hz.
    fn frequency() -> u32;
}

/// Represents a moment in time, obtained by calling `now`.
pub trait Time {
    /// The number of ticks per second
    fn get_freq() -> u32;

    /// The width of a time value
    type Ticks: Ticks;

    /// Returns a timestamp. Depending on the implementation of
    /// Time, this could represent either a static timestamp or
    /// a sample of a counter; if an implementation relies on
    /// it being constant or changing it should use `Timestamp`
    /// or `Counter`.
    fn now(&self) -> Self::Ticks;
}

pub trait ConvertTicks<T: Ticks> {
    /// Returns the number of ticks in the provided number of seconds,
    /// rounding down any fractions. If the value overflows Ticks it
    /// returns `Ticks::max_value()`.
    fn ticks_from_seconds(&self, s: u32) -> T;

    /// Returns the number of ticks in the provided number of milliseconds,
    /// rounding down any fractions. If the value overflows Ticks it
    /// returns `Ticks::max_value()`.
    fn ticks_from_ms(&self, ms: u32) -> T;

    /// Returns the number of ticks in the provided number of microseconds,
    /// rounding down any fractions. If the value overflows Ticks it
    /// returns `Ticks::max_value()`.
    fn ticks_from_us(&self, us: u32) -> T;

    /// Returns the number of seconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_seconds(&self, tick: T) -> u32;

    /// Returns the number of milliseconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_ms(&self, tick: T) -> u32;

    /// Returns the number of microseconds in the provided number of ticks,
    /// rounding down any fractions. If the value overflows u32, `u32::MAX`
    /// is returned,
    fn ticks_to_us(&self, tick: T) -> u32;
}

impl<T: Time + ?Sized> ConvertTicks<<T as Time>::Ticks> for T {
    #[verifier(external_body)]
    #[inline]
    fn ticks_from_seconds(&self, s: u32) -> <T as Time>::Ticks {
        let val = <T as Time>::get_freq() as u64 * s as u64;
        <T as Time>::Ticks::from_or_max(val)
    }

    #[verifier(external_body)]
    #[inline]
    fn ticks_from_ms(&self, ms: u32) -> <T as Time>::Ticks {
        let val = <T as Time>::get_freq() as u64 * ms as u64;
        <T as Time>::Ticks::from_or_max(val / 1_000)
    }

    #[verifier(external_body)]
    #[inline]
    fn ticks_from_us(&self, us: u32) -> <T as Time>::Ticks {
        let val = <T as Time>::get_freq() as u64 * us as u64;
        <T as Time>::Ticks::from_or_max(val / 1_000_000)
    }

    #[inline]
    fn ticks_to_seconds(&self, tick: <T as Time>::Ticks) -> u32 {
        tick.saturating_scale(1, <T as Time>::get_freq())
    }

    #[inline]
    fn ticks_to_ms(&self, tick: <T as Time>::Ticks) -> u32 {
        tick.saturating_scale(1_000, <T as Time>::get_freq())
    }

    #[inline]
    fn ticks_to_us(&self, tick: <T as Time>::Ticks) -> u32 {
        tick.saturating_scale(1_000_000, <T as Time>::get_freq())
    }
}

/// Represents a static moment in time, that does not change over
/// repeated calls to `Time::now`.
pub trait Timestamp: Time {

}

/// Callback handler for when a counter has overflowed past its maximum
/// value and returned to 0.
pub trait OverflowClient {
    fn overflow(&self);
}

// VERUS-TODO: need to model this or add this to verus
// #[verifier::external_type_specification]
// pub struct ExErrorCode(ErrorCode);

/// Represents a free-running hardware counter that can be started and stopped.
#[verifier(external)]
pub trait Counter<'a>: Time {
    /// Specify the callback for when the counter overflows its maximum
    /// value (defined by `Ticks`). If there was a previously registered
    /// callback this call replaces it.
    fn set_overflow_client(&self, client: &'a dyn OverflowClient);

    /// Starts the free-running hardware counter. Valid `Result<(), ErrorCode>` values are:
    ///   - `Ok(())`: the counter is now running
    ///   - `Err(ErrorCode::OFF)`: underlying clocks or other hardware resources
    ///   are not on, such that the counter cannot start.
    ///   - `Err(ErrorCode::FAIL)`: unidentified failure, counter is not running.
    /// After a successful call to `start`, `is_running` MUST return true.
    fn start(&self) -> Result<(), ErrorCode>;

    /// Stops the free-running hardware counter. Valid `Result<(), ErrorCode>` values are:
    ///   - `Ok(())`: the counter is now stopped. No further
    ///   overflow callbacks will be invoked.
    ///   - `Err(ErrorCode::BUSY)`: the counter is in use in a way that means it
    ///   cannot be stopped and is busy.
    ///   - `Err(ErrorCode::FAIL)`: unidentified failure, counter is running.
    /// After a successful call to `stop`, `is_running` MUST return false.
    fn stop(&self) -> Result<(), ErrorCode>;

    /// Resets the counter to 0. This may introduce jitter on the counter.
    /// Resetting the counter has no effect on any pending overflow callbacks.
    /// If a client needs to reset and clear pending callbacks it should
    /// call `stop` before `reset`.
    /// Valid `Result<(), ErrorCode>` values are:
    ///    - `Ok(())`: the counter was reset to 0.
    ///    - `Err(ErrorCode::FAIL)`: the counter was not reset to 0.
    fn reset(&self) -> Result<(), ErrorCode>;

    /// Returns whether the counter is currently running.
    fn is_running(&self) -> bool;
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
    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks);

    /// Return the current alarm value. This is undefined at boot and
    /// otherwise returns `now + dt` from the last call to `set_alarm`.
    fn get_alarm(&self) -> Self::Ticks;

    /// Disable the alarm and stop it from firing in the future.
    /// Valid `Result<(), ErrorCode>` codes are:
    ///   - `Ok(())` the alarm has been disarmed and will not invoke
    ///   the callback in the future
    ///   - `Err(ErrorCode::FAIL)` the alarm could not be disarmed and will invoke
    ///   the callback in the future
    fn disarm(&self) -> Result<(), ErrorCode>;

    /// Returns whether the alarm is currently armed. Note that this
    /// does not reliably indicate whether there will be a future
    /// callback: it is possible that the alarm has triggered (and
    /// disarmed) and a callback is pending and has not been called yet.
    /// In this case it possible for `is_armed` to return false yet to
    /// receive a callback.
    fn is_armed(&self) -> bool;

    /// Return the minimum dt value that is supported. Any dt smaller than
    /// this will automatically be increased to this minimum value.
    fn minimum_dt(&self) -> Self::Ticks;
}

/// Callback handler for when a timer fires.
pub trait TimerClient {
    fn timer(&self);
}

/// Interface for controlling callbacks when an interval has passed.
/// This interface is intended for software that requires repeated
/// and/or one-shot timers and is willing to experience some jitter or
/// imprecision in return for a simpler API that doesn't require
/// actual calculation of counter values. Software that requires more
/// precisely timed callbacks should use the `Alarm` trait instead.
#[verifier(external)]
pub trait Timer<'a>: Time {
    /// Specify the callback to invoke when the timer interval expires.
    /// If there was a previously installed callback this call replaces it.
    fn set_timer_client(&self, client: &'a dyn TimerClient);

    /// Start a one-shot timer that will invoke the callback at least
    /// `interval` ticks in the future. If there is a timer currently pending,
    /// calling this cancels that previous timer. After a callback is invoked
    /// for a one shot timer, the timer MUST NOT invoke the callback again
    /// unless a new timer is started (either with repeating or one shot).
    /// Returns the actual interval for the timer that was registered.
    /// This MUST NOT be smaller than `interval` but MAY be larger.
    fn oneshot(&self, interval: Self::Ticks) -> Self::Ticks;

    /// Start a repeating timer that will invoke the callback every
    /// `interval` ticks in the future. If there is a timer currently
    /// pending, calling this cancels that previous timer.
    /// Returns the actual interval for the timer that was registered.
    /// This MUST NOT be smaller than `interval` but MAY be larger.
    fn repeating(&self, interval: Self::Ticks) -> Self::Ticks;

    /// Return the interval of the last requested timer.
    fn interval(&self) -> Option<Self::Ticks>;

    /// Return if the last requested timer is a one-shot timer.
    fn is_oneshot(&self) -> bool;

    /// Return if the last requested timer is a repeating timer.
    fn is_repeating(&self) -> bool;

    /// Return how many ticks are remaining until the next callback,
    /// or None if the timer is disabled.  This call is useful because
    /// there may be non-negligible delays between when a timer was
    /// requested and it was actually scheduled. Therefore, since a
    /// timer's start might be delayed slightly, the time remaining
    /// might be slightly higher than one would expect if one
    /// calculated it right before the call to start the timer.
    fn time_remaining(&self) -> Option<Self::Ticks>;

    /// Returns whether there is currently a timer enabled and so a callback
    /// will be expected in the future. If `is_enabled` returns false then
    /// the implementation MUST NOT invoke a callback until a call to `oneshot`
    /// or `repeating` restarts the timer.
    fn is_enabled(&self) -> bool;

    /// Cancel the current timer, if any. Value `Result<(), ErrorCode>` values are:
    ///  - `Ok(())`: no callback will be invoked in the future.
    ///  - `Err(ErrorCode::FAIL)`: the timer could not be cancelled and a callback
    ///  will be invoked in the future.
    fn cancel(&self) -> Result<(), ErrorCode>;
}

// The following "frequencies" are represented as variant-less enums. Because
// they can never be constructed, it forces them to be used purely as
// type-markers which are guaranteed to be elided at runtime.
pub enum FrequencyVal {
    /// 48MHz `Frequency`
    Freq48MHz,
    /// 32MHz `Frequency`
    Freq32MHz,
    /// 16MHz `Frequency`
    Freq16MHz,
    /// 10MHz `Frequency`
    Freq10MHz,
    /// 8MHz `Frequency`
    Freq8MHz,
    /// 4MHz `Frequency`
    Freq4MHz,
    /// 1MHz `Frequency`
    Freq1MHz,
    /// 500KHz `Frequency`
    Freq500KHz,
    /// 250KHz `Frequency`
    Freq250KHz,
    /// 125KHz `Frequency`
    Freq125KHz,
    /// 100KHz `Frequency`
    Freq100KHz,
    /// 50KHz `Frequency`
    Freq50KHz,
    /// 32KHz `Frequency`
    Freq32KHz,
    /// 16KHz `Frequency`
    Freq16KHz,
    /// 1KHz `Frequency`
    Freq1KHz,
}

// /// 100MHz `Frequency`
// #[derive(Debug)]
// pub enum Freq100MHz {}
// impl Frequency for Freq100MHz {
//     fn frequency() -> u32 {
//         100_000_000
//     }
// }
// /// 16MHz `Frequency`
// #[derive(Debug)]
// pub enum Freq16MHz {}
// impl Frequency for Freq16MHz {
//     fn frequency() -> u32 {
//         16_000_000
//     }
// }
// /// 10MHz `Frequency`
// pub enum Freq10MHz {}
// impl Frequency for Freq10MHz {
//     fn frequency() -> u32 {
//         10_000_000
//     }
// }
// /// 1MHz `Frequency`
// #[derive(Debug)]
// pub enum Freq1MHz {}
// impl Frequency for Freq1MHz {
//     fn frequency() -> u32 {
//         1_000_000
//     }
// }
// verus! {
// /// 32.768KHz `Frequency`
// #[verifier::external]
// #[derive(Debug)]
// pub enum Freq32KHz {}
// impl Frequency for Freq32KHz {
//     fn frequency() -> u32 {
//         32_768
//     }
// }
// }
// /// 16KHz `Frequency`
// #[derive(Debug)]
// pub enum Freq16KHz {}
// impl Frequency for Freq16KHz {
//     fn frequency() -> u32 {
//         16_000
//     }
// }
// /// 1KHz `Frequency`
// #[derive(Debug)]
// pub enum Freq1KHz {}
// impl Frequency for Freq1KHz {
//     fn frequency() -> u32 {
//         1_000
//     }
// }
/// u32 `Ticks`
#[derive(Debug)]
pub struct Ticks32(u32);

impl Copy for Ticks32 {

}

// Manually implementing the Clone trait
impl Clone for Ticks32 {
    fn clone(&self) -> Ticks32 {
        // Simply return a copy of the value
        *self
    }
}

// impl Clone for Ticks32 {
//     fn clone(&self) -> Self {
//         Self(self.0)
//     }
// }
// impl Copy for Ticks32 {}
impl From<u32> for Ticks32 {
    fn from(val: u32) -> Self {
        Ticks32(val)
    }
}

impl Ticks for Ticks32 {
    closed spec fn get_value(&self) -> int {
        self.0 as int
    }

    closed spec fn spec_width() -> u32 {
        32
    }

    fn width() -> u32 {
        32
    }

    fn into_usize(self) -> usize {
        let ret = self.0 as usize;
        assert(ret <= self.get_value() as usize);
        ret
    }

    fn into_u32(self) -> u32 {
        self.0
    }

    fn wrapping_add(self, other: Self) -> Self {
        Ticks32(self.0.wrapping_add(other.0))
    }

    fn wrapping_sub(self, other: Self) -> Self {
        Ticks32(self.0.wrapping_sub(other.0))
    }

    fn within_range(self, start: Self, end: Self) -> bool {
        self.wrapping_sub(start).0 < end.wrapping_sub(start).0
    }

    /// Returns the maximum value of this type, which should be (2^width)-1.
    fn max_value() -> Self {
        Ticks32(0xFFFFFFFF)
    }

    /// Returns the half the maximum value of this type, which should be (2^width-1).
    fn half_max_value() -> Self {
        Self(1 + (Self::max_value().0 / 2))
    }

    #[inline]
    fn from_or_max(val: u64) -> Self {
        if val < Self::max_value().0 as u64 {
            Self::from(val as u32)
        } else {
            Self::max_value()
        }
    }

    #[inline]
    #[verifier(external_body)]
    fn saturating_scale(self, numerator: u32, denominator: u32) -> u32 {
        let scaled = self.0 as u64 * numerator as u64 / denominator as u64;
        if scaled < u32::MAX as u64 {
            scaled as u32
        } else {
            u32::MAX
        }
    }
}

impl PartialOrd for Ticks32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ticks32 {
    #[verifier(external_body)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialEq for Ticks32 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Ticks32 {

}

/// 24-bit `Ticks`
#[derive(Clone, Copy, Debug)]
pub struct Ticks24(u32);

impl Ticks24 {
    pub fn get_mask() -> u32 {
        0x00FFFFFF
    }
}

impl From<u32> for Ticks24 {
    fn from(val: u32) -> Self {
        Ticks24(val & Self::get_mask())
    }
}

impl Ticks for Ticks24 {
    closed spec fn get_value(&self) -> int {
        self.0 as int
    }

    closed spec fn spec_width() -> u32 {
        24
    }

    fn width() -> u32 {
        24
    }

    fn into_usize(self) -> usize {
        assert(self.0 == self.get_value());
        self.0 as usize
    }

    fn into_u32(self) -> u32 {
        self.0
    }

    fn wrapping_add(self, other: Self) -> Self {
        Ticks24(self.0.wrapping_add(other.0) & Self::get_mask())
    }

    fn wrapping_sub(self, other: Self) -> Self {
        Ticks24(self.0.wrapping_sub(other.0) & Self::get_mask())
    }

    fn within_range(self, start: Self, end: Self) -> bool {
        self.wrapping_sub(start).0 < end.wrapping_sub(start).0
    }

    /// Returns the maximum value of this type, which should be (2^width)-1.
    fn max_value() -> Self {
        Ticks24(Self::get_mask())
    }

    /// Returns the half the maximum value of this type, which should be (2^width-1).
    fn half_max_value() -> Self {
        Self(1 + (Self::max_value().0 / 2))
    }

    #[inline]
    fn from_or_max(val: u64) -> Self {
        if val < Self::max_value().0 as u64 {
            Self::from(val as u32)
        } else {
            Self::max_value()
        }
    }

    #[inline]
    #[verifier(external_body)]
    fn saturating_scale(self, numerator: u32, denominator: u32) -> u32 {
        let scaled = self.0 as u64 * numerator as u64 / denominator as u64;
        if scaled < u32::MAX as u64 {
            scaled as u32
        } else {
            u32::MAX
        }
    }
}

// #[verifier(external_type_specification)]
// pub struct ExOrdering(core::cmp::Ordering);

impl PartialOrd for Ticks24 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ticks24 {
    #[verifier(external_body)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialEq for Ticks24 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Ticks24 {

}

/// 16-bit `Ticks`
#[derive(Clone, Copy, Debug)]
pub struct Ticks16(u16);

impl From<u16> for Ticks16 {
    fn from(val: u16) -> Self {
        Ticks16(val)
    }
}

impl From<u32> for Ticks16 {
    fn from(val: u32) -> Self {
        Ticks16((val & 0xffff) as u16)
    }
}

impl Ticks16 {
    pub fn into_u16(self) -> u16 {
        self.0
    }
}

impl Ticks for Ticks16 {
    closed spec fn get_value(&self) -> int {
        self.0 as int
    }

    closed spec fn spec_width() -> u32 {
        16
    }

    fn width() -> u32 {
        16
    }

    fn into_usize(self) -> usize {
        assert(self.0 == self.get_value());
        self.0 as usize
    }

    fn into_u32(self) -> u32 {
        self.0 as u32
    }

    fn wrapping_add(self, other: Self) -> Self {
        Ticks16(self.0.wrapping_add(other.0))
    }

    fn wrapping_sub(self, other: Self) -> Self {
        Ticks16(self.0.wrapping_sub(other.0))
    }

    fn within_range(self, start: Self, end: Self) -> bool {
        self.wrapping_sub(start).0 < end.wrapping_sub(start).0
    }

    /// Returns the maximum value of this type, which should be (2^width)-1.
    fn max_value() -> Self {
        Ticks16(0xFFFF)
    }

    /// Returns the half the maximum value of this type, which should be (2^width-1).
    fn half_max_value() -> Self {
        Self(1 + (Self::max_value().0 / 2))
    }

    #[inline]
    fn from_or_max(val: u64) -> Self {
        if val < Self::max_value().0 as u64 {
            Self::from(val as u32)
        } else {
            Self::max_value()
        }
    }

    #[inline]
    #[verifier(external_body)]
    fn saturating_scale(self, numerator: u32, denominator: u32) -> u32 {
        let scaled = self.0 as u64 * numerator as u64 / denominator as u64;
        if scaled < u32::MAX as u64 {
            scaled as u32
        } else {
            u32::MAX
        }
    }
}

impl PartialOrd for Ticks16 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ticks16 {
    #[verifier(external_body)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialEq for Ticks16 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Ticks16 {

}


struct FakeAlarm {
    now: Cell<Ticks32>,
    reference: Cell<Ticks32>,
    dt: Cell<Ticks32>,
    armed: Cell<bool>,
    client: Cell<ClientCounter>,
}

impl FakeAlarm {
    fn new() -> Self {
        Self {
            now: Cell::new(1_000u32.into()),
            reference: Cell::new(0u32.into()),
            dt: Cell::new(0u32.into()),
            armed: Cell::new(false),
            client: Cell::new(ClientCounter::new()),
        }
    }

    /// The emulated delay from when hardware timer to when kernel loop will
    /// run to check if alarms have fired or not.
    pub fn hardware_delay(&self) -> Ticks32 {
        Ticks32::from(10)
    }

    /// Fast forwards time to the next time we would fire an alarm and call client. Returns if
    /// alarm is still armed after triggering client
    pub fn trigger_next_alarm(&self) -> bool {
        if !self.is_armed() {
            return false;
        }
        self.now.set(
            self.reference
                .get()
                .wrapping_add(self.dt.get())
                .wrapping_add(self.hardware_delay()),
        );
        // self.client.map(|c| c.alarm());
        // self.client.into_inner().alarm();
        // TODO: call alarm


        self.is_armed()
    }

    /// Runs for the specified number of ticks as long as there are alarms armed.
    pub fn run_for_ticks(&self, left: Ticks32) {
        let final_now = self.now.get().wrapping_add(left);
        let mut left = left.into_u32();

        // while self.is_armed() {
        //     // Ensure that we have enough remaining ticks to handle the next alarm. Reference is
        //     // always in the past, so we need to figure out the difference between the reference
        //     // and now to discount the DT the alarm needs to wait by.
        //     let ticks_from_reference = self.now.get().wrapping_sub(self.reference.get());
        //     let dt = self
        //         .dt
        //         .get()
        //         .into_u32()
        //         .saturating_sub(ticks_from_reference.into_u32());
        //     if dt <= left {
        //         left -= dt;
        //         self.trigger_next_alarm();
        //     } else {
        //         break;
        //     }
        // }
        // Ensure that we ate up all of the time we were suppose to run for
        self.now.set(final_now);
    }
}

/// Clock fundamentally overflows
#[verifier::external]
impl Time for FakeAlarm {
    type Ticks = Ticks32;
    // type Frequency = FrequencyVal::Freq1KHz;

    fn now(&self) -> Ticks32 {
        // Every time we get now, it needs to increment to represent a free running timer
        let new_now = Ticks32::from(self.now.get().into_u32() + 1);
        self.now.set(new_now);
        new_now
    }
    fn get_freq() -> u32 {
        1_000
    }
}

impl<'a> Alarm<'a> for FakeAlarm {
    // fn set_alarm_client(&self, client: &'a dyn AlarmClient) {
    //     self.client.set(client);
    // }

    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks) {
        self.reference.set(reference);
        self.dt.set(dt);
        self.armed.set(true);
    }

    fn get_alarm(&self) -> Self::Ticks {
        self.reference.get().wrapping_add(self.dt.get())
    }

    fn disarm(&self) -> Result<(), ErrorCode> {
        self.armed.set(false);
        Ok(())
    }

    fn is_armed(&self) -> bool {
        self.armed.get()
    }

    fn minimum_dt(&self) -> Self::Ticks {
        0u32.into()
    }
}

struct ClientCounter(Cell<usize>);
impl ClientCounter {
    fn new() -> Self {
        Self(Cell::new(0))
    }
    fn count(&self) -> usize {
        self.0.get()
    }
}

#[verifier::external]
impl AlarmClient for ClientCounter {
    fn alarm(&self) {
        self.0.set(self.0.get() + 1); // fundamentally overflowing operation
    }
}

fn run_until_disarmed(alarm: &FakeAlarm) {
    // Don't loop forever if we never disarm
    for _ in 0..20 {
        if !alarm.trigger_next_alarm() {
            return;
        }
    }
}

fn main() {
    // let alarm = Alarm::new();
    // write dummy negative tests
    {
        let alarm = FakeAlarm::new();
        let client = ClientCounter::new();
        // let dt = u32::MAX.into();

        let mux = MuxAlarm::new(&alarm);
        // alarm.set_alarm_client(&mux);

        // assert_eq!(client.count(), 3);
    }
    // write dummy positive tests

    // TODO: 3 test cases which correspond to the three overlapping cases. past/future/present
}
} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    struct Test1MHz64();
    impl Time for Test1MHz64 {
        fn get_freq(freq_val: FrequencyVal) -> u32 {
            match freq_val {
                FrequencyVal::Freq1MHz => 1_000_000,
                _ => 0,
            }
        }
        type Ticks = Ticks64;

        fn now(&self) -> Self::Ticks {
            0u32.into()
        }
    }
}
