// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Tock syscall driver capsule for Alarms, which issue callbacks when
//! a point in time has been reached.

use kernel::grant::{AllowRoCount, AllowRwCount, Grant, UpcallCount};
use kernel::hil::time::Ticks;
use kernel::syscall::{CommandReturn, SyscallDriver};
use kernel::{ErrorCode, ProcessId};
use vstd::prelude::*;

/// Syscall driver number.
use crate::driver;
// use crate::virtualizers::virtual_alarm_v::{Alarm, AlarmClient, MuxAlarmState};
use crate::virtualizers::virtual_alarm::{Alarm, AlarmClient, MuxAlarmState};
// use crate::virtualizers::new_virtual_alarm::{Alarm, AlarmClient, MuxAlarmState};
pub const DRIVER_NUM: usize = driver::NUM::Alarm as usize;

verus! {

#[derive(Copy, Clone, Debug)]
struct Expiration<T: Ticks> {
    reference: T,
    dt: T,
}

#[derive(Copy, Clone)]
pub struct AlarmData<T: Ticks> {
    expiration: Option<Expiration<T>>,
}

const ALARM_CALLBACK_NUM: usize = 0;
const NUM_UPCALLS: u8 = 1;

impl<T: Ticks> Default for AlarmData<T> {
    fn default() -> AlarmData<T> {
        AlarmData { expiration: None }
    }
}

// struct ExpirationTupleIterator<'a, A:Ticks> {
//     pub array: &'a[Expiration<A>],
//     pub cur: usize,
// }

// struct ExpirationTuple<A: Ticks, UD, F>(Expiration<A>, UD, F);
// impl<I> ExpirationIterator<I> {
//     fn new(iter: I) -> Self {
//         ExpirationIterator {}
//     }
// }

// struct ExpirationGhostIterator<A: Ticks> {
//     remaining_items: Seq<(Expiration<A>)>, // Immutable sequence for ghost state
//     cur_index: int, // Current index in the sequence, starting at 0
// }

// impl<'a, A: Ticks, UD, F> vstd::pervasive::ForLoopGhostIteratorNew for ExpirationTuple<A, UD, F>
// {
//     type GhostIter = ExpirationGhostIterator<A>;

//     open spec fn ghost_iter(&self) -> ExpirationGhostIterator<A> {
//         ExpirationGhostIterator {
//     }
// }

// impl<'a, A: Ticks, UD, F> Iterator for ExpirationTuple< A, UD, F> {
//     type Item = (Expiration<A>, UD, F);

//     fn next(&mut self) -> Option<Self::Item> {
// if self.cur < self.array.len() {
//     let exp = self.array[self.cur].clone();
//     self.cur += 1;
//     Some((exp, self.user_data, self.handler))
// } else {
//     None
// }
// None
// }
// }

// // Implement the required trait for your ExpirationTupleIterator
// impl<'a, A: Ticks, UD, F> vstd::pervasive::ForLoopGhostIteratorNew for ExpirationTupleIterator<'a, A, UD, F> {
//     type GhostIter = ExpirationGhostIterator<A>;

//     open spec fn ghost_iter(&self) -> ExpirationGhostIterator<A> {
//         ExpirationGhostIterator {
//             remaining_items: self.array@, // Assuming `@` syntax works here for the ghost type
//             cur_index: 0,
//         }
//     }
// }

pub struct AlarmDriver<'a, A: Alarm<'a>> {
    alarm: &'a A,
    app_alarms:
        Grant<AlarmData<A::Ticks>, UpcallCount<NUM_UPCALLS>, AllowRoCount<0>, AllowRwCount<0>>,
}
use kernel::grant::AllowRoSize;
use kernel::grant::AllowRwSize;
use kernel::grant::UpcallSize;

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::accept_recursive_types(Upcalls)]
#[verifier::accept_recursive_types(AllowROs)]
#[verifier::accept_recursive_types(AllowRWs)]
pub struct ExGrant<T: Default, Upcalls: UpcallSize, AllowROs: AllowRoSize, AllowRWs: AllowRwSize>(
    Grant<T, Upcalls, AllowROs, AllowRWs>,
);

impl<'a, A: Alarm<'a>> AlarmDriver<'a, A> {
    // VERUS-TODO: To prevent this from being external we might have
    // to model each of these types
    #[verifier::external]
    pub const fn new(
        alarm: &'a A,
        grant: Grant<
            AlarmData<A::Ticks>,
            UpcallCount<NUM_UPCALLS>,
            AllowRoCount<0>,
            AllowRwCount<0>,
        >,
    ) -> AlarmDriver<'a, A> {
        AlarmDriver {
            alarm,
            app_alarms: grant,
        }
    }

    /// Find the earliest [`Expiration`] from an iterator of expirations.
    ///
    /// Each [`Expiration`] value is provided as a tuple, with
    /// - `UD`: an additional user-data argument returned together with the
    ///   [`Expiration`], should it be the earliest, and
    /// - `F`: a call-back function invoked when the [`Expiration`] has already
    ///   expired. The callback is porivded the expiration value and a reference
    ///   to its user-data.
    ///
    /// Whether an [`Expiration`] has expired or not is determined with respect
    /// to `now`. If `now` is in `[exp.reference; exp.reference + exp.dt)`, it
    /// the [`Expiration`] has not yet expired.
    ///
    /// An expired [`Expiration`] is not a candidate for "earliest" expiration.
    /// This means that this function will return `Ok(None)` if it receives an
    /// empty iterator, or all [`Expiration`]s have expired.
    ///
    /// To stop iteration on any expired [`Expiration`], its callback can return
    /// `Some(R)`. Then this function will return `Err(Expiration, UD, R)`.
    /// This avoids consuming the entire iterator.
    fn earliest_alarm<UD, R, F: FnOnce(Expiration<A::Ticks>, &UD) -> Option<R>>(
        now: A::Ticks,
        expirations: impl Iterator<Item = (Expiration<A::Ticks>, UD, F)>,
    ) -> Result<Option<(Expiration<A::Ticks>, UD)>, (Expiration<A::Ticks>, UD, R)> {
        let mut earliest: Option<(Expiration<A::Ticks>, UD)> = None;

        Ok(earliest)
        // Verus-TODO what is the difference between fold and for loop?
        // This is just not supported
        // expirations.fold(
        //     Ok(None),
        //     // |acc, (exp, ud, expired_handler)| match acc {
        //         |acc, tuple| {
        //             let exp = tuple.0;
        //             let ud = tuple.1;
        //             let expired_handler = tuple.2;
        //         match acc {
        //         Ok(earliest) => {
        //             // Your existing logic here
        //             let Expiration {
        //                 reference: exp_ref,
        //                 dt: exp_dt,
        //             } = exp;

        //             // Process the expiration and update earliest if needed
        //             // Return Ok(new_earliest) or Err(...) as needed
        //             Ok(earliest)
        //         }
        //         Err(e) => Err(e),
        //     }
        //     }
        // )
        // for (exp, ud, expired_handler) in expirations {
        //     let Expiration {
        //         reference: exp_ref,
        //         dt: exp_dt,
        //     } = exp;

        //     // Pre-compute the absolute "end" time of this expiration (the
        //     // point at which it should fire):
        //     let exp_end = exp_ref.wrapping_add(exp_dt);

        //     // If `now` is not within `[reference, reference + dt)`, this
        //     // alarm has expired. Call the expired handler. If it returns
        //     // false, stop here.
        //     if !now.within_range(exp_ref, exp_end) {
        //         let expired_handler_res = expired_handler(exp, &ud);
        //         if let Some(retval) = expired_handler_res {
        //             return Err((exp, ud, retval));
        //         }
        //     }

        //     // `exp` has not yet expired. At this point we can assume that
        //     // `now` is within `[exp_ref, exp_end)`. Check whether it will
        //     // expire earlier than the current `earliest`:
        //     match &earliest {
        //         None => {
        //             // Do not have an earliest expiration yet, set this
        //             // expriation as earliest:
        //             earliest = Some((exp, ud));
        //         }

        //         Some((
        //             Expiration {
        //                 reference: earliest_ref,
        //                 dt: earliest_dt,
        //             },
        //             _,
        //         )) => {
        //             // As `now` is within `[ref, end)` for both timers, we
        //             // can check which end time is closer to `now`. We thus
        //             // first compute the end time for the current earliest
        //             // alarm as well ...
        //             let earliest_end = earliest_ref.wrapping_add(*earliest_dt);

        //             // ... and then perform a wrapping_sub against `now` for
        //             // both, checking which is smaller:
        //             let exp_remain = exp_end.wrapping_sub(now);
        //             let earliest_remain = earliest_end.wrapping_sub(now);
        //             if exp_remain < earliest_remain {
        //                 // Our current exp expires earlier than earliest,
        //                 // replace it:
        //                 earliest = Some((exp, ud));
        //             }
        //         }
        //     }
        // }

        // // We have computed earliest by iterating over all alarms, but have not
        // // found one that has already expired. As such return `false`:
        // Ok(earliest)
    }

    /// Re-arm the timer. This must be called in response to the underlying
    /// timer firing, or the set of [`Expiration`]s changing. This will iterate
    /// over all [`Expiration`]s and
    ///
    /// - invoke upcalls for all expired app alarms, resetting them afterwards,
    /// - re-arming the alarm for the next earliest [`Expiration`], or
    /// - disarming the alarm if no unexpired [`Expiration`] is found.
    #[verifier::external_body]
    fn process_rearm_or_callback(&self) {
        // Ask the clock about a current reference once. This can incur a
        // volatile read, and this may not be optimized if done in a loop:
        let now = self.alarm.now();

        let expired_handler = |expired: Expiration<A::Ticks>, process_id: &ProcessId| {
            // This closure is run on every expired alarm, _after_ the `enter()`
            // closure on the Grant iterator has returned. We are thus not
            // risking reentrancy here.

            // Enter the app's grant again:
            let _ = self.app_alarms.enter(*process_id, |alarm_state, upcalls| {
                // Reset this app's alarm:
                alarm_state.expiration = None;

                // Deliver the upcall:
                upcalls
                    .schedule_upcall(
                        ALARM_CALLBACK_NUM,
                        (
                            now.into_u32_left_justified() as usize,
                            expired
                                .reference
                                .wrapping_add(expired.dt)
                                .into_u32_left_justified() as usize,
                            0,
                        ),
                    )
                    .ok();
            });

            // Proceed iteration across expirations:
            None::<()>
        };

        // Compute the earliest alarm, and invoke the `expired_handler` for
        // every expired alarm. This will issue a callback and reset the alarms
        // respectively.
        let res = Self::earliest_alarm(
            now,
            // Pass an interator of all non-None expirations:
            self.app_alarms.iter().filter_map(|app| {
                let process_id = app.processid();
                app.enter(|alarm_state, _upcalls| {
                    if let Some(exp) = alarm_state.expiration {
                        Some((exp, process_id, expired_handler))
                    } else {
                        None
                    }
                })
            }),
        );

        // Arm or disarm the alarm accordingly:
        match res {
            // No pending alarm, disarm:
            Ok(None) => {
                // VERUS-TODO
                //let _ = self.alarm.disarm();
            }

            // A future, non-expired alarm should fire:
            Ok(Some((Expiration { reference, dt }, _))) => {
                // VERUS-TODO
                //self.alarm.set_alarm(reference, dt);
            }

            // The expired closure has requested to stop iteration. This should
            // be unreachable, and hence we panic:
            Err((_, _, ())) => {
                unreachable!();
            }
        }
    }

    // #[verifier::external_body]
    fn rearm_u32_left_justified_expiration(
        now: A::Ticks,
        reference_u32: Option<u32>,
        dt_u32: u32,
        expiration: &mut Option<Expiration<A::Ticks>>,
    ) -> u32 {
        let reference_unshifted = reference_u32;
        // let reference_unshifted = reference_u32.map(|ref_u32| ref_u32 >> A::Ticks::u32_padding());

        // If the underlying timer is less than 32-bit wide, userspace is able
        // to provide a finer `reference` and `dt` resolution than we can
        // possibly represent in the kernel.
        //
        // We do not want to switch back to userspace *before* the timer
        // fires. As such, when userspace gives us reference and ticks values
        // with a precision unrepresentible using our Ticks object, we round
        // `reference` down, and `dt` up (ensuring that the timer cannot fire
        // earlier than requested).
        let dt_unshifted = if let Some(reference_u32) = reference_u32 {
            // Computing unshifted dt for a userspace alarm can
            // underestimate dt in some cases where both reference and
            // dt had low-order bits that are rounded off by
            // unshifting. To ensure `dt` results in an actual
            // expiration that is at least as long as the expected
            // expiration in user space, compute unshifted dt from an
            // unshifted expiration.
            let expiration_shifted = reference_u32.wrapping_add(dt_u32);
            let expiration_unshifted =
                if expiration_shifted & ((1 << A::Ticks::u32_padding()) - 1) != 0 {
                    // By right-shifting, we would decrease the requested dt value,
                    // firing _before_ the time requested by userspace. Add one to
                    // compensate this:
                    (expiration_shifted >> A::Ticks::u32_padding()) + 1
                } else {
                    expiration_shifted >> A::Ticks::u32_padding()
                };

            expiration_unshifted.wrapping_sub(reference_u32 >> A::Ticks::u32_padding())
        } else if dt_u32 & ((1 << A::Ticks::u32_padding()) - 1) != 0 {
            // By right-shifting, we would decrease the requested dt value,
            // firing _before_ the time requested by userspace. Add one to
            // compensate this:
            (dt_u32 >> A::Ticks::u32_padding()) + 1
        } else {
            // dt does not need to be shifted *or* contains no lower bits
            // unrepresentable in the kernel:
            dt_u32 >> A::Ticks::u32_padding()
        };

        // For timers less than 32-bit wide, we do not have to handle a
        // `reference + dt` overflow specially. This is because those timers are
        // conveyed to us left-justified, and as such userspace would already
        // have to take care of such overflow.
        //
        // However, we *may* need to handle overflow when the timer is *wider*
        // than 32 bit. In this case, if `reference + dt` were to overflow, we
        // need to rebase our reference on the full-width `now` time.
        //
        // If userspace didn't give us a reference, we can skip all of this and
        // simply set the unshifted dt.
        let new_exp = match (reference_unshifted, A::Ticks::width() > 32) {
            (Some(userspace_reference_unshifted), true) => {
                // We have a userspace reference and timer is wider than 32 bit.
                //
                // In this case, we need to check whether the lower 32 bits of the
                // timer `reference` have already wrapped, compared to the reference
                // provided by userspace:
                if now.into_u32() < userspace_reference_unshifted {
                    // The lower 32-bit of reference are smaller than the userspace
                    // reference. This means that the full-width timer has had an
                    // increment in the upper bits. We thus set the full-width
                    // reference to the combination of the current upper timer bits
                    // *minus 1*, concatenated to the user-space provided bits.
                    //
                    // Because we don't know the integer type of the Ticks object
                    // (just that it's larger than a u32), we:
                    //
                    // 1. subtract a full `u32::MAX + 1` to incur a downward wrap,
                    //    effectively subtracting `1` from the upper part,
                    // 2. subtract the lower `u32` bits from this value, setting
                    //    those bits to zero,
                    // 3. adding back the userspace-provided reference.

                    // Build 1 << 32:
                    // Verus-TODO: This is not supported, need to model or verify from
                    let bit33 = A::Ticks::from(0xffffffff).wrapping_add(A::Ticks::from(0x1));

                    // Perform step 1, subtracting 1 << 32:
                    let sub_1_upper = now.wrapping_sub(bit33);

                    // Perform step 2, setting first 32 bit to zero:
                    let sub_lower =
                        sub_1_upper.wrapping_sub(A::Ticks::from(sub_1_upper.into_u32()));

                    // Perform step 3, add back the userspace-provided reference:
                    let rebased_reference =
                        sub_lower.wrapping_add(A::Ticks::from(userspace_reference_unshifted));

                    // Finally, return the new expiration. We don't have to do
                    // anything special for `dt`, as it's relative:
                    Expiration {
                        reference: rebased_reference,
                        dt: A::Ticks::from(dt_unshifted),
                    }
                } else {
                    // The lower 32-bit of reference are equal to or larger than the
                    // userspace reference. Thus we can rebase the reference,
                    // touching only the lower 32 bit, by:
                    //
                    // 1. subtract the lower `u32` bits from this value, setting
                    //    those bits to zero,
                    // 2. adding back the userspace-provided reference.

                    // Perform step 1, setting first 32 bit to zero:
                    let sub_lower = now.wrapping_sub(A::Ticks::from(now.into_u32()));

                    // Perform step 2, add back the userspace-provided reference:
                    let rebased_reference =
                        sub_lower.wrapping_add(A::Ticks::from(userspace_reference_unshifted));

                    // Finally, return the new expiration. We don't have to do
                    // anything special for `dt`, as it's relative:
                    Expiration {
                        reference: rebased_reference,
                        dt: A::Ticks::from(dt_unshifted),
                    }
                }
            }

            (Some(userspace_reference_unshifted), false) => {
                // We have a userspace reference and timer is (less than) 32
                // bit. Simply set to unshifted values:

                Expiration {
                    reference: A::Ticks::from(userspace_reference_unshifted),
                    dt: A::Ticks::from(dt_unshifted),
                }
            }

            (None, _) => {
                // We have no userspace reference. Use `now` as a reference:
                Expiration {
                    reference: now,
                    dt: A::Ticks::from(dt_unshifted),
                }
            }
        };

        // Store the new expiration. We already adjusted the armed count above:
        *expiration = Some(new_exp);

        // Return the time left-justified time at which the alarm will fire:
        new_exp
            .reference
            .wrapping_add(new_exp.dt)
            .into_u32_left_justified()
    }
}
}

impl<'a, A: Alarm<'a>> SyscallDriver for AlarmDriver<'a, A> {
    /// Setup and read the alarm.
    ///
    /// ### `command_num`
    ///
    /// - `0`: Driver existence check.
    /// - `1`: Return the clock frequency in Hz.
    /// - `2`: Read the current clock value
    /// - `3`: Stop the alarm if it is outstanding
    /// - `4`: Deprecated
    /// - `5`: Set an alarm to fire at a given clock value `time` relative to `now`
    /// - `6`: Set an alarm to fire at a given clock value `time` relative to a provided
    ///        reference point.
    fn command(
        &self,
        cmd_type: usize,
        data: usize,
        data2: usize,
        caller_id: ProcessId,
    ) -> CommandReturn {
        // Returns the error code to return to the user and whether we need to
        // reset which is the next active alarm. We _don't_ reset if
        //   - we're disabling the underlying alarm anyway,
        //   - the underlying alarm is currently disabled and we're enabling the first alarm, or
        //   - on an error (i.e. no change to the alarms).
        self.app_alarms
            .enter(caller_id, |td, _upcalls| {
                let now = self.alarm.now();

                match cmd_type {
                    // Driver check:
                    //
                    // Don't re-arm the timer:
                    0 => (CommandReturn::success(), false),

                    1 => {
                        // Get clock frequency. We return a frequency scaled by
                        // the amount of padding we add to the `ticks` value
                        // returned in command 2 ("capture time"), such that
                        // userspace knows when the timer will wrap and can
                        // accurately determine the duration of a single tick.
                        //
                        // Don't re-arm the timer:
                        let scaled_freq = <A::Ticks>::u32_left_justified_scale_freq();
                        (CommandReturn::success_u32(scaled_freq), false)
                    }
                    2 => {
                        // Capture time. We pad the underlying timer's ticks to
                        // wrap at exactly `(2 ** 32) - 1`. This predictable
                        // wrapping value allows userspace to build long running
                        // timers beyond `2 ** now.width()` ticks.
                        //
                        // Don't re-arm the timer:
                        (
                            CommandReturn::success_u32(now.into_u32_left_justified()),
                            false,
                        )
                    }
                    3 => {
                        // Stop
                        match td.expiration {
                            None => {
                                // Request to stop when already stopped. Don't
                                // re-arm the timer:
                                (CommandReturn::failure(ErrorCode::ALREADY), false)
                            }
                            Some(_old_expiraton) => {
                                // Clear the expiration:
                                td.expiration = None;

                                // Ask for the timer to be re-armed. We can't do
                                // this here, as it would re-enter the grant
                                // region:
                                (CommandReturn::success(), true)
                            }
                        }
                    }
                    4 => {
                        // Deprecated in 2.0, used to be: set absolute expiration
                        //
                        // Don't re-arm the timer:
                        (CommandReturn::failure(ErrorCode::NOSUPPORT), false)
                    }
                    5 => {
                        // Set relative expiration.
                        //
                        // We provided userspace a potentially padded version of
                        // our in-kernel Ticks object, and as such we have to
                        // invert that operation through a right shift.
                        //
                        // Also, we need to keep track of the currently armed
                        // timers.
                        //
                        // All of this is done in the following helper method:
                        let new_exp_left_justified = Self::rearm_u32_left_justified_expiration(
                            // Current time:
                            now,
                            // No userspace-provided reference:
                            None,
                            // Left-justified `dt` value:
                            data as u32,
                            // Reference to the `Option<Expiration>`, also used
                            // to update the counter of armed alarms:
                            &mut td.expiration,
                        );

                        // Report success, with the left-justified time at which
                        // the alarm will fire. Also ask for the timer to be
                        // re-armed. We can't do this here, as it would re-enter
                        // the grant region:
                        (CommandReturn::success_u32(new_exp_left_justified), true)
                    }
                    6 => {
                        // Also, we need to keep track of the currently armed
                        // timers.
                        //
                        // All of this is done in the following helper method:
                        let new_exp_left_justified = Self::rearm_u32_left_justified_expiration(
                            // Current time:
                            now,
                            // Left-justified userspace-provided reference:
                            Some(data as u32),
                            // Left-justified `dt` value:
                            data2 as u32,
                            // Reference to the `Option<Expiration>`, also used
                            // to update the counter of armed alarms:
                            &mut td.expiration,
                        );

                        // Report success, with the left-justified time at which
                        // the alarm will fire. Also ask for the timer to be
                        // re-armed. We can't do this here, as it would re-enter
                        // the grant region:
                        (CommandReturn::success_u32(new_exp_left_justified), true)
                    }

                    // Unknown command:
                    //
                    // Don't re-arm the timer:
                    _ => (CommandReturn::failure(ErrorCode::NOSUPPORT), false),
                }
            })
            .map_or_else(
                |err| CommandReturn::failure(err.into()),
                |(retval, rearm_timer)| {
                    if rearm_timer {
                        self.process_rearm_or_callback();
                    }
                    retval
                },
            )
    }

    fn allocate_grant(&self, processid: ProcessId) -> Result<(), kernel::process::Error> {
        self.app_alarms.enter(processid, |_, _| {})
    }
}

impl<'a, A: Alarm<'a>> AlarmClient<'a, A> for AlarmDriver<'a, A> {
    fn alarm(&self, _state: &mut Tracked<MuxAlarmState<'a, A>>) {
        self.process_rearm_or_callback();
    }
}
