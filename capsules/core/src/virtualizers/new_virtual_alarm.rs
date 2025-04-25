// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.
//! Virtualize the Alarm interface to enable multiple users of an underlying
//! alarm hardware peripheral.
// use core::cell::Cell;
use vstd::prelude::*;

use kernel::collections::list::{List, ListIterator, ListLink, ListNode};

verus! {

/*
`make -f Verifile verify_virtual_alarm`

Fails with
thread 'rustc' panicked at vir/src/traits.rs:349:13:
assertion failed: !method_impls.contains(&p)
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
warning: 5 warnings emitted
*/
#[verifier::external_fn_specification] // commenting out removes the panic
pub fn ExListIteratornext<'a, T: ?Sized + ListNode<'a, T>>(
    iter: &mut ListIterator<'a, T>,
) -> Option<&'a T> {
    iter.next()
}


} // verus!
