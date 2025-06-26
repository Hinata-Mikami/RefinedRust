// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module allows storing mir bodies with borrowck facts in a thread-local
//! storage. Unfortunately, thread local storage requires all data stored in it
//! to have a `'static` lifetime. Therefore, we transmute the lifetime `'tcx`
//! away when storing the data. To ensure that nothing gets meessed up, we
//! require the client to provide a witness: an instance of type `TyCtxt<'tcx>`
//! that is used to show that the lifetime that the client provided is indeed
//! `'tcx`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::{mem, thread_local};

use rr_rustc_interface::borrowck::consumers::BodyWithBorrowckFacts;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::middle::ty;

thread_local! {
    pub static SHARED_STATE:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

/// # Safety
///
/// See the module level comment.
pub(crate) unsafe fn store_mir_body<'tcx>(
    _tcx: ty::TyCtxt<'tcx>,
    def_id: LocalDefId,
    body_with_facts: BodyWithBorrowckFacts<'tcx>,
) {
    // SAFETY: See the module level comment.
    let body_with_facts: BodyWithBorrowckFacts<'static> = unsafe { mem::transmute(body_with_facts) };
    SHARED_STATE.with(|state| {
        let mut map = state.borrow_mut();
        assert!(map.insert(def_id, body_with_facts).is_none());
    });
}

/// # Safety
///
/// See the module level comment.
pub(crate) unsafe fn retrieve_mir_body<'tcx>(
    _tcx: ty::TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<BodyWithBorrowckFacts<'tcx>> {
    let body_with_facts: Option<BodyWithBorrowckFacts<'static>> = SHARED_STATE.with(|state| {
        let mut map = state.borrow_mut();
        map.remove(&def_id)
    });
    // SAFETY: See the module level comment.
    unsafe { mem::transmute(body_with_facts) }
}
