// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rr_rustc_interface::data_structures::fx::FxHashSet;
use rr_rustc_interface::middle::mir;

/// A set of MIR places.
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub(crate) struct PlaceSet<'tcx> {
    places: FxHashSet<mir::Place<'tcx>>,
}

impl<'tcx> PlaceSet<'tcx> {
    #[must_use]
    pub(crate) fn contains(&self, place: mir::Place<'tcx>) -> bool {
        self.places.contains(&place)
    }
}

impl<'tcx> From<FxHashSet<mir::Place<'tcx>>> for PlaceSet<'tcx> {
    fn from(places: FxHashSet<mir::Place<'tcx>>) -> Self {
        Self { places }
    }
}
