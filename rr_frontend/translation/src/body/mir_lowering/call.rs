// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use radium::specs;
use rr_rustc_interface::middle::ty;

pub(crate) struct ProcedureInst<'tcx, 'def> {
    pub method_params: ty::GenericArgsRef<'tcx>,
    pub type_hint: Vec<specs::Type<'def>>,
    pub lft_hint: Vec<specs::Lft>,
    pub num_of_latebounds: usize,
    pub mapped_early_regions: BTreeMap<specs::Lft, usize>,
}
