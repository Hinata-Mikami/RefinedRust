// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Align locations from `mir_drops_elaborated_and_const_checked` back to the
//! borrow-checked MIR. Body translation traverses dropck MIR, but Polonius facts
//! and region-sensitive types are keyed by borrowck MIR locations. This mapper
//! provides the bridge from target/dropck locations and points back to their
//! source/borrowck counterparts.
//!
//! The mapper is intentionally conservative. It handles cleanup post-borrowck
//! rewrites, synthetic locals introduced by drop elaboration and box-deref
//! elaboration, dead drops, and the common conditional-drop rewrite. Unknown
//! target locations stay unmapped instead of being guessed.
//!
//! # Box deref aliases
//!
//! Dropck MIR can lower a borrowck-level `Box` dereference into a synthetic raw
//! pointer local:
//!
//! ```text
//! // borrowck MIR
//! _dst = copy (*_box)
//!
//! // dropck MIR
//! _alias = copy ((_box.0).0) as *const T (Transmute)
//! _dst = copy (*_alias)
//! ```
//!
//! `observe_inserted_stmt` recognizes these alias initializers structurally and
//! records a [`BoxDerefAlias`]. The mapper then normalizes later `*_alias` uses
//! when comparing target statements/terminators with borrowck MIR, and exposes
//! the alias through [`MappingResult`] so body translation can skip the
//! administrative alias local and translate `*_alias` as the original `*_box`.
//!
//! Alias initializer statements may also be basic-block entry points. Since
//! annotation generation queries start points for successor blocks, `finish`
//! assigns such inserted alias initializers a point mapping to the next real
//! mapped source location in the same block.

mod equiv;
mod format;
mod mapper;
mod result;
mod types;
mod util;

pub use format::{format_inserted_terminator_point_mappings, format_mapping};
pub use result::{BoxDerefAlias, MappingResult, Origin, SourceLoc, SyntheticDropBorrow, TargetLoc};
pub(crate) use result::{SourcePoint, TargetPoint};
use rr_rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::{self, BasicBlock, Body, Local};
use rr_rustc_interface::middle::ty;
use types::*;

#[must_use]
pub fn map_drop_elaborated_to_borrow_checked<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    bc: &Body<'tcx>,
    de: &Body<'tcx>,
) -> MappingResult {
    let mut cx = Mapper::new(tcx, bc, de);
    cx.align_blocks(mir::START_BLOCK, mir::START_BLOCK);
    cx.finish()
}

struct Mapper<'a, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    bc: &'a Body<'tcx>,
    de: &'a Body<'tcx>,
    drop_drop_did: Option<DefId>,
    discriminant_value_did: Option<DefId>,
    source_local_count: usize,
    target_to_source: FxHashMap<TargetLoc, Origin>,
    target_point_phases: FxHashMap<TargetLoc, PointPhase>,
    visited: FxHashSet<(BasicBlock, BasicBlock)>,
    box_deref_aliases: FxHashMap<Local, InternalBoxDerefAlias>,
    synthetic_drop_borrows: FxHashMap<Local, SyntheticDropBorrow>,
    copy_aliases: FxHashMap<Local, NormalizedPlace>,
    bc_predecessors: FxHashMap<BasicBlock, Vec<BasicBlock>>,
}
