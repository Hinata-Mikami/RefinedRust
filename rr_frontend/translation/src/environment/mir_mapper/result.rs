// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use rr_rustc_interface::data_structures::fx::FxHashMap;
use rr_rustc_interface::middle::mir::{self, BasicBlock, Local};

use crate::environment::borrowck::facts;

pub type TargetLoc = (BasicBlock, usize);
pub type SourceLoc = (BasicBlock, usize);
pub(crate) type TargetPoint = (BasicBlock, usize, facts::PointType);
pub(crate) type SourcePoint = (BasicBlock, usize, facts::PointType);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Origin {
    Source(SourceLoc),
    Inserted,
    SplitFrom(SourceLoc),
    FoldedFrom(SourceLoc),
}

/// A synthetic dropck local that represents a lowered borrowck-level `Box` deref.
///
/// Drop elaboration can lower `*_box` to a raw-pointer alias, e.g.:
///
/// ```text
/// _alias = copy ((_box.0).0) as *mut T (Transmute)
/// *_alias
/// ```
///
/// The alias local should be treated as administrative MIR; uses through a
/// dereference correspond to the original borrowck-level `*_box` place.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct BoxDerefAlias {
    pub(super) alias_local: Local,
    pub(super) box_local: Local,
    pub(super) source_loc: Option<SourceLoc>,
}

/// A drop-elaborated borrow introduced to call `Drop::drop` explicitly.
///
/// Rustc can lower a borrowck `Drop(_box)` terminator to target MIR that first
/// creates a synthetic `&mut _box` local and then calls `<Box<_> as Drop>::drop`.
/// The synthetic borrow has erased regions in dropck MIR, so body translation
/// needs a dedicated hook instead of treating it like an ordinary borrowck loan.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct SyntheticDropBorrow {
    pub(super) synthetic_ref_local: Local,
    pub(super) borrow_loc: TargetLoc,
    pub(super) drop_call_loc: TargetLoc,
    pub(super) source_drop_loc: SourceLoc,
}

impl SyntheticDropBorrow {
    #[must_use]
    pub const fn synthetic_ref_local(self) -> Local {
        self.synthetic_ref_local
    }

    #[must_use]
    pub const fn borrow_loc(self) -> TargetLoc {
        self.borrow_loc
    }

    #[must_use]
    pub const fn drop_call_loc(self) -> TargetLoc {
        self.drop_call_loc
    }

    #[must_use]
    pub const fn source_drop_loc(self) -> SourceLoc {
        self.source_drop_loc
    }
}

impl BoxDerefAlias {
    #[must_use]
    pub const fn alias_local(self) -> Local {
        self.alias_local
    }

    #[must_use]
    pub const fn box_local(self) -> Local {
        self.box_local
    }

    #[must_use]
    pub const fn source_loc(self) -> Option<SourceLoc> {
        self.source_loc
    }
}

#[derive(Debug, Default)]
#[expect(clippy::partial_pub_fields, reason = "point mappings use crate-private Polonius fact types")]
pub struct MappingResult {
    pub target_to_source: FxHashMap<TargetLoc, Origin>,
    pub(crate) target_points_to_source: FxHashMap<TargetPoint, SourcePoint>,
    pub unmapped_targets: Vec<TargetLoc>,
    pub(super) box_deref_aliases: FxHashMap<Local, BoxDerefAlias>,
    pub(super) synthetic_drop_borrows_by_local: FxHashMap<Local, SyntheticDropBorrow>,
    pub(super) synthetic_drop_borrows_by_borrow_loc: FxHashMap<TargetLoc, SyntheticDropBorrow>,
    pub(super) synthetic_drop_borrows_by_drop_call_loc: FxHashMap<TargetLoc, SyntheticDropBorrow>,
}

impl MappingResult {
    #[must_use]
    pub fn origin_for_target(&self, target: TargetLoc) -> Option<Origin> {
        self.target_to_source.get(&target).copied()
    }

    /// Return the recorded `Box`-deref alias for a synthetic dropck local.
    ///
    /// The alias is only semantically meaningful when the local is used through
    /// a dereference. A plain use of the alias local is the administrative raw
    /// pointer value introduced by dropck.
    #[must_use]
    pub fn box_deref_alias_for(&self, local: Local) -> Option<BoxDerefAlias> {
        self.box_deref_aliases.get(&local).copied()
    }

    /// Check whether `local` is a synthetic dropck local that aliases `*Box<T>`.
    #[must_use]
    pub fn is_box_deref_alias(&self, local: Local) -> bool {
        self.box_deref_aliases.contains_key(&local)
    }

    /// Iterate over all synthetic dropck locals that alias borrowck-level `Box`
    /// dereferences.
    pub fn box_deref_aliases(&self) -> impl Iterator<Item = BoxDerefAlias> + '_ {
        self.box_deref_aliases.values().copied()
    }

    #[must_use]
    pub fn synthetic_drop_borrow_for_local(&self, local: Local) -> Option<SyntheticDropBorrow> {
        self.synthetic_drop_borrows_by_local.get(&local).copied()
    }

    #[must_use]
    pub fn synthetic_drop_borrow_for_borrow_loc(&self, loc: TargetLoc) -> Option<SyntheticDropBorrow> {
        self.synthetic_drop_borrows_by_borrow_loc.get(&loc).copied()
    }

    #[must_use]
    pub fn synthetic_drop_borrow_for_drop_call_loc(&self, loc: TargetLoc) -> Option<SyntheticDropBorrow> {
        self.synthetic_drop_borrows_by_drop_call_loc.get(&loc).copied()
    }

    #[must_use]
    pub(crate) fn source_point_for_target(&self, target: TargetPoint) -> Option<SourcePoint> {
        self.target_points_to_source.get(&target).copied()
    }

    #[must_use]
    pub(crate) fn source_point_for_target_loc(
        &self,
        target: TargetLoc,
        point_type: facts::PointType,
    ) -> Option<SourcePoint> {
        let (bb, idx) = target;
        self.source_point_for_target((bb, idx, point_type))
    }

    #[must_use]
    pub(crate) fn source_point_for_target_location(
        &self,
        target: mir::Location,
        point_type: facts::PointType,
    ) -> Option<facts::Point> {
        let (block, statement_index, typ) =
            self.source_point_for_target_loc((target.block, target.statement_index), point_type)?;
        Some(facts::Point {
            location: mir::Location {
                block,
                statement_index,
            },
            typ,
        })
    }
}
