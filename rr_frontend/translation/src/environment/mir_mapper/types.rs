// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use rr_rustc_interface::middle::mir::{BasicBlock, Local};

use super::SourceLoc;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(super) struct NormalizedPlace {
    pub(super) local: Local,
    pub(super) projection: Vec<NormalizedPlaceElem>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(super) enum NormalizedPlaceElem {
    Deref,
    Field(usize),
    Index(Local),
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    Downcast(usize),
    OpaqueCast,
    UnwrapUnsafeBinder,
}

#[derive(Clone)]
pub(super) struct InternalBoxDerefAlias {
    pub(super) place: NormalizedPlace,
    pub(super) source_loc: Option<SourceLoc>,
}

pub(super) struct OpenDropBlock {
    pub(super) bb: BasicBlock,
    pub(super) mark_statements: bool,
    pub(super) terminator_phase: PointPhaseKind,
}

pub(super) struct SourceDropCtx {
    pub(super) drop_bb: BasicBlock,
    pub(super) ret: BasicBlock,
    pub(super) unwind: Option<BasicBlock>,
}

pub(super) struct OpenDropMatch {
    pub(super) root_place: NormalizedPlace,
    pub(super) blocks: Vec<OpenDropBlock>,
    pub(super) normal_exits: Vec<BasicBlock>,
    pub(super) unwind_exits: Vec<BasicBlock>,
}

pub(super) enum OpenDropNode {
    LinearGoto {
        target: BasicBlock,
    },
    Dispatch {
        observed_place: Option<NormalizedPlace>,
        targets: Vec<BasicBlock>,
    },
    DropStep {
        place: NormalizedPlace,
        target: BasicBlock,
        unwind: Option<BasicBlock>,
    },
    Unsupported,
}

#[derive(Clone, Copy)]
pub(super) enum PointPhase {
    Direct(SourceLoc),
    PreEffect(SourceLoc),
    PostEffect(SourceLoc),
}

#[derive(Clone, Copy)]
pub(super) enum PointPhaseKind {
    Direct,
    PreEffect,
}

#[derive(Clone, Copy)]
pub(super) enum MirFlavor {
    Source,
    Target,
}

impl PointPhaseKind {
    /// Attach a concrete source location to this phase kind.
    pub(super) const fn with_source(self, source: SourceLoc) -> PointPhase {
        match self {
            Self::Direct => PointPhase::Direct(source),
            Self::PreEffect => PointPhase::PreEffect(source),
        }
    }
}

/// Convert an origin into the default point phase used for direct mappings.
pub(super) const fn point_phase_from_origin(origin: super::Origin) -> Option<PointPhase> {
    match origin {
        super::Origin::Source(source)
        | super::Origin::FoldedFrom(source)
        | super::Origin::SplitFrom(source) => Some(PointPhase::Direct(source)),
        super::Origin::Inserted => None,
    }
}

/// Extract the source location carried by an origin, if any.
pub(super) const fn origin_source_loc(origin: super::Origin) -> Option<SourceLoc> {
    match origin {
        super::Origin::Source(source)
        | super::Origin::FoldedFrom(source)
        | super::Origin::SplitFrom(source) => Some(source),
        super::Origin::Inserted => None,
    }
}

/// Check whether `candidate` is the same place as `base` or below it.
pub(super) fn same_or_subplace(base: &NormalizedPlace, candidate: &NormalizedPlace) -> bool {
    base.local == candidate.local
        && candidate.projection.len() >= base.projection.len()
        && candidate.projection.starts_with(&base.projection)
}
