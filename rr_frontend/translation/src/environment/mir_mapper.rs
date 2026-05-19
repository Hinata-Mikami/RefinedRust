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

#![allow(dead_code)]

use std::collections::VecDeque;

use rr_rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::{self, BasicBlock, Body, Local};
use rr_rustc_interface::middle::ty;

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
    alias_local: Local,
    box_local: Local,
    source_loc: Option<SourceLoc>,
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
    box_deref_aliases: FxHashMap<Local, BoxDerefAlias>,
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

#[must_use]
pub fn map_drop_elaborated_to_borrow_checked<'tcx>(bc: &Body<'tcx>, de: &Body<'tcx>) -> MappingResult {
    let mut cx = Mapper::new(bc, de);
    cx.align_blocks(mir::START_BLOCK, mir::START_BLOCK);
    cx.finish()
}

#[must_use]
pub fn format_mapping<'tcx>(bc: &Body<'tcx>, de: &Body<'tcx>, mapping: &MappingResult) -> String {
    let mut lines = Vec::new();
    let total = count_locations(de);
    lines.push(format!(
        "summary: total={} mapped={} unmapped={}",
        total,
        mapping.target_to_source.len(),
        mapping.unmapped_targets.len()
    ));
    lines.push(String::new());

    let mut locs: Vec<_> = mapping.target_to_source.iter().collect();
    locs.sort_by_key(|((bb, idx), _)| (bb.as_u32(), *idx));
    for ((bb_t, idx_t), origin) in locs {
        lines.push(format!(
            "{:?}[{}] {} -> {}",
            bb_t,
            idx_t,
            describe_location(de, *bb_t, *idx_t),
            format_origin(bc, *origin)
        ));
    }

    if !mapping.unmapped_targets.is_empty() {
        lines.push(String::new());
        lines.push("Unmapped:".to_owned());
        let mut unmapped = mapping.unmapped_targets.clone();
        unmapped.sort_by_key(|(bb, idx)| (bb.as_u32(), *idx));
        for (bb, idx) in unmapped {
            lines.push(format!("{:?}[{}] {}", bb, idx, describe_location(de, bb, idx)));
        }
    }

    let mut aliases = mapping.box_deref_aliases().collect::<Vec<_>>();
    aliases.sort_by_key(|alias| alias.alias_local().as_usize());
    if !aliases.is_empty() {
        lines.push(String::new());
        lines.push("Box deref aliases:".to_owned());
        for alias in aliases {
            let source =
                alias.source_loc().map_or_else(|| "none".to_owned(), |(bb, idx)| format!("{bb:?}[{idx}]"));
            lines.push(format!(
                "{:?} aliases *{:?} (source: {source})",
                alias.alias_local(),
                alias.box_local()
            ));
        }
    }

    lines.join("\n")
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct NormalizedPlace {
    local: Local,
    projection: Vec<NormalizedPlaceElem>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum NormalizedPlaceElem {
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

struct Mapper<'a, 'tcx> {
    bc: &'a Body<'tcx>,
    de: &'a Body<'tcx>,
    source_local_count: usize,
    target_to_source: FxHashMap<TargetLoc, Origin>,
    target_point_phases: FxHashMap<TargetLoc, PointPhase>,
    visited: FxHashSet<(BasicBlock, BasicBlock)>,
    box_deref_aliases: FxHashMap<Local, InternalBoxDerefAlias>,
    bc_predecessors: FxHashMap<BasicBlock, Vec<BasicBlock>>,
}

#[derive(Clone)]
struct InternalBoxDerefAlias {
    place: NormalizedPlace,
    source_loc: Option<SourceLoc>,
}

struct OpenDropBlock {
    bb: BasicBlock,
    mark_statements: bool,
    terminator_phase: PointPhaseKind,
}

struct SourceDropCtx {
    drop_bb: BasicBlock,
    place: NormalizedPlace,
    ret: BasicBlock,
    unwind: Option<BasicBlock>,
}

struct OpenDropMatch {
    root_place: NormalizedPlace,
    blocks: Vec<OpenDropBlock>,
    normal_exits: Vec<BasicBlock>,
    unwind_exits: Vec<BasicBlock>,
}

enum OpenDropNode {
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
enum PointPhase {
    Direct(SourceLoc),
    PreEffect(SourceLoc),
    PostEffect(SourceLoc),
}

#[derive(Clone, Copy)]
enum PointPhaseKind {
    Direct,
    PreEffect,
    PostEffect,
}

impl<'a, 'tcx> Mapper<'a, 'tcx> {
    fn new(bc: &'a Body<'tcx>, de: &'a Body<'tcx>) -> Self {
        Self {
            bc,
            de,
            source_local_count: bc.local_decls.len(),
            target_to_source: FxHashMap::default(),
            target_point_phases: FxHashMap::default(),
            visited: FxHashSet::default(),
            box_deref_aliases: FxHashMap::default(),
            bc_predecessors: compute_predecessors(bc),
        }
    }

    fn finish(self) -> MappingResult {
        let mut unmapped_targets = Vec::new();
        for (bb, data) in self.de.basic_blocks.iter_enumerated() {
            for idx in 0..=data.statements.len() {
                if !self.target_to_source.contains_key(&(bb, idx)) {
                    unmapped_targets.push((bb, idx));
                }
            }
        }

        // Inserted statements may still be translated or used as successor
        // starts. When they precede a mapped source statement in the same
        // block, treat them as happening before that source statement for
        // Polonius point queries.
        let mut target_point_phases = self.target_point_phases.clone();
        let mut target_to_source_entries: Vec<_> = self.target_to_source.iter().collect();
        target_to_source_entries.sort_by_key(|((bb, idx), _)| (bb.as_u32(), *idx));
        for ((bb, idx), origin) in target_to_source_entries {
            if *origin == Origin::Inserted
                && let Some(source) = self.next_mapped_source_after(*bb, *idx)
            {
                target_point_phases.insert((*bb, *idx), PointPhase::PreEffect(source));
            }
        }

        let mut target_points_to_source = FxHashMap::default();
        let mut target_to_source: Vec<_> = self.target_to_source.iter().collect();
        target_to_source.sort_by_key(|((bb, idx), _)| (bb.as_u32(), *idx));
        for (target, origin) in target_to_source {
            let Some(phase) = point_phase_from_origin(*origin) else {
                continue;
            };
            insert_point_mapping(&mut target_points_to_source, *target, phase);
        }
        let mut target_point_phases: Vec<_> = target_point_phases.iter().collect();
        target_point_phases.sort_by_key(|((bb, idx), _)| (bb.as_u32(), *idx));
        for (target, phase) in target_point_phases {
            insert_point_mapping(&mut target_points_to_source, *target, *phase);
        }

        let box_deref_aliases = self
            .box_deref_aliases
            .iter()
            .map(|(alias_local, alias)| {
                (*alias_local, BoxDerefAlias {
                    alias_local: *alias_local,
                    box_local: alias.place.local,
                    source_loc: alias.source_loc,
                })
            })
            .collect();

        MappingResult {
            target_to_source: self.target_to_source,
            target_points_to_source,
            unmapped_targets,
            box_deref_aliases,
        }
    }

    /// Find the source location of the next mapped target location in the same block.
    ///
    /// This is only used for inserted statements. Mapping them to the next real
    /// source point makes statement and successor-start Polonius queries land
    /// before the next semantic source statement in the block.
    fn next_mapped_source_after(&self, bb: BasicBlock, idx: usize) -> Option<SourceLoc> {
        let statements_len = self.de.basic_blocks[bb].statements.len();
        for next_idx in (idx + 1)..=statements_len {
            match self.target_to_source.get(&(bb, next_idx)).copied()? {
                Origin::Source(source) | Origin::FoldedFrom(source) | Origin::SplitFrom(source) => {
                    return Some(source);
                },
                Origin::Inserted => {},
            }
        }
        None
    }

    fn align_blocks(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) {
        if !self.visited.insert((bb_t, bb_s)) {
            return;
        }

        self.align_statements(bb_t, bb_s);
        self.align_terminator(bb_t, bb_s);
    }

    fn align_statements(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) {
        let data_t = &self.de.basic_blocks[bb_t];
        let data_s = &self.bc.basic_blocks[bb_s];

        let mut i_t = 0;
        let mut i_s = 0;

        while i_t < data_t.statements.len() {
            let st = &data_t.statements[i_t];

            if self.is_inserted_stmt(st) {
                let source_loc = (i_s < data_s.statements.len()).then_some((bb_s, i_s));
                let origin = self.observe_inserted_stmt(st, source_loc).unwrap_or(Origin::Inserted);
                self.target_to_source.insert((bb_t, i_t), origin);
                i_t += 1;
                continue;
            }

            while i_s < data_s.statements.len()
                && Self::is_cleanup_erased_source_stmt(&data_s.statements[i_s])
            {
                if matches!(st.kind, mir::StatementKind::Nop) {
                    self.target_to_source.insert((bb_t, i_t), Origin::Source((bb_s, i_s)));
                    i_t += 1;
                }
                i_s += 1;
                if i_t >= data_t.statements.len() {
                    break;
                }
            }

            if i_t >= data_t.statements.len() {
                break;
            }

            if i_s < data_s.statements.len()
                && self.stmt_equiv(&data_t.statements[i_t], &data_s.statements[i_s])
            {
                let source_loc = (bb_s, i_s);
                let origin = if self.stmt_uses_box_deref_alias(&data_t.statements[i_t], source_loc) {
                    Origin::SplitFrom(source_loc)
                } else {
                    Origin::Source(source_loc)
                };
                self.target_to_source.insert((bb_t, i_t), origin);
                i_t += 1;
                i_s += 1;
                continue;
            }

            if let Some(source_loc) = self.try_match_folded_source_stmt(&data_t.statements[i_t], bb_s, i_s) {
                self.target_to_source.insert((bb_t, i_t), Origin::FoldedFrom(source_loc));
                i_t += 1;
                continue;
            }

            break;
        }

        while i_t < data_t.statements.len() {
            let st = &data_t.statements[i_t];
            if self.is_inserted_stmt(st) {
                let source_loc = (i_s < data_s.statements.len()).then_some((bb_s, i_s));
                let origin = self.observe_inserted_stmt(st, source_loc).unwrap_or(Origin::Inserted);
                self.target_to_source.insert((bb_t, i_t), origin);
            } else if let Some(source_loc) = self.try_match_folded_source_stmt(st, bb_s, i_s) {
                self.target_to_source.insert((bb_t, i_t), Origin::FoldedFrom(source_loc));
            } else {
                self.target_to_source.insert((bb_t, i_t), Origin::Inserted);
            }
            i_t += 1;
        }
    }

    fn align_terminator(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) {
        let dt = &self.de.basic_blocks[bb_t];
        let ds = &self.bc.basic_blocks[bb_s];

        let tt = dt.terminator();
        let ts = ds.terminator();
        let loc_t = (bb_t, dt.statements.len());

        if self.terminator_shape_equiv(tt, ts) {
            self.target_to_source.insert(loc_t, Origin::Source((bb_s, ds.statements.len())));
            self.recurse_direct(tt, ts);
            return;
        }

        if self.try_align_folded_source_terminator(bb_t, bb_s) {
            return;
        }

        if self.try_align_rewritten_drop(bb_t, bb_s) {
            return;
        }

        if self.try_align_open_drop_subgraph(bb_t, bb_s) {
            return;
        }

        if self.try_align_eliminated_source_drop(bb_t, bb_s) {
            return;
        }

        if self.try_align_eliminated_cleanup_call(bb_t, bb_s) {
            return;
        }

        if self.try_align_diverging_call(bb_t, bb_s) {
            return;
        }

        self.target_to_source.insert(loc_t, Origin::Inserted);
    }

    fn recurse_direct(&mut self, tt: &mir::Terminator<'tcx>, ts: &mir::Terminator<'tcx>) {
        match (&tt.kind, &ts.kind) {
            (
                mir::TerminatorKind::Goto { target: target_t },
                mir::TerminatorKind::Goto { target: target_s }
                | mir::TerminatorKind::FalseEdge {
                    real_target: target_s,
                    ..
                }
                | mir::TerminatorKind::FalseUnwind {
                    real_target: target_s,
                    ..
                },
            )
            | (
                mir::TerminatorKind::FalseEdge {
                    real_target: target_t,
                    ..
                }
                | mir::TerminatorKind::FalseUnwind {
                    real_target: target_t,
                    ..
                },
                mir::TerminatorKind::Goto { target: target_s },
            ) => self.align_blocks(*target_t, *target_s),

            (
                mir::TerminatorKind::SwitchInt {
                    targets: targets_t, ..
                },
                mir::TerminatorKind::SwitchInt {
                    targets: targets_s, ..
                },
            ) => {
                for (bb_t, bb_s) in targets_t.all_targets().iter().zip(targets_s.all_targets().iter()) {
                    self.align_blocks(*bb_t, *bb_s);
                }
            },

            (
                mir::TerminatorKind::Assert {
                    target: target_t,
                    unwind: unwind_t,
                    ..
                }
                | mir::TerminatorKind::Drop {
                    target: target_t,
                    unwind: unwind_t,
                    ..
                },
                mir::TerminatorKind::Assert {
                    target: target_s,
                    unwind: unwind_s,
                    ..
                }
                | mir::TerminatorKind::Drop {
                    target: target_s,
                    unwind: unwind_s,
                    ..
                },
            ) => {
                self.align_blocks(*target_t, *target_s);
                if let (Some(bb_t), Some(bb_s)) = (unwind_target(*unwind_t), unwind_target(*unwind_s)) {
                    self.align_blocks(bb_t, bb_s);
                }
            },

            (
                mir::TerminatorKind::Call {
                    target: target_t,
                    unwind: unwind_t,
                    ..
                },
                mir::TerminatorKind::Call {
                    target: target_s,
                    unwind: unwind_s,
                    ..
                },
            ) => {
                if let (Some(bb_t), Some(bb_s)) = (*target_t, *target_s) {
                    self.align_blocks(bb_t, bb_s);
                }
                if let (Some(bb_t), Some(bb_s)) = (unwind_target(*unwind_t), unwind_target(*unwind_s)) {
                    self.align_blocks(bb_t, bb_s);
                }
            },

            _ => {},
        }
    }

    fn try_align_rewritten_drop(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let ts = self.bc.basic_blocks[bb_s].terminator();
        let Some(source_place) = self.source_drop_place(ts) else {
            return false;
        };

        let tt = self.de.basic_blocks[bb_t].terminator();
        let Some((a, b)) = self.parse_flag_test(tt) else {
            return false;
        };

        let Some(drop_bb) = self.find_actual_drop_block(a, b, &source_place) else {
            return false;
        };
        let skip_bb = if drop_bb == a { b } else { a };

        let src_drop = (bb_s, self.bc.basic_blocks[bb_s].statements.len());
        let flag_test_loc = (bb_t, self.de.basic_blocks[bb_t].statements.len());
        self.target_to_source.insert(flag_test_loc, Origin::SplitFrom(src_drop));
        self.target_point_phases.insert(flag_test_loc, PointPhase::PreEffect(src_drop));

        let drop_data = &self.de.basic_blocks[drop_bb];
        for i in 0..drop_data.statements.len() {
            self.target_to_source.entry((drop_bb, i)).or_insert(Origin::Inserted);
            self.target_point_phases.insert((drop_bb, i), PointPhase::PreEffect(src_drop));
        }
        let drop_loc = (drop_bb, drop_data.statements.len());
        self.target_to_source.insert(drop_loc, Origin::SplitFrom(src_drop));
        self.target_point_phases.insert(drop_loc, PointPhase::Direct(src_drop));

        if let mir::TerminatorKind::Drop {
            target: ret_s,
            unwind: unwind_s,
            ..
        } = ts.kind
            && let mir::TerminatorKind::Drop {
                target: ret_t,
                unwind: unwind_t,
                ..
            } = self.de.basic_blocks[drop_bb].terminator().kind
        {
            self.align_blocks(skip_bb, ret_s);
            self.align_blocks(ret_t, ret_s);

            if let (Some(bb_t), Some(bb_s)) = (unwind_target(unwind_t), unwind_target(unwind_s)) {
                self.align_blocks(bb_t, bb_s);
            }
            return true;
        }

        false
    }

    fn try_align_open_drop_subgraph(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let Some(open_drop_match) = self.match_open_drop_target(bb_t) else {
            return false;
        };

        let Some(source_drop) = self.find_source_drop_ctx(bb_s, &open_drop_match.root_place) else {
            return false;
        };

        if open_drop_match.normal_exits.is_empty() {
            return false;
        }
        if !open_drop_match.unwind_exits.is_empty() && source_drop.unwind.is_none() {
            return false;
        }

        let src_drop = (source_drop.drop_bb, self.bc.basic_blocks[source_drop.drop_bb].statements.len());
        for block in open_drop_match.blocks {
            if block.mark_statements {
                let data = &self.de.basic_blocks[block.bb];
                for i in 0..data.statements.len() {
                    self.target_to_source.insert((block.bb, i), Origin::SplitFrom(src_drop));
                    self.target_point_phases.insert((block.bb, i), PointPhase::PreEffect(src_drop));
                }
            }

            let loc_t = (block.bb, self.de.basic_blocks[block.bb].statements.len());
            self.target_to_source.insert(loc_t, Origin::SplitFrom(src_drop));
            self.target_point_phases.insert(loc_t, block.terminator_phase.with_source(src_drop));
        }

        for exit_t in open_drop_match.normal_exits {
            self.align_blocks(exit_t, source_drop.ret);
        }
        for exit_t in open_drop_match.unwind_exits {
            if let Some(unwind_s) = source_drop.unwind {
                self.align_blocks(exit_t, unwind_s);
            }
        }

        true
    }

    fn try_align_folded_source_terminator(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let tt = self.de.basic_blocks[bb_t].terminator();
        let loc_t = (bb_t, self.de.basic_blocks[bb_t].statements.len());
        let mut cur_s = bb_s;

        for _ in 0..self.bc.basic_blocks.len() {
            let ds = &self.bc.basic_blocks[cur_s];
            let ts = ds.terminator();
            if self.terminator_shape_equiv(tt, ts) {
                let origin = if cur_s == bb_s {
                    Origin::Source((cur_s, ds.statements.len()))
                } else {
                    Origin::FoldedFrom((cur_s, ds.statements.len()))
                };
                self.target_to_source.insert(loc_t, origin);
                self.recurse_direct(tt, ts);
                return true;
            }

            let next_s = match &ts.kind {
                mir::TerminatorKind::Goto { target }
                | mir::TerminatorKind::FalseEdge {
                    real_target: target,
                    ..
                }
                | mir::TerminatorKind::FalseUnwind {
                    real_target: target,
                    ..
                } => *target,
                _ => return false,
            };

            let next_ts = self.bc.basic_blocks[next_s].terminator();
            if self.terminator_shape_equiv(tt, next_ts) {
                cur_s = next_s;
                continue;
            }

            if self.bc_predecessors.get(&next_s).map_or(0, Vec::len) != 1 {
                return false;
            }

            cur_s = next_s;
        }

        false
    }

    fn match_open_drop_target(&self, entry_bb: BasicBlock) -> Option<OpenDropMatch> {
        // Open-drop matching is intentionally conservative:
        // - interior blocks may only contain administrative statements,
        // - dispatch/drop places must stay anchored under one discovered root place,
        // - exits are only allowed once the subgraph leaves this protocol.
        let mut seen = FxHashSet::default();
        let mut queue = VecDeque::from([(entry_bb, true)]);
        let mut root_place = None;
        let mut blocks = Vec::new();
        let mut normal_exits = Vec::new();
        let mut unwind_exits = Vec::new();

        while let Some((bb, allow_existing_statements)) = queue.pop_front() {
            if !seen.insert((bb, allow_existing_statements)) {
                continue;
            }

            match self.classify_open_drop_node(bb, allow_existing_statements) {
                OpenDropNode::LinearGoto { target } => {
                    if !self.is_open_drop_block(target, root_place.as_ref()) {
                        return None;
                    }
                    blocks.push(OpenDropBlock {
                        bb,
                        mark_statements: self.block_has_only_open_drop_administrative_statements(bb),
                        terminator_phase: PointPhaseKind::PreEffect,
                    });
                    queue.push_back((target, false));
                },
                OpenDropNode::Dispatch {
                    observed_place,
                    targets,
                } => {
                    if let Some(place) = observed_place.as_ref() {
                        if !Self::update_open_drop_root_place(&mut root_place, place) {
                            return None;
                        }
                    } else if root_place.is_none() {
                        return None;
                    }

                    blocks.push(OpenDropBlock {
                        bb,
                        mark_statements: self.block_has_only_open_drop_administrative_statements(bb),
                        terminator_phase: PointPhaseKind::PreEffect,
                    });
                    for target in targets {
                        if !self.is_open_drop_block(target, root_place.as_ref()) {
                            return None;
                        }
                        queue.push_back((target, false));
                    }
                },
                OpenDropNode::DropStep {
                    place,
                    target,
                    unwind,
                } => {
                    if !Self::update_open_drop_root_place(&mut root_place, &place) {
                        return None;
                    }

                    blocks.push(OpenDropBlock {
                        bb,
                        mark_statements: self.block_has_only_open_drop_administrative_statements(bb),
                        terminator_phase: PointPhaseKind::Direct,
                    });

                    if self.is_open_drop_block(target, root_place.as_ref()) {
                        queue.push_back((target, false));
                    } else {
                        normal_exits.push(target);
                    }

                    if let Some(unwind) = unwind {
                        if self.is_open_drop_block(unwind, root_place.as_ref()) {
                            queue.push_back((unwind, false));
                        } else {
                            unwind_exits.push(unwind);
                        }
                    }
                },
                OpenDropNode::Unsupported => return None,
            }
        }

        Some(OpenDropMatch {
            root_place: root_place?,
            blocks,
            normal_exits,
            unwind_exits,
        })
    }

    fn find_source_drop_ctx(
        &self,
        start_bb: BasicBlock,
        target_root_place: &NormalizedPlace,
    ) -> Option<SourceDropCtx> {
        let mut current = start_bb;

        for _ in 0..self.bc.basic_blocks.len() {
            let term = self.bc.basic_blocks[current].terminator();
            let next = match &term.kind {
                mir::TerminatorKind::Drop {
                    place,
                    target,
                    unwind,
                    ..
                } => {
                    let source_place = Self::normalize_source_place(*place);
                    if same_or_subplace(&source_place, target_root_place) {
                        return Some(SourceDropCtx {
                            drop_bb: current,
                            place: source_place,
                            ret: *target,
                            unwind: unwind_target(*unwind),
                        });
                    }
                    *target
                },
                mir::TerminatorKind::Goto { target }
                | mir::TerminatorKind::FalseEdge {
                    real_target: target,
                    ..
                }
                | mir::TerminatorKind::FalseUnwind {
                    real_target: target,
                    ..
                } => *target,
                _ => return None,
            };

            if self.bc_predecessors.get(&next).map_or(0, Vec::len) != 1 {
                let next_term = self.bc.basic_blocks[next].terminator();
                if let mir::TerminatorKind::Drop { place, .. } = &next_term.kind {
                    let source_place = Self::normalize_source_place(*place);
                    if same_or_subplace(&source_place, target_root_place) {
                        current = next;
                        continue;
                    }
                }
                return None;
            }

            current = next;
        }

        None
    }

    fn classify_open_drop_node(&self, bb: BasicBlock, allow_existing_statements: bool) -> OpenDropNode {
        let data = &self.de.basic_blocks[bb];
        if !allow_existing_statements && !self.block_has_only_open_drop_administrative_statements(bb) {
            return OpenDropNode::Unsupported;
        }

        match &data.terminator().kind {
            mir::TerminatorKind::Goto { target } => OpenDropNode::LinearGoto { target: *target },
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let local = match discr {
                    mir::Operand::Copy(place) | mir::Operand::Move(place)
                        if place.projection.is_empty() && self.is_synthetic_local(place.local) =>
                    {
                        place.local
                    },
                    _ => return OpenDropNode::Unsupported,
                };

                OpenDropNode::Dispatch {
                    observed_place: self.discriminant_input_place(&data.statements, local),
                    targets: targets.all_targets().to_vec(),
                }
            },
            mir::TerminatorKind::Drop {
                place,
                target,
                unwind,
                ..
            } => OpenDropNode::DropStep {
                place: self.normalize_place(*place),
                target: *target,
                unwind: unwind_target(*unwind),
            },
            _ => OpenDropNode::Unsupported,
        }
    }

    fn discriminant_input_place(
        &self,
        statements: &[mir::Statement<'tcx>],
        local: Local,
    ) -> Option<NormalizedPlace> {
        statements.iter().rev().find_map(|stmt| {
            let mir::StatementKind::Assign(box (lhs, mir::Rvalue::Discriminant(place))) = &stmt.kind else {
                return None;
            };
            (lhs.projection.is_empty() && lhs.local == local).then(|| self.normalize_place(*place))
        })
    }

    fn is_open_drop_block(&self, bb: BasicBlock, root_place: Option<&NormalizedPlace>) -> bool {
        match self.classify_open_drop_node(bb, false) {
            OpenDropNode::LinearGoto { .. } => true,
            OpenDropNode::Dispatch { observed_place, .. } => match observed_place.as_ref() {
                Some(place) => root_place.is_none_or(|root_place| same_or_subplace(root_place, place)),
                None => root_place.is_some(),
            },
            OpenDropNode::DropStep { place, .. } => {
                root_place.is_none_or(|root_place| same_or_subplace(root_place, &place))
            },
            OpenDropNode::Unsupported => false,
        }
    }

    fn update_open_drop_root_place(
        root_place: &mut Option<NormalizedPlace>,
        place: &NormalizedPlace,
    ) -> bool {
        if let Some(root_place) = root_place {
            same_or_subplace(root_place, place)
        } else {
            *root_place = Some(place.clone());
            true
        }
    }

    fn is_open_drop_administrative_stmt(&self, stmt: &mir::Statement<'tcx>) -> bool {
        matches!(stmt.kind, mir::StatementKind::Nop) || self.is_inserted_stmt(stmt)
    }

    fn block_has_only_open_drop_administrative_statements(&self, bb: BasicBlock) -> bool {
        self.de.basic_blocks[bb]
            .statements
            .iter()
            .all(|stmt| self.is_open_drop_administrative_stmt(stmt))
    }

    fn try_align_eliminated_source_drop(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let tt = self.de.basic_blocks[bb_t].terminator();
        let loc_t = (bb_t, self.de.basic_blocks[bb_t].statements.len());
        let mut cur_s = bb_s;

        for _ in 0..self.bc.basic_blocks.len() {
            let ds = &self.bc.basic_blocks[cur_s];
            let ts = ds.terminator();

            if self.terminator_shape_equiv(tt, ts) {
                let origin = if cur_s == bb_s {
                    Origin::Source((cur_s, ds.statements.len()))
                } else {
                    Origin::FoldedFrom((cur_s, ds.statements.len()))
                };
                self.target_to_source.insert(loc_t, origin);
                self.recurse_direct(tt, ts);
                return true;
            }

            let mir::TerminatorKind::Drop { target: next_s, .. } = ts.kind else {
                return false;
            };

            if self.bc_predecessors.get(&next_s).map_or(0, Vec::len) != 1 {
                return false;
            }

            cur_s = next_s;
        }

        false
    }

    fn parse_flag_test(&self, term: &mir::Terminator<'tcx>) -> Option<(BasicBlock, BasicBlock)> {
        let mir::TerminatorKind::SwitchInt { discr, targets } = &term.kind else {
            return None;
        };

        match discr {
            mir::Operand::Copy(place) | mir::Operand::Move(place)
                if place.projection.is_empty() && self.is_synthetic_bool_local(place.local) => {},
            _ => return None,
        }

        let all_targets = targets.all_targets();
        if all_targets.len() != 2 {
            return None;
        }

        Some((all_targets[0], all_targets[1]))
    }

    fn find_actual_drop_block(
        &self,
        a: BasicBlock,
        b: BasicBlock,
        source_place: &NormalizedPlace,
    ) -> Option<BasicBlock> {
        let a_is_drop = self.is_drop_block_for_place(a, source_place);
        let b_is_drop = self.is_drop_block_for_place(b, source_place);

        match (a_is_drop, b_is_drop) {
            (true, false) => Some(a),
            (false, true) => Some(b),
            _ => None,
        }
    }

    fn is_drop_block_for_place(&self, bb: BasicBlock, source_place: &NormalizedPlace) -> bool {
        let term = self.de.basic_blocks[bb].terminator();
        let mir::TerminatorKind::Drop { place, .. } = &term.kind else {
            return false;
        };

        let target_place = self.normalize_place(*place);
        same_or_subplace(source_place, &target_place)
    }

    fn source_drop_place(&self, term: &mir::Terminator<'tcx>) -> Option<NormalizedPlace> {
        match &term.kind {
            mir::TerminatorKind::Drop { place, .. } => Some(self.normalize_place(*place)),
            _ => None,
        }
    }

    fn try_match_folded_source_stmt(
        &self,
        target_stmt: &mir::Statement<'tcx>,
        bb_s: BasicBlock,
        i_s: usize,
    ) -> Option<SourceLoc> {
        let mut bb = bb_s;
        let mut idx = i_s;

        for _ in 0..self.bc.basic_blocks.len() {
            let data = &self.bc.basic_blocks[bb];
            while idx < data.statements.len() {
                let loc = (bb, idx);
                let stmt = &data.statements[idx];
                if !Self::is_cleanup_erased_source_stmt(stmt) && self.stmt_equiv(target_stmt, stmt) {
                    return Some(loc);
                }
                idx += 1;
            }

            let next_bb = self.single_linear_successor(bb)?;
            bb = next_bb;
            idx = 0;
        }

        None
    }

    fn single_linear_successor(&self, bb: BasicBlock) -> Option<BasicBlock> {
        let succ = normal_successor(self.bc.basic_blocks[bb].terminator())?;
        (self.bc_predecessors.get(&succ)?.len() == 1).then_some(succ)
    }

    /// Match calls whose borrowck cleanup edge was erased by drop elaboration.
    ///
    /// Borrowck MIR can contain calls such as:
    ///
    /// ```text
    /// bb_t: _x = f(...) -> [return: bb_ret, unwind: bb_cleanup]
    /// bb_cleanup: resume
    /// ```
    ///
    /// In dropck MIR, if the cleanup block only resumes and no destructors need
    /// to run on that path, rustc rewrites the same call to:
    ///
    /// ```text
    /// bb_t: _x = f(...) -> [return: bb_ret, unwind continue]
    /// ```
    ///
    /// The call still corresponds to the borrowck call terminator, so map its
    /// points to the source call instead of treating it as inserted target MIR.
    fn try_align_eliminated_cleanup_call(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let dt = &self.de.basic_blocks[bb_t];
        let ds = &self.bc.basic_blocks[bb_s];
        let tt = dt.terminator();
        let ts = ds.terminator();

        let (
            mir::TerminatorKind::Call {
                args: args_t,
                destination: dest_t,
                target: target_t,
                unwind: unwind_t,
                ..
            },
            mir::TerminatorKind::Call {
                args: args_s,
                destination: dest_s,
                target: target_s,
                unwind: unwind_s,
                ..
            },
        ) = (&tt.kind, &ts.kind)
        else {
            return false;
        };

        let Some(unwind_s) = unwind_target(*unwind_s) else {
            return false;
        };

        if unwind_target(*unwind_t).is_some() || !self.is_unwind_resume_block(unwind_s) {
            return false;
        }

        if target_t.is_some() != target_s.is_some()
            || !self.place_equiv(*dest_t, *dest_s)
            || args_t.len() != args_s.len()
        {
            return false;
        }

        self.target_to_source
            .insert((bb_t, dt.statements.len()), Origin::Source((bb_s, ds.statements.len())));

        if let (Some(target_t), Some(target_s)) = (*target_t, *target_s) {
            self.align_blocks(target_t, target_s);
        }

        true
    }

    fn try_align_diverging_call(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let dt = &self.de.basic_blocks[bb_t];
        let ds = &self.bc.basic_blocks[bb_s];
        let tt = dt.terminator();
        let ts = ds.terminator();

        let (
            mir::TerminatorKind::Call {
                func: func_t,
                args: args_t,
                destination: dest_t,
                target: None,
                unwind: unwind_t,
                ..
            },
            mir::TerminatorKind::Call {
                func: func_s,
                args: args_s,
                destination: dest_s,
                target: None,
                unwind: unwind_s,
                ..
            },
        ) = (&tt.kind, &ts.kind)
        else {
            return false;
        };

        if !self.call_func_equiv(func_t, func_s)
            || args_t.len() != args_s.len()
            || !self.place_equiv(*dest_t, *dest_s)
        {
            return false;
        }

        self.target_to_source
            .insert((bb_t, dt.statements.len()), Origin::Source((bb_s, ds.statements.len())));

        if let (Some(bb_t), Some(bb_s)) = (unwind_target(*unwind_t), unwind_target(*unwind_s)) {
            self.align_blocks(bb_t, bb_s);
        }

        true
    }

    fn is_unwind_resume_block(&self, bb: BasicBlock) -> bool {
        self.bc.basic_blocks[bb].statements.is_empty()
            && matches!(self.bc.basic_blocks[bb].terminator().kind, mir::TerminatorKind::UnwindResume)
    }

    fn stmt_equiv(&self, target: &mir::Statement<'tcx>, source: &mir::Statement<'tcx>) -> bool {
        match (&target.kind, &source.kind) {
            (
                mir::StatementKind::Assign(box (lhs_t, rhs_t)),
                mir::StatementKind::Assign(box (lhs_s, rhs_s)),
            ) => self.place_equiv(*lhs_t, *lhs_s) && self.rvalue_equiv(rhs_t, rhs_s),
            (mir::StatementKind::StorageLive(local_t), mir::StatementKind::StorageLive(local_s))
            | (mir::StatementKind::StorageDead(local_t), mir::StatementKind::StorageDead(local_s)) => {
                local_t == local_s
            },
            (mir::StatementKind::FakeRead(fake_read_t), mir::StatementKind::FakeRead(fake_read_s)) => {
                fake_read_t == fake_read_s
            },
            (
                mir::StatementKind::SetDiscriminant {
                    place: place_t,
                    variant_index: variant_t,
                },
                mir::StatementKind::SetDiscriminant {
                    place: place_s,
                    variant_index: variant_s,
                },
            ) => variant_t == variant_s && self.place_equiv(**place_t, **place_s),
            (mir::StatementKind::PlaceMention(place_t), mir::StatementKind::PlaceMention(place_s)) => {
                self.place_equiv(**place_t, **place_s)
            },
            (
                mir::StatementKind::AscribeUserType(place_t, variance_t),
                mir::StatementKind::AscribeUserType(place_s, variance_s),
            ) => {
                variance_t == variance_s
                    && place_t.as_ref().1 == place_s.as_ref().1
                    && self.place_equiv(place_t.as_ref().0, place_s.as_ref().0)
            },
            (mir::StatementKind::Intrinsic(intrinsic_t), mir::StatementKind::Intrinsic(intrinsic_s)) => {
                intrinsic_t == intrinsic_s
            },
            (mir::StatementKind::Coverage(kind_t), mir::StatementKind::Coverage(kind_s)) => kind_t == kind_s,
            (mir::StatementKind::ConstEvalCounter, mir::StatementKind::ConstEvalCounter)
            | (mir::StatementKind::Nop, mir::StatementKind::Nop) => true,
            (
                mir::StatementKind::BackwardIncompatibleDropHint {
                    place: place_t,
                    reason: reason_t,
                },
                mir::StatementKind::BackwardIncompatibleDropHint {
                    place: place_s,
                    reason: reason_s,
                },
            ) => reason_t == reason_s && self.place_equiv(**place_t, **place_s),
            _ => false,
        }
    }

    fn terminator_shape_equiv(&self, target: &mir::Terminator<'tcx>, source: &mir::Terminator<'tcx>) -> bool {
        use mir::TerminatorKind::{
            Assert, Call, Drop, FalseEdge, FalseUnwind, Goto, Return, SwitchInt, Unreachable, UnwindResume,
            UnwindTerminate,
        };

        match (&target.kind, &source.kind) {
            (Goto { .. }, Goto { .. })
            | (Goto { .. }, FalseEdge { .. })
            | (Goto { .. }, FalseUnwind { .. })
            | (FalseEdge { .. }, Goto { .. })
            | (FalseUnwind { .. }, Goto { .. })
            | (Return, Return)
            | (UnwindResume, UnwindResume)
            | (Unreachable, Unreachable) => true,

            (UnwindTerminate(a), UnwindTerminate(b)) => a == b,

            (
                SwitchInt {
                    discr: discr_t,
                    targets: targets_t,
                },
                SwitchInt {
                    discr: discr_s,
                    targets: targets_s,
                },
            ) => self.operand_equiv(discr_t, discr_s) && switch_values(targets_t) == switch_values(targets_s),

            (
                Assert {
                    cond: cond_t,
                    expected: expected_t,
                    msg: msg_t,
                    ..
                },
                Assert {
                    cond: cond_s,
                    expected: expected_s,
                    msg: msg_s,
                    ..
                },
            ) => {
                expected_t == expected_s
                    && self.operand_equiv(cond_t, cond_s)
                    && self.assert_msg_equiv(msg_t, msg_s)
            },

            (Drop { place: place_t, .. }, Drop { place: place_s, .. }) => {
                self.place_equiv(*place_t, *place_s)
            },

            (
                Call {
                    func: func_t,
                    args: args_t,
                    destination: dest_t,
                    target: target_t,
                    ..
                },
                Call {
                    func: func_s,
                    args: args_s,
                    destination: dest_s,
                    target: target_s,
                    ..
                },
            ) => {
                self.call_func_equiv(func_t, func_s)
                    && args_t.len() == args_s.len()
                    && args_t
                        .iter()
                        .zip(args_s.iter())
                        .all(|(arg_t, arg_s)| self.operand_equiv(&arg_t.node, &arg_s.node))
                    && self.place_equiv(*dest_t, *dest_s)
                    && target_t.is_some() == target_s.is_some()
            },

            _ => false,
        }
    }

    fn is_inserted_stmt(&self, stmt: &mir::Statement<'tcx>) -> bool {
        match &stmt.kind {
            mir::StatementKind::StorageLive(local) | mir::StatementKind::StorageDead(local) => {
                self.is_synthetic_local(*local)
            },
            mir::StatementKind::Assign(box (lhs, _)) => {
                lhs.projection.is_empty() && self.is_synthetic_local(lhs.local)
            },
            _ => false,
        }
    }

    /// Observe inserted synthetic statements while aligning blocks.
    ///
    /// In particular, this recognizes dropck's lowered `Box` deref alias:
    ///
    /// ```text
    /// _alias = copy ((_box.0).0) as *const/*mut T (Transmute)
    /// ```
    ///
    /// The statement itself remains inserted or split from the source statement
    /// that first uses `*_box`, but subsequent `*_alias` places are normalized
    /// back to `*_box` for structural matching.
    fn observe_inserted_stmt(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        source_loc: Option<SourceLoc>,
    ) -> Option<Origin> {
        let mir::StatementKind::Assign(box (lhs, rhs)) = &stmt.kind else {
            return None;
        };

        if !lhs.projection.is_empty() || !self.is_synthetic_local(lhs.local) {
            return None;
        }

        let mir::Rvalue::Cast(mir::CastKind::Transmute, mir::Operand::Copy(rhs_place), _) = rhs else {
            return None;
        };

        if !self.de.local_decls[rhs_place.local].ty.is_box() {
            return None;
        }

        let projections = rhs_place.projection.as_ref();
        if projections.len() < 2 {
            return None;
        }

        let is_box_projection = matches!(projections[0], mir::ProjectionElem::Field(field, _) if field.as_usize() == 0)
            && matches!(projections[1], mir::ProjectionElem::Field(field, _) if field.as_usize() == 0);
        if !is_box_projection {
            return None;
        }

        let split_from = source_loc.filter(|(bb, idx)| {
            self.source_stmt_uses_box_deref(&self.bc.basic_blocks[*bb].statements[*idx], rhs_place.local)
        });

        self.box_deref_aliases.insert(lhs.local, InternalBoxDerefAlias {
            place: NormalizedPlace {
                local: rhs_place.local,
                projection: Vec::new(),
            },
            source_loc: split_from,
        });

        split_from.map(Origin::SplitFrom)
    }

    fn source_stmt_uses_box_deref(&self, stmt: &mir::Statement<'tcx>, local: Local) -> bool {
        match &stmt.kind {
            mir::StatementKind::Assign(box (_, rhs)) => {
                self.rvalue_uses_box_deref_of_local(rhs, local, MirFlavor::Source)
            },
            mir::StatementKind::SetDiscriminant { place, .. }
            | mir::StatementKind::PlaceMention(place)
            | mir::StatementKind::BackwardIncompatibleDropHint { place, .. } => {
                self.place_uses_box_deref_of_local(**place, local, MirFlavor::Source)
            },
            mir::StatementKind::AscribeUserType(place, _) => {
                self.place_uses_box_deref_of_local(place.as_ref().0, local, MirFlavor::Source)
            },
            _ => false,
        }
    }

    fn stmt_uses_box_deref_alias(&self, stmt: &mir::Statement<'tcx>, source_loc: SourceLoc) -> bool {
        match &stmt.kind {
            mir::StatementKind::Assign(box (lhs, rhs)) => {
                self.place_uses_alias_with_origin(*lhs, source_loc, MirFlavor::Target)
                    || self.rvalue_uses_alias_with_origin(rhs, source_loc, MirFlavor::Target)
            },
            mir::StatementKind::SetDiscriminant { place, .. }
            | mir::StatementKind::PlaceMention(place)
            | mir::StatementKind::BackwardIncompatibleDropHint { place, .. } => {
                self.place_uses_alias_with_origin(**place, source_loc, MirFlavor::Target)
            },
            mir::StatementKind::AscribeUserType(place, _) => {
                self.place_uses_alias_with_origin(place.as_ref().0, source_loc, MirFlavor::Target)
            },
            _ => false,
        }
    }

    fn rvalue_uses_box_deref_of_local(
        &self,
        rvalue: &mir::Rvalue<'tcx>,
        local: Local,
        flavor: MirFlavor,
    ) -> bool {
        match rvalue {
            mir::Rvalue::Use(operand, _)
            | mir::Rvalue::Repeat(operand, _)
            | mir::Rvalue::WrapUnsafeBinder(operand, _)
            | mir::Rvalue::UnaryOp(_, operand)
            | mir::Rvalue::Cast(_, operand, _) => {
                self.operand_uses_box_deref_of_local(operand, local, flavor)
            },
            mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Reborrow(_, _, place)
            | mir::Rvalue::Discriminant(place)
            | mir::Rvalue::CopyForDeref(place) => self.place_uses_box_deref_of_local(*place, local, flavor),
            mir::Rvalue::BinaryOp(_, operands) => {
                self.operand_uses_box_deref_of_local(&operands.as_ref().0, local, flavor)
                    || self.operand_uses_box_deref_of_local(&operands.as_ref().1, local, flavor)
            },
            mir::Rvalue::Aggregate(_, operands) => operands
                .iter()
                .any(|operand| self.operand_uses_box_deref_of_local(operand, local, flavor)),
            mir::Rvalue::ThreadLocalRef(_) => false,
        }
    }

    fn operand_uses_box_deref_of_local(
        &self,
        operand: &mir::Operand<'tcx>,
        local: Local,
        flavor: MirFlavor,
    ) -> bool {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.place_uses_box_deref_of_local(*place, local, flavor)
            },
            mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => false,
        }
    }

    fn place_uses_box_deref_of_local(
        &self,
        place: mir::Place<'tcx>,
        local: Local,
        flavor: MirFlavor,
    ) -> bool {
        let normalized = self.normalize_place_for_flavor(place, flavor);
        normalized.local == local && matches!(normalized.projection.first(), Some(NormalizedPlaceElem::Deref))
    }

    fn rvalue_uses_alias_with_origin(
        &self,
        rvalue: &mir::Rvalue<'tcx>,
        source_loc: SourceLoc,
        flavor: MirFlavor,
    ) -> bool {
        match rvalue {
            mir::Rvalue::Use(operand, _)
            | mir::Rvalue::Repeat(operand, _)
            | mir::Rvalue::WrapUnsafeBinder(operand, _)
            | mir::Rvalue::UnaryOp(_, operand)
            | mir::Rvalue::Cast(_, operand, _) => {
                self.operand_uses_alias_with_origin(operand, source_loc, flavor)
            },
            mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Reborrow(_, _, place)
            | mir::Rvalue::Discriminant(place)
            | mir::Rvalue::CopyForDeref(place) => {
                self.place_uses_alias_with_origin(*place, source_loc, flavor)
            },
            mir::Rvalue::BinaryOp(_, operands) => {
                self.operand_uses_alias_with_origin(&operands.as_ref().0, source_loc, flavor)
                    || self.operand_uses_alias_with_origin(&operands.as_ref().1, source_loc, flavor)
            },
            mir::Rvalue::Aggregate(_, operands) => operands
                .iter()
                .any(|operand| self.operand_uses_alias_with_origin(operand, source_loc, flavor)),
            mir::Rvalue::ThreadLocalRef(_) => false,
        }
    }

    fn operand_uses_alias_with_origin(
        &self,
        operand: &mir::Operand<'tcx>,
        source_loc: SourceLoc,
        flavor: MirFlavor,
    ) -> bool {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.place_uses_alias_with_origin(*place, source_loc, flavor)
            },
            mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => false,
        }
    }

    fn place_uses_alias_with_origin(
        &self,
        place: mir::Place<'tcx>,
        source_loc: SourceLoc,
        _flavor: MirFlavor,
    ) -> bool {
        self.box_deref_aliases
            .get(&place.local)
            .is_some_and(|alias| alias.source_loc == Some(source_loc))
    }

    fn is_cleanup_erased_source_stmt(stmt: &mir::Statement<'tcx>) -> bool {
        matches!(
            &stmt.kind,
            mir::StatementKind::AscribeUserType(_, _)
            | mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Coverage(_)
            | mir::StatementKind::Assign(box (_, mir::Rvalue::Ref(_, mir::BorrowKind::Fake(_), _)))
        )
    }

    fn operand_equiv(&self, target: &mir::Operand<'tcx>, source: &mir::Operand<'tcx>) -> bool {
        match (target, source) {
            (mir::Operand::Copy(place_t), mir::Operand::Copy(place_s))
            | (mir::Operand::Move(place_t), mir::Operand::Move(place_s)) => {
                self.place_equiv(*place_t, *place_s)
            },
            (mir::Operand::Constant(const_t), mir::Operand::Constant(const_s)) => {
                Self::const_operand_equiv(const_t, const_s)
            },
            (mir::Operand::RuntimeChecks(checks_t), mir::Operand::RuntimeChecks(checks_s)) => {
                checks_t == checks_s
            },
            _ => false,
        }
    }

    fn const_operand_equiv(target: &mir::ConstOperand<'tcx>, source: &mir::ConstOperand<'tcx>) -> bool {
        if let (Some(target_did), Some(source_did)) = (const_fn_def_id(target), const_fn_def_id(source)) {
            return target_did == source_did;
        }

        target.const_.ty() == source.const_.ty() && target.const_ == source.const_
    }

    fn call_func_equiv(&self, target: &mir::Operand<'tcx>, source: &mir::Operand<'tcx>) -> bool {
        match (operand_fn_def_id(target), operand_fn_def_id(source)) {
            (Some(target_did), Some(source_did)) => target_did == source_did,
            _ => self.operand_equiv(target, source),
        }
    }

    fn assert_msg_equiv(&self, target: &mir::AssertMessage<'tcx>, source: &mir::AssertMessage<'tcx>) -> bool {
        use mir::AssertKind;

        match (target, source) {
            (
                AssertKind::BoundsCheck {
                    len: len_t,
                    index: index_t,
                },
                AssertKind::BoundsCheck {
                    len: len_s,
                    index: index_s,
                },
            ) => self.operand_equiv(len_t, len_s) && self.operand_equiv(index_t, index_s),
            (AssertKind::Overflow(op_t, lhs_t, rhs_t), AssertKind::Overflow(op_s, lhs_s, rhs_s)) => {
                op_t == op_s && self.operand_equiv(lhs_t, lhs_s) && self.operand_equiv(rhs_t, rhs_s)
            },
            (AssertKind::OverflowNeg(op_t), AssertKind::OverflowNeg(op_s))
            | (AssertKind::DivisionByZero(op_t), AssertKind::DivisionByZero(op_s))
            | (AssertKind::RemainderByZero(op_t), AssertKind::RemainderByZero(op_s))
            | (AssertKind::InvalidEnumConstruction(op_t), AssertKind::InvalidEnumConstruction(op_s)) => {
                self.operand_equiv(op_t, op_s)
            },
            (
                AssertKind::MisalignedPointerDereference {
                    required: required_t,
                    found: found_t,
                },
                AssertKind::MisalignedPointerDereference {
                    required: required_s,
                    found: found_s,
                },
            ) => self.operand_equiv(required_t, required_s) && self.operand_equiv(found_t, found_s),
            (AssertKind::NullPointerDereference, AssertKind::NullPointerDereference) => true,
            (AssertKind::ResumedAfterReturn(kind_t), AssertKind::ResumedAfterReturn(kind_s))
            | (AssertKind::ResumedAfterPanic(kind_t), AssertKind::ResumedAfterPanic(kind_s))
            | (AssertKind::ResumedAfterDrop(kind_t), AssertKind::ResumedAfterDrop(kind_s)) => {
                kind_t == kind_s
            },
            _ => false,
        }
    }

    fn rvalue_equiv(&self, target: &mir::Rvalue<'tcx>, source: &mir::Rvalue<'tcx>) -> bool {
        match (target, source) {
            (mir::Rvalue::Use(operand_t, retag_t), mir::Rvalue::Use(operand_s, retag_s)) => {
                retag_t == retag_s && self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::Ref(_, borrow_kind_t, place_t), mir::Rvalue::Ref(_, borrow_kind_s, place_s)) => {
                borrow_kind_t == borrow_kind_s && self.place_equiv(*place_t, *place_s)
            },
            (mir::Rvalue::RawPtr(mutability_t, place_t), mir::Rvalue::RawPtr(mutability_s, place_s)) => {
                mutability_t == mutability_s && self.place_equiv(*place_t, *place_s)
            },
            (
                mir::Rvalue::Reborrow(_, mutability_t, place_t),
                mir::Rvalue::Reborrow(_, mutability_s, place_s),
            ) => mutability_t == mutability_s && self.place_equiv(*place_t, *place_s),
            (mir::Rvalue::BinaryOp(op_t, operands_t), mir::Rvalue::BinaryOp(op_s, operands_s)) => {
                op_t == op_s
                    && self.operand_equiv(&operands_t.as_ref().0, &operands_s.as_ref().0)
                    && self.operand_equiv(&operands_t.as_ref().1, &operands_s.as_ref().1)
            },
            (mir::Rvalue::UnaryOp(op_t, operand_t), mir::Rvalue::UnaryOp(op_s, operand_s)) => {
                op_t == op_s && self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::Discriminant(place_t), mir::Rvalue::Discriminant(place_s))
            | (mir::Rvalue::CopyForDeref(place_t), mir::Rvalue::CopyForDeref(place_s)) => {
                self.place_equiv(*place_t, *place_s)
            },
            (mir::Rvalue::Aggregate(kind_t, operands_t), mir::Rvalue::Aggregate(kind_s, operands_s)) => {
                aggregate_kind_equiv(kind_t.as_ref(), kind_s.as_ref())
                    && operands_t.len() == operands_s.len()
                    && operands_t
                        .iter()
                        .zip(operands_s.iter())
                        .all(|(operand_t, operand_s)| self.operand_equiv(operand_t, operand_s))
            },
            (mir::Rvalue::Cast(kind_t, operand_t, _), mir::Rvalue::Cast(kind_s, operand_s, _)) => {
                cast_kind_equiv(*kind_t, *kind_s) && self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::Repeat(operand_t, len_t), mir::Rvalue::Repeat(operand_s, len_s)) => {
                len_t == len_s && self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::WrapUnsafeBinder(operand_t, _), mir::Rvalue::WrapUnsafeBinder(operand_s, _)) => {
                self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::ThreadLocalRef(def_id_t), mir::Rvalue::ThreadLocalRef(def_id_s)) => {
                def_id_t == def_id_s
            },
            _ => false,
        }
    }

    fn place_equiv(&self, target: mir::Place<'tcx>, source: mir::Place<'tcx>) -> bool {
        self.normalize_place_for_flavor(target, MirFlavor::Target)
            == self.normalize_place_for_flavor(source, MirFlavor::Source)
    }

    fn normalize_place_for_flavor(&self, place: mir::Place<'tcx>, flavor: MirFlavor) -> NormalizedPlace {
        match flavor {
            MirFlavor::Source => Self::normalize_source_place(place),
            MirFlavor::Target => self.normalize_place(place),
        }
    }

    fn normalize_source_place(place: mir::Place<'tcx>) -> NormalizedPlace {
        NormalizedPlace {
            local: place.local,
            projection: place.projection.iter().map(normalize_projection_elem).collect(),
        }
    }

    fn normalize_place(&self, place: mir::Place<'tcx>) -> NormalizedPlace {
        if let Some(alias) = self.box_deref_aliases.get(&place.local)
            && matches!(place.projection.first(), Some(mir::ProjectionElem::Deref))
        {
            let mut projection = alias.place.projection.clone();
            projection.push(NormalizedPlaceElem::Deref);
            projection.extend(place.projection[1..].iter().map(|elem| normalize_projection_elem(*elem)));
            return NormalizedPlace {
                local: alias.place.local,
                projection,
            };
        }

        Self::normalize_source_place(place)
    }

    const fn is_synthetic_local(&self, local: Local) -> bool {
        local.as_usize() >= self.source_local_count
    }

    fn is_synthetic_bool_local(&self, local: Local) -> bool {
        self.is_synthetic_local(local) && self.de.local_decls[local].ty.is_bool()
    }
}

#[derive(Clone, Copy)]
enum MirFlavor {
    Source,
    Target,
}

impl PointPhaseKind {
    const fn with_source(self, source: SourceLoc) -> PointPhase {
        match self {
            Self::Direct => PointPhase::Direct(source),
            Self::PreEffect => PointPhase::PreEffect(source),
            Self::PostEffect => PointPhase::PostEffect(source),
        }
    }
}

const fn point_phase_from_origin(origin: Origin) -> Option<PointPhase> {
    match origin {
        Origin::Source(source) | Origin::FoldedFrom(source) | Origin::SplitFrom(source) => {
            Some(PointPhase::Direct(source))
        },
        Origin::Inserted => None,
    }
}

fn insert_point_mapping(
    target_points_to_source: &mut FxHashMap<TargetPoint, SourcePoint>,
    target: TargetLoc,
    phase: PointPhase,
) {
    let (target_bb, target_idx) = target;
    let (source, start_source_kind, mid_source_kind) = match phase {
        PointPhase::Direct(source) => (source, facts::PointType::Start, facts::PointType::Mid),
        PointPhase::PreEffect(source) => (source, facts::PointType::Start, facts::PointType::Start),
        PointPhase::PostEffect(source) => (source, facts::PointType::Mid, facts::PointType::Mid),
    };
    let (source_bb, source_idx) = source;

    target_points_to_source
        .insert((target_bb, target_idx, facts::PointType::Start), (source_bb, source_idx, start_source_kind));
    target_points_to_source
        .insert((target_bb, target_idx, facts::PointType::Mid), (source_bb, source_idx, mid_source_kind));
}

fn compute_predecessors(body: &Body<'_>) -> FxHashMap<BasicBlock, Vec<BasicBlock>> {
    let mut predecessors: FxHashMap<_, Vec<_>> = FxHashMap::default();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for succ in real_targets(data.terminator()) {
            predecessors.entry(succ).or_default().push(bb);
        }
    }
    predecessors
}

fn real_targets(terminator: &mir::Terminator<'_>) -> Vec<BasicBlock> {
    match &terminator.kind {
        mir::TerminatorKind::Goto { target }
        | mir::TerminatorKind::Assert { target, .. }
        | mir::TerminatorKind::Drop { target, .. } => vec![*target],
        mir::TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
        mir::TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
        mir::TerminatorKind::FalseEdge { real_target, .. }
        | mir::TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
        mir::TerminatorKind::Yield { resume, .. } => vec![*resume],
        mir::TerminatorKind::InlineAsm { targets, .. } => targets.to_vec(),
        mir::TerminatorKind::CoroutineDrop
        | mir::TerminatorKind::Return
        | mir::TerminatorKind::Unreachable
        | mir::TerminatorKind::UnwindResume
        | mir::TerminatorKind::UnwindTerminate(_)
        | mir::TerminatorKind::TailCall { .. } => vec![],
    }
}

const fn normal_successor(terminator: &mir::Terminator<'_>) -> Option<BasicBlock> {
    match &terminator.kind {
        mir::TerminatorKind::Goto { target }
        | mir::TerminatorKind::Assert { target, .. }
        | mir::TerminatorKind::Drop { target, .. }
        | mir::TerminatorKind::FalseEdge {
            real_target: target,
            ..
        }
        | mir::TerminatorKind::FalseUnwind {
            real_target: target,
            ..
        } => Some(*target),
        mir::TerminatorKind::Call { target, .. } => *target,
        _ => None,
    }
}

fn switch_values(targets: &mir::SwitchTargets) -> Vec<u128> {
    targets.iter().map(|(value, _)| value).collect()
}

fn operand_fn_def_id(operand: &mir::Operand<'_>) -> Option<DefId> {
    let mir::Operand::Constant(constant) = operand else {
        return None;
    };

    const_fn_def_id(constant)
}

fn const_fn_def_id(constant: &mir::ConstOperand<'_>) -> Option<DefId> {
    let ty::TyKind::FnDef(did, _) = constant.const_.ty().kind() else {
        return None;
    };

    Some(*did)
}

fn cast_kind_equiv(target: mir::CastKind, source: mir::CastKind) -> bool {
    // Drop elaboration lowers this pointer coercion to the more primitive
    // `PtrToPtr` cast. Treat them as the same shape for source mapping.
    if matches!(
        (target, source),
        (
            mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::MutToConstPointer, _),
            mir::CastKind::PtrToPtr,
        ) | (
            mir::CastKind::PtrToPtr,
            mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::MutToConstPointer, _),
        )
    ) {
        return true;
    }

    target == source
}

fn aggregate_kind_equiv<'tcx>(target: &mir::AggregateKind<'tcx>, source: &mir::AggregateKind<'tcx>) -> bool {
    match (target, source) {
        // Aggregate generic arguments carry NLL regions in borrowck MIR and erased
        // regions in dropck MIR. For mapping, the ADT identity and variant are the
        // semantic shape we need.
        (
            mir::AggregateKind::Adt(def_id_t, variant_t, _, _, active_field_t),
            mir::AggregateKind::Adt(def_id_s, variant_s, _, _, active_field_s),
        ) => def_id_t == def_id_s && variant_t == variant_s && active_field_t == active_field_s,
        (mir::AggregateKind::Closure(def_id_t, _), mir::AggregateKind::Closure(def_id_s, _))
        | (mir::AggregateKind::Coroutine(def_id_t, _), mir::AggregateKind::Coroutine(def_id_s, _))
        | (
            mir::AggregateKind::CoroutineClosure(def_id_t, _),
            mir::AggregateKind::CoroutineClosure(def_id_s, _),
        ) => def_id_t == def_id_s,
        (mir::AggregateKind::Array(ty_t), mir::AggregateKind::Array(ty_s)) => ty_t == ty_s,
        (mir::AggregateKind::Tuple, mir::AggregateKind::Tuple) => true,
        (mir::AggregateKind::RawPtr(ty_t, mutability_t), mir::AggregateKind::RawPtr(ty_s, mutability_s)) => {
            ty_t == ty_s && mutability_t == mutability_s
        },
        _ => false,
    }
}

const fn normalize_projection_elem(elem: mir::PlaceElem<'_>) -> NormalizedPlaceElem {
    match elem {
        mir::ProjectionElem::Deref => NormalizedPlaceElem::Deref,
        mir::ProjectionElem::Field(field, _) => NormalizedPlaceElem::Field(field.as_usize()),
        mir::ProjectionElem::Index(local) => NormalizedPlaceElem::Index(local),
        mir::ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => NormalizedPlaceElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        },
        mir::ProjectionElem::Subslice { from, to, from_end } => {
            NormalizedPlaceElem::Subslice { from, to, from_end }
        },
        mir::ProjectionElem::Downcast(_, variant_index) => {
            NormalizedPlaceElem::Downcast(variant_index.as_usize())
        },
        mir::ProjectionElem::OpaqueCast(_) => NormalizedPlaceElem::OpaqueCast,
        mir::ProjectionElem::UnwrapUnsafeBinder(_) => NormalizedPlaceElem::UnwrapUnsafeBinder,
    }
}

const fn unwind_target(action: mir::UnwindAction) -> Option<BasicBlock> {
    match action {
        mir::UnwindAction::Cleanup(bb) => Some(bb),
        mir::UnwindAction::Continue | mir::UnwindAction::Unreachable | mir::UnwindAction::Terminate(_) => {
            None
        },
    }
}

fn same_or_subplace(base: &NormalizedPlace, candidate: &NormalizedPlace) -> bool {
    base.local == candidate.local
        && candidate.projection.len() >= base.projection.len()
        && candidate.projection.starts_with(&base.projection)
}

fn count_locations(body: &Body<'_>) -> usize {
    body.basic_blocks.iter().map(|bb| bb.statements.len() + 1).sum()
}

fn format_origin(bc: &Body<'_>, origin: Origin) -> String {
    match origin {
        Origin::Source((bb, idx)) => {
            format!("Source({:?}[{}] {})", bb, idx, describe_location(bc, bb, idx))
        },
        Origin::Inserted => "Inserted".to_owned(),
        Origin::SplitFrom((bb, idx)) => {
            format!("SplitFrom({:?}[{}] {})", bb, idx, describe_location(bc, bb, idx))
        },
        Origin::FoldedFrom((bb, idx)) => {
            format!("FoldedFrom({:?}[{}] {})", bb, idx, describe_location(bc, bb, idx))
        },
    }
}

fn describe_location(body: &Body<'_>, bb: BasicBlock, idx: usize) -> String {
    let data = &body.basic_blocks[bb];
    if idx < data.statements.len() {
        format!("{:?}", data.statements[idx].kind)
    } else {
        format!("{:?}", data.terminator().kind)
    }
}
