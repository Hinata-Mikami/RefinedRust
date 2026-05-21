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

use std::collections::VecDeque;

use rr_rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};
use rr_rustc_interface::middle::mir::{self, BasicBlock, Body, Local};
use rr_rustc_interface::middle::ty;

use super::types::*;
use super::util::*;
use super::{BoxDerefAlias, Mapper, MappingResult, Origin, SourceLoc, SyntheticDropBorrow, TargetLoc};
use crate::search;

impl<'a, 'tcx> Mapper<'a, 'tcx> {
    pub(super) fn new(tcx: ty::TyCtxt<'tcx>, bc: &'a Body<'tcx>, de: &'a Body<'tcx>) -> Self {
        Self {
            tcx,
            bc,
            de,
            drop_drop_did: resolve_drop_drop_did(tcx),
            discriminant_value_did: search::try_resolve_did(tcx, &[
                "core",
                "intrinsics",
                "discriminant_value",
            ]),
            source_local_count: bc.local_decls.len(),
            target_to_source: FxHashMap::default(),
            target_point_phases: FxHashMap::default(),
            visited: FxHashSet::default(),
            box_deref_aliases: FxHashMap::default(),
            synthetic_drop_borrows: FxHashMap::default(),
            copy_aliases: FxHashMap::default(),
            bc_predecessors: compute_predecessors(bc),
        }
    }

    pub(super) fn finish(mut self) -> MappingResult {
        self.collect_synthetic_drop_borrows_from_mapping();

        let mut unmapped_targets = Vec::new();
        for (bb, data) in self.de.basic_blocks.iter_enumerated() {
            for idx in 0..=data.statements.len() {
                if !self.target_to_source.contains_key(&(bb, idx)) {
                    unmapped_targets.push((bb, idx));
                }
            }
        }

        // Inserted target locations may still be translated directly or used
        // as successor starts by annotation generation. They have no source
        // statement, but Polonius facts are indexed by borrowck source points,
        // so give them a conservative source phase when it is structurally
        // clear where they sit relative to source MIR.
        let mut target_point_phases = self.target_point_phases.clone();
        let mut target_to_source_entries: Vec<_> = self.target_to_source.iter().collect();
        target_to_source_entries.sort_by_key(|((bb, idx), _)| (bb.as_u32(), *idx));
        for ((bb, idx), origin) in target_to_source_entries {
            if target_point_phases.contains_key(&(*bb, *idx)) {
                continue;
            }

            if *origin == Origin::Inserted
                && let Some(source) = self.next_mapped_source_after(*bb, *idx)
            {
                target_point_phases.insert((*bb, *idx), PointPhase::PreEffect(source));
            } else if *origin == Origin::Inserted
                && *idx == 0
                && let Some(source) = self.source_successor_for_inserted_block_start(*bb)
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
            synthetic_drop_borrows_by_local: self.synthetic_drop_borrows.clone(),
            synthetic_drop_borrows_by_borrow_loc: self
                .synthetic_drop_borrows
                .values()
                .map(|borrow| (borrow.borrow_loc(), *borrow))
                .collect(),
            synthetic_drop_borrows_by_drop_call_loc: self
                .synthetic_drop_borrows
                .values()
                .map(|borrow| (borrow.drop_call_loc(), *borrow))
                .collect(),
        }
    }

    fn collect_synthetic_drop_borrows_from_mapping(&mut self) {
        let entries: Vec<_> =
            self.target_to_source.iter().map(|(target, origin)| (*target, *origin)).collect();
        for ((bb_t, idx_t), origin) in entries {
            let Some((bb_s, idx_s)) = origin_source_loc(origin) else {
                continue;
            };
            if idx_t != self.de.basic_blocks[bb_t].statements.len()
                || idx_s != self.bc.basic_blocks[bb_s].statements.len()
            {
                continue;
            }

            let mir::TerminatorKind::Drop {
                place: source_place,
                ..
            } = self.bc.basic_blocks[bb_s].terminator().kind
            else {
                continue;
            };
            let source_place = Self::normalize_source_place(source_place);

            let mir::TerminatorKind::Call { func, args, .. } = &self.de.basic_blocks[bb_t].terminator().kind
            else {
                continue;
            };
            if !self.is_drop_drop_call(func) {
                continue;
            }
            if args.len() != 1 {
                continue;
            }
            let mir::Operand::Move(arg_place) = args[0].node else {
                continue;
            };
            if !arg_place.projection.is_empty() || self.synthetic_drop_borrows.contains_key(&arg_place.local)
            {
                continue;
            }

            let Some((borrow_idx, borrowed_place)) =
                self.find_synthetic_drop_borrow_stmt(bb_t, arg_place.local)
            else {
                continue;
            };
            if borrowed_place != source_place {
                continue;
            }

            let src_drop = (bb_s, idx_s);
            let borrow_loc = (bb_t, borrow_idx);
            self.synthetic_drop_borrows.insert(arg_place.local, SyntheticDropBorrow {
                synthetic_ref_local: arg_place.local,
                borrow_loc,
                drop_call_loc: (bb_t, idx_t),
                source_drop_loc: src_drop,
            });
            self.mark_phase(borrow_loc, PointPhase::PreEffect(src_drop));
            self.mark_phase((bb_t, idx_t), PointPhase::Direct(src_drop));
        }
    }

    fn mark_origin(&mut self, loc: TargetLoc, origin: Origin) {
        self.target_to_source.insert(loc, origin);
    }

    fn mark_phase(&mut self, loc: TargetLoc, phase: PointPhase) {
        self.target_point_phases.insert(loc, phase);
    }

    fn mark_origin_with_phase(&mut self, loc: TargetLoc, origin: Origin, phase: PointPhase) {
        self.mark_origin(loc, origin);
        self.mark_phase(loc, phase);
    }

    fn mark_block_statements_with_phase(&mut self, bb: BasicBlock, origin: Origin, phase: PointPhase) {
        for idx in 0..self.de.basic_blocks[bb].statements.len() {
            self.mark_origin_with_phase((bb, idx), origin, phase);
        }
    }

    fn mark_inserted_block_statements_with_phase(&mut self, bb: BasicBlock, phase: PointPhase) {
        for idx in 0..self.de.basic_blocks[bb].statements.len() {
            self.target_to_source.entry((bb, idx)).or_insert(Origin::Inserted);
            self.mark_phase((bb, idx), phase);
        }
    }

    fn source_chain_origin(&self, start_bb: BasicBlock, current_bb: BasicBlock) -> Origin {
        let loc = (current_bb, self.bc.basic_blocks[current_bb].statements.len());
        if current_bb == start_bb { Origin::Source(loc) } else { Origin::FoldedFrom(loc) }
    }

    fn has_single_source_predecessor(&self, bb: BasicBlock) -> bool {
        self.bc_predecessors.get(&bb).is_some_and(|preds| preds.len() == 1)
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

    /// Infer a point for an inserted target terminator after statement folding.
    ///
    /// When a source drop is eliminated, `align_statements` may still fold
    /// statements from the drop's normal successor into the current target
    /// block. If the target terminator then matches the terminator immediately
    /// after that last folded source statement, map its points directly to that
    /// source terminator. This keeps the inference local to an already mapped
    /// predecessor statement and avoids guessing across joins.
    fn source_terminator_after_previous_mapped_statement(
        &self,
        bb_t: BasicBlock,
        idx_t: usize,
    ) -> Option<SourceLoc> {
        if idx_t != self.de.basic_blocks[bb_t].statements.len() || idx_t == 0 {
            return None;
        }

        let (bb_s, idx_s) = origin_source_loc(self.target_to_source.get(&(bb_t, idx_t - 1)).copied()?)?;
        let source_data = &self.bc.basic_blocks[bb_s];
        if idx_s + 1 != source_data.statements.len() {
            return None;
        }

        let target_term = self.de.basic_blocks[bb_t].terminator();
        let source_term = source_data.terminator();
        self.terminator_shape_equiv(target_term, source_term)
            .then_some((bb_s, source_data.statements.len()))
    }

    /// Infer a source point for the start of an inserted target block.
    ///
    /// This covers blocks that exist only in dropck MIR but are still visible to
    /// the target CFG, most notably collapsed cleanup joins. Example:
    /// borrowck has two cleanup drop blocks that both continue to a shared
    /// `resume` block, while dropck may merge those paths into one target
    /// `resume` block. Annotation generation asks for the start point of that
    /// inserted successor block when computing terminator dying loans.
    ///
    /// We infer the point from every mapped predecessor edge:
    /// - identify whether the target predecessor reaches `bb_t` through its normal or unwind edge,
    /// - follow the corresponding edge in the mapped source predecessor,
    /// - if the inserted target block's terminator matches a later source terminator along a linear normal
    ///   path, use that source terminator point,
    /// - otherwise use the start of the corresponding source successor block.
    ///
    /// All predecessor edges must agree on the same source location. If they do
    /// not, we return `None` and leave the mapping boundary to fail loudly.
    fn source_successor_for_inserted_block_start(&self, bb_t: BasicBlock) -> Option<SourceLoc> {
        let mut source = None;
        let target_term = self.de.basic_blocks[bb_t].terminator();

        for (pred_t, data_t) in self.de.basic_blocks.iter_enumerated() {
            if !terminator_targets(data_t.terminator()).contains(&bb_t) {
                continue;
            }

            let pred_loc_t = (pred_t, data_t.statements.len());
            let pred_loc_s = origin_source_loc(self.target_to_source.get(&pred_loc_t).copied()?)?;
            let succ_source = matching_source_successor(
                data_t.terminator(),
                bb_t,
                self.bc.basic_blocks[pred_loc_s.0].terminator(),
            )?;
            let succ_source =
                if let Some(matched) = self.find_matching_source_terminator_from(succ_source, target_term) {
                    let source_data = &self.bc.basic_blocks[matched];
                    (matched, source_data.statements.len())
                } else {
                    (succ_source, 0)
                };

            if source.is_some_and(|existing| existing != succ_source) {
                return None;
            }
            source = Some(succ_source);
        }

        source
    }

    fn find_matching_source_terminator_from(
        &self,
        start: BasicBlock,
        target: &mir::Terminator<'tcx>,
    ) -> Option<BasicBlock> {
        // Source cleanup chains can have extra drop blocks between the source
        // successor edge and the terminator that corresponds to the inserted
        // target block. Only follow single normal-successor chains; joins and
        // branches are deliberately not guessed here.
        let mut current = start;
        for _ in 0..self.bc.basic_blocks.len() {
            let source = self.bc.basic_blocks[current].terminator();
            if self.terminator_shape_equiv(target, source) {
                return Some(current);
            }
            current = normal_successor(source)?;
        }
        None
    }

    pub(super) fn align_blocks(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) {
        self.align_blocks_with_origin(bb_t, bb_s, false);
    }

    fn align_blocks_with_origin(&mut self, bb_t: BasicBlock, bb_s: BasicBlock, folded_from_source: bool) {
        if !self.visited.insert((bb_t, bb_s)) {
            return;
        }

        self.align_statements(bb_t, bb_s, folded_from_source);
        self.align_terminator(bb_t, bb_s, folded_from_source);
    }

    fn align_statements(&mut self, bb_t: BasicBlock, bb_s: BasicBlock, folded_from_source: bool) {
        let data_t = &self.de.basic_blocks[bb_t];
        let data_s = &self.bc.basic_blocks[bb_s];

        let mut i_t = 0;
        let mut i_s = 0;

        while i_t < data_t.statements.len() {
            let st = &data_t.statements[i_t];

            if let Some(source_loc) = self.try_match_lowered_discriminant_value_stmt(st, bb_s, i_s) {
                self.mark_origin((bb_t, i_t), Origin::Source(source_loc));
                i_t += 1;
                continue;
            }

            if self.is_inserted_stmt(st) {
                let source_loc = (i_s < data_s.statements.len()).then_some((bb_s, i_s));
                let origin = self.observe_inserted_stmt(st, source_loc).unwrap_or(Origin::Inserted);
                self.mark_origin((bb_t, i_t), origin);
                i_t += 1;
                continue;
            }

            while i_s < data_s.statements.len()
                && Self::is_cleanup_erased_source_stmt(&data_s.statements[i_s])
            {
                if matches!(st.kind, mir::StatementKind::Nop) {
                    self.mark_origin((bb_t, i_t), Origin::Source((bb_s, i_s)));
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
                } else if folded_from_source {
                    Origin::FoldedFrom(source_loc)
                } else {
                    Origin::Source(source_loc)
                };
                self.mark_origin((bb_t, i_t), origin);
                i_t += 1;
                i_s += 1;
                continue;
            }

            if let Some(source_loc) = self.try_match_folded_source_stmt(&data_t.statements[i_t], bb_s, i_s) {
                self.mark_origin((bb_t, i_t), Origin::FoldedFrom(source_loc));
                i_t += 1;
                continue;
            }

            break;
        }

        while i_t < data_t.statements.len() {
            let st = &data_t.statements[i_t];
            if let Some(source_loc) = self.try_match_lowered_discriminant_value_stmt(st, bb_s, i_s) {
                self.mark_origin((bb_t, i_t), Origin::Source(source_loc));
            } else if self.is_inserted_stmt(st) {
                let source_loc = (i_s < data_s.statements.len()).then_some((bb_s, i_s));
                let origin = self.observe_inserted_stmt(st, source_loc).unwrap_or(Origin::Inserted);
                self.mark_origin((bb_t, i_t), origin);
            } else if let Some(source_loc) = self.try_match_folded_source_stmt(st, bb_s, i_s) {
                self.mark_origin((bb_t, i_t), Origin::FoldedFrom(source_loc));
            } else {
                self.mark_origin((bb_t, i_t), Origin::Inserted);
            }
            i_t += 1;
        }
    }

    fn align_terminator(&mut self, bb_t: BasicBlock, bb_s: BasicBlock, folded_from_source: bool) {
        let dt = &self.de.basic_blocks[bb_t];
        let ds = &self.bc.basic_blocks[bb_s];

        let tt = dt.terminator();
        let ts = ds.terminator();
        let loc_t = (bb_t, dt.statements.len());

        if self.terminator_shape_equiv(tt, ts) {
            let source_loc = (bb_s, ds.statements.len());
            let origin =
                if folded_from_source { Origin::FoldedFrom(source_loc) } else { Origin::Source(source_loc) };
            self.mark_origin(loc_t, origin);
            self.recurse_direct(tt, ts);
            return;
        }

        if self.try_align_lowered_discriminant_value_goto(bb_t, bb_s) {
            return;
        }

        if self.try_align_folded_source_terminator(bb_t, bb_s) {
            return;
        }

        if self.try_align_rewritten_drop(bb_t, bb_s) {
            return;
        }

        if self.try_align_explicit_drop_call(bb_t, bb_s) {
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

        if let Some(source_loc) = self.source_terminator_after_previous_mapped_statement(bb_t, loc_t.1) {
            self.mark_origin(loc_t, Origin::FoldedFrom(source_loc));
            self.recurse_direct(tt, self.bc.basic_blocks[source_loc.0].terminator());
            return;
        }

        self.mark_origin(loc_t, Origin::Inserted);
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
            ) => self.align_successor(*target_t, *target_s),

            (
                mir::TerminatorKind::SwitchInt {
                    targets: targets_t, ..
                },
                mir::TerminatorKind::SwitchInt {
                    targets: targets_s, ..
                },
            ) => {
                for (bb_t, bb_s) in targets_t.all_targets().iter().zip(targets_s.all_targets().iter()) {
                    self.align_successor(*bb_t, *bb_s);
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
                self.align_successor(*target_t, *target_s);
                if let (Some(bb_t), Some(bb_s)) = (unwind_target(*unwind_t), unwind_target(*unwind_s)) {
                    self.align_successor(bb_t, bb_s);
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
                    self.align_successor(bb_t, bb_s);
                }
                if let (Some(bb_t), Some(bb_s)) = (unwind_target(*unwind_t), unwind_target(*unwind_s)) {
                    self.align_successor(bb_t, bb_s);
                }
            },

            _ => {},
        }
    }

    fn align_successor(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) {
        let (bb_s, folded_from_source) = self.skip_source_forwarding_blocks(bb_s);
        self.align_blocks_with_origin(bb_t, bb_s, folded_from_source);
    }

    fn skip_source_forwarding_blocks(&self, mut bb_s: BasicBlock) -> (BasicBlock, bool) {
        let mut folded_from_source = false;
        for _ in 0..self.bc.basic_blocks.len() {
            let data = &self.bc.basic_blocks[bb_s];
            if !data.statements.is_empty() {
                break;
            }

            let (mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }) = data.terminator().kind
            else {
                break;
            };

            folded_from_source = true;
            bb_s = target;
        }

        (bb_s, folded_from_source)
    }

    fn try_align_rewritten_drop(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let tt = self.de.basic_blocks[bb_t].terminator();
        let mut cur_s = bb_s;

        for _ in 0..self.bc.basic_blocks.len() {
            let ts = self.bc.basic_blocks[cur_s].terminator();
            let Some(source_place) = self.source_drop_place(ts) else {
                return false;
            };

            let Some((a, b, administrative_statements)) = self.parse_drop_flag_test(bb_t, tt, &source_place)
            else {
                return false;
            };

            let Some(drop_bb) = self.find_actual_drop_block(a, b, &source_place) else {
                let mir::TerminatorKind::Drop { target: next_s, .. } = ts.kind else {
                    return false;
                };

                if !self.has_single_source_predecessor(next_s) {
                    return false;
                }

                cur_s = next_s;
                continue;
            };

            return self.align_rewritten_drop_match(
                bb_t,
                cur_s,
                ts,
                a,
                b,
                administrative_statements,
                drop_bb,
            );
        }

        false
    }

    fn align_rewritten_drop_match(
        &mut self,
        bb_t: BasicBlock,
        bb_s: BasicBlock,
        ts: &mir::Terminator<'tcx>,
        a: BasicBlock,
        b: BasicBlock,
        administrative_statements: Vec<usize>,
        drop_bb: BasicBlock,
    ) -> bool {
        let skip_bb = if drop_bb == a { b } else { a };

        let src_drop = (bb_s, self.bc.basic_blocks[bb_s].statements.len());
        for idx in administrative_statements {
            self.mark_origin_with_phase(
                (bb_t, idx),
                Origin::SplitFrom(src_drop),
                PointPhase::PreEffect(src_drop),
            );
        }
        let flag_test_loc = (bb_t, self.de.basic_blocks[bb_t].statements.len());
        self.mark_origin_with_phase(
            flag_test_loc,
            Origin::SplitFrom(src_drop),
            PointPhase::PreEffect(src_drop),
        );

        self.mark_inserted_block_statements_with_phase(drop_bb, PointPhase::PreEffect(src_drop));
        let drop_loc = (drop_bb, self.de.basic_blocks[drop_bb].statements.len());
        self.mark_origin_with_phase(drop_loc, Origin::SplitFrom(src_drop), PointPhase::Direct(src_drop));

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

    fn try_align_explicit_drop_call(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let ds = &self.bc.basic_blocks[bb_s];
        let mir::TerminatorKind::Drop {
            place: source_place,
            target: target_s,
            unwind: unwind_s,
            ..
        } = ds.terminator().kind
        else {
            return false;
        };
        let source_place = Self::normalize_source_place(source_place);

        let dt = &self.de.basic_blocks[bb_t];
        let mir::TerminatorKind::Call {
            func: func_t,
            args: args_t,
            target: target_t,
            unwind: unwind_t,
            ..
        } = &dt.terminator().kind
        else {
            return false;
        };

        if !self.is_drop_drop_call(func_t) {
            return false;
        }

        if args_t.len() != 1 {
            return false;
        }
        let arg = &args_t[0];
        let mir::Operand::Move(arg_place) = arg.node else {
            return false;
        };
        if !arg_place.projection.is_empty() {
            return false;
        }

        let Some((borrow_idx, borrowed_place)) = self.find_synthetic_drop_borrow_stmt(bb_t, arg_place.local)
        else {
            return false;
        };
        if borrowed_place != source_place {
            return false;
        }

        let Some(target_t) = *target_t else {
            return false;
        };
        let src_drop = (bb_s, ds.statements.len());
        let drop_call_loc = (bb_t, dt.statements.len());
        let borrow_loc = (bb_t, borrow_idx);
        let synthetic_borrow = SyntheticDropBorrow {
            synthetic_ref_local: arg_place.local,
            borrow_loc,
            drop_call_loc,
            source_drop_loc: src_drop,
        };

        self.synthetic_drop_borrows.insert(arg_place.local, synthetic_borrow);
        self.mark_origin_with_phase(borrow_loc, Origin::Inserted, PointPhase::PreEffect(src_drop));
        self.mark_origin_with_phase(drop_call_loc, Origin::SplitFrom(src_drop), PointPhase::Direct(src_drop));

        self.align_blocks(target_t, target_s);
        if let (Some(bb_t), Some(bb_s)) = (unwind_target(*unwind_t), unwind_target(unwind_s)) {
            self.align_blocks(bb_t, bb_s);
        }
        true
    }

    fn find_synthetic_drop_borrow_stmt(
        &self,
        bb_t: BasicBlock,
        synthetic_ref_local: Local,
    ) -> Option<(usize, NormalizedPlace)> {
        self.de.basic_blocks[bb_t].statements.iter().enumerate().rev().find_map(|(idx, stmt)| {
            let mir::StatementKind::Assign(box (
                lhs,
                mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place),
            )) = &stmt.kind
            else {
                return None;
            };
            (lhs.projection.is_empty() && lhs.local == synthetic_ref_local)
                .then(|| (idx, self.normalize_place(*place)))
        })
    }

    fn is_drop_drop_call(&self, func: &mir::Operand<'tcx>) -> bool {
        let Some(drop_drop_did) = self.drop_drop_did else {
            return false;
        };
        operand_fn_def_id(func) == Some(drop_drop_did)
    }

    fn is_discriminant_value_call(&self, func: &mir::Operand<'tcx>) -> bool {
        let Some(discriminant_value_did) = self.discriminant_value_did else {
            return false;
        };
        operand_fn_def_id(func) == Some(discriminant_value_did)
    }

    fn try_match_lowered_discriminant_value_stmt(
        &self,
        stmt_t: &mir::Statement<'tcx>,
        bb_s: BasicBlock,
        idx_s: usize,
    ) -> Option<SourceLoc> {
        if idx_s != self.bc.basic_blocks[bb_s].statements.len() {
            return None;
        }

        let mir::StatementKind::Assign(box (lhs_t, mir::Rvalue::Discriminant(place_t))) = &stmt_t.kind else {
            return None;
        };

        let mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target: Some(_),
            ..
        } = &self.bc.basic_blocks[bb_s].terminator().kind
        else {
            return None;
        };

        if !self.is_discriminant_value_call(func) || args.len() != 1 {
            return None;
        }
        if !self.place_equiv(*lhs_t, *destination) {
            return None;
        }
        if !self.discriminant_place_matches_call_arg(*place_t, &args[0].node) {
            return None;
        }

        Some((bb_s, idx_s))
    }

    fn discriminant_place_matches_call_arg(
        &self,
        place_t: mir::Place<'tcx>,
        arg_s: &mir::Operand<'tcx>,
    ) -> bool {
        let (mir::Operand::Copy(arg_place_s) | mir::Operand::Move(arg_place_s)) = arg_s else {
            return false;
        };

        let discr_place = self.normalize_place_for_flavor(place_t, MirFlavor::Target);
        let arg_place = self.normalize_place_for_flavor(*arg_place_s, MirFlavor::Source);
        discr_place.local == arg_place.local
            && discr_place.projection.len() == arg_place.projection.len() + 1
            && discr_place.projection.first() == Some(&NormalizedPlaceElem::Deref)
            && discr_place.projection[1..] == arg_place.projection
    }

    fn try_align_lowered_discriminant_value_goto(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let dt = &self.de.basic_blocks[bb_t];
        let ds = &self.bc.basic_blocks[bb_s];
        let loc_t = (bb_t, dt.statements.len());
        let source_loc = (bb_s, ds.statements.len());

        let mir::TerminatorKind::Goto { target: target_t } = dt.terminator().kind else {
            return false;
        };
        let mir::TerminatorKind::Call {
            func,
            target: Some(target_s),
            ..
        } = &ds.terminator().kind
        else {
            return false;
        };

        if !self.is_discriminant_value_call(func) {
            return false;
        }
        if dt.statements.is_empty()
            || self.target_to_source.get(&(bb_t, dt.statements.len() - 1)).copied()
                != Some(Origin::Source(source_loc))
        {
            return false;
        }

        self.mark_origin_with_phase(loc_t, Origin::SplitFrom(source_loc), PointPhase::PostEffect(source_loc));
        self.align_successor(target_t, *target_s);
        true
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
                self.mark_block_statements_with_phase(
                    block.bb,
                    Origin::SplitFrom(src_drop),
                    PointPhase::PreEffect(src_drop),
                );
            }

            let loc_t = (block.bb, self.de.basic_blocks[block.bb].statements.len());
            self.mark_origin_with_phase(
                loc_t,
                Origin::SplitFrom(src_drop),
                block.terminator_phase.with_source(src_drop),
            );
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
                let origin = self.source_chain_origin(bb_s, cur_s);
                self.mark_origin(loc_t, origin);
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

            if !self.has_single_source_predecessor(next_s) {
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

            if !self.has_single_source_predecessor(next) {
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
                let origin = self.source_chain_origin(bb_s, cur_s);
                self.mark_origin(loc_t, origin);
                self.recurse_direct(tt, ts);
                return true;
            }

            // Drop elaboration can prove a specific value is uninitialized on a
            // normal return path and replace the corresponding source `Drop`
            // terminator by a plain `goto` to the drop's return block. The
            // target goto has no effect of its own, so Polonius point queries
            // should observe the point before the source drop effect.
            if let (
                mir::TerminatorKind::Goto { target: target_t },
                mir::TerminatorKind::Drop {
                    target: target_s, ..
                },
            ) = (&tt.kind, &ts.kind)
                && self.drop_target_successor_equiv(*target_t, *target_s)
            {
                let src_drop = (cur_s, ds.statements.len());
                self.mark_origin_with_phase(
                    loc_t,
                    Origin::SplitFrom(src_drop),
                    PointPhase::PreEffect(src_drop),
                );
                self.align_blocks(*target_t, *target_s);
                return true;
            }

            // Cleanup paths may keep administrative discriminant reads for a
            // moved value even though the source `Drop` itself was eliminated.
            // These inserted blocks are still CFG successors, so map their
            // locations to the point before the eliminated drop effect.
            if let (
                mir::TerminatorKind::Goto { target: target_t },
                mir::TerminatorKind::Drop {
                    target: target_s, ..
                },
            ) = (&tt.kind, &ts.kind)
                && !self.de.basic_blocks[bb_t].statements.is_empty()
                && self.block_has_only_open_drop_administrative_statements(bb_t)
            {
                let src_drop = (cur_s, ds.statements.len());
                self.mark_block_statements_with_phase(
                    bb_t,
                    Origin::SplitFrom(src_drop),
                    PointPhase::PreEffect(src_drop),
                );
                self.mark_origin_with_phase(
                    loc_t,
                    Origin::SplitFrom(src_drop),
                    PointPhase::PreEffect(src_drop),
                );
                self.align_blocks(*target_t, *target_s);
                return true;
            }

            let mir::TerminatorKind::Drop { target: next_s, .. } = ts.kind else {
                return false;
            };

            if !self.has_single_source_predecessor(next_s) {
                return false;
            }

            cur_s = next_s;
        }

        false
    }

    fn drop_target_successor_equiv(&self, target_t: BasicBlock, target_s: BasicBlock) -> bool {
        let data_t = &self.de.basic_blocks[target_t];
        let data_s = &self.bc.basic_blocks[target_s];

        data_t.statements.is_empty()
            && data_s.statements.is_empty()
            && self.terminator_shape_equiv(data_t.terminator(), data_s.terminator())
    }

    fn parse_drop_flag_test(
        &self,
        bb_t: BasicBlock,
        term: &mir::Terminator<'tcx>,
        source_place: &NormalizedPlace,
    ) -> Option<(BasicBlock, BasicBlock, Vec<usize>)> {
        let mir::TerminatorKind::SwitchInt { discr, targets } = &term.kind else {
            return None;
        };

        let mut administrative_statements = Vec::new();
        match discr {
            mir::Operand::Copy(place) | mir::Operand::Move(place)
                if place.projection.is_empty() && self.is_synthetic_bool_local(place.local) => {},
            mir::Operand::Copy(place) | mir::Operand::Move(place)
                if place.projection.is_empty()
                    && self.is_synthetic_local(place.local)
                    && let Some(idx) =
                        self.find_discriminant_stmt_for_place(bb_t, place.local, source_place) =>
            {
                administrative_statements.push(idx);
            },
            _ => return None,
        }

        let all_targets = targets.all_targets();
        if all_targets.len() != 2 {
            return None;
        }

        Some((all_targets[0], all_targets[1], administrative_statements))
    }

    fn find_discriminant_stmt_for_place(
        &self,
        bb_t: BasicBlock,
        local: Local,
        source_place: &NormalizedPlace,
    ) -> Option<usize> {
        self.de.basic_blocks[bb_t].statements.iter().enumerate().rev().find_map(|(idx, stmt)| {
            let mir::StatementKind::Assign(box (lhs, mir::Rvalue::Discriminant(place))) = &stmt.kind else {
                return None;
            };
            (lhs.projection.is_empty()
                && lhs.local == local
                && same_or_subplace(source_place, &self.normalize_place(*place)))
            .then_some(idx)
        })
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
        self.has_single_source_predecessor(succ).then_some(succ)
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
                func: func_t,
                args: args_t,
                destination: dest_t,
                target: target_t,
                unwind: unwind_t,
                ..
            },
            mir::TerminatorKind::Call {
                func: func_s,
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
            || !self.call_core_equiv(func_t, args_t, *dest_t, func_s, args_s, *dest_s)
        {
            return false;
        }

        self.mark_origin((bb_t, dt.statements.len()), Origin::Source((bb_s, ds.statements.len())));

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

        if !self.call_core_equiv(func_t, args_t, *dest_t, func_s, args_s, *dest_s) {
            return false;
        }

        self.mark_origin((bb_t, dt.statements.len()), Origin::Source((bb_s, ds.statements.len())));

        if let (Some(bb_t), Some(bb_s)) = (unwind_target(*unwind_t), unwind_target(*unwind_s)) {
            self.align_blocks(bb_t, bb_s);
        }

        true
    }

    fn is_unwind_resume_block(&self, bb: BasicBlock) -> bool {
        self.bc.basic_blocks[bb].statements.is_empty()
            && matches!(self.bc.basic_blocks[bb].terminator().kind, mir::TerminatorKind::UnwindResume)
    }
}
