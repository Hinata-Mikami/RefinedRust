// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Align locations from `mir_drops_elaborated_and_const_checked` back to the
//! borrow-checked MIR. The current mapper is intentionally conservative: it
//! handles cleanup post-borrowck rewrites, synthetic locals introduced by drop
//! elaboration and box-deref elaboration, dead drops, and the common
//! conditional-drop rewrite. Open-drop subgraphs still need a dedicated
//! matcher.

#![allow(dead_code)]

use rr_rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};
use rr_rustc_interface::middle::mir::{self, BasicBlock, Body, Local};

pub type TargetLoc = (BasicBlock, usize);
pub type SourceLoc = (BasicBlock, usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Origin {
    Source(SourceLoc),
    Inserted,
    SplitFrom(SourceLoc),
    FoldedFrom(SourceLoc),
}

#[derive(Debug, Default)]
pub struct MappingResult {
    pub target_to_source: FxHashMap<TargetLoc, Origin>,
    pub unmapped_targets: Vec<TargetLoc>,
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
    Other(String),
}

struct Mapper<'a, 'tcx> {
    bc: &'a Body<'tcx>,
    de: &'a Body<'tcx>,
    source_local_count: usize,
    target_to_source: FxHashMap<TargetLoc, Origin>,
    visited: FxHashSet<(BasicBlock, BasicBlock)>,
    box_deref_aliases: FxHashMap<Local, BoxDerefAlias>,
    bc_predecessors: FxHashMap<BasicBlock, Vec<BasicBlock>>,
    de_predecessors: FxHashMap<BasicBlock, Vec<BasicBlock>>,
}

#[derive(Clone)]
struct BoxDerefAlias {
    place: NormalizedPlace,
    source_loc: Option<SourceLoc>,
}

struct OpenDropBlock {
    bb: BasicBlock,
    mark_statements: bool,
}

struct OpenDropMatch {
    blocks: Vec<OpenDropBlock>,
    leaf_blocks: Vec<BasicBlock>,
}

impl<'a, 'tcx> Mapper<'a, 'tcx> {
    fn new(bc: &'a Body<'tcx>, de: &'a Body<'tcx>) -> Self {
        Self {
            bc,
            de,
            source_local_count: bc.local_decls.len(),
            target_to_source: Default::default(),
            visited: Default::default(),
            box_deref_aliases: Default::default(),
            bc_predecessors: compute_predecessors(bc),
            de_predecessors: compute_predecessors(de),
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

        MappingResult {
            target_to_source: self.target_to_source,
            unmapped_targets,
        }
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

            while i_s < data_s.statements.len() && self.is_cleanup_erased_source_stmt(&data_s.statements[i_s])
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

        self.target_to_source.insert(loc_t, Origin::Inserted);
    }

    fn recurse_direct(&mut self, tt: &mir::Terminator<'tcx>, ts: &mir::Terminator<'tcx>) {
        match (&tt.kind, &ts.kind) {
            (
                mir::TerminatorKind::Goto { target: target_t },
                mir::TerminatorKind::Goto { target: target_s },
            ) => self.align_blocks(*target_t, *target_s),

            (
                mir::TerminatorKind::Goto { target: target_t },
                mir::TerminatorKind::FalseEdge { real_target, .. }
                | mir::TerminatorKind::FalseUnwind { real_target, .. },
            ) => self.align_blocks(*target_t, *real_target),

            (
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
                },
                mir::TerminatorKind::Assert {
                    target: target_s,
                    unwind: unwind_s,
                    ..
                },
            ) => {
                self.align_blocks(*target_t, *target_s);
                if let (Some(bb_t), Some(bb_s)) = (unwind_target(unwind_t), unwind_target(unwind_s)) {
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
                if let (Some(bb_t), Some(bb_s)) = (unwind_target(unwind_t), unwind_target(unwind_s)) {
                    self.align_blocks(bb_t, bb_s);
                }
            },

            (
                mir::TerminatorKind::Drop {
                    target: target_t,
                    unwind: unwind_t,
                    ..
                },
                mir::TerminatorKind::Drop {
                    target: target_s,
                    unwind: unwind_s,
                    ..
                },
            ) => {
                self.align_blocks(*target_t, *target_s);
                if let (Some(bb_t), Some(bb_s)) = (unwind_target(unwind_t), unwind_target(unwind_s)) {
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
        self.target_to_source
            .insert((bb_t, self.de.basic_blocks[bb_t].statements.len()), Origin::SplitFrom(src_drop));

        let drop_data = &self.de.basic_blocks[drop_bb];
        for i in 0..drop_data.statements.len() {
            self.target_to_source.entry((drop_bb, i)).or_insert(Origin::Inserted);
        }
        self.target_to_source
            .insert((drop_bb, drop_data.statements.len()), Origin::SplitFrom(src_drop));

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

            if let (Some(bb_t), Some(bb_s)) = (unwind_target(&unwind_t), unwind_target(&unwind_s)) {
                self.align_blocks(bb_t, bb_s);
            }
            return true;
        }

        false
    }

    fn try_align_open_drop_subgraph(&mut self, bb_t: BasicBlock, bb_s: BasicBlock) -> bool {
        let Some(target_root_place) = self.open_drop_root_place(bb_t) else {
            return false;
        };

        let Some(source_drop_bb) = self.find_linear_source_drop_matching(bb_s, &target_root_place) else {
            return false;
        };

        let ts = self.bc.basic_blocks[source_drop_bb].terminator();
        let mir::TerminatorKind::Drop {
            place: source_place,
            target: ret_s,
            unwind: unwind_s,
            ..
        } = &ts.kind
        else {
            return false;
        };

        let source_place = self.normalize_source_place(*source_place);
        let Some(open_drop_match) = self.match_open_drop_target(bb_t, &source_place) else {
            return false;
        };

        for &leaf_bb in &open_drop_match.leaf_blocks {
            let leaf_term = self.de.basic_blocks[leaf_bb].terminator();
            let mir::TerminatorKind::Drop {
                target: ret_t,
                unwind: unwind_t,
                ..
            } = &leaf_term.kind
            else {
                return false;
            };

            if !self.unwind_actions_compatible(unwind_t, unwind_s) {
                return false;
            }

            let _ = ret_t;
        }

        let src_drop = (source_drop_bb, self.bc.basic_blocks[source_drop_bb].statements.len());
        for block in open_drop_match.blocks {
            if block.mark_statements {
                let data = &self.de.basic_blocks[block.bb];
                for i in 0..data.statements.len() {
                    self.target_to_source.insert((block.bb, i), Origin::SplitFrom(src_drop));
                }
            }

            let loc_t = (block.bb, self.de.basic_blocks[block.bb].statements.len());
            self.target_to_source.insert(loc_t, Origin::SplitFrom(src_drop));
        }

        for leaf_bb in open_drop_match.leaf_blocks {
            let leaf_term = self.de.basic_blocks[leaf_bb].terminator();
            let mir::TerminatorKind::Drop {
                target: ret_t,
                unwind: unwind_t,
                ..
            } = &leaf_term.kind
            else {
                return false;
            };

            self.align_blocks(*ret_t, *ret_s);
            if let (Some(bb_t), Some(bb_s)) = (unwind_target(unwind_t), unwind_target(unwind_s)) {
                self.align_blocks(bb_t, bb_s);
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

    fn match_open_drop_target(
        &self,
        entry_bb: BasicBlock,
        source_place: &NormalizedPlace,
    ) -> Option<OpenDropMatch> {
        let mut blocks = Vec::new();
        let mut current = entry_bb;
        let mut allow_existing_statements = true;

        for _ in 0..self.de.basic_blocks.len() {
            if let Some(next_bb) = self.open_drop_goto_target(current, allow_existing_statements) {
                if !allow_existing_statements && !self.has_unique_target_predecessor(next_bb, current) {
                    return None;
                }

                blocks.push(OpenDropBlock {
                    bb: current,
                    mark_statements: false,
                });
                current = next_bb;
                allow_existing_statements = false;
                continue;
            }

            if let Some((root_place, targets)) = self.open_drop_dispatch_info(current) {
                if root_place != *source_place {
                    return None;
                }

                let mut leaf_blocks = Vec::new();
                blocks.push(OpenDropBlock {
                    bb: current,
                    mark_statements: true,
                });

                for target_bb in targets {
                    let Some(leaf_place) = self.open_drop_leaf_place(target_bb, false) else {
                        return None;
                    };
                    if !self.has_unique_target_predecessor(target_bb, current)
                        || !same_or_subplace(source_place, &leaf_place)
                    {
                        return None;
                    }

                    blocks.push(OpenDropBlock {
                        bb: target_bb,
                        mark_statements: false,
                    });
                    leaf_blocks.push(target_bb);
                }

                return Some(OpenDropMatch {
                    blocks,
                    leaf_blocks,
                });
            }

            if let Some(leaf_place) = self.open_drop_leaf_place(current, allow_existing_statements)
                && same_or_subplace(source_place, &leaf_place)
                && leaf_place != *source_place
            {
                blocks.push(OpenDropBlock {
                    bb: current,
                    mark_statements: false,
                });
                return Some(OpenDropMatch {
                    blocks,
                    leaf_blocks: vec![current],
                });
            }

            return None;
        }

        None
    }

    fn open_drop_root_place(&self, entry_bb: BasicBlock) -> Option<NormalizedPlace> {
        let mut current = entry_bb;
        let mut allow_existing_statements = true;

        for _ in 0..self.de.basic_blocks.len() {
            if let Some(next_bb) = self.open_drop_goto_target(current, allow_existing_statements) {
                if !allow_existing_statements && !self.has_unique_target_predecessor(next_bb, current) {
                    return None;
                }

                current = next_bb;
                allow_existing_statements = false;
                continue;
            }

            if let Some((root_place, _)) = self.open_drop_dispatch_info(current) {
                return Some(root_place);
            }

            if let Some(leaf_place) = self.open_drop_leaf_place(current, allow_existing_statements) {
                return Some(leaf_place);
            }

            return None;
        }

        None
    }

    fn find_linear_source_drop_matching(
        &self,
        start_bb: BasicBlock,
        target_root_place: &NormalizedPlace,
    ) -> Option<BasicBlock> {
        let mut current = start_bb;

        for _ in 0..self.bc.basic_blocks.len() {
            let term = self.bc.basic_blocks[current].terminator();
            let next = match &term.kind {
                mir::TerminatorKind::Drop { place, target, .. } => {
                    let source_place = self.normalize_source_place(*place);
                    if same_or_subplace(&source_place, target_root_place) {
                        return Some(current);
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
                    let source_place = self.normalize_source_place(*place);
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

    fn open_drop_goto_target(&self, bb: BasicBlock, allow_existing_statements: bool) -> Option<BasicBlock> {
        let data = &self.de.basic_blocks[bb];
        if !allow_existing_statements && !data.statements.is_empty() {
            return None;
        }

        match &data.terminator().kind {
            mir::TerminatorKind::Goto { target } => Some(*target),
            _ => None,
        }
    }

    fn open_drop_dispatch_info(&self, bb: BasicBlock) -> Option<(NormalizedPlace, Vec<BasicBlock>)> {
        let data = &self.de.basic_blocks[bb];
        if data.statements.len() != 1 {
            return None;
        }

        let mir::StatementKind::Assign(box (lhs, mir::Rvalue::Discriminant(discr_place))) =
            &data.statements[0].kind
        else {
            return None;
        };
        if !lhs.projection.is_empty() || !self.is_synthetic_local(lhs.local) {
            return None;
        }
        let root_place = self.normalize_place(*discr_place);

        let mir::TerminatorKind::SwitchInt { discr, targets } = &data.terminator().kind else {
            return None;
        };
        let local = match discr {
            mir::Operand::Copy(place) | mir::Operand::Move(place)
                if place.projection.is_empty() && place.local == lhs.local =>
            {
                place.local
            },
            _ => return None,
        };

        let _ = local;
        Some((root_place, targets.all_targets().to_vec()))
    }

    fn open_drop_leaf_place(
        &self,
        bb: BasicBlock,
        allow_existing_statements: bool,
    ) -> Option<NormalizedPlace> {
        let data = &self.de.basic_blocks[bb];
        if !allow_existing_statements && !data.statements.is_empty() {
            return None;
        }

        let mir::TerminatorKind::Drop { place, .. } = &data.terminator().kind else {
            return None;
        };
        Some(self.normalize_place(*place))
    }

    fn has_unique_target_predecessor(&self, bb: BasicBlock, predecessor: BasicBlock) -> bool {
        matches!(self.de_predecessors.get(&bb), Some(preds) if preds.len() == 1 && preds[0] == predecessor)
    }

    fn unwind_actions_compatible(&self, target: &mir::UnwindAction, source: &mir::UnwindAction) -> bool {
        match (unwind_target(target), unwind_target(source)) {
            (Some(_), Some(_)) => true,
            (None, None) => true,
            _ => false,
        }
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

        let local = match discr {
            mir::Operand::Copy(place) | mir::Operand::Move(place)
                if place.projection.is_empty() && self.is_synthetic_bool_local(place.local) =>
            {
                place.local
            },
            _ => return None,
        };

        let _ = local;
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
                if !self.is_cleanup_erased_source_stmt(stmt) && self.stmt_equiv(target_stmt, stmt) {
                    return Some(loc);
                }
                idx += 1;
            }

            let Some(next_bb) = self.single_linear_successor(bb) else {
                return None;
            };
            bb = next_bb;
            idx = 0;
        }

        None
    }

    fn single_linear_successor(&self, bb: BasicBlock) -> Option<BasicBlock> {
        let succ = normal_successor(self.bc.basic_blocks[bb].terminator())?;
        (self.bc_predecessors.get(&succ)?.len() == 1).then_some(succ)
    }

    fn stmt_equiv(&self, target: &mir::Statement<'tcx>, source: &mir::Statement<'tcx>) -> bool {
        self.statement_key(target, MirFlavor::Target) == self.statement_key(source, MirFlavor::Source)
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
            ) => {
                self.operand_key(discr_t, MirFlavor::Target) == self.operand_key(discr_s, MirFlavor::Source)
                    && switch_values(targets_t) == switch_values(targets_s)
            },

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
                    && self.operand_key(cond_t, MirFlavor::Target)
                        == self.operand_key(cond_s, MirFlavor::Source)
                    && format!("{msg_t:?}") == format!("{msg_s:?}")
            },

            (Drop { place: place_t, .. }, Drop { place: place_s, .. }) => {
                self.normalize_place(*place_t) == self.normalize_source_place(*place_s)
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
                self.operand_key(func_t, MirFlavor::Target) == self.operand_key(func_s, MirFlavor::Source)
                    && args_t.len() == args_s.len()
                    && args_t.iter().zip(args_s.iter()).all(|(arg_t, arg_s)| {
                        self.operand_key(&arg_t.node, MirFlavor::Target)
                            == self.operand_key(&arg_s.node, MirFlavor::Source)
                    })
                    && self.place_key(*dest_t, MirFlavor::Target)
                        == self.place_key(*dest_s, MirFlavor::Source)
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

        self.box_deref_aliases.insert(lhs.local, BoxDerefAlias {
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
            mir::StatementKind::SetDiscriminant { place, .. } => {
                self.place_uses_box_deref_of_local(**place, local, MirFlavor::Source)
            },
            mir::StatementKind::PlaceMention(place)
            | mir::StatementKind::Retag(_, place)
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
            mir::StatementKind::SetDiscriminant { place, .. } => {
                self.place_uses_alias_with_origin(**place, source_loc, MirFlavor::Target)
            },
            mir::StatementKind::PlaceMention(place)
            | mir::StatementKind::Retag(_, place)
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
            mir::Rvalue::Use(operand)
            | mir::Rvalue::Repeat(operand, _)
            | mir::Rvalue::WrapUnsafeBinder(operand, _) => {
                self.operand_uses_box_deref_of_local(operand, local, flavor)
            },
            mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Discriminant(place)
            | mir::Rvalue::CopyForDeref(place) => self.place_uses_box_deref_of_local(*place, local, flavor),
            mir::Rvalue::BinaryOp(_, operands) => {
                self.operand_uses_box_deref_of_local(&operands.as_ref().0, local, flavor)
                    || self.operand_uses_box_deref_of_local(&operands.as_ref().1, local, flavor)
            },
            mir::Rvalue::UnaryOp(_, operand) | mir::Rvalue::Cast(_, operand, _) => {
                self.operand_uses_box_deref_of_local(operand, local, flavor)
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
            mir::Rvalue::Use(operand)
            | mir::Rvalue::Repeat(operand, _)
            | mir::Rvalue::WrapUnsafeBinder(operand, _) => {
                self.operand_uses_alias_with_origin(operand, source_loc, flavor)
            },
            mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Discriminant(place)
            | mir::Rvalue::CopyForDeref(place) => {
                self.place_uses_alias_with_origin(*place, source_loc, flavor)
            },
            mir::Rvalue::BinaryOp(_, operands) => {
                self.operand_uses_alias_with_origin(&operands.as_ref().0, source_loc, flavor)
                    || self.operand_uses_alias_with_origin(&operands.as_ref().1, source_loc, flavor)
            },
            mir::Rvalue::UnaryOp(_, operand) | mir::Rvalue::Cast(_, operand, _) => {
                self.operand_uses_alias_with_origin(operand, source_loc, flavor)
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

    fn is_cleanup_erased_source_stmt(&self, stmt: &mir::Statement<'tcx>) -> bool {
        match &stmt.kind {
            mir::StatementKind::AscribeUserType(_, _)
            | mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Coverage(_) => true,
            mir::StatementKind::Assign(box (_, mir::Rvalue::Ref(_, mir::BorrowKind::Fake(_), _))) => true,
            _ => false,
        }
    }

    fn statement_key(&self, stmt: &mir::Statement<'tcx>, flavor: MirFlavor) -> String {
        match &stmt.kind {
            mir::StatementKind::Assign(box (lhs, rhs)) => {
                format!("Assign({}, {})", self.place_key(*lhs, flavor), self.rvalue_key(rhs, flavor))
            },
            mir::StatementKind::StorageLive(local) => format!("StorageLive({:?})", local),
            mir::StatementKind::StorageDead(local) => format!("StorageDead({:?})", local),
            mir::StatementKind::FakeRead(fake_read) => format!("FakeRead({fake_read:?})"),
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                format!("SetDiscriminant({}, {})", self.place_key(**place, flavor), variant_index.as_usize())
            },
            mir::StatementKind::PlaceMention(place) => {
                format!("PlaceMention({})", self.place_key(**place, flavor))
            },
            mir::StatementKind::Retag(kind, place) => {
                format!("Retag({kind:?}, {})", self.place_key(**place, flavor))
            },
            mir::StatementKind::AscribeUserType(place, variance) => {
                let (place, projection) = place.as_ref();
                format!("AscribeUserType({}, {projection:?}, {variance:?})", self.place_key(*place, flavor))
            },
            mir::StatementKind::Intrinsic(intrinsic) => format!("Intrinsic({intrinsic:?})"),
            mir::StatementKind::Coverage(kind) => format!("Coverage({kind:?})"),
            mir::StatementKind::ConstEvalCounter => "ConstEvalCounter".to_owned(),
            mir::StatementKind::BackwardIncompatibleDropHint { place, reason } => {
                format!("BackwardIncompatibleDropHint({}, {reason:?})", self.place_key(**place, flavor))
            },
            mir::StatementKind::Nop => "Nop".to_owned(),
        }
    }

    fn operand_key(&self, operand: &mir::Operand<'tcx>, flavor: MirFlavor) -> String {
        match operand {
            mir::Operand::Copy(place) => format!("Copy({})", self.place_key(*place, flavor)),
            mir::Operand::Move(place) => format!("Move({})", self.place_key(*place, flavor)),
            mir::Operand::Constant(constant) => format!("Const({:?})", constant.const_),
            mir::Operand::RuntimeChecks(checks) => format!("RuntimeChecks({checks:?})"),
        }
    }

    fn rvalue_key(&self, rvalue: &mir::Rvalue<'tcx>, flavor: MirFlavor) -> String {
        match rvalue {
            mir::Rvalue::Use(operand) => format!("Use({})", self.operand_key(operand, flavor)),
            mir::Rvalue::Ref(_, borrow_kind, place) => {
                format!("Ref({borrow_kind:?}, {})", self.place_key(*place, flavor))
            },
            mir::Rvalue::RawPtr(mutability, place) => {
                format!("RawPtr({mutability:?}, {})", self.place_key(*place, flavor))
            },
            mir::Rvalue::BinaryOp(op, operands) => format!(
                "BinaryOp({op:?}, {}, {})",
                self.operand_key(&operands.as_ref().0, flavor),
                self.operand_key(&operands.as_ref().1, flavor)
            ),
            mir::Rvalue::UnaryOp(op, operand) => {
                format!("UnaryOp({op:?}, {})", self.operand_key(operand, flavor))
            },
            mir::Rvalue::Discriminant(place) => format!("Discriminant({})", self.place_key(*place, flavor)),
            mir::Rvalue::Aggregate(kind, operands) => {
                let ops = operands
                    .iter()
                    .map(|operand| self.operand_key(operand, flavor))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("Aggregate({:?}, [{}])", kind.as_ref(), ops)
            },
            mir::Rvalue::Cast(kind, operand, ty) => {
                format!("Cast({kind:?}, {}, {ty:?})", self.operand_key(operand, flavor))
            },
            mir::Rvalue::CopyForDeref(place) => format!("CopyForDeref({})", self.place_key(*place, flavor)),
            mir::Rvalue::Repeat(operand, len) => {
                format!("Repeat({}, {len:?})", self.operand_key(operand, flavor))
            },
            mir::Rvalue::WrapUnsafeBinder(operand, ty) => {
                format!("WrapUnsafeBinder({}, {ty:?})", self.operand_key(operand, flavor))
            },
            mir::Rvalue::ThreadLocalRef(def_id) => format!("ThreadLocalRef({def_id:?})"),
        }
    }

    fn place_key(&self, place: mir::Place<'tcx>, flavor: MirFlavor) -> String {
        format_normalized_place(&self.normalize_place_for_flavor(place, flavor))
    }

    fn normalize_place_for_flavor(&self, place: mir::Place<'tcx>, flavor: MirFlavor) -> NormalizedPlace {
        match flavor {
            MirFlavor::Source => self.normalize_source_place(place),
            MirFlavor::Target => self.normalize_place(place),
        }
    }

    fn normalize_source_place(&self, place: mir::Place<'tcx>) -> NormalizedPlace {
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

        self.normalize_source_place(place)
    }

    fn is_synthetic_local(&self, local: Local) -> bool {
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
        mir::TerminatorKind::Goto { target } | mir::TerminatorKind::Assert { target, .. } => vec![*target],
        mir::TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
        mir::TerminatorKind::Drop { target, .. } => vec![*target],
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

fn normal_successor(terminator: &mir::Terminator<'_>) -> Option<BasicBlock> {
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

fn normalize_projection_elem(elem: mir::PlaceElem<'_>) -> NormalizedPlaceElem {
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
        _ => NormalizedPlaceElem::Other(format!("{elem:?}")),
    }
}

fn unwind_target(action: &mir::UnwindAction) -> Option<BasicBlock> {
    match action {
        mir::UnwindAction::Cleanup(bb) => Some(*bb),
        mir::UnwindAction::Continue | mir::UnwindAction::Unreachable | mir::UnwindAction::Terminate(_) => {
            None
        },
    }
}

fn format_normalized_place(place: &NormalizedPlace) -> String {
    let mut out = format!("{:?}", place.local);
    for projection in &place.projection {
        match projection {
            NormalizedPlaceElem::Deref => out.push_str(".*"),
            NormalizedPlaceElem::Field(field) => out.push_str(&format!(".{field}")),
            NormalizedPlaceElem::Index(local) => out.push_str(&format!("[{:?}]", local)),
            NormalizedPlaceElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => out.push_str(&format!("[const {offset}/{min_length}/{from_end}]")),
            NormalizedPlaceElem::Subslice { from, to, from_end } => {
                out.push_str(&format!("[{from}..{to};{from_end}]"));
            },
            NormalizedPlaceElem::Downcast(variant) => out.push_str(&format!(" as {variant}")),
            NormalizedPlaceElem::Other(other) => out.push_str(&format!("<{other}>")),
        }
    }
    out
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
