// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet};

use log::{debug, info};
use rr_rustc_interface::data_structures::graph::dominators::dominators;
use rr_rustc_interface::index::{Idx as _, IndexVec};
use rr_rustc_interface::middle::mir;

use crate::environment::mir_utils::real_edges::RealEdges;
use crate::environment::procedure::BasicBlockIndex;

/// Walk up the CFG graph an collect all basic blocks that belong to the loop body.
fn collect_loop_body(
    head: BasicBlockIndex,
    back_edge_source: BasicBlockIndex,
    real_edges: &RealEdges,
    body: &mut HashSet<BasicBlockIndex>,
) {
    let mut work_queue = vec![back_edge_source];
    body.insert(back_edge_source);

    while let Some(current) = work_queue.pop() {
        for &predecessor in real_edges.predecessors(current) {
            if body.contains(&predecessor) {
                continue;
            }
            body.insert(predecessor);
            if predecessor != head {
                work_queue.push(predecessor);
            }
        }
    }

    debug!("Loop body (head={:?}): {:?}", head, body);
}

/// Returns the list of basic blocks ordered in the topological order (ignoring back edges).
fn order_basic_blocks(
    mir: &mir::Body<'_>,
    real_edges: &RealEdges,
    back_edges: &HashSet<(BasicBlockIndex, BasicBlockIndex)>,
    loop_depth: &dyn Fn(BasicBlockIndex) -> usize,
) -> Vec<BasicBlockIndex> {
    fn visit(
        real_edges: &RealEdges,
        back_edges: &HashSet<(BasicBlockIndex, BasicBlockIndex)>,
        loop_depth: &dyn Fn(BasicBlockIndex) -> usize,
        current: BasicBlockIndex,
        sorted_blocks: &mut Vec<BasicBlockIndex>,
        permanent_mark: &mut IndexVec<BasicBlockIndex, bool>,
        temporary_mark: &mut IndexVec<BasicBlockIndex, bool>,
    ) {
        if permanent_mark[current] {
            return;
        }

        assert!(!temporary_mark[current], "Not a DAG!");
        temporary_mark[current] = true;

        let curr_depth = loop_depth(current);

        // We want to order the loop body before exit edges
        let successors: (Vec<_>, Vec<_>) =
            real_edges.successors(current).iter().partition(|&&bb| loop_depth(bb) < curr_depth);

        for group in <[_; 2]>::from(successors) {
            for &successor in group {
                if back_edges.contains(&(current, successor)) {
                    continue;
                }
                visit(
                    real_edges,
                    back_edges,
                    loop_depth,
                    successor,
                    sorted_blocks,
                    permanent_mark,
                    temporary_mark,
                );
            }
        }

        permanent_mark[current] = true;

        sorted_blocks.push(current);
    }

    let basic_blocks = &mir.basic_blocks;
    let mut sorted_blocks = Vec::new();
    let mut permanent_mark = IndexVec::<BasicBlockIndex, bool>::from_elem_n(false, basic_blocks.len());
    let mut temporary_mark = permanent_mark.clone();

    while let Some(index) = permanent_mark.iter().position(|x| !*x) {
        let index = BasicBlockIndex::new(index);
        visit(
            real_edges,
            back_edges,
            loop_depth,
            index,
            &mut sorted_blocks,
            &mut permanent_mark,
            &mut temporary_mark,
        );
    }

    sorted_blocks.reverse();
    sorted_blocks
}

/// Struct that contains information about all loops in the procedure.
#[derive(Clone)]
pub(crate) struct ProcedureLoops {
    /// A list of basic blocks that are loop heads.
    loop_heads: HashSet<BasicBlockIndex>,
    /// A map from loop heads to the corresponding bodies.
    loop_bodies: HashMap<BasicBlockIndex, HashSet<BasicBlockIndex>>,
    ordered_loop_bodies: HashMap<BasicBlockIndex, Vec<BasicBlockIndex>>,
    /// A map from loop bodies to the ordered vector of enclosing loop heads (from outer to inner).
    enclosing_loop_heads: HashMap<BasicBlockIndex, Vec<BasicBlockIndex>>,
}

impl ProcedureLoops {
    pub(crate) fn new(mir: &mir::Body<'_>, real_edges: &RealEdges) -> Self {
        let dominators = dominators(&mir.basic_blocks);

        let mut back_edges: HashSet<(_, _)> = HashSet::new();
        for bb in mir.basic_blocks.indices() {
            for successor in real_edges.successors(bb) {
                if dominators.dominates(*successor, bb) {
                    back_edges.insert((bb, *successor));
                    debug!("Loop head: {:?}", successor);
                }
            }
        }

        let mut loop_bodies = HashMap::new();
        for &(source, target) in &back_edges {
            let body = loop_bodies.entry(target).or_insert_with(HashSet::new);
            collect_loop_body(target, source, real_edges, body);
        }

        let mut enclosing_loop_heads_set: HashMap<BasicBlockIndex, HashSet<BasicBlockIndex>> = HashMap::new();
        for (&loop_head, loop_body) in &loop_bodies {
            for &block in loop_body {
                let heads_set = enclosing_loop_heads_set.entry(block).or_default();
                heads_set.insert(loop_head);
            }
        }

        let loop_heads: HashSet<_> = loop_bodies.keys().copied().collect();
        let mut loop_head_depths = HashMap::new();
        for &loop_head in &loop_heads {
            loop_head_depths.insert(loop_head, enclosing_loop_heads_set[&loop_head].len());
        }

        let mut enclosing_loop_heads = HashMap::new();
        for (&block, loop_heads) in &enclosing_loop_heads_set {
            let mut heads: Vec<BasicBlockIndex> = loop_heads.iter().copied().collect();
            heads.sort_by_key(|bbi| loop_head_depths[bbi]);
            enclosing_loop_heads.insert(block, heads);
        }

        let get_loop_depth = |bb: BasicBlockIndex| {
            enclosing_loop_heads
                .get(&bb)
                .and_then(|heads| heads.last())
                .map_or(0, |bb_head| loop_head_depths[bb_head])
        };

        let ordered_blocks = order_basic_blocks(mir, real_edges, &back_edges, &get_loop_depth);
        let block_order: HashMap<BasicBlockIndex, usize> =
            ordered_blocks.iter().copied().enumerate().map(|(i, v)| (v, i)).collect();
        debug!("ordered_blocks: {:?}", ordered_blocks);

        let mut ordered_loop_bodies = HashMap::new();
        for (&loop_head, loop_body) in &loop_bodies {
            let mut ordered_body: Vec<_> = loop_body.iter().copied().collect();
            ordered_body.sort_by_key(|bb| block_order[bb]);
            debug_assert_eq!(loop_head, ordered_body[0]);
            ordered_loop_bodies.insert(loop_head, ordered_body);
        }

        // In Rust, the evaluation of a loop guard may happen over several blocks.
        // Here, we identify the CFG blocks that decide whether to exit from the loop or not.
        // They are those blocks in the loop that:
        // 1. have a SwitchInt terminator (TODO: can we remove this condition?)
        // 2. have an out-edge that exits from the loop
        let mut loop_exit_blocks = HashMap::new();
        for &loop_head in &loop_heads {
            let loop_head_depth = loop_head_depths[&loop_head];
            let loop_body = &loop_bodies[&loop_head];
            let ordered_loop_body = &ordered_loop_bodies[&loop_head];

            let mut exit_blocks = vec![];
            let mut border = HashSet::new();
            border.insert(loop_head);

            for &curr_bb in ordered_loop_body {
                debug_assert!(border.contains(&curr_bb));

                // Decide if this block has an exit edge
                let term = mir[curr_bb].terminator();
                let is_switch_int = matches!(term.kind, mir::TerminatorKind::SwitchInt { .. });
                let has_exit_edge =
                    real_edges.successors(curr_bb).iter().any(|&bb| get_loop_depth(bb) < loop_head_depth);
                if is_switch_int && has_exit_edge {
                    exit_blocks.push(curr_bb);
                }

                border.remove(&curr_bb);

                for &succ_bb in real_edges.successors(curr_bb) {
                    if !back_edges.contains(&(curr_bb, succ_bb)) {
                        // Consider only forward in-loop edges
                        if loop_body.contains(&succ_bb) {
                            border.insert(succ_bb);
                        }
                    }
                }
            }

            loop_exit_blocks.insert(loop_head, exit_blocks);
        }
        debug!("loop_exit_blocks: {:?}", loop_exit_blocks);

        Self {
            loop_heads,
            loop_bodies,
            ordered_loop_bodies,
            enclosing_loop_heads,
        }
    }

    pub(crate) fn dump_body_head(&self) {
        info!("loop heads: {:?}", self.loop_heads);
        for (head, bodies) in &self.loop_bodies {
            info!("loop {:?} -> {:?}", head, bodies);
        }
    }

    #[must_use]
    pub(crate) fn is_loop_head(&self, bbi: BasicBlockIndex) -> bool {
        self.loop_heads.contains(&bbi)
    }

    /// Get the loop head, if any
    /// Note: a loop head **is** loop head of itself
    #[must_use]
    pub(crate) fn get_loop_head(&self, bbi: BasicBlockIndex) -> Option<BasicBlockIndex> {
        self.enclosing_loop_heads.get(&bbi).and_then(|heads| heads.last()).copied()
    }

    /// Get the (topologically ordered) body of a loop, given a loop head
    #[must_use]
    pub(crate) fn get_loop_body(&self, loop_head: BasicBlockIndex) -> &[BasicBlockIndex] {
        debug_assert!(self.is_loop_head(loop_head));
        &self.ordered_loop_bodies[&loop_head]
    }
}
