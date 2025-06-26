// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rr_rustc_interface::index::IndexVec;
use rr_rustc_interface::middle::mir;

/// A data structure to store the non-virtual CFG edges of a MIR body.
pub(crate) struct RealEdges {
    successors: IndexVec<mir::BasicBlock, Vec<mir::BasicBlock>>,
    predecessors: IndexVec<mir::BasicBlock, Vec<mir::BasicBlock>>,
}

impl RealEdges {
    pub(crate) fn new(body: &mir::Body<'_>) -> Self {
        let mut successors: IndexVec<_, Vec<_>> = body.basic_blocks.iter().map(|_| Vec::new()).collect();
        let mut predecessors: IndexVec<_, Vec<_>> = body.basic_blocks.iter().map(|_| Vec::new()).collect();

        for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
            let targets = real_targets(bb_data.terminator());
            for &target in &targets {
                successors[bb].push(target);
                predecessors[target].push(bb);
            }
        }

        Self {
            successors,
            predecessors,
        }
    }

    #[must_use]
    pub(crate) fn successors(&self, bb: mir::BasicBlock) -> &[mir::BasicBlock] {
        &self.successors[bb]
    }

    #[must_use]
    pub(crate) fn predecessors(&self, bb: mir::BasicBlock) -> &[mir::BasicBlock] {
        &self.predecessors[bb]
    }
}

fn real_targets(terminator: &mir::Terminator<'_>) -> Vec<mir::BasicBlock> {
    match &terminator.kind {
        mir::TerminatorKind::Goto { target } | mir::TerminatorKind::Assert { target, .. } => {
            vec![*target]
        },

        mir::TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),

        mir::TerminatorKind::CoroutineDrop
        | mir::TerminatorKind::Return
        | mir::TerminatorKind::Unreachable
        | mir::TerminatorKind::UnwindResume
        | mir::TerminatorKind::UnwindTerminate(_)
        | mir::TerminatorKind::TailCall { .. } => vec![],

        mir::TerminatorKind::Drop { target, .. } => vec![*target],

        mir::TerminatorKind::Call { target, .. } => match target {
            Some(target) => vec![*target],
            None => vec![],
        },

        mir::TerminatorKind::FalseEdge { real_target, .. }
        | mir::TerminatorKind::FalseUnwind { real_target, .. } => {
            vec![*real_target]
        },

        mir::TerminatorKind::Yield { resume, .. } => vec![*resume],

        mir::TerminatorKind::InlineAsm { targets, .. } => vec![targets[0]],
    }
}
