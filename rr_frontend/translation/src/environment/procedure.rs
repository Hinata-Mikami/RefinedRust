// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashSet;
use std::rc::Rc;

use log::trace;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use crate::environment::mir_utils::real_edges::RealEdges;
use crate::environment::{loops, Environment};

/// Index of a Basic Block
pub type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub struct Procedure<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    proc_def_id: DefId,
    mir: Rc<mir::Body<'tcx>>,
    real_edges: RealEdges,
    loop_info: loops::ProcedureLoops,
    reachable_basic_blocks: HashSet<mir::BasicBlock>,
    //nonspec_basic_blocks: HashSet<BasicBlock>,
}

impl<'tcx> Procedure<'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    pub fn new(env: &Environment<'tcx>, proc_def_id: DefId) -> Self {
        trace!("Encoding procedure {:?}", proc_def_id);
        let tcx = env.tcx();
        let mir = env.local_mir(proc_def_id.expect_local());
        let real_edges = RealEdges::new(&mir);
        let reachable_basic_blocks = build_reachable_basic_blocks(&mir, &real_edges);
        //let nonspec_basic_blocks = build_nonspec_basic_blocks(&mir, &real_edges, &tcx);
        let loop_info = loops::ProcedureLoops::new(&mir, &real_edges);

        Self {
            tcx,
            proc_def_id,
            mir,
            real_edges,
            loop_info,
            reachable_basic_blocks,
            //nonspec_basic_blocks,
        }
    }

    #[must_use]
    pub const fn loop_info(&self) -> &loops::ProcedureLoops {
        &self.loop_info
    }

    /// Get definition ID of the procedure.
    #[must_use]
    pub const fn get_id(&self) -> DefId {
        self.proc_def_id
    }

    /// Get the MIR of the procedure
    #[must_use]
    pub fn get_mir(&self) -> &mir::Body<'tcx> {
        &self.mir
    }

    /// Get the typing context.
    #[must_use]
    pub const fn get_tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    #[must_use]
    pub fn get_def_path(&self) -> String {
        let def_path = self.tcx.def_path(self.proc_def_id);
        let mut crate_name = self.tcx.crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate_verbose());
        crate_name
    }

    /// Check whether the block is reachable
    #[must_use]
    pub fn is_reachable_block(&self, bbi: BasicBlockIndex) -> bool {
        self.reachable_basic_blocks.contains(&bbi)
    }

    #[must_use]
    pub fn is_panic_block(&self, bbi: BasicBlockIndex) -> bool {
        let mir::TerminatorKind::Call { func, .. } = &self.mir[bbi].terminator().kind else {
            return false;
        };

        let mir::Operand::Constant(box mir::Constant { literal, .. }) = func else {
            return false;
        };

        let mir::ConstantKind::Ty(c) = literal else {
            return false;
        };

        let ty::TyKind::FnDef(def_id, ..) = c.ty().kind() else {
            return false;
        };

        // let func_proc_name = self.tcx.absolute_item_path_str(def_id);
        let func_proc_name = self.tcx.def_path_str(*def_id);

        func_proc_name == "std::rt::begin_panic"
            || func_proc_name == "core::panicking::panic"
            || func_proc_name == "core::panicking::panic_fmt"
    }

    /// Get the successors of a basic block.
    #[must_use]
    pub fn successors(&self, bbi: mir::BasicBlock) -> &[mir::BasicBlock] {
        self.real_edges.successors(bbi)
    }

    /// Get the predecessors of a basic block.
    #[must_use]
    pub fn predecessors(&self, bbi: mir::BasicBlock) -> &[mir::BasicBlock] {
        self.real_edges.predecessors(bbi)
    }
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_reachable_basic_blocks(mir: &mir::Body, real_edges: &RealEdges) -> HashSet<mir::BasicBlock> {
    let mut reachable_basic_blocks: HashSet<mir::BasicBlock> = HashSet::new();
    let mut visited: HashSet<mir::BasicBlock> = HashSet::new();
    let mut to_visit: Vec<mir::BasicBlock> = vec![mir.basic_blocks.indices().next().unwrap()];

    while let Some(source) = to_visit.pop() {
        if visited.contains(&source) {
            continue;
        }

        visited.insert(source);
        reachable_basic_blocks.insert(source);

        for &target in real_edges.successors(source) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }
        }
    }

    reachable_basic_blocks
}
