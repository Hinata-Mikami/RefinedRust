// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{btree_map, BTreeMap, HashMap, HashSet};

use log::{info, trace, warn};
use radium::coq;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::interpret::{ConstValue, ErrorHandled, Scalar};
use rr_rustc_interface::middle::mir::tcx::PlaceTy;
use rr_rustc_interface::middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, BorrowKind, Constant, ConstantKind, Local, LocalKind, Location,
    Mutability, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, StatementKind, Terminator,
    TerminatorKind, UnOp, VarDebugInfoContents,
};
use rr_rustc_interface::middle::ty::fold::TypeFolder;
use rr_rustc_interface::middle::ty::{ConstKind, Ty, TyKind};
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{abi, ast, middle};
use typed_arena::Arena;

use super::TX;
use crate::base::*;
use crate::body::checked_op_analysis::CheckedOpLocalAnalysis;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::environment::{dump_borrowck_info, polonius_info, Environment};
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::spec_parsers::parse_utils::ParamLookup;
use crate::spec_parsers::verbose_function_spec_parser::{
    ClosureMetaInfo, FunctionRequirements, FunctionSpecParser, VerboseFunctionSpecParser,
};
use crate::traits::{registry, resolution};
use crate::{base, consts, procedures, regions, search, traits, types};

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Parse the attributes on spec closure `did` as loop annotations and add it as an invariant
    /// to the generated code.
    pub(super) fn parse_attributes_on_loop_spec_closure(
        &self,
        loop_head: BasicBlock,
        did: Option<DefId>,
    ) -> radium::LoopSpec {
        // for now: just make invariants True.

        // need to do:
        // - find out the locals in the right order, make parameter names for them. based on their type and
        //   initialization status, get the refinement type.
        // - output/pretty-print this map when generating the typing proof of each function. [done]
        //  + should not be a separate definition, but rather a "set (.. := ...)" with a marker type so
        //    automation can find it.

        // representation of loop invariants:
        // - introduce parameters for them.

        let mut rfn_binders = Vec::new();
        let prop_body = radium::IProp::True;

        // determine invariant on initialization:
        // - we need this both for the refinement invariant (though this could be removed if we make uninit
        //   generic over the refinement)
        // - in order to establish the initialization invariant in each loop iteration, since we don't have
        //   proper subtyping for uninit => maybe we could fix this too by making uninit variant in the
        //   refinement type? then we could have proper subtyping lemmas.
        //  + to bring it to the right refinement type initially, maybe have some automation /
        //  annotation
        // TODO: consider changing it like that.
        //
        // Note that StorageDead will not help us for determining initialization/ making it invariant, since
        // it only applies to full stack slots, not individual paths. one thing that makes it more
        // complicated in the frontend: initialization may in practice also be path-dependent.
        //  - this does not cause issues with posing a too strong loop invariant,
        //  - but this poses an issue for annotations
        //
        //

        // get locals
        for (_, name, ty) in &self.fn_locals {
            // get the refinement type
            let mut rfn_ty = ty.get_rfn_type();
            // wrap it in place_rfn, since we reason about places
            rfn_ty = coq::term::Type::PlaceRfn(Box::new(rfn_ty));

            // determine their initialization status
            //let initialized = true; // TODO
            // determine the actual refinement type for the current initialization status.

            let rfn_name = format!("r_{}", name);
            rfn_binders.push(coq::binder::Binder::new(Some(rfn_name), rfn_ty));
        }

        // TODO what do we do about stuff connecting borrows?
        if let Some(did) = did {
            let attrs = self.env.get_attributes(did);
            info!("attrs for loop {:?}: {:?}", loop_head, attrs);
        } else {
            info!("no attrs for loop {:?}", loop_head);
        }

        let pred = radium::IPropPredicate::new(rfn_binders, prop_body);
        radium::LoopSpec {
            func_predicate: pred,
        }
    }

    /// Find the optional `DefId` of the closure giving the invariant for the loop with head `head_bb`.
    pub(super) fn find_loop_spec_closure(
        &self,
        head_bb: BasicBlock,
    ) -> Result<Option<DefId>, TranslationError<'tcx>> {
        let bodies = self.proc.loop_info().get_loop_body(head_bb);
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // we go in order through the bodies in order to not stumble upon an annotation for a
        // nested loop!
        for body in bodies {
            // check that we did not go below a nested loop
            if self.proc.loop_info().get_loop_head(*body) == Some(head_bb) {
                // check the statements for an assignment
                let data = basic_blocks.get(*body).unwrap();
                for stmt in &data.statements {
                    if let StatementKind::Assign(box (pl, _)) = stmt.kind {
                        if let Some(did) = self.is_spec_closure_local(pl.local)? {
                            return Ok(Some(did));
                        }
                    }
                }
            }
        }

        Ok(None)
    }
}
