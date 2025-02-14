// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

mod checked_op_analysis;

use std::collections::{btree_map, BTreeMap, HashMap, HashSet};

use log::{info, trace, warn};
use radium::coq;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::interpret::{ConstValue, ErrorHandled, Scalar};
use rr_rustc_interface::middle::mir::tcx::PlaceTy;
use rr_rustc_interface::middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, BorrowKind, Constant, ConstantKind, Local, Location, Mutability,
    NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, StatementKind, Terminator, TerminatorKind,
    UnOp, VarDebugInfoContents,
};
use rr_rustc_interface::middle::ty::fold::TypeFolder;
use rr_rustc_interface::middle::ty::{ConstKind, Ty, TyKind};
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{abi, ast, middle};
use typed_arena::Arena;

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::environment::{dump_borrowck_info, polonius_info, Environment};
use crate::spec_parsers::parse_utils::ParamLookup;
use crate::spec_parsers::verbose_function_spec_parser::{
    ClosureMetaInfo, FunctionRequirements, FunctionSpecParser, VerboseFunctionSpecParser,
};
use crate::traits::{registry, resolution};
use crate::{base, consts, procedures, regions, search, traits, types};

pub mod signature;
mod translation;

/// Get the syntypes of function arguments for a procedure call.
pub fn get_arg_syntypes_for_procedure_call<'tcx, 'def>(
    tcx: ty::TyCtxt<'tcx>,
    ty_translator: &types::LocalTX<'def, 'tcx>,
    callee_did: DefId,
    ty_params: &[ty::GenericArg<'tcx>],
) -> Result<Vec<radium::SynType>, TranslationError<'tcx>> {
    let caller_did = ty_translator.get_proc_did();

    // Get the type of the callee, fully instantiated
    let full_ty: ty::EarlyBinder<Ty<'tcx>> = tcx.type_of(callee_did);
    let full_ty = full_ty.instantiate(tcx, ty_params);

    // We create a dummy scope in order to make the lifetime lookups succeed, since we only want
    // syntactic types here.
    // Since we do the substitution of the generics above, we should translate generics and
    // traits in the caller's scope.
    let scope = ty_translator.scope.borrow();
    let param_env: ty::ParamEnv<'tcx> = tcx.param_env(scope.did);
    let callee_state = types::CalleeState::new(&param_env, &scope.generic_scope);
    let mut dummy_state = types::STInner::CalleeTranslation(callee_state);

    let mut syntypes = Vec::new();
    match full_ty.kind() {
        ty::TyKind::FnDef(_, _) => {
            let sig = full_ty.fn_sig(tcx);
            for ty in sig.inputs().skip_binder() {
                let st = ty_translator.translator.translate_type_to_syn_type(*ty, &mut dummy_state)?;
                syntypes.push(st);
            }
        },
        ty::TyKind::Closure(_, args) => {
            let clos_args = args.as_closure();
            let sig = clos_args.sig();
            let pre_sig = sig.skip_binder();
            // we also need to add the closure argument here

            let tuple_ty = clos_args.tupled_upvars_ty();
            match clos_args.kind() {
                ty::ClosureKind::Fn | ty::ClosureKind::FnMut => {
                    syntypes.push(radium::SynType::Ptr);
                },
                ty::ClosureKind::FnOnce => {
                    let st =
                        ty_translator.translator.translate_type_to_syn_type(tuple_ty, &mut dummy_state)?;
                    syntypes.push(st);
                },
            }
            for ty in pre_sig.inputs() {
                let st = ty_translator.translator.translate_type_to_syn_type(*ty, &mut dummy_state)?;
                syntypes.push(st);
            }
        },
        _ => unimplemented!(),
    }

    Ok(syntypes)
}
