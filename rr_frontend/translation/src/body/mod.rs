// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

mod checked_op_analysis;

use rr_rustc_interface::hir;
use rr_rustc_interface::middle::ty;

use crate::base::*;
use crate::types;

pub mod signature;
mod translation;

/// Get the syntypes of function arguments for a procedure call.
pub fn get_arg_syntypes_for_procedure_call<'tcx, 'def>(
    tcx: ty::TyCtxt<'tcx>,
    ty_translator: &types::LocalTX<'def, 'tcx>,
    callee_did: hir::def_id::DefId,
    ty_params: &[ty::GenericArg<'tcx>],
) -> Result<Vec<radium::SynType>, TranslationError<'tcx>> {
    // Get the type of the callee, fully instantiated
    let full_ty: ty::EarlyBinder<ty::Ty<'tcx>> = tcx.type_of(callee_did);
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
