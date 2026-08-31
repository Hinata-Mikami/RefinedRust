// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, BTreeSet};

use log::{info, trace};
use radium::specs::traits::ReqInfo as _;
use radium::{code, coq, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::span;

use super::{PreparedFunctionCall, TX};
use crate::base::*;
use crate::body::function_translation::{ExprInfo, ExprWithInfo};
use crate::body::mir_lowering::{
    MirConstantTranslation as _, MirPlaceTranslation as _, MirRvalueTranslation as _, MirTranslationCtx as _,
    MirTypeTranslation as _, ProcedureInst, TranslationKey,
};
use crate::environment::borrowck::facts;
use crate::error::Message;
use crate::regions::{CallAssignmentInputs, CallEffectDiscovery, CallRegionInputs};
use crate::traits::registry::ResolvedTraitReq;
use crate::traits::resolution;
use crate::types::STInner;
use crate::{procedures, search, types};

/// Get the syntypes of function arguments for a procedure call.
pub(crate) fn get_arg_syntypes_for_procedure_call<'tcx, 'def>(
    tcx: ty::TyCtxt<'tcx>,
    ty_translator: &types::TX<'def, 'tcx>,
    caller_env: &types::scope::Params<'tcx, 'def>,
    typing_env: &ty::TypingEnv<'tcx>,
    callee_did: DefId,
    ty_params: &[ty::GenericArg<'tcx>],
) -> Result<Vec<lang::SynType>, TranslationError> {
    // Get the type of the callee, fully instantiated
    let full_ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = tcx.type_of(callee_did);
    let full_ty = full_ty.instantiate(tcx, ty_params).skip_norm_wip();

    // We create a dummy scope in order to make the lifetime lookups succeed, since we only want
    // syntactic types here.
    // Since we do the substitution of the generics above, we should translate generics and
    // traits in the caller's scope.
    let callee_state = types::CalleeState::new(*typing_env, caller_env);
    let mut dummy_state = STInner::CalleeTranslation(callee_state);

    let mut syntypes = Vec::new();
    match full_ty.kind() {
        ty::TyKind::FnDef(_, _) => {
            let sig = full_ty.fn_sig(tcx);
            for ty in sig.inputs().skip_binder() {
                let st = ty_translator.translate_type_to_syn_type(*ty, &mut dummy_state)?;
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
                    syntypes.push(lang::SynType::Ref);
                },
                ty::ClosureKind::FnOnce => {
                    let st = ty_translator.translate_type_to_syn_type(tuple_ty, &mut dummy_state)?;
                    syntypes.push(st);
                },
            }

            trace!("assembling arg syntypes for closure call: sig inputs={:?}", pre_sig.inputs());
            let tupled_inputs = pre_sig.inputs();
            assert_eq!(tupled_inputs.len(), 1);
            let input_tuple_ty = tupled_inputs[0];
            if let ty::TyKind::Tuple(args) = input_tuple_ty.kind() {
                for ty in *args {
                    let st = ty_translator.translate_type_to_syn_type(ty, &mut dummy_state)?;
                    syntypes.push(st);
                }
            } else {
                unreachable!();
            }
        },
        _ => unimplemented!(),
    }

    Ok(syntypes)
}

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    fn caller_has_type_param(&self, index: u32) -> bool {
        let mut did = Some(self.proc.get_id());
        while let Some(current_did) = did {
            let generics = self.tcx.generics_of(current_did);
            if generics.own_params.iter().any(|param| {
                param.index == index && matches!(param.kind, ty::GenericParamDefKind::Type { .. })
            }) {
                return true;
            }
            did = generics.parent;
        }
        false
    }

    fn validate_inline_type_instantiation(
        &self,
        ty_params: ty::GenericArgsRef<'tcx>,
    ) -> Result<(), TranslationError> {
        for arg in ty_params {
            let ty::GenericArgKind::Type(arg_ty) = arg.kind() else {
                continue;
            };
            let ty::TyKind::Param(param) = arg_ty.kind() else {
                return Err(TranslationError::ErrorReported(
                    self.tcx.dcx().span_err(
                        self.tcx.def_span(self.proc.get_id()),
                        Message::UnsupportedFeature(
                            "rr::inline function type arguments must be direct type parameters of the caller"
                                .to_owned(),
                        ),
                    ),
                ));
            };
            if !self.caller_has_type_param(param.index) {
                return Err(TranslationError::ErrorReported(self.tcx.dcx().span_err(
                    self.tcx.def_span(self.proc.get_id()),
                    Message::UnsupportedFeature(
                        "rr::inline function type arguments must come from the caller's generic parameters"
                            .to_owned(),
                    ),
                )));
            }
        }
        Ok(())
    }

    fn register_inline_callee_dependencies(
        &mut self,
        callee_did: DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
    ) -> Result<(Vec<String>, Vec<String>), TranslationError> {
        let dependencies = self
            .procedure_registry()
            .lookup_inline_function_dependencies(callee_did)
            .cloned()
            .ok_or_else(|| {
                TranslationError::ErrorReported(
                    self.tcx.dcx().err(Message::UnknownProcedure(format!("{callee_did:?}"))),
                )
            })?;

        if dependencies
            .procedures
            .iter()
            .any(|dependency| matches!(dependency, procedures::InlineProcedureDependency::Function { .. }))
        {
            self.validate_inline_type_instantiation(ty_params)?;
        }

        let mut procedure_locations = Vec::with_capacity(dependencies.procedures.len());
        for dependency in dependencies.procedures {
            match dependency {
                procedures::InlineProcedureDependency::Function {
                    did,
                    args,
                    loc_name,
                } => {
                    let meta = self.procedure_registry().lookup_function(did).ok_or_else(|| {
                        TranslationError::ErrorReported(
                            self.tcx.dcx().err(Message::UnknownProcedure(format!("{did:?}"))),
                        )
                    })?;
                    if meta.get_mode().is_inline() {
                        return Err(TranslationError::ErrorReported(self.tcx.dcx().span_err(
                            self.tcx.def_span(self.proc.get_id()),
                            Message::UnsupportedFeature(
                                "rr::inline functions cannot depend on other rr::inline functions".to_owned(),
                            ),
                        )));
                    }

                    let instantiated_args = self.tcx.mk_args_from_iter(args.iter().map(|arg| {
                        ty::EarlyBinder::bind(self.tcx, arg).instantiate(self.tcx, ty_params).skip_norm_wip()
                    }));
                    let trait_specs =
                        self.resolve_trait_requirements_of_call(did, instantiated_args, true)?;
                    let (expr, _) = self.register_use_procedure(did, instantiated_args, trait_specs)?;
                    let code::Expr::MetaParam(caller_loc_name) = expr else {
                        unreachable!("register_use_procedure always returns a location parameter")
                    };
                    info!("Forwarded inline dependency {loc_name} as caller dependency {caller_loc_name}");
                    procedure_locations.push(caller_loc_name);
                },
                procedures::InlineProcedureDependency::PanicShim { loc_name } => {
                    self.panic_shim_used = true;
                    procedure_locations.push(loc_name);
                },
            }
        }

        let mut static_locations = Vec::with_capacity(dependencies.statics.len());
        for did in dependencies.statics {
            let static_meta = self.const_registry.get_static(self.tcx, &did)?;
            static_locations.push(static_meta.loc_name.clone());
            self.collected_statics.insert(did);
        }

        for layout_ty in dependencies.layout_types {
            let layout_ty = types::scope::erase_regions(self.tcx, layout_ty);
            let instantiated_ty = ty::EarlyBinder::bind(self.tcx, layout_ty)
                .instantiate(self.tcx, ty_params)
                .skip_norm_wip();
            let instantiated_ty = types::scope::erase_regions(self.tcx, instantiated_ty);
            self.ty_translator.translate_type_to_syn_type(instantiated_ty)?;
        }

        Ok((procedure_locations, static_locations))
    }

    /// Internally register that we have used a procedure with a particular instantiation of generics, and
    /// return the code parameter name.
    /// Arguments:
    /// - `callee_did`: the `DefId` of the callee
    /// - `ty_params`: the instantiation for the callee's type parameters
    /// - `trait_specs`: if the callee has any trait assumptions, these are specification parameter terms for
    ///   these traits
    fn register_use_procedure(
        &mut self,
        callee_did: DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
        trait_specs: Vec<ResolvedTraitReq<'tcx, 'def>>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        trace!("enter register_use_procedure callee_did={callee_did:?} ty_params={ty_params:?}");
        // The key does not include the associated types, as the resolution of the associated types
        // should always be unique for one combination of type parameters, as long as we remain in
        // the same environment (which is the case within this procedure).
        // Therefore, already the type parameters are sufficient to distinguish different
        // instantiations.
        let key = types::generate_args_inst_key(self.tcx, ty_params)?;

        let tcx = self.tcx;

        let late_bounds = if let Some(impl_did) = tcx.impl_of_assoc(callee_did)
            && tcx.impl_is_of_trait(impl_did)
        {
            // Fixup: We need a matching workaround as we do in the encoding of the function type
            // in an impl member, to deal with quirks around lifetime elision.
            let expected_sig = self.trait_registry.get_expected_sig_for_impl_fn(callee_did);
            expected_sig.bound_vars().as_slice()
        } else {
            let fn_ty: ty::EarlyBinder<'_, ty::Ty<'_>> = tcx.type_of(callee_did);
            let fn_ty = fn_ty.instantiate(tcx, ty_params).skip_norm_wip();
            let fnsig = fn_ty.fn_sig(tcx);

            fnsig.bound_vars().as_slice()
        };

        // re-quantify
        let quantified_args = self.ty_translator.get_generic_abstraction_for_procedure(
            callee_did,
            ty_params,
            late_bounds,
            trait_specs,
            true,
        )?;
        let expected_num_lft_hints = quantified_args.scope.get_lfts().len();

        let loc_key = key.clone();
        let tup = TranslationKey::Function(OrderedDefId::new(tcx, callee_did), key);
        let res;
        if let Some(proc_use) = self.collected_procedures().get(&tup) {
            res = proc_use.loc_name.clone();
        } else {
            let meta = self.procedure_registry().lookup_function(callee_did).ok_or_else(|| {
                TranslationError::ErrorReported(
                    self.tcx.dcx().err(Message::UnknownProcedure(format!("{:?}", callee_did))),
                )
            })?;
            // explicit instantiation is needed sometimes
            let spec_term = if meta.get_mode().is_inline() {
                if self
                    .procedure_registry()
                    .lookup_function_mode(self.proc.get_id())
                    .is_some_and(procedures::Mode::is_inline)
                {
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().span_err(
                        self.tcx.def_span(self.proc.get_id()),
                        Message::UnsupportedFeature(
                            "rr::inline functions cannot depend on other rr::inline functions".to_owned(),
                        ),
                    )));
                }
                let (dependency_locations, static_locations) =
                    self.register_inline_callee_dependencies(callee_did, ty_params)?;
                let callee_spec =
                    self.procedure_registry().lookup_function_spec(callee_did).ok_or_else(|| {
                        TranslationError::ErrorReported(
                            self.tcx.dcx().err(Message::UnknownProcedure(format!("{:?}", callee_did))),
                        )
                    })?;
                let lifetime_names = callee_spec
                    .get_generics()
                    .get_lfts()
                    .iter()
                    .map(|param| param.lft().to_string())
                    .collect();
                code::UsedProcedureSpec::InlineCode {
                    code_name: meta.get_code_name().to_owned(),
                    lifetime_names,
                    dependency_locations,
                    static_locations,
                }
            } else {
                code::UsedProcedureSpec::Literal(meta.get_spec_name().to_owned())
            };

            let code_name = meta.get_name();
            let loc_name = format!("{}_loc", types::mangle_name_with_tys(code_name, loc_key.as_slice()));

            let syntypes = {
                let scope = self.ty_translator.scope.borrow();
                let typing_env = ty::TypingEnv::post_analysis(tcx, scope.did);
                get_arg_syntypes_for_procedure_call(
                    tcx,
                    self.ty_translator.translator,
                    // note: this is sufficient (without the lifetime map) as we erase lifetimes here anyways
                    &scope.generic_scope,
                    &typing_env,
                    callee_did,
                    ty_params.as_slice(),
                )?
            };

            let fn_inst = quantified_args.fn_scope_inst;

            info!(
                "Registered procedure instance {} of {:?} with {:?} and layouts {:?}",
                loc_name, callee_did, fn_inst, syntypes
            );

            let proc_use =
                code::UsedProcedure::new(loc_name, spec_term, quantified_args.scope, fn_inst, syntypes);

            res = proc_use.loc_name.clone();
            if self
                .procedure_registry()
                .lookup_function_mode(self.proc.get_id())
                .is_some_and(procedures::Mode::is_inline)
            {
                self.direct_call_dependencies.insert(tup.clone(), (callee_did, ty_params));
            }
            self.collected_procedures_mut().insert(tup, proc_use);
        }
        trace!("leave register_use_procedure");
        let inst = ProcedureInst {
            method_params: ty_params,
            type_hint: quantified_args.callee_ty_param_inst,
            lft_hint: quantified_args.callee_lft_param_inst,
            num_of_latebounds: quantified_args.num_of_latebounds,
            expected_num_lft_hints: Some(expected_num_lft_hints),
            mapped_early_regions: BTreeMap::new(),
        };
        Ok((code::Expr::MetaParam(res), Some(ExprInfo::Call(inst))))
    }

    /// Internally register that we have used a trait method with a particular instantiation of
    /// generics, and return the code parameter name.
    fn register_use_trait_method(
        &mut self,
        callee_did: DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
        trait_specs: Vec<ResolvedTraitReq<'tcx, 'def>>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        trace!("enter register_use_trait_method did={:?} ty_params={:?}", callee_did, ty_params);
        // Does not include the associated types in the key; see `register_use_procedure` for an
        // explanation.
        let key = types::generate_args_inst_key(self.tcx, ty_params)?;

        let (method_loc_name, (method_spec_term, spec_scope, spec_inst), mapped_early_regions, method_params) =
            self.ty_translator.register_use_trait_procedure(self.tcx, callee_did, ty_params);

        let tcx = self.tcx;
        let fn_ty: ty::EarlyBinder<'_, ty::Ty<'_>> = tcx.type_of(callee_did);
        let fn_ty = fn_ty.instantiate(tcx, ty_params).skip_norm_wip();
        let fnsig = fn_ty.fn_sig(tcx);

        // re-quantify
        let mut quantified_args = self.ty_translator.get_generic_abstraction_for_procedure(
            callee_did,
            method_params,
            fnsig.bound_vars().as_slice(),
            trait_specs,
            false,
        )?;

        // we add spec_scope and spec_inst as the first lifetimes to quantify in the new scope
        let mut function_spec_scope: specs::GenericScope<'_, _> = spec_scope.into();
        function_spec_scope.append(&quantified_args.scope);
        let expected_num_lft_hints = function_spec_scope.get_lfts().len();

        let ty_param_hint = quantified_args.callee_ty_param_inst;
        let mut lft_param_hint = spec_inst.lft_insts;
        lft_param_hint.append(&mut quantified_args.callee_lft_param_inst);

        let tup = TranslationKey::Function(OrderedDefId::new(tcx, callee_did), key);
        let res;
        if let Some(proc_use) = self.collected_procedures().get(&tup) {
            res = proc_use.loc_name.clone();
        } else {
            // TODO: should we use ty_params or method_params?
            let syntypes = {
                let scope = self.ty_translator.scope.borrow();
                let typing_env = ty::TypingEnv::post_analysis(tcx, scope.did);
                get_arg_syntypes_for_procedure_call(
                    tcx,
                    self.ty_translator.translator,
                    &scope.generic_scope,
                    &typing_env,
                    callee_did,
                    ty_params.as_slice(),
                )?
            };

            let fn_inst = quantified_args.fn_scope_inst;

            info!(
                "Registered procedure instance {} of {:?} with {:?} and layouts {:?}",
                method_loc_name, callee_did, fn_inst, syntypes
            );

            let proc_use = code::UsedProcedure::new(
                method_loc_name,
                method_spec_term,
                function_spec_scope,
                fn_inst,
                syntypes,
            );

            trace!("register_use_trait_method: generated proc_use for {callee_did:?}: {proc_use:?}");

            res = proc_use.loc_name.clone();
            self.collected_procedures_mut().insert(tup, proc_use);
        }
        trace!("leave register_use_trait_method");

        let inst = ProcedureInst {
            method_params: ty_params,
            type_hint: ty_param_hint,
            lft_hint: lft_param_hint,
            num_of_latebounds: quantified_args.num_of_latebounds,
            expected_num_lft_hints: Some(expected_num_lft_hints),
            mapped_early_regions,
        };
        Ok((code::Expr::MetaParam(res), Some(ExprInfo::Call(inst))))
    }

    fn create_closure_impl_abstraction(
        &self,
        info: &procedures::ClosureImplInfo<'tcx, 'def>,
        closure_did: DefId,
        closure_args: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
        kind: ty::ClosureKind,
        params: ty::GenericArgsRef<'tcx>,
    ) -> types::AbstractedGenerics<'def> {
        trace!("enter create_closure_impl_abstraction with closure_args={closure_args:?}, params={params:?}");

        // we lift the scope, all the generics below to the trait impl, not to the trait method itself.
        let mut new_scope = specs::GenericScope::empty();

        assert!(info.scope.get_surrounding_ty_params_with_assocs().params.is_empty());
        assert!(info.scope.get_surrounding_trait_requirements().is_empty());

        for ty in &info.scope.get_direct_ty_params().params {
            let mut ty = ty.clone();
            ty.set_origin(specs::TyParamOrigin::SurroundingImpl);
            new_scope.add_ty_param(ty);
        }
        for req in info.scope.get_direct_trait_requirements() {
            let mut req = *req;
            req.set_origin(specs::TyParamOrigin::SurroundingImpl);
            new_scope.add_trait_requirement(req);
        }
        for lft in info.scope.get_lfts() {
            new_scope.add_lft_param(lft.to_owned());
        }
        // also add the lifetime for the call function itself as a dummy
        if kind == ty::ClosureKind::Fn || kind == ty::ClosureKind::FnMut {
            new_scope.add_lft_param(specs::LftParam::new(
                coq::Ident::new("_ref_lft"),
                specs::LftParamOrigin::FunctionRebound,
            ));
            // this does not have an instantiation hint
        }
        trace!("new_scope={new_scope:?}");

        // for the instantiation hints, we proceed as follows:
        // - the type parameters are the same as on the surrounding function
        // - similarly, the lifetime parameters carry over
        // - but in addition, we have to add the capture lifetimes
        // - as well as the lifetime of the closure arg (for Fn/FnMut)

        // instantiate the type parameters directly with the parameters of the surrounding function
        // (identity, the type parameters are the same)
        let ty_param_inst_hint: Vec<specs::Type<'def>> =
            new_scope.identity_instantiation().get_all_ty_params_with_assocs();
        let mut lft_param_inst_hint: Vec<specs::Lft> = Vec::new();

        // compute the instantiation of late bounds
        let late_inst = {
            let mut scope = self.ty_translator.scope.borrow_mut();
            let mut state = STInner::InFunction(&mut scope);
            self.trait_registry.compute_closure_late_bound_inst(&mut state, closure_args, params)
        };
        for region in late_inst {
            let translated_region = self.ty_translator.translate_region(region);
            lft_param_inst_hint.push(translated_region);
        }
        // compute the instantiation of external regions
        let external_inst = {
            let mut scope = self.ty_translator.scope.borrow_mut();
            let mut state = STInner::InFunction(&mut scope);
            self.trait_registry.compute_closure_extern_inst(&mut state, closure_did, closure_args)
        };
        for r in external_inst {
            let lft = self.ty_translator.translate_region(r);
            lft_param_inst_hint.push(lft);
        }

        // we just requantify all the generics and directly instantiate
        let fn_scope_inst: specs::GenericScopeInst<'def> = new_scope.identity_instantiation();

        let res = types::AbstractedGenerics {
            scope: new_scope,
            fn_scope_inst,
            num_of_latebounds: 0,
            callee_lft_param_inst: lft_param_inst_hint,
            callee_ty_param_inst: ty_param_inst_hint,
        };
        trace!("leave create_closure_impl_abstraction with res={res:?}");
        res
    }

    /// Internally register that we have used a closure impl with a particular instantiation of generics, and
    /// return the code parameter name.
    /// Arguments:
    /// - `callee_did`: the `DefId` of the callee
    /// - `ty_params`: the instantiation for the callee's type parameters
    /// - `trait_specs`: if the callee has any trait assumptions, these are specification parameter terms for
    ///   these traits
    fn register_use_closure(
        &mut self,
        closure_did: DefId,
        closure_args: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
        call_fn_did: DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
        _trait_specs: Vec<ResolvedTraitReq<'tcx, 'def>>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        trace!(
            "enter register_use_closure closure_did={closure_did:?}, closure_args={closure_args:?}, call_fn_did={call_fn_did:?}, ty_params={ty_params:?}"
        );

        let trait_did = self.tcx.parent(call_fn_did);
        let Some(closure_kind) = search::get_closure_kind_of_trait_did(self.tcx, trait_did) else {
            self.tcx.dcx().span_bug(
                self.tcx.def_span(trait_did),
                format!("expected closure trait, found non-closure trait: {trait_did:?}"),
            )
        };

        trace!("determined closure kind: {closure_kind:?}");

        // The key does not include the associated types, as the resolution of the associated types
        // should always be unique for one combination of type parameters, as long as we remain in
        // the same environment (which is the case within this procedure).
        // Therefore, already the type parameters are sufficient to distinguish different
        // instantiations.
        let key = types::generate_args_inst_key(self.tcx, ty_params)?;

        let info = self.procedure_registry().lookup_closure_info(closure_did).unwrap();

        let quantified_scope =
            self.create_closure_impl_abstraction(info, closure_did, closure_args, closure_kind, ty_params);
        let expected_num_lft_hints = quantified_scope.scope.get_lfts().len();

        let loc_key = key.clone();
        let tup = TranslationKey::Function(OrderedDefId::new(self.tcx, call_fn_did), key);
        let res;
        if let Some(proc_use) = self.collected_procedures().get(&tup) {
            res = proc_use.loc_name.clone();
        } else {
            let (_, meta) =
                self.trait_registry.lookup_closure_impl(closure_did, closure_kind).ok_or_else(|| {
                    TranslationError::ErrorReported(self.tcx.dcx().span_err(
                        self.tcx.def_span(closure_did),
                        Message::ClosureImplNotRegisteredWithRefinedRust(closure_kind),
                    ))
                })?;

            // explicit instantiation is needed sometimes
            let spec_term = code::UsedProcedureSpec::Literal(meta.get_spec_name().to_owned());

            let code_name = meta.get_name();
            let loc_name = format!("{}_loc", types::mangle_name_with_tys(code_name, loc_key.as_slice()));

            let syntypes = {
                let scope = self.ty_translator.scope.borrow();
                let typing_env = ty::TypingEnv::post_analysis(self.tcx, scope.did);
                get_arg_syntypes_for_procedure_call(
                    self.tcx,
                    self.ty_translator.translator,
                    // note: this is sufficient (without the lifetime map) as we erase lifetimes here anyways
                    &scope.generic_scope,
                    &typing_env,
                    call_fn_did,
                    ty_params.as_slice(),
                )?
            };

            info!(
                "Registered procedure instance of closure impl {loc_name} of ({closure_did:?}, {closure_kind:?}) with {:?} and layouts {:?}",
                quantified_scope.fn_scope_inst, syntypes
            );

            let proc_use = code::UsedProcedure::new(
                loc_name,
                spec_term,
                quantified_scope.scope,
                quantified_scope.fn_scope_inst,
                syntypes,
            );

            res = proc_use.loc_name.clone();
            self.collected_procedures_mut().insert(tup, proc_use);
        }
        trace!("leave register_use_closure");
        let inst = ProcedureInst {
            method_params: ty_params,
            type_hint: quantified_scope.callee_ty_param_inst,
            lft_hint: quantified_scope.callee_lft_param_inst,
            num_of_latebounds: quantified_scope.num_of_latebounds,
            expected_num_lft_hints: Some(expected_num_lft_hints),
            mapped_early_regions: BTreeMap::new(),
        };
        Ok((code::Expr::MetaParam(res), Some(ExprInfo::Call(inst))))
    }

    /// Resolve the trait requirements of a function call.
    /// The target of the call, [did], should have been resolved as much as possible,
    /// as the requirements of a call can be different depending on which impl we consider.
    fn resolve_trait_requirements_of_call(
        &self,
        did: DefId,
        params: ty::GenericArgsRef<'tcx>,
        include_self: bool,
    ) -> Result<Vec<ResolvedTraitReq<'tcx, 'def>>, TranslationError> {
        let mut scope = self.ty_translator.scope.borrow_mut();
        let mut state = STInner::InFunction(&mut scope);
        // NB: include the `Self` requirement to handle trait default fns
        self.trait_registry
            .resolve_trait_requirements_in_state(&mut state, did, params, include_self)
    }

    /// Translate the use of an `FnDef`, registering that the current function needs to link against
    /// a particular monomorphization of the used function.
    pub(crate) fn translate_fn_def_use(
        &mut self,
        ty: ty::Ty<'tcx>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        let ty::TyKind::FnDef(defid, params) = ty.kind() else {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::ExpectedFnDefType)));
        };
        let params = params.no_bound_vars().expect("called FnDef arguments must not contain bound variables");

        let current_typing_env = ty::TypingEnv::post_analysis(self.tcx, self.proc.get_id());

        // Check whether we are calling into a trait method.
        // This works since we did not resolve concrete instances, so this is always an abstract
        // reference to the trait.
        let calling_trait = self.tcx.trait_of_assoc(*defid);

        // Check whether we are calling a plain function or a trait method
        let Some(_) = calling_trait else {
            // resolve the trait requirements
            let trait_spec_terms = self.resolve_trait_requirements_of_call(*defid, params, true)?;

            // track that we are using this function and generate the Coq location name
            return self.register_use_procedure(*defid, params, trait_spec_terms);
        };

        // Otherwise, we are calling a trait method
        // Resolve the trait instance using trait selection
        let Some((resolved_did, resolved_params, kind)) = resolution::resolve_assoc_item(
            self.tcx,
            current_typing_env,
            *defid,
            params,
            ty::Binder::dummy(()),
        ) else {
            return Err(TranslationError::ErrorReported(
                self.tcx
                    .dcx()
                    .err(Message::TraitResolution(format!("Could not resolve trait {:?}", defid))),
            ));
        };

        info!(
            "Resolved trait method {:?} as {:?} with substs {:?} and kind {:?}",
            defid, resolved_did, resolved_params, kind
        );

        match kind {
            resolution::TraitResolutionKind::UserDefined => {
                // We can statically resolve the particular trait instance,
                // but need to apply the spec to the instance's spec attributes

                // resolve the trait requirements
                let trait_spec_terms =
                    self.resolve_trait_requirements_of_call(resolved_did, resolved_params, true)?;

                self.register_use_procedure(resolved_did, resolved_params, trait_spec_terms)
            },

            resolution::TraitResolutionKind::Param => {
                // In this case, we have already applied it to the spec attribute

                // resolve the trait requirements
                let trait_spec_terms = self.resolve_trait_requirements_of_call(*defid, params, false)?;

                self.register_use_trait_method(resolved_did, resolved_params, trait_spec_terms)
            },

            resolution::TraitResolutionKind::Closure => {
                // Here, we are calling a concretely known and defined closure.
                // We are calling one of the impl shims that we generate!

                // the args are just the closure args. We can ignore them.
                let clos_args = resolved_params.as_closure();

                // resolve the trait requirements, which are also the trait requirements of the
                // auto-generated impl
                let trait_spec_terms = self.resolve_trait_requirements_of_call(*defid, params, true)?;

                self.register_use_closure(resolved_did, clos_args, *defid, params, trait_spec_terms)
            },
        }
    }

    /// Split the type of a function operand of a call expression to a base type and an instantiation for
    /// generics.
    fn call_expr_op_split_inst(
        &self,
        constant: &mir::Const<'tcx>,
    ) -> Result<(DefId, ty::PolyFnSig<'tcx>, ty::GenericArgsRef<'tcx>, ty::PolyFnSig<'tcx>), TranslationError>
    {
        match constant {
            mir::Const::Ty(ty, _) | mir::Const::Val(_, ty) => {
                match ty.kind() {
                    ty::TyKind::FnDef(def, args) => {
                        let args = args
                            .no_bound_vars()
                            .expect("call operand FnDef arguments must not contain bound variables");
                        let ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = self.tcx.type_of(*def);

                        let ty_ident = ty.instantiate_identity().skip_norm_wip();
                        assert!(ty_ident.is_fn());
                        let ident_sig = ty_ident.fn_sig(self.tcx);

                        let ty_instantiated = ty.instantiate(self.tcx, args.as_slice()).skip_norm_wip();
                        let instantiated_sig = ty_instantiated.fn_sig(self.tcx);

                        Ok((*def, ident_sig, args, instantiated_sig))
                    },
                    // TODO handle FnPtr, closure
                    _ => Err(TranslationError::ErrorReported(
                        self.tcx.dcx().err(Message::Unimplemented("implement function pointers".to_owned())),
                    )),
                }
            },
            mir::Const::Unevaluated(_, _) => Err(TranslationError::ErrorReported(
                self.tcx
                    .dcx()
                    .err(Message::Unimplemented("implement ConstantKind::Unevaluated".to_owned())),
            )),
        }
    }

    fn call_func_const_from_terminator<'b>(
        terminator: &'b mir::Terminator<'tcx>,
    ) -> Option<&'b mir::Const<'tcx>> {
        let mir::TerminatorKind::Call {
            func: mir::Operand::Constant(func_constant),
            ..
        } = &terminator.kind
        else {
            return None;
        };
        Some(&func_constant.const_)
    }

    pub(super) fn prepare_inline_call_reborrows(
        &mut self,
        reachable_blocks: &BTreeSet<mir::BasicBlock>,
    ) -> Result<(), TranslationError> {
        for bb in reachable_blocks {
            let data = &self.proc.dropck_mir().basic_blocks[*bb];
            let mir::TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
                continue;
            };
            let mir::Operand::Constant(func_constant) = func else {
                continue;
            };
            let (did, ..) = self.call_expr_op_split_inst(&func_constant.const_)?;
            if !self.procedure_registry.lookup_function_mode(did).is_some_and(procedures::Mode::is_inline) {
                continue;
            }

            for arg in args {
                let (mir::Operand::Move(arg_place) | mir::Operand::Copy(arg_place)) = &arg.node else {
                    continue;
                };
                if !arg_place.projection.is_empty() {
                    continue;
                }

                let assignment = data.statements.iter().enumerate().rev().find_map(|(idx, stmt)| {
                    let mir::StatementKind::Assign(deref!((lhs, rvalue))) = &stmt.kind else {
                        return None;
                    };
                    if !lhs.projection.is_empty() || lhs.local != arg_place.local {
                        return None;
                    }
                    Some((idx, rvalue))
                });
                let Some((statement_index, rvalue)) = assignment else {
                    continue;
                };
                let mir::Rvalue::Ref(_, borrow_kind, _) = rvalue else {
                    continue;
                };
                let mt = match borrow_kind {
                    mir::BorrowKind::Shared => code::Mutability::Shared,
                    mir::BorrowKind::Mut { .. } => code::Mutability::Mut,
                    mir::BorrowKind::Fake(_) => continue,
                };
                let loc = mir::Location {
                    block: *bb,
                    statement_index,
                };
                self.inline_call_reborrows.insert(loc, mt);
            }
        }
        Ok(())
    }

    pub(crate) fn prepare_function_calls(
        &mut self,
        reachable_blocks: &BTreeSet<mir::BasicBlock>,
    ) -> Result<(), TranslationError> {
        struct PendingCall<'tcx, 'def> {
            loc: mir::Location,
            func_expr: code::Expr,
            call_info: ProcedureInst<'tcx, 'def>,
            lhs_ty: mir::PlaceTy<'tcx>,
            is_strong_update: bool,
            output_ty: ty::Binder<'tcx, ty::Ty<'tcx>>,
            normal_target: Option<facts::PointIndex>,
            discovery: CallEffectDiscovery<'tcx>,
        }

        let mut call_locations = Vec::new();
        for bb in reachable_blocks {
            let data = &self.proc.dropck_mir().basic_blocks[*bb];
            let loc = mir::Location {
                block: *bb,
                statement_index: data.statements.len(),
            };
            if let mir::TerminatorKind::Call { func, .. } = &data.terminator().kind
                && !self.is_call_destination_panic(func)
                && self.proc.synthetic_drop_borrow_for_drop_call(loc).is_none()
                && !self.is_call_destination_discriminant(func)
            {
                call_locations.push(loc);
            }
        }

        let mut pending = Vec::new();
        for loc in call_locations {
            let mir::TerminatorKind::Call {
                func,
                destination,
                target,
                ..
            } = &self.proc.dropck_mir().basic_blocks[loc.block].terminator().kind
            else {
                unreachable!();
            };
            let func = func.clone();
            let destination = *destination;
            let target = *target;
            let mir::Operand::Constant(deref!(func_constant)) = &func else {
                return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                    Message::UnsupportedFeature(format!(
                        "RefinedRust does currently not support this kind of call operand (got: {func:?})"
                    )),
                )));
            };
            let source_call = self.proc.source_call_for_target(loc);
            let source_func_constant = source_call.and_then(Self::call_func_const_from_terminator).copied();
            let normal_target = source_call
                .and_then(|terminator| {
                    let mir::TerminatorKind::Call { target, .. } = &terminator.kind else {
                        return None;
                    };
                    *target
                })
                .map(|block| {
                    self.annotations.start_point_for_source(mir::Location {
                        block,
                        statement_index: 0,
                    })
                })
                .or_else(|| {
                    target.map(|block| {
                        self.annotations.start_point_for_target(mir::Location {
                            block,
                            statement_index: 0,
                        })
                    })
                });
            let call_func_constant = source_func_constant.as_ref().unwrap_or(&func_constant.const_);
            if source_func_constant.is_none() {
                self.proc.ensure_region_type(call_func_constant.ty(), || {
                    format!("target call function type at {loc:?} without mapped borrowck source call")
                });
            }

            let (_, _, source_params, inst_sig) = self.call_expr_op_split_inst(call_func_constant)?;
            let (func_expr, info) = if let Some(source_func_constant) = &source_func_constant {
                self.translate_constant(source_func_constant)?
            } else {
                self.translate_operand(&func, false)?
            };
            let Some(ExprInfo::Call(call_info)) = info else {
                unreachable!("Logic error in call target translation");
            };
            let output_ty = inst_sig.output();
            self.proc
                .ensure_region_type(output_ty.skip_binder(), || format!("call output type at {loc:?}"));
            let lhs_ty = self.proc.region_type_of_place(&destination);
            let is_strong_update = !self.check_place_below_reference(&destination);
            let discovery = self.annotations.preregister_call_effects(
                &self.ty_translator,
                self.proc.get_id(),
                loc,
                &CallRegionInputs {
                    source_params,
                    resolved_params: call_info.method_params,
                    source_sig: inst_sig,
                    num_late_bounds: call_info.num_of_latebounds,
                    mapped_early_regions: &call_info.mapped_early_regions,
                },
                &CallAssignmentInputs {
                    lhs_ty,
                    is_strong_update,
                    output_ty,
                    normal_target,
                },
            )?;
            pending.push(PendingCall {
                loc,
                func_expr,
                call_info,
                lhs_ty,
                is_strong_update,
                output_ty,
                normal_target,
                discovery,
            });
        }

        for call in &mut pending {
            self.annotations.classify_call_effects(call.loc, &mut call.discovery);
        }
        for call in &pending {
            self.annotations.register_call_classification_effects(call.loc, &call.discovery);
        }

        for call in pending {
            let annotation_plan = self.annotations.prepare_call_annotation_plan(
                &self.ty_translator,
                call.loc,
                &CallAssignmentInputs {
                    lhs_ty: call.lhs_ty,
                    is_strong_update: call.is_strong_update,
                    output_ty: call.output_ty,
                    normal_target: call.normal_target,
                },
                call.discovery,
            )?;
            self.prepared_calls.insert(call.loc, PreparedFunctionCall {
                func_expr: call.func_expr,
                call_info: call.call_info,
                annotation_plan,
            });
        }
        Ok(())
    }

    pub(crate) fn translate_function_call(
        &mut self,
        func: &mir::Operand<'tcx>,
        args: &[span::Spanned<mir::Operand<'tcx>>],
        destination: &mir::Place<'tcx>,
        target: Option<mir::BasicBlock>,
        unwind: mir::UnwindAction,
        loc: mir::Location,
    ) -> Result<code::Stmt, TranslationError> {
        let PreparedFunctionCall {
            func_expr,
            mut call_info,
            mut annotation_plan,
        } = self
            .prepared_calls
            .remove(&loc)
            .unwrap_or_else(|| panic!("missing prepared ordinary call at {loc:?}: {func:?}"));

        // translate the arguments
        let mut translated_args = Vec::new();
        for arg in args {
            // to_ty is the type the function expects

            //let ty = arg.ty(&self.proc.dropck_mir().local_decls, self.tcx);
            let (translated_arg, _) = self.translate_operand(&arg.node, true)?;
            translated_args.push(translated_arg);
        }

        let lhs_shape_ty = self.shape_type_of_place(destination);
        call_info.lft_hint.append(&mut annotation_plan.late_lft_hints);
        if let Some(expected) = call_info.expected_num_lft_hints
            && call_info.lft_hint.len() != expected
        {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!(
                    "function call at {loc:?} has {} lifetime hints, but its specialized specification expects {expected}",
                    call_info.lft_hint.len()
                ),
            ))));
        }
        for hint in annotation_plan.unconstrained_lft_hints.drain(..) {
            self.translated_fn.add_unconstrained_lft_hint(hint);
        }

        let mut prim_stmts = Vec::new();
        annotation_plan.push_pre_call_stmts(&mut prim_stmts);
        annotation_plan.push_pre_assign_stmts(&mut prim_stmts);

        let ty_hint = call_info.type_hint.into_iter().map(|x| code::RustType::of_type(&x)).collect();
        assert!(
            annotation_plan.assign_expr.is_none(),
            "call assignment unexpectedly requires an expression annotation at {loc:?}"
        );

        let place_st = self.translate_type_to_syn_type(lhs_shape_ty.ty)?;
        let destination = code::CallDestination {
            order: lang::Order::Na1,
            ot: place_st.into(),
            destination: self.translate_place(destination)?,
        };

        let normal = if let Some(target) = target {
            let mut normal_stmts = Vec::new();
            annotation_plan.push_post_assign_stmts(&mut normal_stmts);

            let cont_stmt = self.translate_goto_like(&loc, target)?;
            code::Stmt::Prim(normal_stmts, Box::new(cont_stmt))
        } else {
            code::Stmt::Stuck
        };

        let unwind = self.translate_unwind_action(&loc, unwind)?;

        let call = code::Stmt::Call {
            f: func_expr,
            lfts: call_info.lft_hint,
            tys: ty_hint,
            args: translated_args,
            destination: Box::new(Some(destination)),
            normal: Box::new(normal),
            unwind: Box::new(unwind),
        };

        Ok(code::Stmt::Prim(prim_stmts, Box::new(call)))
    }
}
