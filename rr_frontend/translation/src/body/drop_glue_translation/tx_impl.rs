// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use log::{info, trace};
use radium::{code, coq, lang, specs};
use rr_rustc_interface::abi;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty::TypeFolder as _;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::type_ir::TypeSuperFoldable as _;

use super::DropGlueTX;
use crate::base::*;
use crate::body::function_translation::get_arg_syntypes_for_procedure_call;
use crate::body::mir_lowering::{
    MirConstantTranslation, MirDropTranslation, MirRvalueTranslation, MirTranslationCtx, MirTypeTranslation,
    ProcedureInst, TraitMethodUseData, TranslationKey, make_virtual_drop_glue_method_for_param_from_scope,
};
use crate::error::Message;
use crate::traits::registry::ResolvedTraitReq;
use crate::traits::resolution;
use crate::{procedures, rustcmp, types};

impl<'a, 'def: 'a, 'tcx: 'def> MirTranslationCtx<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {
    type ExprInfo = ProcedureInst<'tcx, 'def>;

    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn body(&self) -> &mir::Body<'tcx> {
        self.body
    }

    fn proc_def_id(&self) -> DefId {
        self.adt_did
    }

    fn procedure_registry(&self) -> &procedures::Scope<'tcx, 'def> {
        self.procedure_registry
    }

    fn normalization_scope_did(&self) -> DefId {
        self.adt_did
    }

    fn variable_map(&self) -> &HashMap<mir::Local, String> {
        &self.variable_map
    }

    fn collected_procedures(&self) -> &HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>> {
        &self.collected_procedures
    }

    fn collected_procedures_mut(&mut self) -> &mut HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>> {
        &mut self.collected_procedures
    }

    fn normalize_place(&self, place: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        *place
    }

    fn permits_non_copy_mir_copy(&self, place: &mir::Place<'tcx>) -> bool {
        // Rustc drop-glue shims copy their `&mut Self` argument into branch-local temporaries before
        // calling `Drop::drop`. These are compiler-generated control-flow aliases, not Rust copies.
        place.projection.is_empty()
            && matches!(self.shape_type_of_place(place).ty.kind(), ty::TyKind::Ref(_, _, ty::Mutability::Mut))
    }
}

struct DropGlueGenericCollector<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    tyvars: BTreeSet<ty::ParamTy>,
    regions: Vec<ty::Region<'tcx>>,
    projections: HashSet<ty::AliasTy<'tcx>>,
}

impl<'tcx> DropGlueGenericCollector<'tcx> {
    fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            tyvars: BTreeSet::new(),
            regions: Vec::new(),
            projections: HashSet::new(),
        }
    }

    fn push_region(&mut self, region: ty::Region<'tcx>) {
        if !self.regions.contains(&region) {
            self.regions.push(region);
        }
    }

    fn get_result(self) -> (BTreeSet<ty::ParamTy>, Vec<ty::Region<'tcx>>, Vec<ty::AliasTy<'tcx>>) {
        let mut projections: Vec<_> = self.projections.into_iter().collect();
        projections.sort_by(|a, b| rustcmp::cmp_alias_ty(self.tcx, a, b));
        (self.tyvars, self.regions, projections)
    }
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for DropGlueGenericCollector<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_ty(&mut self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        match t.kind() {
            ty::TyKind::Param(param) => {
                self.tyvars.insert(*param);
                t
            },
            ty::TyKind::Alias(_, alias_ty) if matches!(alias_ty.kind, ty::AliasTyKind::Projection { .. }) => {
                self.projections.insert(*alias_ty);
                t.super_fold_with(self)
            },
            _ => t.super_fold_with(self),
        }
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        self.push_region(r);
        r
    }
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> DropGlueTX<'a, 'def, 'tcx> {
    fn resolve_trait_requirements_of_call(
        &self,
        did: DefId,
        args: ty::GenericArgsRef<'tcx>,
        include_self: bool,
    ) -> Result<Vec<ResolvedTraitReq<'tcx, 'def>>, TranslationError> {
        let mut state = self.shim_state();
        self.ty_translator.trait_registry().resolve_trait_requirements_in_state(
            &mut state,
            did,
            args,
            include_self,
            true,
        )
    }

    fn register_use_drop_call_procedure(
        &mut self,
        callee_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
        late_bounds: &[ty::BoundVariableKind<'tcx>],
        trait_reqs: Vec<ResolvedTraitReq<'tcx, 'def>>,
    ) -> Result<(code::Expr, ProcedureInst<'tcx, 'def>), TranslationError> {
        trace!("enter register_use_drop_call_procedure callee_did={callee_did:?} args={args:?}");

        let key = types::generate_args_inst_key(self.tcx, args)?;
        let quantified_args = self.get_drop_glue_generic_abstraction_with_mode(
            args,
            late_bounds,
            trait_reqs,
            types::GenericAbstractionMode::FromOwner(callee_did),
        )?;

        let used_key = TranslationKey::Function(OrderedDefId::new(self.tcx, callee_did), key.clone());
        let res;
        if let Some(proc_use) = self.collected_procedures().get(&used_key) {
            res = proc_use.loc_name.clone();
        } else {
            let meta = self.procedure_registry().lookup_function(callee_did).ok_or_else(|| {
                TranslationError::ErrorReported(
                    self.tcx.dcx().err(Message::UnknownProcedure(format!("{:?}", callee_did))),
                )
            })?;
            let spec_term = code::UsedProcedureSpec::Literal(meta.get_spec_name().to_owned());
            let loc_name = format!("{}_loc", types::mangle_name_with_tys(meta.get_name(), key.as_slice()));
            let typing_env = ty::TypingEnv::post_analysis(self.tcx, self.adt_did);
            let syntypes = get_arg_syntypes_for_procedure_call(
                self.tcx,
                self.ty_translator,
                &self.generic_scope,
                &typing_env,
                callee_did,
                args.as_slice(),
            )?;
            let fn_inst = quantified_args.fn_scope_inst;

            info!(
                "Registered drop-glue destructor call instance {} of {:?} with {:?} and layouts {:?}",
                loc_name, callee_did, fn_inst, syntypes
            );

            let proc_use =
                code::UsedProcedure::new(loc_name, spec_term, quantified_args.scope, fn_inst, syntypes);
            res = proc_use.loc_name.clone();
            self.collected_procedures_mut().insert(used_key, proc_use);
        }

        let inst = ProcedureInst {
            method_params: args,
            type_hint: quantified_args.callee_ty_param_inst,
            lft_hint: quantified_args.callee_lft_param_inst,
            num_of_latebounds: quantified_args.num_of_latebounds,
            expected_num_lft_hints: None,
            mapped_early_regions: BTreeMap::new(),
        };
        trace!("leave register_use_drop_call_procedure");
        Ok((code::Expr::MetaParam(res), inst))
    }

    fn translate_drop_call_fn_def_use(
        &mut self,
        ty: ty::Ty<'tcx>,
    ) -> Result<(code::Expr, Option<ProcedureInst<'tcx, 'def>>), TranslationError> {
        let ty::TyKind::FnDef(defid, args) = ty.kind() else {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::ExpectedFnDefType)));
        };
        let args = args.no_bound_vars().expect("drop-call FnDef arguments must not contain bound variables");

        let Some(_) = self.tcx.trait_of_assoc(*defid) else {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!("drop-glue Call terminator only supports destructor trait calls, got {defid:?}"),
            ))));
        };

        let typing_env = ty::TypingEnv::post_analysis(self.tcx, self.adt_did);
        let Some((resolved_did, resolved_args, kind)) =
            resolution::resolve_assoc_item(self.tcx, typing_env, *defid, args, ty::Binder::dummy(()))
        else {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::TraitResolution(
                format!("Could not resolve drop-glue destructor trait call {defid:?}"),
            ))));
        };

        info!(
            "Resolved drop-glue destructor call {:?} as {:?} with args {:?} and kind {:?}",
            defid, resolved_did, resolved_args, kind
        );

        let (func_expr, call_info) = match kind {
            resolution::TraitResolutionKind::UserDefined => {
                let late_bounds = self.get_drop_call_late_bounds(resolved_did, resolved_args);
                let trait_reqs =
                    self.resolve_trait_requirements_of_call(resolved_did, resolved_args, true)?;
                self.register_use_drop_call_procedure(resolved_did, resolved_args, late_bounds, trait_reqs)?
            },
            resolution::TraitResolutionKind::Param => {
                return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                    Message::UnsupportedFeature(format!(
                        "drop-glue destructor calls are expected to resolve to concrete Drop impls, got generic trait resolution for {defid:?} as {resolved_did:?} with args {resolved_args:?}"
                    )),
                )));
            },
            resolution::TraitResolutionKind::Closure => {
                return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                    Message::UnsupportedFeature(format!(
                        "drop-glue destructor calls do not support closure resolution: {defid:?}"
                    )),
                )));
            },
        };

        Ok((func_expr, Some(call_info)))
    }

    fn get_drop_call_late_bounds(
        &self,
        callee_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> &'tcx [ty::BoundVariableKind<'tcx>] {
        if let Some(impl_did) = self.tcx.impl_of_assoc(callee_did)
            && self.tcx.impl_is_of_trait(impl_did)
        {
            let expected_sig = self.ty_translator.trait_registry().get_expected_sig_for_impl_fn(callee_did);
            expected_sig.bound_vars().as_slice()
        } else {
            let fn_ty: ty::EarlyBinder<'_, ty::Ty<'_>> = self.tcx.type_of(callee_did);
            let fn_ty = fn_ty.instantiate(self.tcx, args).skip_norm_wip();
            let fnsig = fn_ty.fn_sig(self.tcx);
            fnsig.bound_vars().as_slice()
        }
    }

    fn get_drop_glue_generic_abstraction_with_mode(
        &self,
        args: ty::GenericArgsRef<'tcx>,
        late_bounds: &[ty::BoundVariableKind<'tcx>],
        trait_reqs: Vec<ResolvedTraitReq<'tcx, 'def>>,
        mode: types::GenericAbstractionMode,
    ) -> Result<types::AbstractedGenerics<'def>, TranslationError> {
        trace!("enter drop-glue get_drop_glue_generic_abstraction mode={mode:?} args={args:?}");

        let mut collector = DropGlueGenericCollector::new(self.tcx);
        let mut callee_lft_param_inst = Vec::new();
        let mut bound_lfts = Vec::new();

        for arg in args {
            if let Some(region) = arg.as_region() {
                let lft = self.translate_drop_glue_region(region)?;
                if !bound_lfts.contains(&lft) {
                    bound_lfts.push(lft.clone());
                }
                callee_lft_param_inst.push(lft);
            }
            if let Some(ty) = arg.as_type() {
                collector.fold_ty(ty);
            }
        }

        let (tyvars, regions, projections) = collector.get_result();

        let mut scope = specs::GenericScope::empty();
        let mut fn_inst = specs::GenericScopeInst::empty();

        for lft_name in &bound_lfts {
            scope.add_lft_param(specs::LftParam::new(
                lft_name.clone(),
                specs::LftParamOrigin::FunctionRebound,
            ));
            fn_inst.add_lft_param(lft_name.clone());
        }

        for region in regions {
            let lft_name = self.translate_drop_glue_region(region)?;
            if !bound_lfts.contains(&lft_name) {
                scope.add_lft_param(specs::LftParam::new(
                    lft_name.clone(),
                    specs::LftParamOrigin::FunctionRebound,
                ));
                bound_lfts.push(lft_name.clone());
            }
            callee_lft_param_inst.push(lft_name);
        }

        for (late_bound_idx, late_bound) in late_bounds.iter().enumerate() {
            let ty::BoundVariableKind::Region(region) = late_bound else {
                return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                    Message::UnsupportedFeature(format!(
                        "drop-glue generic abstraction only supports late-bound regions, got {late_bound:?}"
                    )),
                )));
            };
            let lft_name = region.get_name(self.tcx).map_or_else(
                || coq::Ident::new(&format!("late_lft_{late_bound_idx}")),
                |name| coq::Ident::new(&format!("lft_{name}")),
            );
            scope.add_lft_param(specs::LftParam::new(
                lft_name.clone(),
                specs::LftParamOrigin::FunctionRebound,
            ));
            fn_inst.add_lft_param(lft_name);
        }

        let mut callee_ty_param_inst = Vec::new();
        for param in &tyvars {
            let lit = specs::LiteralTyParam::new(param.name.as_str());
            callee_ty_param_inst.push(specs::Type::LiteralParam(lit.clone()));
            scope.add_ty_param(lit);
        }
        for alias_ty in projections {
            let ty::AliasTyKind::Projection { def_id: assoc_did } = alias_ty.kind else {
                continue;
            };
            let trait_did = self.tcx.parent(assoc_did);
            let entry = self.generic_scope.trait_scope().lookup_trait_use(self.tcx, trait_did, alias_ty.args);
            let assoc_type = entry.get_associated_type_use(self.tcx, assoc_did);
            if let specs::Type::LiteralParam(mut lit) = assoc_type {
                lit.set_origin(specs::TyParamOrigin::Direct);
                scope.add_ty_param(lit.clone());
                callee_ty_param_inst.push(specs::Type::LiteralParam(lit));
            }
        }

        let num_surrounding_params = match mode {
            types::GenericAbstractionMode::FromOwner(owner_did) => {
                types::scope::Params::determine_number_of_surrounding_params(owner_did, self.tcx)
            },
            types::GenericAbstractionMode::AllDirect => 0,
        };
        for arg in &args.as_slice()[..num_surrounding_params] {
            if let Some(ty) = arg.as_type() {
                let translated_ty = self.translate_drop_glue_spec_type(ty)?;
                fn_inst.add_surrounding_ty_param(translated_ty);
            }
        }
        for arg in &args.as_slice()[num_surrounding_params..] {
            if let Some(ty) = arg.as_type() {
                let translated_ty = self.translate_drop_glue_spec_type(ty)?;
                fn_inst.add_direct_ty_param(translated_ty);
            }
        }

        for req in trait_reqs {
            let mut assoc_inst = Vec::new();
            for ty in req.req_inst.assoc_ty_inst {
                let mut state = self.shim_state();
                assoc_inst.push(self.ty_translator.translate_type_in_state(ty, &mut state)?);
            }
            let trait_req = specs::traits::ReqInst::new(
                req.req_inst.spec,
                req.req_inst.origin,
                req.req_inst.attr_dependency,
                assoc_inst,
                req.req_inst.of_trait,
                req.req_inst.scope,
            );
            fn_inst.add_trait_requirement(trait_req);
        }

        info!("Drop-glue abstraction scope: {:?}", scope);
        info!("Drop-glue fn instantiation: {fn_inst:?}");
        info!("Drop-glue callee instantiation: {:?}, {:?}", callee_lft_param_inst, callee_ty_param_inst);

        Ok(types::AbstractedGenerics {
            scope,
            callee_lft_param_inst,
            callee_ty_param_inst,
            num_of_latebounds: late_bounds.len(),
            fn_scope_inst: fn_inst,
        })
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirDropTranslation<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {
    fn get_drop_glue_generic_abstraction(
        &self,
        owner_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
        trait_reqs: Vec<ResolvedTraitReq<'tcx, 'def>>,
    ) -> Result<types::AbstractedGenerics<'def>, TranslationError> {
        self.get_drop_glue_generic_abstraction_with_mode(
            args,
            &[],
            trait_reqs,
            types::GenericAbstractionMode::FromOwner(owner_did),
        )
    }

    fn get_tuple_drop_glue_generic_abstraction(
        &self,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<types::AbstractedGenerics<'def>, TranslationError> {
        let trait_reqs = {
            let mut state = self.shim_state();
            self.ty_translator
                .trait_registry()
                .resolve_drop_glue_requirements_for_args(&mut state, args)?
        };
        self.get_drop_glue_generic_abstraction_with_mode(
            args,
            &[],
            trait_reqs,
            types::GenericAbstractionMode::AllDirect,
        )
    }

    fn translate_drop_glue_type(&self, ty: ty::Ty<'tcx>) -> Result<specs::Type<'def>, TranslationError> {
        self.ty_translator.translate_type_in_state(ty, &mut self.shim_state())
    }

    fn resolve_drop_glue_trait_requirements(
        &self,
        owner_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<Vec<ResolvedTraitReq<'tcx, 'def>>, TranslationError> {
        let mut state = self.shim_state();
        self.ty_translator
            .trait_registry()
            .resolve_trait_requirements_in_state(&mut state, owner_did, args, true, true)
    }

    fn make_virtual_drop_glue_method_for_param(&self, dropped_ty: ty::Ty<'tcx>) -> TraitMethodUseData<'def> {
        make_virtual_drop_glue_method_for_param_from_scope(self.tcx, &self.generic_scope, dropped_ty)
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirTypeTranslation<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {
    fn translate_type_to_syn_type(&self, ty: ty::Ty<'tcx>) -> Result<lang::SynType, TranslationError> {
        self.ty_translator.translate_type_to_syn_type(ty, &mut self.shim_state())
    }

    fn translate_type(&self, ty: ty::Ty<'tcx>) -> Result<specs::Type<'def>, TranslationError> {
        self.ty_translator.translate_type_in_state(ty, &mut self.shim_state())
    }

    fn generate_structlike_use(
        &self,
        ty: ty::Ty<'tcx>,
        variant: Option<abi::VariantIdx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_structlike_use(ty, variant, &mut self.shim_state())
    }

    fn generate_enum_use(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_enum_use(adt_def, args, &mut self.shim_state())
    }

    fn generate_enum_use_with_regions(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_enum_use(adt_def, args, &mut self.shim_state())
    }

    fn generate_struct_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_struct_use(variant_id, args, &mut self.shim_state())
    }

    fn generate_enum_variant_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_enum_variant_use(variant_id, args, &mut self.shim_state())
    }

    fn generate_tuple_use<F>(&self, tys: F) -> Result<specs::types::LiteralUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::Ty<'tcx>>,
    {
        self.ty_translator.generate_tuple_use(tys, &mut self.shim_state())
    }

    fn get_field_name_of(
        &self,
        field: abi::FieldIdx,
        ty: ty::Ty<'tcx>,
        variant: Option<usize>,
    ) -> Result<String, TranslationError> {
        self.ty_translator.get_field_name_of(field, ty, variant)
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirConstantTranslation<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {
    fn translate_fn_def_constant(
        &mut self,
        ty: ty::Ty<'tcx>,
    ) -> Result<(code::Expr, Option<Self::ExprInfo>), TranslationError> {
        self.translate_drop_call_fn_def_use(ty)
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirRvalueTranslation<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {}
