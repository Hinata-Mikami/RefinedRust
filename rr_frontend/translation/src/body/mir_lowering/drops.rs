// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;
use std::iter;

use log::{info, trace};
use radium::{code, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use super::{MirTranslationCtx, MirTypeTranslation, ProcedureInst, TraitMethodUseData, TranslationKey};
use crate::base::*;
use crate::error::Message;
use crate::traits::registry::{self, ResolvedTraitReq};
use crate::{procedures, types};

pub(crate) trait MirDropTranslation<'def, 'tcx: 'def>:
    MirTranslationCtx<'def, 'tcx> + MirTypeTranslation<'def, 'tcx>
{
    fn get_drop_glue_generic_abstraction(
        &self,
        owner_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
        trait_reqs: Vec<ResolvedTraitReq<'tcx, 'def>>,
    ) -> Result<types::AbstractedGenerics<'def>, TranslationError>;

    fn resolve_drop_glue_trait_requirements(
        &self,
        owner_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<Vec<ResolvedTraitReq<'tcx, 'def>>, TranslationError>;

    fn get_tuple_drop_glue_generic_abstraction(
        &self,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<types::AbstractedGenerics<'def>, TranslationError>;

    fn translate_drop_glue_type(&self, ty: ty::Ty<'tcx>) -> Result<specs::Type<'def>, TranslationError>;

    fn make_virtual_drop_glue_method_for_param(&self, dropped_ty: ty::Ty<'tcx>) -> TraitMethodUseData<'def>;

    /// Internally register that we have used ADT drop glue for a concrete dropped type, and return
    /// the code parameter and call instantiation.
    fn register_use_drop_glue(
        &mut self,
        dropped_ty: ty::Ty<'tcx>,
    ) -> Result<(code::Expr, ProcedureInst<'tcx, 'def>), TranslationError> {
        trace!("enter register_use_drop_glue dropped_ty={dropped_ty:?}");

        let function_did = self.normalization_scope_did();
        let dropped_ty = types::normalize_in_function(function_did, self.tcx(), dropped_ty)?;

        match dropped_ty.kind() {
            ty::TyKind::Adt(adt_def, adt_args) => self.register_use_adt_drop_glue(*adt_def, adt_args),
            ty::TyKind::Tuple(args) => self.register_use_tuple_drop_glue(args),
            ty::TyKind::Param(_) => self.register_use_assumed_drop_glue(dropped_ty),
            ty::TyKind::Alias(alias_ty) if matches!(alias_ty.kind, ty::AliasTyKind::Projection { .. }) => {
                self.register_use_assumed_drop_glue(dropped_ty)
            },
            _ => Err(TranslationError::ErrorReported(self.tcx().dcx().err(Message::UnsupportedFeature(
                format!("drop-glue calls are currently only supported for ADTs and abstract generic types, got {dropped_ty:?}"),
            )))),
        }
    }

    fn register_use_adt_drop_glue(
        &mut self,
        adt_def: ty::AdtDef<'tcx>,
        adt_args: ty::GenericArgsRef<'tcx>,
    ) -> Result<(code::Expr, ProcedureInst<'tcx, 'def>), TranslationError> {
        let key = procedures::DropGlueKey::Adt(OrderedDefId::new(self.tcx(), adt_def.did()));
        let generics_key = types::generate_args_inst_key(self.tcx(), adt_args)?;
        let trait_reqs = self.resolve_drop_glue_trait_requirements(adt_def.did(), adt_args)?;
        let quantified_args = self.get_drop_glue_generic_abstraction(adt_def.did(), adt_args, trait_reqs)?;

        self.register_use_concrete_drop_glue(key, generics_key, adt_args, quantified_args)
    }

    fn register_use_tuple_drop_glue(
        &mut self,
        args: &'tcx ty::List<ty::Ty<'tcx>>,
    ) -> Result<(code::Expr, ProcedureInst<'tcx, 'def>), TranslationError> {
        let arity = args.len();
        if arity == 0 {
            return Err(TranslationError::ErrorReported(self.tcx().dcx().err(Message::UnsupportedFeature(
                "drop-glue calls for () should have been skipped as trivial".to_owned(),
            ))));
        }
        if arity > 5 {
            return Err(TranslationError::ErrorReported(self.tcx().dcx().err(Message::UnsupportedFeature(
                format!("drop-glue calls for tuples are only supported up to arity 5, got arity {arity}"),
            ))));
        }

        self.generate_tuple_use(args.iter())?;

        let method_params_vec: Vec<_> = args.iter().map(ty::GenericArg::from).collect();
        let method_params = self.tcx().mk_args(&method_params_vec);
        let generics_key = types::generate_args_inst_key(self.tcx(), method_params)?;

        let quantified_args = self.get_tuple_drop_glue_generic_abstraction(method_params)?;

        self.register_use_concrete_drop_glue(
            procedures::DropGlueKey::Tuple(arity),
            generics_key,
            method_params,
            quantified_args,
        )
    }

    fn register_use_concrete_drop_glue(
        &mut self,
        key: procedures::DropGlueKey,
        generics_key: types::GenericsKey<'tcx>,
        method_params: ty::GenericArgsRef<'tcx>,
        quantified_args: types::AbstractedGenerics<'def>,
    ) -> Result<(code::Expr, ProcedureInst<'tcx, 'def>), TranslationError> {
        let used_key = TranslationKey::DropGlue(key.clone(), generics_key.clone());
        let res;
        if let Some(proc_use) = self.collected_procedures().get(&used_key) {
            res = proc_use.loc_name.clone();
        } else {
            let meta = self.procedure_registry().lookup_drop_glue(&key).ok_or_else(|| {
                TranslationError::ErrorReported(
                    self.tcx().dcx().err(Message::UnknownProcedure(format!("{:?}", key))),
                )
            })?;

            let spec_term = code::UsedProcedureSpec::Literal(meta.get_spec_name().to_owned());
            let loc_name =
                format!("{}_loc", types::mangle_name_with_tys(meta.get_name(), generics_key.as_slice()));
            let syntypes = vec![lang::SynType::Ptr];
            let fn_inst = quantified_args.fn_scope_inst;

            info!(
                "Registered drop-glue instance {} for {:?} with {:?} and layouts {:?}",
                loc_name, key, fn_inst, syntypes
            );

            let proc_use =
                code::UsedProcedure::new(loc_name, spec_term, quantified_args.scope, fn_inst, syntypes);

            res = proc_use.loc_name.clone();
            self.collected_procedures_mut().insert(used_key, proc_use);
        }

        trace!("leave register_use_drop_glue");
        let inst = ProcedureInst {
            method_params,
            type_hint: quantified_args.callee_ty_param_inst,
            lft_hint: quantified_args.callee_lft_param_inst,
            num_of_latebounds: quantified_args.num_of_latebounds,
            mapped_early_regions: BTreeMap::new(),
        };

        Ok((code::Expr::MetaParam(res), inst))
    }

    fn register_use_assumed_drop_glue(
        &mut self,
        dropped_ty: ty::Ty<'tcx>,
    ) -> Result<(code::Expr, ProcedureInst<'tcx, 'def>), TranslationError> {
        let key = TranslationKey::AssumedDropGlue(dropped_ty);

        let res;
        if let Some(proc_use) = self.collected_procedures().get(&key) {
            res = proc_use.loc_name.clone();
        } else {
            let method_use = self.make_virtual_drop_glue_method_for_param(dropped_ty);
            let syntypes = vec![lang::SynType::Ptr];
            let scope = method_use.spec_scope.into();
            let mut fn_inst = specs::GenericScopeInst::empty();
            for lft in method_use.spec_inst.lft_insts {
                fn_inst.add_lft_param(lft);
            }

            info!(
                "Registered assumed drop-glue instance {} for {:?} with {:?} and layouts {:?}",
                method_use.loc_name, dropped_ty, fn_inst, syntypes
            );

            let proc_use =
                code::UsedProcedure::new(method_use.loc_name, method_use.spec_term, scope, fn_inst, syntypes);

            res = proc_use.loc_name.clone();
            self.collected_procedures_mut().insert(key, proc_use);
        }

        trace!("leave register_use_drop_glue");
        let empty_args: &[ty::GenericArg<'tcx>] = &[];
        let inst = ProcedureInst {
            method_params: self.tcx().mk_args(empty_args),
            type_hint: Vec::new(),
            lft_hint: Vec::new(),
            num_of_latebounds: 0,
            mapped_early_regions: BTreeMap::new(),
        };

        Ok((code::Expr::MetaParam(res), inst))
    }
}

pub(crate) fn make_virtual_drop_glue_method_for_param_from_scope<'tcx, 'def>(
    tcx: ty::TyCtxt<'tcx>,
    scope: &types::scope::Params<'tcx, 'def>,
    dropped_ty: ty::Ty<'tcx>,
) -> TraitMethodUseData<'def> {
    let arg = ty::GenericArg::from(dropped_ty);
    let trait_use = scope
        .trait_scope()
        .lookup_virtual_trait_use(tcx, registry::VirtualTrait::DropGlue, &[arg]);

    super::make_trait_method_use_data(trait_use.trait_use, "drop_glue", "drop_glue", iter::empty())
}
