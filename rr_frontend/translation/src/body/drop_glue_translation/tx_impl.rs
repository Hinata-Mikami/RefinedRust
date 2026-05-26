// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeSet, HashMap, HashSet};

use log::{info, trace};
use radium::{code, lang, specs};
use rr_rustc_interface::abi;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty::TypeFolder as _;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::type_ir::TypeSuperFoldable as _;

use super::DropGlueTX;
use crate::base::*;
use crate::body::mir_lowering::{
    MirConstantTranslation, MirDropTranslation, MirRvalueTranslation, MirTranslationCtx, MirTypeTranslation,
    TranslationKey,
};
use crate::{procedures, rustcmp, types};

impl<'a, 'def: 'a, 'tcx: 'def> MirTranslationCtx<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {
    type ExprInfo = ();

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
            ty::TyKind::Alias(alias_ty) if matches!(alias_ty.kind, ty::AliasTyKind::Projection { .. }) => {
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

impl<'a, 'def: 'a, 'tcx: 'def> MirDropTranslation<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {
    fn get_drop_glue_generic_abstraction(
        &self,
        owner_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<types::AbstractedGenerics<'def>, TranslationError> {
        trace!("enter drop-glue get_drop_glue_generic_abstraction owner_did={owner_did:?} args={args:?}");

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

        let mut callee_ty_param_inst = Vec::new();
        for param in &tyvars {
            let lit = specs::LiteralTyParam::new(param.name.as_str());
            callee_ty_param_inst.push(specs::Type::LiteralParam(lit.clone()));
            scope.add_ty_param(lit);
        }
        for alias_ty in projections {
            let assoc_did = alias_ty.kind.def_id();
            let trait_did = self.tcx.parent(assoc_did);
            let entry = self.generic_scope.trait_scope().lookup_trait_use(self.tcx, trait_did, alias_ty.args);
            let assoc_type = entry.get_associated_type_use(self.tcx, assoc_did);
            if let specs::Type::LiteralParam(mut lit) = assoc_type {
                lit.set_origin(specs::TyParamOrigin::Direct);
                scope.add_ty_param(lit.clone());
                callee_ty_param_inst.push(specs::Type::LiteralParam(lit));
            }
        }

        let num_surrounding_params =
            types::scope::Params::determine_number_of_surrounding_params(owner_did, self.tcx);
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

        info!("Drop-glue abstraction scope: {:?}", scope);
        info!("Drop-glue fn instantiation: {fn_inst:?}");
        info!("Drop-glue callee instantiation: {:?}, {:?}", callee_lft_param_inst, callee_ty_param_inst);

        Ok(types::AbstractedGenerics {
            scope,
            callee_lft_param_inst,
            callee_ty_param_inst,
            num_of_latebounds: 0,
            fn_scope_inst: fn_inst,
        })
    }

    fn translate_drop_glue_type(&self, ty: ty::Ty<'tcx>) -> Result<specs::Type<'def>, TranslationError> {
        self.ty_translator.translate_type_in_state(ty, &mut self.shim_state())
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirTypeTranslation<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {
    fn translate_type_to_syn_type(&self, ty: ty::Ty<'tcx>) -> Result<lang::SynType, TranslationError> {
        self.ty_translator.translate_type_to_syn_type(ty, &mut self.shim_state())
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

impl<'a, 'def: 'a, 'tcx: 'def> MirConstantTranslation<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {}

impl<'a, 'def: 'a, 'tcx: 'def> MirRvalueTranslation<'def, 'tcx> for DropGlueTX<'a, 'def, 'tcx> {}
