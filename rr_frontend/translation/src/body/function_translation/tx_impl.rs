// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use radium::{code, lang, specs};
use rr_rustc_interface::abi;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use super::{ExprInfo, ExprWithInfo, TX};
use crate::base::*;
use crate::body::mir_lowering::{
    MirConstantTranslation, MirDropTranslation, MirPlaceTranslation as _, MirRvalueTranslation,
    MirTranslationCtx, MirTypeTranslation, TraitMethodUseData, TranslationKey, make_realized_method_spec,
    make_virtual_drop_glue_method_for_param_from_scope,
};
use crate::traits::registry::{self, ResolvedTraitReq};
use crate::{error, procedures, types};

impl<'a, 'def: 'a, 'tcx: 'def> MirTranslationCtx<'def, 'tcx> for TX<'a, 'def, 'tcx> {
    type ExprInfo = ExprInfo<'tcx, 'def>;

    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn body(&self) -> &mir::Body<'tcx> {
        self.proc.dropck_mir()
    }

    fn proc_def_id(&self) -> DefId {
        self.proc.get_id()
    }

    fn procedure_registry(&self) -> &procedures::Scope<'tcx, 'def> {
        self.procedure_registry
    }

    fn normalization_scope_did(&self) -> DefId {
        self.ty_translator.scope.borrow().did
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
        self.proc.normalize_executable_place(place)
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirDropTranslation<'def, 'tcx> for TX<'a, 'def, 'tcx> {
    fn get_drop_glue_generic_abstraction(
        &self,
        owner_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
        trait_reqs: Vec<ResolvedTraitReq<'tcx, 'def>>,
    ) -> Result<types::AbstractedGenerics<'def>, TranslationError> {
        self.ty_translator
            .get_generic_abstraction_for_item(owner_did, args, &[], trait_reqs, true)
            .map(types::AbstractedGenerics::all_as_realization_context)
    }

    fn resolve_drop_glue_trait_requirements(
        &self,
        owner_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<Vec<ResolvedTraitReq<'tcx, 'def>>, TranslationError> {
        let mut scope = self.ty_translator.scope.borrow_mut();
        let mut state = types::STInner::InFunction(&mut scope);
        self.trait_registry
            .resolve_trait_requirements_in_state(&mut state, owner_did, args, true, true)
    }

    fn get_tuple_drop_glue_generic_abstraction(
        &self,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<types::AbstractedGenerics<'def>, TranslationError> {
        let trait_reqs = {
            let mut scope = self.ty_translator.scope.borrow_mut();
            let mut state = types::STInner::InFunction(&mut scope);
            self.trait_registry.resolve_drop_glue_requirements_for_args(&mut state, args)?
        };
        self.ty_translator
            .get_generic_abstraction_for_args_all_direct(args, &[], trait_reqs)
            .map(types::AbstractedGenerics::all_as_realization_context)
    }

    fn translate_drop_glue_type(&self, ty: ty::Ty<'tcx>) -> Result<specs::Type<'def>, TranslationError> {
        self.ty_translator.translate_type(ty)
    }

    fn make_virtual_drop_glue_method_for_param(&self, dropped_ty: ty::Ty<'tcx>) -> TraitMethodUseData<'def> {
        let scope = self.ty_translator.scope.borrow();
        make_virtual_drop_glue_method_for_param_from_scope(self.tcx, &scope.generic_scope, dropped_ty)
    }

    fn get_realized_drop_glue_spec(
        &self,
        dropped_ty: ty::Ty<'tcx>,
    ) -> Result<Option<code::UsedProcedureSpec<'def>>, TranslationError> {
        let Some(impl_) = ({
            let mut scope = self.ty_translator.scope.borrow_mut();
            let mut state = types::STInner::InFunction(&mut scope);
            self.trait_registry.get_drop_glue_impl_spec_term_in_state(&mut state, dropped_ty)?
        }) else {
            return Ok(None);
        };
        let trait_spec = self
            .trait_registry
            .lookup_virtual_trait(registry::VirtualTrait::DropGlue)
            .ok_or_else(|| {
                TranslationError::ErrorReported(self.tcx.dcx().err(error::Message::TraitResolution(
                    "virtual DropGlue trait is not registered with RefinedRust".to_owned(),
                )))
            })?;

        Ok(Some(make_realized_method_spec(
            &impl_,
            trait_spec,
            "drop_glue",
            specs::traits::ReqScopeInst::new(Vec::new()),
        )))
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirTypeTranslation<'def, 'tcx> for TX<'a, 'def, 'tcx> {
    fn translate_type_to_syn_type(&self, ty: ty::Ty<'tcx>) -> Result<lang::SynType, TranslationError> {
        self.ty_translator.translate_type_to_syn_type(ty)
    }

    fn translate_type(&self, ty: ty::Ty<'tcx>) -> Result<specs::Type<'def>, TranslationError> {
        self.ty_translator.translate_type(ty)
    }

    fn generate_structlike_use(
        &self,
        ty: ty::Ty<'tcx>,
        variant: Option<abi::VariantIdx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_structlike_use(ty, variant)
    }

    fn generate_enum_use(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_enum_use(adt_def, args)
    }

    fn generate_enum_use_with_regions(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_enum_use_with_regions(adt_def, args)
    }

    fn generate_struct_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_struct_use(variant_id, args)
    }

    fn generate_enum_variant_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError> {
        self.ty_translator.generate_enum_variant_use(variant_id, args)
    }

    fn generate_tuple_use<F>(&self, tys: F) -> Result<specs::types::LiteralUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::Ty<'tcx>>,
    {
        self.ty_translator.generate_tuple_use(tys)
    }

    fn get_field_name_of(
        &self,
        field: abi::FieldIdx,
        ty: ty::Ty<'tcx>,
        variant: Option<usize>,
    ) -> Result<String, TranslationError> {
        self.ty_translator.translator.get_field_name_of(field, ty, variant)
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirConstantTranslation<'def, 'tcx> for TX<'a, 'def, 'tcx> {
    fn translate_fn_def_constant(
        &mut self,
        ty: ty::Ty<'tcx>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        self.translate_fn_def_use(ty)
    }

    fn translate_static_ref_constant(
        &mut self,
        did: DefId,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        let ordered_did = OrderedDefId::new(self.tcx, did);
        let s = self.const_registry.get_static(self.tcx, &ordered_did)?;
        self.collected_statics.insert(ordered_did);
        Ok((code::Expr::Literal(code::Literal::Loc(s.loc_name.clone())), None))
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> MirRvalueTranslation<'def, 'tcx> for TX<'a, 'def, 'tcx> {
    fn translate_ref_rvalue(
        &mut self,
        loc: mir::Location,
        region: ty::Region<'tcx>,
        bk: mir::BorrowKind,
        place: &mir::Place<'tcx>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        let translated_pl = self.translate_place(place)?;
        let translated_bk = Self::translate_borrow_kind(self.tcx, bk)?;
        let region = self.proc.source_borrow_region_for_target(loc).unwrap_or(region);
        let lft = self.annotations.prepare_borrow_lifetime_plan(&self.ty_translator, loc, region).lft;
        let ty_annot = self.get_type_annotation_for_borrow(bk, false, place)?;

        Ok((
            code::Expr::Borrow {
                lft,
                bk: translated_bk,
                ty: ty_annot,
                e: Box::new(translated_pl),
            },
            None,
        ))
    }

    fn aggregate_kind_for_translation<'b>(
        &'b self,
        loc: mir::Location,
        target_kind: &'b mir::AggregateKind<'tcx>,
    ) -> &'b mir::AggregateKind<'tcx> {
        self.proc.source_aggregate_kind_for_target(loc).unwrap_or(target_kind)
    }
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Get the type to annotate a borrow with.
    fn get_type_annotation_for_borrow(
        &self,
        _bk: mir::BorrowKind,
        raw: bool,
        pl: &mir::Place<'tcx>,
    ) -> Result<Option<code::RustType>, TranslationError> {
        let ty = self.proc.region_type_of_place(pl);

        // For borrows, we can safely ignore the downcast type -- we cannot borrow a particularly variant
        let mut translated_ty = self.ty_translator.translate_type(ty.ty)?;
        if raw {
            translated_ty.make_raw();
        }
        let annot_ty = code::RustType::of_type(&translated_ty);

        Ok(Some(annot_ty))
    }
}
