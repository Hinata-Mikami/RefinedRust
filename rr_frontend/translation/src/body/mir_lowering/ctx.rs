// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cmp;
use std::collections::HashMap;

use radium::{code, lang, specs};
use rr_rustc_interface::abi;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use crate::base::*;
use crate::error::Message;
use crate::{procedures, rustcmp, types};

#[derive(PartialEq, Eq, Hash, Debug)]
pub(crate) enum TranslationKey<'tcx> {
    Function(OrderedDefId, types::GenericsKey<'tcx>),
    DropGlue(procedures::DropGlueKey, types::GenericsKey<'tcx>),
    AssumedDropGlue(ty::Ty<'tcx>),
}

impl<'tcx> TranslationKey<'tcx> {
    pub(crate) fn cmp(&self, tcx: ty::TyCtxt<'tcx>, b: &Self) -> cmp::Ordering {
        match (self, b) {
            (Self::Function(a_did, a_args), Self::Function(b_did, b_args)) => {
                let did_ord = a_did.cmp(b_did);
                did_ord.then_with(|| rustcmp::cmp_tys(tcx, a_args, b_args))
            },
            (Self::DropGlue(a_key, a_args), Self::DropGlue(b_key, b_args)) => {
                a_key.cmp(b_key).then_with(|| rustcmp::cmp_tys(tcx, a_args, b_args))
            },
            (Self::AssumedDropGlue(a), Self::AssumedDropGlue(b)) => rustcmp::cmp_tys(tcx, &[*a], &[*b]),
            (Self::Function(_, _), Self::DropGlue(_, _) | Self::AssumedDropGlue(_))
            | (Self::DropGlue(_, _), Self::AssumedDropGlue(_)) => cmp::Ordering::Less,
            (Self::DropGlue(_, _) | Self::AssumedDropGlue(_), Self::Function(_, _))
            | (Self::AssumedDropGlue(_), Self::DropGlue(_, _)) => cmp::Ordering::Greater,
        }
    }
}

pub(crate) trait MirTranslationCtx<'def, 'tcx: 'def> {
    type ExprInfo;

    fn tcx(&self) -> ty::TyCtxt<'tcx>;

    fn body(&self) -> &mir::Body<'tcx>;

    fn proc_def_id(&self) -> DefId;

    fn procedure_registry(&self) -> &procedures::Scope<'tcx, 'def>;

    fn normalization_scope_did(&self) -> DefId;

    fn variable_map(&self) -> &HashMap<mir::Local, String>;

    fn collected_procedures(&self) -> &HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>>;

    fn collected_procedures_mut(&mut self) -> &mut HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>>;

    fn normalize_place(&self, place: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        *place
    }

    /// Whether this translation context recognizes a rustc-generated non-`Copy` MIR copy.
    fn permits_non_copy_mir_copy(&self, _place: &mir::Place<'tcx>) -> bool {
        false
    }

    /// Get the shape/layout type of a local in the translated MIR body.
    fn shape_type_of_local(&self, local: mir::Local) -> Result<ty::Ty<'tcx>, TranslationError> {
        self.body().local_decls.get(local).map(|decl| decl.ty).ok_or_else(|| {
            TranslationError::ErrorReported(self.tcx().dcx().err(Message::UnknownVar(format!("{local:?}"))))
        })
    }

    /// Get the shape/layout type of a place expression in the translated MIR body.
    fn shape_type_of_place(&self, place: &mir::Place<'tcx>) -> mir::PlaceTy<'tcx> {
        let normalized = self.normalize_place(place);
        normalized.ty(&self.body().local_decls, self.tcx())
    }

    /// Get the shape/layout type of an operand in the translated MIR body.
    fn shape_type_of_operand(&self, op: &mir::Operand<'tcx>) -> ty::Ty<'tcx> {
        op.ty(&self.body().local_decls, self.tcx())
    }
}

pub(crate) trait MirTypeTranslation<'def, 'tcx: 'def>: MirTranslationCtx<'def, 'tcx> {
    fn translate_type_to_syn_type(&self, ty: ty::Ty<'tcx>) -> Result<lang::SynType, TranslationError>;

    fn generate_structlike_use(
        &self,
        ty: ty::Ty<'tcx>,
        variant: Option<abi::VariantIdx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError>;

    fn generate_enum_use(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError>;

    fn generate_enum_use_with_regions(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError>;

    fn generate_struct_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError>;

    fn generate_enum_variant_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError>;

    fn generate_tuple_use<F>(&self, tys: F) -> Result<specs::types::LiteralUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::Ty<'tcx>>;

    fn get_field_name_of(
        &self,
        field: abi::FieldIdx,
        ty: ty::Ty<'tcx>,
        variant: Option<usize>,
    ) -> Result<String, TranslationError>;
}
