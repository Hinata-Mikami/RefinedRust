// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use radium::code;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use super::{TX, TranslationKey};
use crate::base::*;
use crate::error::Message;
use crate::{procedures, types};

#[expect(dead_code)]
pub(crate) trait MirTranslationCtx<'def, 'tcx: 'def> {
    fn tcx(&self) -> ty::TyCtxt<'tcx>;

    fn body(&self) -> &mir::Body<'tcx>;

    fn proc_def_id(&self) -> DefId;

    fn ty_translator(&self) -> &types::LocalTX<'def, 'tcx>;

    fn procedure_registry(&self) -> &procedures::Scope<'tcx, 'def>;

    fn variable_map(&self) -> &HashMap<mir::Local, String>;

    fn variable_map_mut(&mut self) -> &mut HashMap<mir::Local, String>;

    fn collected_procedures(&self) -> &HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>>;

    fn collected_procedures_mut(&mut self) -> &mut HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>>;

    fn normalize_place(&self, place: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        *place
    }

    fn normalization_scope_did(&self) -> DefId {
        self.ty_translator().scope.borrow().did
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

impl<'a, 'def: 'a, 'tcx: 'def> MirTranslationCtx<'def, 'tcx> for TX<'a, 'def, 'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn body(&self) -> &mir::Body<'tcx> {
        self.proc.dropck_mir()
    }

    fn proc_def_id(&self) -> DefId {
        self.proc.get_id()
    }

    fn ty_translator(&self) -> &types::LocalTX<'def, 'tcx> {
        &self.ty_translator
    }

    fn procedure_registry(&self) -> &procedures::Scope<'tcx, 'def> {
        self.procedure_registry
    }

    fn variable_map(&self) -> &HashMap<mir::Local, String> {
        &self.variable_map
    }

    fn variable_map_mut(&mut self) -> &mut HashMap<mir::Local, String> {
        &mut self.variable_map
    }

    fn collected_procedures(&self) -> &HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>> {
        &self.collected_procedures
    }

    fn collected_procedures_mut(&mut self) -> &mut HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>> {
        &mut self.collected_procedures
    }

    fn normalize_place(&self, place: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        self.proc.normalize_box_deref_alias_place(place)
    }
}
