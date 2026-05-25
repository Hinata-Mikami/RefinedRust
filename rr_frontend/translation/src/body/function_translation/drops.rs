// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use log::{info, trace};
use radium::{code, lang};
use rr_rustc_interface::middle::ty;

use super::calls::ProcedureInst;
use super::{ExprInfo, ExprWithInfo, TX};
use crate::base::*;
use crate::body::mir_lowering::TranslationKey;
use crate::error::Message;
use crate::{procedures, types};

const CORE_PTR_DROP_GLUE_SPEC: &str = "type_of_core_ptr_drop_glue";

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Internally register that we have used ADT drop glue for a concrete dropped type, and return
    /// the code parameter name.
    pub(super) fn register_use_drop_glue(
        &mut self,
        dropped_ty: ty::Ty<'tcx>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        trace!("enter register_use_drop_glue dropped_ty={dropped_ty:?}");

        let function_did = self.ty_translator.scope.borrow().did;
        let dropped_ty = types::normalize_in_function(function_did, self.tcx, dropped_ty)?;

        match dropped_ty.kind() {
            ty::TyKind::Adt(adt_def, adt_args) => self.register_use_adt_drop_glue(*adt_def, adt_args),
            ty::TyKind::Param(_) => self.register_use_assumed_drop_glue(dropped_ty),
            ty::TyKind::Alias(alias_ty) if matches!(alias_ty.kind, ty::AliasTyKind::Projection { .. }) => {
                self.register_use_assumed_drop_glue(dropped_ty)
            },
            _ => Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!("drop-glue calls are currently only supported for ADTs and abstract generic types, got {dropped_ty:?}"),
            )))),
        }
    }

    fn register_use_adt_drop_glue(
        &mut self,
        adt_def: ty::AdtDef<'tcx>,
        adt_args: ty::GenericArgsRef<'tcx>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        let key = procedures::DropGlueKey::Adt(OrderedDefId::new(self.tcx, adt_def.did()));
        let generics_key = types::generate_args_inst_key(self.tcx, adt_args)?;
        let quantified_args = self.ty_translator.get_generic_abstraction_for_item(
            adt_def.did(),
            adt_args,
            &[],
            Vec::new(),
            true,
        )?;

        let used_key = TranslationKey::DropGlue(key.clone(), generics_key.clone());
        let res;
        if let Some(proc_use) = self.collected_procedures.get(&used_key) {
            res = proc_use.loc_name.clone();
        } else {
            let meta = self.procedure_registry.lookup_drop_glue(&key).ok_or_else(|| {
                TranslationError::ErrorReported(
                    self.tcx.dcx().err(Message::UnknownProcedure(format!("{:?}", key))),
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
            self.collected_procedures.insert(used_key, proc_use);
        }

        trace!("leave register_use_drop_glue");
        let inst = ProcedureInst {
            method_params: adt_args,
            type_hint: quantified_args.callee_ty_param_inst,
            lft_hint: quantified_args.callee_lft_param_inst,
            num_of_latebounds: quantified_args.num_of_latebounds,
            mapped_early_regions: BTreeMap::new(),
        };

        Ok((code::Expr::MetaParam(res), Some(ExprInfo::Call(inst))))
    }

    fn register_use_assumed_drop_glue(
        &mut self,
        dropped_ty: ty::Ty<'tcx>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError> {
        let key = TranslationKey::AssumedDropGlue(dropped_ty);
        let translated_ty = self.ty_translator.translate_type(dropped_ty)?;

        let res;
        if let Some(proc_use) = self.collected_procedures.get(&key) {
            res = proc_use.loc_name.clone();
        } else {
            let spec_term = code::UsedProcedureSpec::Literal(CORE_PTR_DROP_GLUE_SPEC.to_owned());
            let loc_name = types::drop_glue_loc_name_for_ty(dropped_ty);
            let syntypes = vec![lang::SynType::Ptr];
            let mut fn_inst = radium::specs::GenericScopeInst::empty();
            fn_inst.add_direct_ty_param(translated_ty.clone());

            info!(
                "Registered assumed drop-glue instance {} for {:?} with {:?} and layouts {:?}",
                loc_name, dropped_ty, fn_inst, syntypes
            );

            let proc_use = code::UsedProcedure::new(
                loc_name,
                spec_term,
                radium::specs::GenericScope::empty(),
                fn_inst,
                syntypes,
            );

            res = proc_use.loc_name.clone();
            self.collected_procedures.insert(key, proc_use);
        }

        trace!("leave register_use_drop_glue");
        let empty_args: &[ty::GenericArg<'tcx>] = &[];
        let inst = ProcedureInst {
            method_params: self.tcx.mk_args(empty_args),
            type_hint: vec![translated_ty],
            lft_hint: Vec::new(),
            num_of_latebounds: 0,
            mapped_early_regions: BTreeMap::new(),
        };

        Ok((code::Expr::MetaParam(res), Some(ExprInfo::Call(inst))))
    }
}
