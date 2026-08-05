// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::info;
use radium::{code, lang};
use rr_rustc_interface::abi;
use rr_rustc_interface::middle::{mir, ty};

use super::{MirTranslationCtx, MirTypeTranslation};
use crate::base::*;
use crate::error::Message;
use crate::types;

pub(crate) trait MirPlaceTranslation<'def, 'tcx: 'def>:
    MirTranslationCtx<'def, 'tcx> + MirTypeTranslation<'def, 'tcx>
{
    /// Translate a place to a Caesium lvalue.
    fn translate_place(&self, pl: &mir::Place<'tcx>) -> Result<code::Expr, TranslationError> {
        // Normalize only administrative aliases that the translation context has validated.
        let normalized = self.normalize_place(pl);
        let pl = &normalized;

        // Get the type of the underlying local. We will use this to
        // get the necessary layout information for dereferencing
        let mut cur_ty = self.shape_type_of_local(pl.local).map(mir::PlaceTy::from_ty)?;

        let local_name = self.variable_map().get(&pl.local).ok_or_else(|| {
            TranslationError::ErrorReported(
                self.tcx().dcx().err(Message::UnknownVar(format!("{:?}", pl.local))),
            )
        })?;

        let mut acc_expr = code::Expr::Var(local_name.to_owned());

        // iterate in evaluation order
        for it in pl.projection {
            match &it {
                mir::ProjectionElem::Deref => {
                    if matches!(cur_ty.ty.kind(), ty::TyKind::Adt(def, _) if def.is_box()) {
                        return Err(TranslationError::ErrorReported(self.tcx().dcx().err(
                            Message::UnsupportedFeature(format!(
                                "direct Box dereference reached executable MIR translation for {:?}; expected rustc's validated raw-pointer lowering",
                                cur_ty.ty
                            )),
                        )));
                    }

                    // use the type of the dereferencee
                    let st = self.translate_type_to_syn_type(cur_ty.ty)?;
                    acc_expr = code::Expr::Deref {
                        ot: st.into(),
                        e: Box::new(acc_expr),
                    };
                },
                mir::ProjectionElem::Field(f, _) => {
                    // `t` is the type of the field we are accessing!
                    let lit = self.generate_structlike_use(cur_ty.ty, cur_ty.variant_index)?;
                    // TODO: does not do the right thing for accesses to fields of zero-sized objects.
                    let struct_sls = lit.generate_raw_syn_type_term();
                    let name = self.get_field_name_of(
                        *f,
                        cur_ty.ty,
                        cur_ty.variant_index.map(abi::VariantIdx::as_usize),
                    )?;

                    acc_expr = code::Expr::FieldOf {
                        e: Box::new(acc_expr),
                        name,
                        sls: struct_sls.to_string(),
                    };
                },
                mir::ProjectionElem::Index(v) => {
                    let ty::TyKind::Array(element_ty, _) = cur_ty.ty.kind() else {
                        return Err(TranslationError::ErrorReported(self.tcx().dcx().err(
                            Message::UnsupportedFeature(format!(
                                "RefinedRust only supports indexing fixed arrays, got {:?}",
                                cur_ty.ty
                            )),
                        )));
                    };

                    let element_layout = self.translate_type_to_syn_type(*element_ty)?.into();
                    let index_ty = self.shape_type_of_local(*v)?;
                    let index_ot: lang::OpType = self.translate_type_to_syn_type(index_ty)?.into();
                    let index_name = self.variable_map().get(v).ok_or_else(|| {
                        TranslationError::ErrorReported(
                            self.tcx().dcx().err(Message::UnknownVar(format!("{v:?}"))),
                        )
                    })?;
                    let index = code::Expr::Copy {
                        ot: index_ot.clone(),
                        e: Box::new(code::Expr::Var(index_name.to_owned())),
                    };

                    acc_expr = code::Expr::BinOp {
                        o: code::Binop::PtrOffset(element_layout),
                        ot1: lang::OpType::Ptr,
                        ot2: index_ot,
                        e1: Box::new(acc_expr),
                        e2: Box::new(index),
                    };
                },
                mir::ProjectionElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let ty::TyKind::Array(element_ty, len) = cur_ty.ty.kind() else {
                        return Err(TranslationError::ErrorReported(self.tcx().dcx().err(
                            Message::UnsupportedFeature(format!(
                                "RefinedRust only supports constant indexing of fixed arrays, got {:?}",
                                cur_ty.ty
                            )),
                        )));
                    };
                    let Some(len) = len.try_to_target_usize(self.tcx()) else {
                        return Err(TranslationError::ErrorReported(self.tcx().dcx().err(
                            Message::UnsupportedFeature(format!(
                                "RefinedRust cannot evaluate the length of indexed array {:?}",
                                cur_ty.ty
                            )),
                        )));
                    };
                    let offset = if *from_end { len - *offset } else { *offset };

                    let element_layout = self.translate_type_to_syn_type(*element_ty)?.into();
                    acc_expr = code::Expr::BinOp {
                        o: code::Binop::PtrOffset(element_layout),
                        ot1: lang::OpType::Ptr,
                        ot2: lang::OpType::Int(lang::IntType::USize),
                        e1: Box::new(acc_expr),
                        e2: Box::new(code::Expr::Literal(code::Literal::USize(offset))),
                    };
                },
                mir::ProjectionElem::Subslice { .. } => {
                    return Err(TranslationError::ErrorReported(
                        self.tcx()
                            .dcx()
                            .err(Message::UnsupportedFeature("places: implement subslicing".to_owned())),
                    ));
                },
                mir::ProjectionElem::Downcast(_, variant_idx) => {
                    info!("Downcast of ty {:?} to {:?}", cur_ty, variant_idx);
                    if let ty::TyKind::Adt(def, args) = cur_ty.ty.kind() {
                        if def.is_enum() {
                            let enum_use = self.generate_enum_use(*def, args)?;
                            let els = enum_use.generate_raw_syn_type_term();

                            let variant_name =
                                types::TX::get_variant_name_of(self.tcx(), cur_ty.ty, *variant_idx)?;

                            acc_expr = code::Expr::EnumData {
                                els: els.to_string(),
                                variant: variant_name,
                                e: Box::new(acc_expr),
                            }
                        } else {
                            return Err(TranslationError::ErrorReported(
                                self.tcx().dcx().err(Message::AdtDowncastOnNonEnumType),
                            ));
                        }
                    } else {
                        return Err(TranslationError::ErrorReported(
                            self.tcx().dcx().err(Message::AdtDowncastOnNonEnumType),
                        ));
                    }
                },
                mir::ProjectionElem::OpaqueCast(_) => {
                    return Err(TranslationError::ErrorReported(
                        self.tcx()
                            .dcx()
                            .err(Message::UnsupportedFeature("places: implement opaque casts".to_owned())),
                    ));
                },
                mir::ProjectionElem::UnwrapUnsafeBinder(_) => {
                    return Err(TranslationError::ErrorReported(self.tcx().dcx().err(
                        Message::UnsupportedFeature("places: implement UnwrapUnsafeBinder".to_owned()),
                    )));
                },
            }
            // update cur_ty
            cur_ty = cur_ty.projection_ty(self.tcx(), it);
        }
        info!("translating place {:?} to {:?}", pl, acc_expr);
        Ok(acc_expr)
    }
}

impl<'def, 'tcx: 'def, T> MirPlaceTranslation<'def, 'tcx> for T where
    T: MirTranslationCtx<'def, 'tcx> + MirTypeTranslation<'def, 'tcx>
{
}
