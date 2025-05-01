// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::{info, trace};
use radium::coq;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{abi, index};

use super::TX;
use crate::base::*;
use crate::regions;

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate an aggregate expression.
    fn translate_aggregate(
        &mut self,
        kind: &mir::AggregateKind<'tcx>,
        op: &index::IndexVec<abi::FieldIdx, mir::Operand<'tcx>>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        // translate operands
        let mut translated_ops: Vec<radium::Expr> = Vec::new();
        let mut operand_types: Vec<ty::Ty<'tcx>> = Vec::new();

        for o in op {
            let translated_o = self.translate_operand(o, true)?;
            let type_of_o = self.get_type_of_operand(o);
            translated_ops.push(translated_o);
            operand_types.push(type_of_o);
        }

        match *kind {
            mir::AggregateKind::Tuple => {
                if operand_types.is_empty() {
                    // translate to unit literal
                    return Ok(radium::Expr::Literal(radium::Literal::ZST));
                }

                let struct_use = self.ty_translator.generate_tuple_use(operand_types.iter().copied())?;
                let sl = struct_use.generate_raw_syn_type_term();
                let initializers: Vec<_> =
                    translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();

                Ok(radium::Expr::StructInitE {
                    sls: coq::term::App::new_lhs(sl.to_string()),
                    components: initializers,
                })
            },

            mir::AggregateKind::Adt(did, variant, args, ..) => {
                // get the adt def
                let adt_def: ty::AdtDef<'tcx> = self.env.tcx().adt_def(did);

                if adt_def.is_struct() {
                    let variant = adt_def.variant(variant);
                    let struct_use = self.ty_translator.generate_struct_use(variant.def_id, args)?;

                    let Some(struct_use) = struct_use else {
                        // if not, it's replaced by unit
                        return Ok(radium::Expr::Literal(radium::Literal::ZST));
                    };

                    let sl = struct_use.generate_raw_syn_type_term();
                    let initializers: Vec<_> = translated_ops
                        .into_iter()
                        .zip(variant.fields.iter())
                        .map(|(o, field)| (field.name.to_string(), o))
                        .collect();

                    return Ok(radium::Expr::StructInitE {
                        sls: coq::term::App::new_lhs(sl.to_string()),
                        components: initializers,
                    });
                }

                if adt_def.is_enum() {
                    let variant_def = adt_def.variant(variant);

                    let struct_use =
                        self.ty_translator.generate_enum_variant_use(variant_def.def_id, args)?;
                    let sl = struct_use.generate_raw_syn_type_term();

                    let initializers: Vec<_> = translated_ops
                        .into_iter()
                        .zip(variant_def.fields.iter())
                        .map(|(o, field)| (field.name.to_string(), o))
                        .collect();

                    let variant_e = radium::Expr::StructInitE {
                        sls: coq::term::App::new_lhs(sl.to_string()),
                        components: initializers,
                    };

                    let enum_use = self.ty_translator.generate_enum_use(adt_def, args)?;
                    let els = enum_use.generate_raw_syn_type_term();

                    info!("generating enum annotation for type {:?}", enum_use);
                    let ty = radium::RustType::of_type(&radium::Type::Literal(enum_use));
                    let variant_name = variant_def.name.to_string();

                    return Ok(radium::Expr::EnumInitE {
                        els: coq::term::App::new_lhs(els.to_string()),
                        variant: variant_name,
                        ty,
                        initializer: Box::new(variant_e),
                    });
                }

                // TODO
                Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support aggregate rvalue for other ADTs (got: {kind:?}, {op:?})"
                    ),
                })
            },
            mir::AggregateKind::Closure(def, _args) => {
                trace!("Translating Closure aggregate value for {:?}", def);

                // We basically translate this to a tuple
                if operand_types.is_empty() {
                    // translate to unit literal
                    return Ok(radium::Expr::Literal(radium::Literal::ZST));
                }

                let struct_use = self.ty_translator.generate_tuple_use(operand_types.iter().copied())?;
                let sl = struct_use.generate_raw_syn_type_term();

                let initializers: Vec<_> =
                    translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();

                Ok(radium::Expr::StructInitE {
                    sls: coq::term::App::new_lhs(sl.to_string()),
                    components: initializers,
                })
            },

            _ => {
                // TODO
                Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support this kind of aggregate rvalue (got: {kind:?}, {op:?})"
                    ),
                })
            },
        }
    }

    fn translate_cast(
        &mut self,
        kind: mir::CastKind,
        op: &mir::Operand<'tcx>,
        to_ty: ty::Ty<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        let op_ty = self.get_type_of_operand(op);
        let op_st = self.ty_translator.translate_type_to_syn_type(op_ty)?;
        let op_ot = op_st.into();

        let translated_op = self.translate_operand(op, true)?;

        let target_st = self.ty_translator.translate_type_to_syn_type(to_ty)?;
        let target_ot = target_st.into();

        match kind {
            mir::CastKind::PointerCoercion(x) => match x {
                ty::adjustment::PointerCoercion::MutToConstPointer => Ok(radium::Expr::UnOp {
                    o: radium::Unop::Cast(radium::OpType::Ptr),
                    ot: radium::OpType::Ptr,
                    e: Box::new(translated_op),
                }),

                ty::adjustment::PointerCoercion::ArrayToPointer
                | ty::adjustment::PointerCoercion::ClosureFnPointer(_)
                | ty::adjustment::PointerCoercion::ReifyFnPointer
                | ty::adjustment::PointerCoercion::UnsafeFnPointer
                | ty::adjustment::PointerCoercion::Unsize => Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support this kind of pointer coercion (got: {kind:?})"
                    ),
                }),
            },

            mir::CastKind::DynStar => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support dyn* cast".to_owned(),
            }),

            mir::CastKind::IntToInt => {
                // Cast integer to integer
                Ok(radium::Expr::UnOp {
                    o: radium::Unop::Cast(target_ot),
                    ot: op_ot,
                    e: Box::new(translated_op),
                })
            },

            mir::CastKind::IntToFloat => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support int-to-float cast".to_owned(),
            }),

            mir::CastKind::FloatToInt => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support float-to-int cast".to_owned(),
            }),

            mir::CastKind::FloatToFloat => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support float-to-float cast".to_owned(),
            }),

            mir::CastKind::PtrToPtr => {
                match (op_ty.kind(), to_ty.kind()) {
                    (ty::TyKind::RawPtr(_), ty::TyKind::RawPtr(_)) => Ok(radium::Expr::UnOp {
                        o: radium::Unop::Cast(radium::OpType::Ptr),
                        ot: radium::OpType::Ptr,
                        e: Box::new(translated_op),
                    }),

                    _ => {
                        // TODO: any other cases we should handle?
                        Err(TranslationError::UnsupportedFeature {
                            description: format!(
                                "RefinedRust does currently not support ptr-to-ptr cast (got: {kind:?}, {op:?}, {to_ty:?})"
                            ),
                        })
                    },
                }
            },

            mir::CastKind::FnPtrToPtr => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support fnptr-to-ptr cast (got: {kind:?}, {op:?}, {to_ty:?})"
                ),
            }),

            mir::CastKind::Transmute => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support transmute cast (got: {kind:?}, {op:?}, {to_ty:?})"
                ),
            }),

            mir::CastKind::PointerExposeAddress => {
                // Cast pointer to integer
                Ok(radium::Expr::UnOp {
                    o: radium::Unop::Cast(target_ot),
                    ot: radium::OpType::Ptr,
                    e: Box::new(translated_op),
                })
            },

            mir::CastKind::PointerFromExposedAddress => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of cast (got: {kind:?}, {op:?}, {to_ty:?})"
                ),
            }),
        }
    }

    /// Translate an operand.
    /// This will either generate an lvalue (in case of Move or Copy) or an rvalue (in most cases
    /// of Constant). How this is used depends on the context. (e.g., Use of an integer constant
    /// does not typecheck, and produces a stuck program).
    pub(super) fn translate_operand(
        &mut self,
        op: &mir::Operand<'tcx>,
        to_rvalue: bool,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        match op {
            // In Caesium: typed_place needs deref (not use) for place accesses.
            // use is used top-level to convert an lvalue to an rvalue, which is why we use it here.
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                // check if this goes to a temporary of a checked op
                let place_kind = if self.checked_op_temporaries.contains_key(&place.local) {
                    assert!(place.projection.len() == 1);

                    let mir::ProjectionElem::Field(f, _0) = place.projection[0] else {
                        unreachable!("invariant violation for access to checked op temporary");
                    };

                    if f.index() != 0 {
                        // make this a constant false -- our semantics directly checks for overflows
                        // and otherwise throws UB.
                        return Ok(radium::Expr::Literal(radium::Literal::Bool(false)));
                    }

                    // access to the result of the op
                    self.make_local_place(place.local)
                } else {
                    *place
                };

                let translated_place = self.translate_place(&place_kind)?;
                let ty = self.get_type_of_place(place);

                let st = self.ty_translator.translate_type_to_syn_type(ty.ty)?;

                if to_rvalue {
                    Ok(radium::Expr::Use {
                        ot: st.into(),
                        e: Box::new(translated_place),
                    })
                } else {
                    Ok(translated_place)
                }
            },
            mir::Operand::Constant(constant) => {
                // TODO: possibly need different handling of the rvalue flag
                // when this also handles string literals etc.
                return self.translate_constant(constant.as_ref());
            },
        }
    }

    /// Translates an Rvalue.
    pub(super) fn translate_rvalue(
        &mut self,
        loc: mir::Location,
        rval: &mir::Rvalue<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        match rval {
            mir::Rvalue::Use(op) => {
                // converts an lvalue to an rvalue
                self.translate_operand(op, true)
            },

            mir::Rvalue::Ref(region, bk, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_bk = TX::translate_borrow_kind(*bk)?;
                let ty_annot = self.get_type_annotation_for_borrow(*bk, pl)?;

                if let Some(loan) = self.info.get_optional_loan_at_location(loc) {
                    let atomic_region = self.info.atomic_region_of_loan(loan);
                    let lft = self.ty_translator.format_atomic_region(&atomic_region);
                    Ok(radium::Expr::Borrow {
                        lft,
                        bk: translated_bk,
                        ty: ty_annot,
                        e: Box::new(translated_pl),
                    })
                } else {
                    info!("Didn't find loan at {:?}: {:?}; region {:?}", loc, rval, region);
                    let region = regions::region_to_region_vid(*region);
                    let lft = self.format_region(region);

                    Ok(radium::Expr::Borrow {
                        lft,
                        bk: translated_bk,
                        ty: ty_annot,
                        e: Box::new(translated_pl),
                    })
                }
            },

            mir::Rvalue::AddressOf(mt, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_mt = TX::translate_mutability(*mt);

                Ok(radium::Expr::AddressOf {
                    mt: translated_mt,
                    e: Box::new(translated_pl),
                })
            },

            mir::Rvalue::BinaryOp(op, operands) => {
                let e1 = &operands.as_ref().0;
                let e2 = &operands.as_ref().1;

                let e1_ty = self.get_type_of_operand(e1);
                let e2_ty = self.get_type_of_operand(e2);
                let e1_st = self.ty_translator.translate_type_to_syn_type(e1_ty)?;
                let e2_st = self.ty_translator.translate_type_to_syn_type(e2_ty)?;

                let translated_e1 = self.translate_operand(e1, true)?;
                let translated_e2 = self.translate_operand(e2, true)?;
                let translated_op = self.translate_binop(*op, &operands.as_ref().0, &operands.as_ref().1)?;

                Ok(radium::Expr::BinOp {
                    o: translated_op,
                    ot1: e1_st.into(),
                    ot2: e2_st.into(),
                    e1: Box::new(translated_e1),
                    e2: Box::new(translated_e2),
                })
            },

            mir::Rvalue::CheckedBinaryOp(op, operands) => {
                let e1 = &operands.as_ref().0;
                let e2 = &operands.as_ref().1;

                let e1_ty = self.get_type_of_operand(e1);
                let e2_ty = self.get_type_of_operand(e2);
                let e1_st = self.ty_translator.translate_type_to_syn_type(e1_ty)?;
                let e2_st = self.ty_translator.translate_type_to_syn_type(e2_ty)?;

                let translated_e1 = self.translate_operand(e1, true)?;
                let translated_e2 = self.translate_operand(e2, true)?;
                let translated_op = TX::translate_checked_binop(*op)?;

                Ok(radium::Expr::BinOp {
                    o: translated_op,
                    ot1: e1_st.into(),
                    ot2: e2_st.into(),
                    e1: Box::new(translated_e1),
                    e2: Box::new(translated_e2),
                })
            },

            mir::Rvalue::UnaryOp(op, operand) => {
                let translated_e1 = self.translate_operand(operand, true)?;
                let e1_ty = self.get_type_of_operand(operand);
                let e1_st = self.ty_translator.translate_type_to_syn_type(e1_ty)?;
                let translated_op = TX::translate_unop(*op, e1_ty)?;

                Ok(radium::Expr::UnOp {
                    o: translated_op,
                    ot: e1_st.into(),
                    e: Box::new(translated_e1),
                })
            },

            mir::Rvalue::NullaryOp(_, _) => {
                // TODO: SizeOf
                Err(TranslationError::UnsupportedFeature {
                    description: "RefinedRust does currently not support nullary ops (AlignOf, Sizeof)"
                        .to_owned(),
                })
            },

            mir::Rvalue::Discriminant(pl) => {
                let ty = self.get_type_of_place(pl);
                let translated_pl = self.translate_place(pl)?;
                info!("getting discriminant of {:?} at type {:?}", pl, ty);

                let ty::TyKind::Adt(adt_def, args) = ty.ty.kind() else {
                    return Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "RefinedRust does currently not support discriminant accesses on non-enum types ({:?}, got {:?})",
                            rval, ty.ty
                        ),
                    });
                };

                let enum_use = self.ty_translator.generate_enum_use(*adt_def, args)?;
                let els = enum_use.generate_raw_syn_type_term();

                let discriminant_acc = radium::Expr::EnumDiscriminant {
                    els: els.to_string(),
                    e: Box::new(translated_pl),
                };

                Ok(discriminant_acc)
            },

            mir::Rvalue::Aggregate(kind, op) => self.translate_aggregate(kind.as_ref(), op),

            mir::Rvalue::Cast(kind, op, to_ty) => self.translate_cast(*kind, op, *to_ty),

            mir::Rvalue::CopyForDeref(_)
            | mir::Rvalue::Len(..)
            | mir::Rvalue::Repeat(..)
            | mir::Rvalue::ThreadLocalRef(..)
            | mir::Rvalue::ShallowInitBox(_, _) => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of rvalue (got: {:?})",
                    rval
                ),
            }),
        }
    }

    /// Get the type to annotate a borrow with.
    fn get_type_annotation_for_borrow(
        &self,
        bk: mir::BorrowKind,
        pl: &mir::Place<'tcx>,
    ) -> Result<Option<radium::RustType>, TranslationError<'tcx>> {
        let mir::BorrowKind::Mut { .. } = bk else {
            return Ok(None);
        };

        let ty = self.get_type_of_place(pl);

        // For borrows, we can safely ignore the downcast type -- we cannot borrow a particularly variant
        let translated_ty = self.ty_translator.translate_type(ty.ty)?;
        let annot_ty = radium::RustType::of_type(&translated_ty);

        Ok(Some(annot_ty))
    }

    /// Translate binary operators.
    /// We need access to the operands, too, to handle the offset operator and get the right
    /// Caesium layout annotation.
    fn translate_binop(
        &self,
        op: mir::BinOp,
        e1: &mir::Operand<'tcx>,
        _e2: &mir::Operand<'tcx>,
    ) -> Result<radium::Binop, TranslationError<'tcx>> {
        match op {
            mir::BinOp::Add | mir::BinOp::AddUnchecked => Ok(radium::Binop::Add),
            mir::BinOp::Sub | mir::BinOp::SubUnchecked => Ok(radium::Binop::Sub),
            mir::BinOp::Mul | mir::BinOp::MulUnchecked => Ok(radium::Binop::Mul),
            mir::BinOp::Div => Ok(radium::Binop::Div),
            mir::BinOp::Rem => Ok(radium::Binop::Mod),

            mir::BinOp::BitXor => Ok(radium::Binop::BitXor),
            mir::BinOp::BitAnd => Ok(radium::Binop::BitAnd),
            mir::BinOp::BitOr => Ok(radium::Binop::BitOr),
            mir::BinOp::Shl | mir::BinOp::ShlUnchecked => Ok(radium::Binop::Shl),
            mir::BinOp::Shr | mir::BinOp::ShrUnchecked => Ok(radium::Binop::Shr),

            mir::BinOp::Eq => Ok(radium::Binop::Eq),
            mir::BinOp::Lt => Ok(radium::Binop::Lt),
            mir::BinOp::Le => Ok(radium::Binop::Le),
            mir::BinOp::Ne => Ok(radium::Binop::Ne),
            mir::BinOp::Ge => Ok(radium::Binop::Ge),
            mir::BinOp::Gt => Ok(radium::Binop::Gt),

            mir::BinOp::Offset => {
                // we need to get the layout of the thing we're offsetting
                // try to get the type of e1.
                let e1_ty = self.get_type_of_operand(e1);
                let off_ty = TX::get_offset_ty(e1_ty)?;
                let st = self.ty_translator.translate_type_to_syn_type(off_ty)?;
                let ly = st.into();
                Ok(radium::Binop::PtrOffset(ly))
            },
        }
    }

    /// Get the inner type of a type to which we can apply the offset operator.
    fn get_offset_ty(ty: ty::Ty<'tcx>) -> Result<ty::Ty<'tcx>, TranslationError<'tcx>> {
        match ty.kind() {
            ty::TyKind::Array(t, _) | ty::TyKind::Slice(t) | ty::TyKind::Ref(_, t, _) => Ok(*t),
            ty::TyKind::RawPtr(tm) => Ok(tm.ty),
            _ => Err(TranslationError::UnknownError(format!("cannot take offset of {}", ty))),
        }
    }

    /// Translate checked binary operators.
    /// We need access to the operands, too, to handle the offset operator and get the right
    /// Caesium layout annotation.
    fn translate_checked_binop(op: mir::BinOp) -> Result<radium::Binop, TranslationError<'tcx>> {
        match op {
            mir::BinOp::Add => Ok(radium::Binop::CheckedAdd),
            mir::BinOp::Sub => Ok(radium::Binop::CheckedSub),
            mir::BinOp::Mul => Ok(radium::Binop::CheckedMul),
            mir::BinOp::Shl => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support checked Shl".to_owned(),
            }),
            mir::BinOp::Shr => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support checked Shr".to_owned(),
            }),
            _ => Err(TranslationError::UnknownError(
                "unexpected checked binop that is not Add, Sub, Mul, Shl, or Shr".to_owned(),
            )),
        }
    }

    /// Translate unary operators.
    fn translate_unop(op: mir::UnOp, ty: ty::Ty<'tcx>) -> Result<radium::Unop, TranslationError<'tcx>> {
        match op {
            mir::UnOp::Not => match ty.kind() {
                ty::TyKind::Bool => Ok(radium::Unop::NotBool),
                ty::TyKind::Int(_) | ty::TyKind::Uint(_) => Ok(radium::Unop::NotInt),
                _ => Err(TranslationError::UnknownError(
                    "application of UnOp::Not to non-{Int, Bool}".to_owned(),
                )),
            },
            mir::UnOp::Neg => Ok(radium::Unop::Neg),
        }
    }

    /// Translate a `BorrowKind`.
    fn translate_borrow_kind(kind: mir::BorrowKind) -> Result<radium::BorKind, TranslationError<'tcx>> {
        match kind {
            mir::BorrowKind::Shared => Ok(radium::BorKind::Shared),
            mir::BorrowKind::Shallow => {
                // TODO: figure out what to do with this
                // arises in match lowering
                Err(TranslationError::UnsupportedFeature {
                    description: "RefinedRust does currently not support shallow borrows".to_owned(),
                })
            },
            mir::BorrowKind::Mut { .. } => {
                // TODO: handle two-phase borrows?
                Ok(radium::BorKind::Mutable)
            },
        }
    }

    const fn translate_mutability(mt: mir::Mutability) -> radium::Mutability {
        match mt {
            mir::Mutability::Mut => radium::Mutability::Mut,
            mir::Mutability::Not => radium::Mutability::Shared,
        }
    }
}
