// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::info;
use radium::code;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::span;

use super::TX;
use crate::base::*;

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate a scalar at a specific type to a `code::Expr`.
    // TODO: Use `TryFrom` instead
    fn translate_scalar(
        &mut self,
        sc: &mir::interpret::Scalar,
        ty: ty::Ty<'tcx>,
    ) -> Result<code::Expr, TranslationError<'tcx>> {
        // TODO: Use `TryFrom` instead
        fn translate_literal<'tcx, T>(
            sc: mir::interpret::InterpResult<'tcx, T>,
            fptr: fn(T) -> code::Literal,
        ) -> Result<code::Expr, TranslationError<'tcx>> {
            sc.discard_err()
                .map_or(Err(TranslationError::InvalidLayout), |lit| Ok(code::Expr::Literal(fptr(lit))))
        }

        match ty.kind() {
            ty::TyKind::Bool => translate_literal(sc.to_bool(), code::Literal::Bool),

            ty::TyKind::Int(it) => match it {
                ty::IntTy::I8 => translate_literal(sc.to_i8(), code::Literal::I8),
                ty::IntTy::I16 => translate_literal(sc.to_i16(), code::Literal::I16),
                ty::IntTy::I32 => translate_literal(sc.to_i32(), code::Literal::I32),
                ty::IntTy::I128 => translate_literal(sc.to_i128(), code::Literal::I128),
                ty::IntTy::I64 => translate_literal(sc.to_i64(), code::Literal::I64),
                // for Radium, we use 64-bit pointers
                ty::IntTy::Isize => translate_literal(sc.to_i64(), code::Literal::ISize),
            },

            ty::TyKind::Uint(it) => match it {
                ty::UintTy::U8 => translate_literal(sc.to_u8(), code::Literal::U8),
                ty::UintTy::U16 => translate_literal(sc.to_u16(), code::Literal::U16),
                ty::UintTy::U32 => translate_literal(sc.to_u32(), code::Literal::U32),
                ty::UintTy::U128 => translate_literal(sc.to_u128(), code::Literal::U128),
                ty::UintTy::U64 => translate_literal(sc.to_u64(), code::Literal::U64),
                // for Radium, we use 64-bit pointers
                ty::UintTy::Usize => translate_literal(sc.to_u64(), code::Literal::USize),
            },

            ty::TyKind::Char => translate_literal(sc.to_char(), code::Literal::Char),

            ty::TyKind::FnDef(_, _) => self.translate_fn_def_use(ty).map(Into::into),

            ty::TyKind::Tuple(tys) => {
                if tys.is_empty() {
                    return Ok(code::Expr::Literal(code::Literal::ZST));
                }

                Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support compound construction of tuples using literals (got: {:?})",
                        ty
                    ),
                })
            },

            ty::TyKind::Ref(_, _, _) => match sc {
                mir::interpret::Scalar::Int(_) => unreachable!(),

                mir::interpret::Scalar::Ptr(pointer, _) => {
                    let glob_alloc = self.env.tcx().global_alloc(pointer.provenance.alloc_id());
                    match glob_alloc {
                        mir::interpret::GlobalAlloc::Static(did) => {
                            info!(
                                "Found static GlobalAlloc {:?} for Ref scalar {:?} at type {:?}",
                                did, sc, ty
                            );

                            let s = self.const_registry.get_static(did)?;
                            self.collected_statics.insert(did);
                            Ok(code::Expr::Literal(code::Literal::Loc(s.loc_name.clone())))
                        },
                        mir::interpret::GlobalAlloc::Memory(_) => {
                            // TODO: this is needed
                            Err(TranslationError::UnsupportedFeature {
                                description: format!(
                                    "RefinedRust does currently not support GlobalAlloc {:?} for scalar {:?} at type {:?}",
                                    glob_alloc, sc, ty
                                ),
                            })
                        },
                        _ => Err(TranslationError::UnsupportedFeature {
                            description: format!(
                                "RefinedRust does currently not support GlobalAlloc {:?} for scalar {:?} at type {:?}",
                                glob_alloc, sc, ty
                            ),
                        }),
                    }
                },
            },

            _ => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support layout for const value: (got: {:?})",
                    ty
                ),
            }),
        }
    }

    //enum ConstantKind {
    //Scalar(mir::interpret::Scalar, ty::Ty<'tcx>),
    //Fn(ty::Ty<'tcx>),
    //}

    /// Translate a constant value from const evaluation.
    fn translate_constant_value(
        &mut self,
        v: mir::ConstValue,
        ty: ty::Ty<'tcx>,
    ) -> Result<code::Expr, TranslationError<'tcx>> {
        match v {
            mir::ConstValue::Scalar(sc) => self.translate_scalar(&sc, ty),
            mir::ConstValue::ZeroSized => {
                // TODO are there more special cases we need to handle somehow?
                match ty.kind() {
                    ty::TyKind::FnDef(_, _) => {
                        info!("Translating ZST val for function call target: {:?}", ty);
                        self.translate_fn_def_use(ty).map(Into::into)
                    },
                    _ => Ok(code::Expr::Literal(code::Literal::ZST)),
                }
            },
            _ => {
                // TODO: do we actually care about this case or is this just something that can
                // appear as part of CTFE/MIRI?
                Err(TranslationError::UnsupportedFeature {
                    description: format!("Unsupported Constant: ConstValue; {:?}", v),
                })
            },
        }
    }

    /// Translate a `mir::Constant` to a `code::Expr`.
    pub(crate) fn translate_constant(
        &mut self,
        constant: &mir::Const<'tcx>,
    ) -> Result<code::Expr, TranslationError<'tcx>> {
        match constant {
            mir::Const::Ty(_const_ty, v) => {
                match v.kind() {
                    ty::ConstKind::Value(v) => {
                        // this doesn't contain the necessary structure anymore. Need to reconstruct using the
                        // type.
                        match v.valtree.try_to_scalar() {
                            Some(sc) => self.translate_scalar(&sc, v.ty),
                            _ => Err(TranslationError::UnsupportedFeature {
                                description: format!("const value not supported: {:?}", v),
                            }),
                        }
                    },
                    _ => Err(TranslationError::UnsupportedFeature {
                        description: "Unsupported ConstKind".to_owned(),
                    }),
                }
            },
            mir::Const::Val(val, ty) => self.translate_constant_value(*val, *ty),
            mir::Const::Unevaluated(c, ty) => {
                // call const evaluation
                let typing_env = ty::TypingEnv::post_analysis(self.env.tcx(), self.proc.get_id());
                match self.env.tcx().const_eval_resolve(typing_env, *c, span::DUMMY_SP) {
                    Ok(res) => self.translate_constant_value(res, *ty),
                    Err(e) => match e {
                        mir::interpret::ErrorHandled::Reported(_, _) => {
                            Err(TranslationError::UnsupportedFeature {
                                description: "Cannot interpret constant".to_owned(),
                            })
                        },
                        mir::interpret::ErrorHandled::TooGeneric(_) => {
                            Err(TranslationError::UnsupportedFeature {
                                description: "Const use is too generic".to_owned(),
                            })
                        },
                    },
                }
            },
        }
    }
}
