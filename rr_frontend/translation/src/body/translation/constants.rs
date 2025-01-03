// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{btree_map, BTreeMap, HashMap, HashSet};

use log::{info, trace, warn};
use radium::coq;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::interpret::{ConstValue, ErrorHandled, Scalar};
use rr_rustc_interface::middle::mir::tcx::PlaceTy;
use rr_rustc_interface::middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, BorrowKind, Constant, ConstantKind, Local, LocalKind, Location,
    Mutability, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, StatementKind, Terminator,
    TerminatorKind, UnOp, VarDebugInfoContents,
};
use rr_rustc_interface::middle::ty::fold::TypeFolder;
use rr_rustc_interface::middle::ty::{ConstKind, Ty, TyKind};
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{abi, ast, middle};
use typed_arena::Arena;

use super::TX;
use crate::base::*;
use crate::body::checked_op_analysis::CheckedOpLocalAnalysis;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::environment::{dump_borrowck_info, polonius_info, Environment};
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::spec_parsers::parse_utils::ParamLookup;
use crate::spec_parsers::verbose_function_spec_parser::{
    ClosureMetaInfo, FunctionRequirements, FunctionSpecParser, VerboseFunctionSpecParser,
};
use crate::traits::{registry, resolution};
use crate::{base, consts, procedures, regions, search, traits, types};

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate a scalar at a specific type to a `radium::Expr`.
    // TODO: Use `TryFrom` instead
    fn translate_scalar(
        &mut self,
        sc: &Scalar,
        ty: Ty<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        // TODO: Use `TryFrom` instead
        fn translate_literal<'tcx, T, U>(
            sc: Result<T, U>,
            fptr: fn(T) -> radium::Literal,
        ) -> Result<radium::Expr, TranslationError<'tcx>> {
            sc.map_or(Err(TranslationError::InvalidLayout), |lit| Ok(radium::Expr::Literal(fptr(lit))))
        }

        match ty.kind() {
            TyKind::Bool => translate_literal(sc.to_bool(), radium::Literal::Bool),

            TyKind::Int(it) => match it {
                ty::IntTy::I8 => translate_literal(sc.to_i8(), radium::Literal::I8),
                ty::IntTy::I16 => translate_literal(sc.to_i16(), radium::Literal::I16),
                ty::IntTy::I32 => translate_literal(sc.to_i32(), radium::Literal::I32),
                ty::IntTy::I128 => translate_literal(sc.to_i128(), radium::Literal::I128),

                // For Radium, the pointer size is 8 bytes
                ty::IntTy::I64 | ty::IntTy::Isize => translate_literal(sc.to_i64(), radium::Literal::I64),
            },

            TyKind::Uint(it) => match it {
                ty::UintTy::U8 => translate_literal(sc.to_u8(), radium::Literal::U8),
                ty::UintTy::U16 => translate_literal(sc.to_u16(), radium::Literal::U16),
                ty::UintTy::U32 => translate_literal(sc.to_u32(), radium::Literal::U32),
                ty::UintTy::U128 => translate_literal(sc.to_u128(), radium::Literal::U128),

                // For Radium, the pointer is 8 bytes
                ty::UintTy::U64 | ty::UintTy::Usize => translate_literal(sc.to_u64(), radium::Literal::U64),
            },

            TyKind::Char => translate_literal(sc.to_char(), radium::Literal::Char),

            TyKind::FnDef(_, _) => self.translate_fn_def_use(ty),

            TyKind::Tuple(tys) => {
                if tys.is_empty() {
                    return Ok(radium::Expr::Literal(radium::Literal::ZST));
                }

                Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support compound construction of tuples using literals (got: {:?})",
                        ty
                    ),
                })
            },

            TyKind::Ref(_, _, _) => match sc {
                Scalar::Int(_) => unreachable!(),

                Scalar::Ptr(pointer, _) => {
                    let glob_alloc = self.env.tcx().global_alloc(pointer.provenance);
                    match glob_alloc {
                        middle::mir::interpret::GlobalAlloc::Static(did) => {
                            info!(
                                "Found static GlobalAlloc {:?} for Ref scalar {:?} at type {:?}",
                                did, sc, ty
                            );

                            let s = self.const_registry.get_static(did)?;
                            self.collected_statics.insert(did);
                            Ok(radium::Expr::Literal(radium::Literal::Loc(s.loc_name.clone())))
                        },
                        middle::mir::interpret::GlobalAlloc::Memory(alloc) => {
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

    /// Translate a constant value from const evaluation.
    fn translate_constant_value(
        &mut self,
        v: mir::interpret::ConstValue<'tcx>,
        ty: Ty<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        match v {
            ConstValue::Scalar(sc) => self.translate_scalar(&sc, ty),
            ConstValue::ZeroSized => {
                // TODO are there more special cases we need to handle somehow?
                match ty.kind() {
                    TyKind::FnDef(_, _) => {
                        info!("Translating ZST val for function call target: {:?}", ty);
                        self.translate_fn_def_use(ty)
                    },
                    _ => Ok(radium::Expr::Literal(radium::Literal::ZST)),
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

    /// Translate a Constant to a `radium::Expr`.
    pub(super) fn translate_constant(
        &mut self,
        constant: &Constant<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        match constant.literal {
            ConstantKind::Ty(v) => {
                let const_ty = v.ty();

                match v.kind() {
                    ConstKind::Value(v) => {
                        // this doesn't contain the necessary structure anymore. Need to reconstruct using the
                        // type.
                        match v.try_to_scalar() {
                            Some(sc) => self.translate_scalar(&sc, const_ty),
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
            ConstantKind::Val(val, ty) => self.translate_constant_value(val, ty),
            ConstantKind::Unevaluated(c, ty) => {
                // call const evaluation
                let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(self.proc.get_id());
                match self.env.tcx().const_eval_resolve(param_env, c, None) {
                    Ok(res) => self.translate_constant_value(res, ty),
                    Err(e) => match e {
                        ErrorHandled::Reported(_) => Err(TranslationError::UnsupportedFeature {
                            description: "Cannot interpret constant".to_owned(),
                        }),
                        ErrorHandled::TooGeneric => Err(TranslationError::UnsupportedFeature {
                            description: "Const use is too generic".to_owned(),
                        }),
                    },
                }
            },
        }
    }
}
