// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;
use std::iter::repeat_n;

use log::{info, trace, warn};
use radium::{code, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{bug, mir, ty};

use super::{ExprInfo, TX};
use crate::base::*;
use crate::body::mir_lowering::{
    MirDropTranslation as _, MirPlaceTranslation as _, MirRvalueTranslation as _, MirTranslationCtx as _,
    MirTypeTranslation as _, translate_unwind_action,
};
use crate::error::Message;
use crate::{search, types};

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    fn check_call_destination(func: &mir::Operand<'_>, target_did: DefId) -> bool {
        let mir::Operand::Constant(box c) = func else {
            return false;
        };

        let mir::Const::Val(_, ty) = c.const_ else {
            return false;
        };

        let ty::TyKind::FnDef(did, _) = ty.kind() else {
            return false;
        };

        target_did == *did
    }

    /// Check if a call goes to `std::rt::begin_panic`
    pub(super) fn is_call_destination_panic(&self, func: &mir::Operand<'_>) -> bool {
        if let Some(panic_id_std) = search::try_resolve_did(self.tcx, &["std", "panicking", "begin_panic"]) {
            if Self::check_call_destination(func, panic_id_std) {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of std::panicking::begin_panic");
        }

        if let Some(panic_id_core) = search::try_resolve_did(self.tcx, &["core", "panicking", "panic"]) {
            if Self::check_call_destination(func, panic_id_core) {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of core::panicking::panic");
        }

        if let Some(panic_fmt_id) = search::try_resolve_did(self.tcx, &["core", "panicking", "panic_fmt"])
            && Self::check_call_destination(func, panic_fmt_id)
        {
            return true;
        }

        false
    }

    // Check if the destination of this call is `core::intrinsics::discriminant_value`.
    pub(super) fn is_call_destination_discriminant(&self, func: &mir::Operand<'_>) -> bool {
        if let Some(discriminant_did) =
            search::try_resolve_did(self.tcx, &["core", "intrinsics", "discriminant_value"])
        {
            if Self::check_call_destination(func, discriminant_did) {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of core::intrinsics::discriminant_value");
        }

        false
    }

    fn make_discriminant_shim(
        &mut self,
        op: &mir::Operand<'tcx>,
        dest: &mir::Place<'tcx>,
    ) -> Result<Vec<code::PrimStmt>, TranslationError> {
        let (translated_op, _) = self.translate_operand(op, false)?;
        let ty = self.shape_type_of_operand(op);

        let st = self.translate_type_to_syn_type(ty)?;
        let translated_rhs = code::Expr::Deref {
            ot: st.into(),
            e: Box::new(translated_op),
        };

        let ty::TyKind::Ref(_, ty, _) = ty.kind() else {
            unreachable!();
        };
        let ty::TyKind::Adt(adt_def, args) = ty.kind() else {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!("RefinedRust does currently not support discriminant accesses on non-enum types (got {:?})", ty),
            ))));
        };
        let enum_use = self.generate_enum_use(*adt_def, args)?;
        let els = enum_use.generate_raw_syn_type_term();

        let discriminant_acc = code::Expr::EnumDiscriminant {
            els: els.to_string(),
            e: Box::new(translated_rhs),
        };

        let translated_place = self.translate_place(dest)?;

        // get the discriminant type
        let it = adt_def.repr().discr_type();
        let translated_it = types::TX::translate_integer_type(it);

        let assign = code::PrimStmt::Assign {
            ot: lang::OpType::Int(translated_it),
            e1: Box::new(translated_place),
            e2: Box::new(discriminant_acc),
        };

        Ok(vec![assign])
    }

    pub(super) fn translate_unwind_action(
        &mut self,
        loc: &mir::Location,
        action: mir::UnwindAction,
    ) -> Result<code::Stmt, TranslationError> {
        let translated = translate_unwind_action(action, |target| self.translate_goto_like(loc, target))?;
        if matches!(action, mir::UnwindAction::Continue) {
            let mut plan = self.annotations.prepare_unwind_annotation_plan(&self.ty_translator, *loc);
            return Ok(code::Stmt::Prim(plan.take_pre_stmts(), Box::new(translated)));
        }
        Ok(translated)
    }

    /// Translate a terminator.
    pub(crate) fn translate_terminator(
        &mut self,
        term: &mir::Terminator<'tcx>,
        loc: mir::Location,
    ) -> Result<code::Stmt, TranslationError> {
        match &term.kind {
            mir::TerminatorKind::Goto { target } => self.translate_goto_like(&loc, *target),

            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                trace!("translating Call {:?}", term);
                if let Some(drop_borrow) = self.proc.synthetic_drop_borrow_for_drop_call(loc) {
                    // Dropck lowers open drops to an explicit `Drop::drop(&mut place)` call fed by a synthetic
                    // pointer. Translate this as a real destructor call, but do not use ordinary source-call
                    // region annotations because the borrowck source terminator is `Drop`, not `Call`.
                    let Some(target) = target else {
                        bug!("drop-elaborated Drop::drop call without normal target at {loc:?}");
                    };
                    let [arg] = args.as_ref() else {
                        return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                            Message::UnsupportedFeature(format!(
                                "drop-elaborated Drop::drop call at {loc:?} has unexpected arguments: {term:?}"
                            )),
                        )));
                    };
                    let (mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place)) = &arg.node else {
                        return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                            Message::UnsupportedFeature(format!(
                                "drop-elaborated Drop::drop call at {loc:?} has non-place argument: {term:?}"
                            )),
                        )));
                    };
                    if arg_place.local != drop_borrow.synthetic_ref_local() || !arg_place.projection.is_empty() {
                        return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                            Message::UnsupportedFeature(format!(
                                "drop-elaborated Drop::drop call at {loc:?} does not use the synthetic drop pointer: {term:?}"
                            )),
                        )));
                    }

                    let (func_expr, info) = self.translate_operand(func, false)?;
                    let Some(ExprInfo::Call(mut call_info)) = info else {
                        unreachable!("Logic error in drop call target translation");
                    };
                    // Ordinary calls instantiate late-bound lifetimes from Polonius call-region facts.
                    // This target call corresponds to a source `Drop` terminator instead, so use the
                    // always-in-scope function lifetime for the implicit `&mut self` lifetime.
                    call_info
                        .lft_hint
                        .extend(repeat_n(specs::Lft::new("_flft"), call_info.num_of_latebounds));
                    let translated_arg = self.translate_operand(&arg.node, true)?.0;
                    let ty_hint = call_info.type_hint.into_iter().map(|x| code::RustType::of_type(&x)).collect();
                    let destination_st = self.translate_type_to_syn_type(self.shape_type_of_place(destination).ty)?;
                    let destination = code::CallDestination {
                        order: lang::Order::Na1,
                        ot: destination_st.into(),
                        destination: self.translate_place(destination)?,
                    };
                    let normal = self.translate_goto_like(&loc, *target)?;
                    let unwind = self.translate_unwind_action(&loc, *unwind)?;
                    let call = code::Stmt::Call {
                        f: func_expr,
                        lfts: call_info.lft_hint,
                        tys: ty_hint,
                        args: vec![translated_arg],
                        destination: Box::new(Some(destination)),
                        normal: Box::new(normal),
                        unwind: Box::new(unwind),
                    };
                    return Ok(call);
                }

                if self.is_call_destination_panic(func) {
                    info!("Replacing direct panic call with its MIR unwind action");
                    return self.translate_unwind_action(&loc, *unwind);
                }
                if self.is_call_destination_discriminant(func) {
                    let op = &args[0].node;
                    let stmt = self.make_discriminant_shim(op, destination)?;
                    let goto = self.translate_goto_like(&loc, target.unwrap())?;

                    return Ok(code::Stmt::Prim(stmt, Box::new(goto)));
                }

                self.translate_function_call(func, args, destination, *target, *unwind, loc)
            },

            mir::TerminatorKind::Return => {
                let return_synty = self.translate_type_to_syn_type(self.return_ty)?;
                let mut annotation_plan = self.annotations.prepare_return_annotation_plan(
                    &self.ty_translator,
                    self.return_ty,
                );
                let annots = annotation_plan.take_pre_stmts();

                // read from the return place
                // Is this semantics accurate wrt what the intended MIR semantics is?
                // Possibly handle this differently by making the first argument of a function a dedicated
                // return place? See also discussion at https://github.com/rust-lang/rust/issues/71117
                let stmt = code::Stmt::Return(code::Expr::Move {
                    ot: (&return_synty).into(),
                    e: Box::new(code::Expr::Var(self.return_name.clone())),
                });

                // TODO is this right?
                Ok(code::Stmt::Prim(annots, Box::new(stmt)))
            },

            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let (operand, _) = self.translate_operand(discr, true)?;
                let all_targets: &[mir::BasicBlock] = targets.all_targets();

                if self.shape_type_of_operand(discr).is_bool() {
                    // we currently special-case this as Caesium has a built-in if and this is more
                    // convenient to handle for the type-checker

                    // implementation detail: the first index is the `false` branch, the second the
                    // `true` branch
                    let true_target = all_targets[1];
                    let false_target = all_targets[0];

                    let true_branch = self.translate_goto_like(&loc, true_target)?;
                    let false_branch = self.translate_goto_like(&loc, false_target)?;

                    let stmt = code::Stmt::If {
                        e: operand,
                        ot: lang::OpType::Bool,
                        s1: Box::new(true_branch),
                        s2: Box::new(false_branch),
                    };

                    return Ok(stmt);
                }

                //info!("switchint: {:?}", term.kind);
                let (operand, _) = self.translate_operand(discr, true)?;
                let ty = self.shape_type_of_operand(discr);

                let mut target_map: BTreeMap<u128, usize> = BTreeMap::new();
                let mut translated_targets: Vec<code::Stmt> = Vec::new();

                for (idx, (tgt, bb)) in targets.iter().enumerate() {
                    let bb: mir::BasicBlock = bb;
                    let translated_target = self.translate_goto_like(&loc, bb)?;

                    target_map.insert(tgt, idx);
                    translated_targets.push(translated_target);
                }

                let translated_default = self.translate_goto_like(&loc, targets.otherwise())?;
                let translated_ty = self.ty_translator.translate_type(ty)?;
                let specs::Type::Int(it) = translated_ty else {
                    return Err(TranslationError::ErrorReported(
                        self.tcx.dcx().err(Message::SwitchIntOnNonIntegerType),
                    ));
                };

                Ok(code::Stmt::Switch {
                    e: operand,
                    it,
                    index_map: target_map,
                    bs: translated_targets,
                    def: Box::new(translated_default),
                })
            },

            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                ..
            } => {
                let (cond_translated, _) = self.translate_operand(cond, true)?;
                let comp = code::Expr::BinOp {
                    o: code::Binop::Eq,
                    ot1: lang::OpType::Bool,
                    ot2: lang::OpType::Bool,
                    e1: Box::new(cond_translated),
                    e2: Box::new(code::Expr::Literal(code::Literal::Bool(*expected))),
                };

                let normal = self.translate_goto_like(&loc, *target)?;
                let unwind = self.translate_unwind_action(&loc, *unwind)?;
                let stmt = code::Stmt::If {
                    e: comp,
                    ot: lang::OpType::Bool,
                    s1: Box::new(normal),
                    s2: Box::new(unwind),
                };
                Ok(stmt)
            },

            mir::TerminatorKind::Drop {
                place,
                target,
                unwind,
                ..
            } => {
                let mut stmt = self.translate_goto_like(&loc, *target)?;

                let shape_ty = self.shape_type_of_place(place).ty;
                let typing_env = ty::TypingEnv::post_analysis(self.tcx, self.proc.get_id());
                if self.tcx.needs_drop_raw(typing_env.as_query_input(shape_ty)) {
                    let dropped_ty = self.proc.region_type_of_place(place).ty;
                    let (func_expr, call_info) = self.register_use_drop_glue(dropped_ty)?;

                    let place_translated = self.translate_place(place)?;
                    let raw_place = code::Expr::AddressOf {
                        pk: code::PtrKind::Ref,
                        mt: code::Mutability::Mut,
                        e: Box::new(place_translated),
                    };

                    let ty_hint = call_info.type_hint.into_iter().map(|x| code::RustType::of_type(&x)).collect();
                    let unwind = self.translate_unwind_action(&loc, *unwind)?;
                    stmt = code::Stmt::Call {
                        f: func_expr,
                        lfts: call_info.lft_hint,
                        tys: ty_hint,
                        args: vec![raw_place],
                        destination: Box::new(None),
                        normal: Box::new(stmt),
                        unwind: Box::new(unwind),
                    };
                }

                Ok(stmt)
            },

            // just a goto for our purposes
            mir::TerminatorKind::FalseEdge { real_target, .. }
            // this is just a virtual edge for the borrowchecker, we can translate this to a normal goto
            | mir::TerminatorKind::FalseUnwind { real_target, .. } => {
                self.translate_goto_like(&loc, *real_target)
            },

            mir::TerminatorKind::TailCall { .. } => {
                Err(TranslationError::ErrorReported(
                    self.tcx.dcx().err(Message::Unimplemented("implement TailCall".to_owned())),
                ))
            },

            mir::TerminatorKind::Unreachable => Ok(code::Stmt::Stuck),

            mir::TerminatorKind::UnwindResume => {
                let mut plan = self.annotations.prepare_unwind_annotation_plan(&self.ty_translator, loc);
                Ok(code::Stmt::Prim(plan.take_pre_stmts(), Box::new(code::Stmt::Unwind)))
            },

            mir::TerminatorKind::UnwindTerminate(_) => Ok(code::Stmt::UnwindTerminate),

            mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::InlineAsm { .. }
            | mir::TerminatorKind::Yield { .. } => Err(TranslationError::ErrorReported(
                self.tcx.dcx().err(Message::UnsupportedFeature(format!(
                    "RefinedRust does currently not support this kind of terminator (got: {:?})",
                    term
                ))),
            )),
        }
    }
}
