// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;
use std::iter::repeat_n;

use log::info;
use radium::{code, lang, specs};
use rr_rustc_interface::middle::{mir, ty};

use super::DropGlueTX;
use crate::base::*;
use crate::body::mir_lowering::{
    MirDropTranslation as _, MirPlaceTranslation as _, MirRvalueTranslation as _, MirTranslationCtx as _,
    MirTypeTranslation as _,
};
use crate::error::Message;

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> DropGlueTX<'a, 'def, 'tcx> {
    /// Translate a single rustc-generated drop-glue basic block.
    pub(crate) fn translate_basic_block(
        &mut self,
        bb_idx: mir::BasicBlock,
        bb: &mir::BasicBlockData<'tcx>,
    ) -> Result<code::Stmt, TranslationError> {
        let mut prim_stmts = Vec::new();
        if bb_idx == mir::BasicBlock::from_u32(0) {
            prim_stmts.extend(self.initial_always_live_stmts()?);
        }

        for (idx, stmt) in bb.statements.iter().enumerate() {
            let loc = mir::Location {
                block: bb_idx,
                statement_index: idx,
            };
            self.translate_statement(loc, stmt, &mut prim_stmts)?;
        }

        let loc = mir::Location {
            block: bb_idx,
            statement_index: bb.statements.len(),
        };
        let cont_stmt = self.translate_terminator(bb.terminator(), loc)?;
        Ok(code::Stmt::Prim(prim_stmts, Box::new(cont_stmt)))
    }

    /// Translate a single drop-glue MIR statement.
    pub(crate) fn translate_statement(
        &mut self,
        loc: mir::Location,
        stmt: &mir::Statement<'tcx>,
        prim_stmts: &mut Vec<code::PrimStmt>,
    ) -> Result<(), TranslationError> {
        match &stmt.kind {
            mir::StatementKind::Assign(assign) => {
                let (plc, val) = assign.as_ref();
                let plc_ty = self.shape_type_of_place(plc);
                let (translated_val, _) = self.translate_rvalue(loc, val)?;
                let translated_place = self.translate_place(plc)?;
                let synty = self.translate_type_to_syn_type(plc_ty.ty)?;
                prim_stmts.push(code::PrimStmt::Assign {
                    ot: synty.into(),
                    e1: Box::new(translated_place),
                    e2: Box::new(translated_val),
                });
            },

            mir::StatementKind::StorageLive(local) => {
                if let Some(local_name) = self.variable_map().get(local) {
                    let ty = self.shape_type_of_local(*local)?;
                    let translated_st = self.translate_type_to_syn_type(ty)?;
                    let var = code::Variable::new(local_name.to_owned(), translated_st);
                    prim_stmts.push(code::PrimStmt::LocalLive(var));
                }
            },

            mir::StatementKind::StorageDead(local) => {
                if let Some(local_name) = self.variable_map().get(local) {
                    prim_stmts.push(code::PrimStmt::LocalDead(local_name.to_owned()));
                }
            },

            mir::StatementKind::FakeRead(fake_read) => {
                info!("Ignoring drop-glue FakeRead at {loc:?}: {fake_read:?}");
            },

            mir::StatementKind::PlaceMention(place) => {
                info!("Ignoring drop-glue PlaceMention at {loc:?}: {place:?}");
            },

            mir::StatementKind::AscribeUserType(_, _)
            | mir::StatementKind::Coverage(_)
            | mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop => {},

            mir::StatementKind::Intrinsic(intrinsic) => match intrinsic.as_ref() {
                mir::NonDivergingIntrinsic::Assume(_) => {
                    info!("Ignoring drop-glue Assume intrinsic at {loc:?}: {intrinsic:?}");
                },
                mir::NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                        Message::UnsupportedFeature(format!(
                            "drop-glue translation does not support MIR statement at {loc:?}: {stmt:?}"
                        )),
                    )));
                },
            },

            mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::BackwardIncompatibleDropHint { .. } => {
                return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                    Message::UnsupportedFeature(format!(
                        "drop-glue translation does not support MIR statement at {loc:?}: {stmt:?}"
                    )),
                )));
            },
        }

        Ok(())
    }

    /// Translate a goto-like jump to `target`.
    pub(crate) fn translate_goto_like(&mut self, _loc: mir::Location, target: mir::BasicBlock) -> code::Stmt {
        self.enqueue_basic_block(target);
        code::Stmt::GotoBlock(target.as_usize())
    }

    /// Translate a drop-glue terminator conservatively.
    pub(crate) fn translate_terminator(
        &mut self,
        term: &mir::Terminator<'tcx>,
        loc: mir::Location,
    ) -> Result<code::Stmt, TranslationError> {
        match &term.kind {
            mir::TerminatorKind::Goto { target } => Ok(self.translate_goto_like(loc, *target)),
            mir::TerminatorKind::Return => Ok(code::Stmt::Return(code::Expr::Literal(code::Literal::ZST))),
            mir::TerminatorKind::Unreachable => Ok(code::Stmt::Stuck),

            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let (operand, _) = self.translate_operand(discr, true)?;
                let all_targets: &[mir::BasicBlock] = targets.all_targets();

                if self.shape_type_of_operand(discr).is_bool() {
                    let true_target = all_targets[1];
                    let false_target = all_targets[0];

                    let true_branch = self.translate_goto_like(loc, true_target);
                    let false_branch = self.translate_goto_like(loc, false_target);

                    return Ok(code::Stmt::If {
                        e: operand,
                        ot: lang::OpType::Bool,
                        s1: Box::new(true_branch),
                        s2: Box::new(false_branch),
                    });
                }

                let ty = self.shape_type_of_operand(discr);
                let mut target_map: BTreeMap<u128, usize> = BTreeMap::new();
                let mut translated_targets: Vec<code::Stmt> = Vec::new();

                for (idx, (value, bb)) in targets.iter().enumerate() {
                    let translated_target = self.translate_goto_like(loc, bb);
                    target_map.insert(value, idx);
                    translated_targets.push(translated_target);
                }

                let translated_default = self.translate_goto_like(loc, targets.otherwise());
                let translated_ty = self.translate_drop_glue_type(ty)?;
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

            mir::TerminatorKind::Drop { place, target, .. } => {
                let stmt = self.translate_goto_like(loc, *target);
                let mut prim_stmts = Vec::new();

                let ty = self.semantic_type_of_place(place)?;
                let typing_env = ty::TypingEnv::post_analysis(self.tcx, self.adt_did);
                if self.tcx.needs_drop_raw(typing_env.as_query_input(ty)) {
                    let (func_expr, call_info) = self.register_use_drop_glue(ty)?;

                    let place_translated = self.translate_place(place)?;
                    let raw_place = code::Expr::AddressOf {
                        pk: code::PtrKind::Ref,
                        mt: code::Mutability::Mut,
                        e: Box::new(place_translated),
                    };

                    let ty_hint =
                        call_info.type_hint.into_iter().map(|x| code::RustType::of_type(&x)).collect();
                    let call_expr = code::Expr::Call {
                        f: Box::new(func_expr),
                        lfts: call_info.lft_hint,
                        tys: ty_hint,
                        args: vec![raw_place],
                    };
                    prim_stmts.push(code::PrimStmt::ExprS(Box::new(call_expr)));
                }

                Ok(code::Stmt::Prim(prim_stmts, Box::new(stmt)))
            },

            mir::TerminatorKind::Call {
                func, args, target, ..
            } => {
                let Some(target) = target else {
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                        Message::UnsupportedFeature(format!(
                            "drop-glue destructor call at {loc:?} does not have a normal target: {term:?}"
                        )),
                    )));
                };

                let (func_expr, call_info) = self.translate_operand(func, false)?;
                let Some(mut call_info) = call_info else {
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                        Message::UnsupportedFeature(format!(
                            "drop-glue Call terminator at {loc:?} does not have a supported destructor target: {term:?}"
                        )),
                    )));
                };

                let mut translated_args = Vec::new();
                for arg in args {
                    translated_args.push(self.translate_operand(&arg.node, true)?.0);
                }

                // Drop-glue MIR has no source-call region facts. Use the always-in-scope function
                // lifetime for destructor-call late bounds, matching synthetic `Drop::drop` calls.
                call_info.lft_hint.extend(repeat_n(specs::Lft::new("_flft"), call_info.num_of_latebounds));
                let ty_hint = call_info.type_hint.into_iter().map(|x| code::RustType::of_type(&x)).collect();
                let call_expr = code::Expr::Call {
                    f: Box::new(func_expr),
                    lfts: call_info.lft_hint,
                    tys: ty_hint,
                    args: translated_args,
                };

                let stmt = self.translate_goto_like(loc, *target);
                Ok(code::Stmt::Prim(vec![code::PrimStmt::ExprS(Box::new(call_expr))], Box::new(stmt)))
            },

            mir::TerminatorKind::TailCall { .. }
            | mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::InlineAsm { .. }
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::Assert { .. }
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. } => {
                Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                    format!("drop-glue translation does not support MIR terminator at {loc:?}: {term:?}"),
                ))))
            },
        }
    }
}
