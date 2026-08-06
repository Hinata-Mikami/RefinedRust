// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::info;
use radium::code;
use rr_rustc_interface::middle::{mir, ty};

use super::TX;
use crate::base::*;
use crate::body::mir_lowering::{
    MirPlaceTranslation as _, MirRvalueTranslation as _, MirTranslationCtx as _, MirTypeTranslation as _,
};
use crate::error::Message;
use crate::procedures;

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate a single basic block.
    pub(crate) fn translate_basic_block(
        &mut self,
        bb_idx: mir::BasicBlock,
        bb: &mir::BasicBlockData<'tcx>,
    ) -> Result<code::Stmt, TranslationError> {
        let mut prim_stmts = Vec::new();

        for (idx, stmt) in bb.statements.iter().enumerate() {
            let loc = mir::Location {
                block: bb_idx,
                statement_index: idx,
            };
            let mut statement_annotation_plan = self.annotations.prepare_statement_annotation_plan(
                &self.ty_translator,
                loc,
                idx.checked_sub(1).map(|statement_index| mir::Location {
                    block: bb_idx,
                    statement_index,
                }),
            );
            statement_annotation_plan.push_pre_stmts(&mut prim_stmts);

            if self.is_administrative_alias_stmt(stmt) {
                info!("skipping synthetic administrative alias statement: {stmt:?}");
                continue;
            }

            if let mir::StatementKind::Assign(b) = &stmt.kind {
                let (plc, val) = b.as_ref();
                if self.proc.synthetic_drop_borrow_for_assignment(loc).is_some() {
                    let plc_ty = self.shape_type_of_place(plc);
                    let mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, borrowed_place) = val else {
                        return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                            Message::UnsupportedFeature(format!(
                                "synthetic drop borrow assignment is not a mutable borrow at {loc:?}: {stmt:?}"
                            )),
                        )));
                    };
                    let borrowed_place = self.translate_place(borrowed_place)?;
                    let raw_ptr = code::Expr::AddressOf {
                        pk: code::PtrKind::Ref,
                        mt: code::Mutability::Mut,
                        e: Box::new(borrowed_place),
                    };
                    let translated_place = self.translate_place(plc)?;
                    let synty = self.translate_type_to_syn_type(plc_ty.ty)?;
                    prim_stmts.push(code::PrimStmt::Assign {
                        ot: synty.into(),
                        e1: Box::new(translated_place),
                        e2: Box::new(raw_ptr),
                    });
                    continue;
                }
            }

            match &stmt.kind {
                mir::StatementKind::Assign(b) => {
                    let (plc, val) = b.as_ref();

                    if (self.is_spec_closure_local(plc.local)?).is_some() {
                        info!("skipping assignment to spec closure local: {:?}", plc);
                    } else {
                        let plc_ty = self.shape_type_of_place(plc);
                        let plc_region_ty = self.proc.region_type_of_place(plc);
                        let rhs_region_ty = self.proc.region_type_of_rvalue(loc, val);
                        // Assignment annotations depend on regionful borrowck types, but the
                        // executable statement is the dropck statement we are translating.
                        let annotation_val = self.proc.source_rvalue_for_target(loc).unwrap_or(val);
                        let rvalue_operand_tys =
                            self.proc.region_types_of_rvalue_operands_for_target(loc, val);
                        let shared_borrow_access_region =
                            self.proc.shared_borrow_access_region_for_target(loc, val);
                        let plc_strongly_writeable = !self.check_place_below_reference(plc);
                        let mut annotation_plan = self.annotations.prepare_assignment_annotation_plan(
                            &self.ty_translator,
                            &mut self.translated_fn,
                            loc,
                            annotation_val,
                            plc_region_ty,
                            rhs_region_ty,
                            &rvalue_operand_tys,
                            plc_strongly_writeable,
                            shared_borrow_access_region,
                        )?;
                        annotation_plan.push_pre_stmts(&mut prim_stmts);

                        let (e, _) = self.translate_rvalue(loc, val)?;
                        let expr_annot = annotation_plan.expr.take();
                        let translated_val = code::Expr::with_optional_annotation(
                            e,
                            expr_annot,
                            Some("assignment".to_owned()),
                        );
                        let translated_place = self.translate_place(plc)?;
                        let synty = self.translate_type_to_syn_type(plc_ty.ty)?;
                        prim_stmts.push(code::PrimStmt::Assign {
                            ot: synty.into(),
                            e1: Box::new(translated_place),
                            e2: Box::new(translated_val),
                        });

                        annotation_plan.push_post_stmts(&mut prim_stmts);
                    }
                },

                mir::StatementKind::FakeRead(b) => {
                    // we can probably ignore this, but I'm not sure
                    info!("Ignoring FakeRead: {:?}", b);
                },

                mir::StatementKind::Intrinsic(intrinsic) => {
                    match intrinsic.as_ref() {
                        mir::NonDivergingIntrinsic::Assume(_) => {
                            // ignore
                            info!("Ignoring Assume: {:?}", intrinsic);
                        },
                        mir::NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                                Message::UnsupportedFeature(
                                    "RefinedRust does currently not support the CopyNonOverlapping Intrinsic"
                                        .to_owned(),
                                ),
                            )));
                        },
                    }
                },

                mir::StatementKind::PlaceMention(place) => {
                    // TODO: this is missed UB
                    info!("Ignoring PlaceMention: {:?}", place);
                },

                mir::StatementKind::SetDiscriminant {
                    place: _place,
                    variant_index: _variant_index,
                } => {
                    // TODO
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                        Message::UnsupportedFeature(
                            "RefinedRust does currently not support SetDiscriminant".to_owned(),
                        ),
                    )));
                },

                | mir::StatementKind::StorageLive(l) => {
                    let ty = self.shape_type_of_local(*l)?;
                    let translated_st = self.translate_type_to_syn_type(ty)?;

                    if let Some(local_name) = self.variable_map().get(l) {
                        let var = code::Variable::new(local_name.to_owned(), translated_st);
                        prim_stmts.push(code::PrimStmt::LocalLive(var));
                    } else if self.proc.is_administrative_alias(*l) {
                        info!("ignoring StorageLive for synthetic administrative alias local {l:?}");
                    } else {
                        let ty::TyKind::Closure(did, _) = ty.kind() else {
                            unreachable!()
                        };
                        assert!(self.procedure_registry().lookup_function_mode(*did).is_some_and(procedures::Mode::is_ignore));
                    }
                },

                | mir::StatementKind::StorageDead(l) => {
                    let local_decls = &self.proc.dropck_mir().local_decls;
                    let local_decl = local_decls.get(*l).unwrap();
                    let ty = local_decl.ty;

                    if let Some(local_name) = self.variable_map().get(l) {
                        prim_stmts.push(code::PrimStmt::LocalDead(local_name.to_owned()));
                    } else if self.proc.is_administrative_alias(*l) {
                        info!("ignoring StorageDead for synthetic administrative alias local {l:?}");
                    } else {
                        let ty::TyKind::Closure(did, _) = ty.kind() else {
                            unreachable!()
                        };
                        assert!(self.procedure_registry().lookup_function_mode(*did).is_some_and(procedures::Mode::is_ignore));
                    }
                },

                // don't need that info
                | mir::StatementKind::AscribeUserType(_, _)
                // don't need that
                | mir::StatementKind::Coverage(_)
                // no-op
                | mir::StatementKind::ConstEvalCounter
                // ignore
                | mir::StatementKind::Nop
                // just ignore
                | mir::StatementKind::BackwardIncompatibleDropHint { .. } => (),
            }
        }

        let idx = bb.statements.len();
        let loc = mir::Location {
            block: bb_idx,
            statement_index: idx,
        };
        let mut terminator_entry_plan = self.annotations.prepare_statement_annotation_plan(
            &self.ty_translator,
            loc,
            idx.checked_sub(1).map(|statement_index| mir::Location {
                block: bb_idx,
                statement_index,
            }),
        );
        terminator_entry_plan.push_pre_stmts(&mut prim_stmts);
        let terminator = bb.terminator();
        let cont_stmt: code::Stmt = self.translate_terminator(terminator, loc)?;

        let cont_stmt = code::Stmt::Prim(prim_stmts, Box::new(cont_stmt));

        Ok(cont_stmt)
    }
}
