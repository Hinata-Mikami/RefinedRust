// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{btree_map, BTreeMap, HashMap, HashSet};

use log::info;
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

use super::TX;
use crate::base::*;
use crate::traits::{registry, resolution};
use crate::{base, consts, procedures, regions, search, traits, types};

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate a single basic block.
    pub(super) fn translate_basic_block(
        &mut self,
        bb_idx: BasicBlock,
        bb: &BasicBlockData<'tcx>,
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        // we translate from back to front, starting with the terminator, since Caesium statements
        // have a continuation (the next statement to execute)

        // first do the endlfts for the things right before the terminator
        let mut idx = bb.statements.len();
        let loc = Location {
            block: bb_idx,
            statement_index: idx,
        };
        let dying = self.info.get_dying_loans(loc);
        // TODO zombie?
        let _dying_zombie = self.info.get_dying_zombie_loans(loc);
        let mut cont_stmt: radium::Stmt = self.translate_terminator(bb.terminator(), loc, dying)?;

        //cont_stmt = self.prepend_endlfts(cont_stmt, loc, dying);
        //cont_stmt = self.prepend_endlfts(cont_stmt, loc, dying_zombie);

        for stmt in bb.statements.iter().rev() {
            idx -= 1;
            let loc = Location {
                block: bb_idx,
                statement_index: idx,
            };

            // get all dying loans, and emit endlfts for these.
            // We loop over all predecessor locations, since some loans may end at the start of a
            // basic block (in particular related to NLL stuff)
            let pred = self.get_loc_predecessors(loc);
            let mut dying_loans = HashSet::new();
            for p in pred {
                let dying_between = self.info.get_loans_dying_between(p, loc, false);
                for l in &dying_between {
                    dying_loans.insert(*l);
                }
                // also include zombies
                let dying_between = self.info.get_loans_dying_between(p, loc, true);
                for l in &dying_between {
                    dying_loans.insert(*l);
                }
            }
            // we prepend them before the current statement

            match &stmt.kind {
                StatementKind::Assign(b) => {
                    let (plc, val) = b.as_ref();

                    if (self.is_spec_closure_local(plc.local)?).is_some() {
                        info!("skipping assignment to spec closure local: {:?}", plc);
                    } else if let Some(rewritten_ty) = self.checked_op_temporaries.get(&plc.local) {
                        // if this is a checked op, be sure to remember it
                        info!("rewriting assignment to checked op: {:?}", plc);

                        let synty = self.ty_translator.translate_type_to_syn_type(*rewritten_ty)?;

                        let translated_val = self.translate_rvalue(loc, val)?;
                        let translated_place = self.translate_place(plc)?;

                        // this should be a temporary
                        assert!(plc.projection.is_empty());

                        let ot = synty.into();
                        cont_stmt = radium::Stmt::Assign {
                            ot,
                            e1: translated_place,
                            e2: translated_val,
                            s: Box::new(cont_stmt),
                        };
                    } else {
                        let plc_ty = self.get_type_of_place(plc);
                        let rhs_ty = val.ty(&self.proc.get_mir().local_decls, self.env.tcx());

                        let borrow_annots = regions::assignment::get_assignment_loan_annots(
                            &mut self.inclusion_tracker, &self.ty_translator,
                            loc, val);

                        let plc_ty = self.get_type_of_place(plc);
                        let plc_strongly_writeable = !self.check_place_below_reference(plc);
                        let assignment_annots =
                            regions::assignment::get_assignment_annots(
                                self.env, &mut self.inclusion_tracker, &self.ty_translator,
                                loc, plc_strongly_writeable, plc_ty, rhs_ty);

                        // TODO; maybe move this to rvalue
                        let composite_annots = regions::composite::get_composite_rvalue_creation_annots(
                            self.env, &mut self.inclusion_tracker, &self.ty_translator, loc, rhs_ty);

                        let unconstrained_annots = regions::assignment::make_unconstrained_region_annotations(self.env, &self.inclusion_tracker, &self.ty_translator, loc, assignment_annots.unconstrained_regions)?;

                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            assignment_annots.stmt_annot,
                            &Some("post-assignment".to_owned()),
                        );

                        let translated_val = radium::Expr::with_optional_annotation(
                            self.translate_rvalue(loc, val)?,
                            assignment_annots.expr_annot,
                            Some("assignment".to_owned()),
                        );
                        let translated_place = self.translate_place(plc)?;
                        let synty = self.ty_translator.translate_type_to_syn_type(plc_ty.ty)?;
                        cont_stmt = radium::Stmt::Assign {
                            ot: synty.into(),
                            e1: translated_place,
                            e2: translated_val,
                            s: Box::new(cont_stmt),
                        };
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            assignment_annots.new_dyn_inclusions,
                            &Some("assignment".to_owned()),
                        );
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            borrow_annots,
                            &Some("borrow".to_owned()),
                        );
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            composite_annots,
                            &Some("composite".to_owned()),
                        );
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            unconstrained_annots,
                            &Some("assignment (unconstrained)".to_owned()),
                        );
                    }
                },

                StatementKind::Deinit(_) => {
                    // TODO: find out where this is emitted
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support Deinit".to_owned(),
                    });
                },

                StatementKind::FakeRead(b) => {
                    // we can probably ignore this, but I'm not sure
                    info!("Ignoring FakeRead: {:?}", b);
                },

                StatementKind::Intrinsic(intrinsic) => {
                    match intrinsic.as_ref() {
                        NonDivergingIntrinsic::Assume(_) => {
                            // ignore
                            info!("Ignoring Assume: {:?}", intrinsic);
                        },
                        NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                            return Err(TranslationError::UnsupportedFeature {
                                description: "RefinedRust does currently not support the CopyNonOverlapping Intrinsic".to_owned(),
                            });
                        },
                    }
                },

                StatementKind::PlaceMention(place) => {
                    // TODO: this is missed UB
                    info!("Ignoring PlaceMention: {:?}", place);
                },

                StatementKind::SetDiscriminant {
                    place: _place,
                    variant_index: _variant_index,
                } => {
                    // TODO
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support SetDiscriminant".to_owned(),
                    });
                },

                // don't need that info
                | StatementKind::AscribeUserType(_, _)
                // don't need that
                | StatementKind::Coverage(_)
                // no-op
                | StatementKind::ConstEvalCounter
                // ignore
                | StatementKind::Nop
                // just ignore
                | StatementKind::StorageLive(_)
                // just ignore
                | StatementKind::StorageDead(_)
                // just ignore retags
                | StatementKind::Retag(_, _) => (),
            }

            cont_stmt = self.prepend_endlfts(cont_stmt, dying_loans.into_iter());
        }

        Ok(cont_stmt)
    }

    /// Get predecessors in the CFG.
    fn get_loc_predecessors(&self, loc: Location) -> Vec<Location> {
        if loc.statement_index > 0 {
            let pred = Location {
                block: loc.block,
                statement_index: loc.statement_index - 1,
            };
            vec![pred]
        } else {
            // check for gotos that go to this basic block
            let pred_bbs = self.proc.predecessors(loc.block);
            let basic_blocks = &self.proc.get_mir().basic_blocks;
            pred_bbs
                .iter()
                .map(|bb| {
                    let data = &basic_blocks[*bb];
                    Location {
                        block: *bb,
                        statement_index: data.statements.len(),
                    }
                })
                .collect()
        }
    }
}
