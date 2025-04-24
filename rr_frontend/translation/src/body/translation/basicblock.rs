// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashSet;

use log::info;
use rr_rustc_interface::middle::mir;

use super::TX;
use crate::base::*;
use crate::regions;

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate a single basic block.
    pub(super) fn translate_basic_block(
        &mut self,
        bb_idx: mir::BasicBlock,
        bb: &mir::BasicBlockData<'tcx>,
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        let mut prim_stmts = Vec::new();

        for (idx, stmt) in bb.statements.iter().enumerate() {
            let loc = mir::Location {
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
            prim_stmts.extend(self.generate_endlfts(dying_loans.into_iter()));

            match &stmt.kind {
                mir::StatementKind::Assign(b) => {
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
                        prim_stmts.push(radium::PrimStmt::Assign {
                            ot,
                            e1: translated_place,
                            e2: translated_val,
                        });
                    } else {
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

                        let unconstrained_annots = regions::assignment::make_unconstrained_region_annotations(
                            &mut self.inclusion_tracker, &self.ty_translator, assignment_annots.unconstrained_regions, loc,
                            Some(val))?;


                        prim_stmts.push(radium::PrimStmt::Annot{
                            a: unconstrained_annots,
                            why: Some("assignment (unconstrained)".to_owned()),
                        });

                        prim_stmts.push(radium::PrimStmt::Annot{
                            a: composite_annots,
                            why: Some("composite".to_owned()),
                        });

                        prim_stmts.push(radium::PrimStmt::Annot{
                            a: borrow_annots,
                            why: Some("borrow".to_owned()),
                        });

                        prim_stmts.push(radium::PrimStmt::Annot{
                            a: assignment_annots.new_dyn_inclusions,
                            why: Some("assignment".to_owned()),
                        });


                        let translated_val = radium::Expr::with_optional_annotation(
                            self.translate_rvalue(loc, val)?,
                            assignment_annots.expr_annot,
                            Some("assignment".to_owned()),
                        );
                        let translated_place = self.translate_place(plc)?;
                        let synty = self.ty_translator.translate_type_to_syn_type(plc_ty.ty)?;
                        prim_stmts.push(radium::PrimStmt::Assign {
                            ot: synty.into(),
                            e1: translated_place,
                            e2: translated_val,
                        });

                        prim_stmts.push(radium::PrimStmt::Annot{
                            a: assignment_annots.stmt_annot,
                            why: Some("post-assignment".to_owned()),
                        });
                    }
                },

                mir::StatementKind::Deinit(_) => {
                    // TODO: find out where this is emitted
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support Deinit".to_owned(),
                    });
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
                            return Err(TranslationError::UnsupportedFeature {
                                description: "RefinedRust does currently not support the CopyNonOverlapping Intrinsic".to_owned(),
                            });
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
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support SetDiscriminant".to_owned(),
                    });
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
                | mir::StatementKind::StorageLive(_)
                // just ignore
                | mir::StatementKind::StorageDead(_)
                // just ignore retags
                | mir::StatementKind::Retag(_, _) => (),
            }
        }

        let idx = bb.statements.len();
        let loc = mir::Location {
            block: bb_idx,
            statement_index: idx,
        };
        let dying = self.info.get_dying_loans(loc);
        // TODO zombie?
        let _dying_zombie = self.info.get_dying_zombie_loans(loc);
        let cont_stmt: radium::Stmt = self.translate_terminator(bb.terminator(), loc, dying)?;

        let cont_stmt = radium::Stmt::Prim(prim_stmts, Box::new(cont_stmt));

        Ok(cont_stmt)
    }

    /// Get predecessors in the CFG.
    fn get_loc_predecessors(&self, loc: mir::Location) -> Vec<mir::Location> {
        if loc.statement_index > 0 {
            let pred = mir::Location {
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
                    mir::Location {
                        block: *bb,
                        statement_index: data.statements.len(),
                    }
                })
                .collect()
        }
    }
}
