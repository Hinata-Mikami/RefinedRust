// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::mem;

use log::info;
use radium::{code, coq};
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::type_ir::TypeFolder as _;

use super::TX;
use super::calls::ProcedureInst;
use crate::base::TranslationError;
use crate::environment::borrowck::facts;
use crate::error::Message;
use crate::regions;

#[derive(Debug, Default)]
pub(crate) struct AnnotationGroup {
    pub annotations: Vec<code::Annotation>,
    pub why: Option<String>,
}

impl AnnotationGroup {
    fn new(annotations: Vec<code::Annotation>, why: impl Into<String>) -> Self {
        Self {
            annotations,
            why: Some(why.into()),
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct CallAnnotationPlan {
    pub pre_call: Vec<AnnotationGroup>,
    pub pre_assign: Vec<AnnotationGroup>,
    pub assign_expr: Option<code::Annotation>,
    pub post_assign: Vec<AnnotationGroup>,
    pub post_call_before_goto: Vec<AnnotationGroup>,
}

#[derive(Debug)]
pub(crate) struct BorrowLifetimePlan {
    pub lft: coq::Ident,
}

impl CallAnnotationPlan {
    pub(crate) fn push_pre_call_stmts(&mut self, prim_stmts: &mut Vec<code::PrimStmt>) {
        push_groups(prim_stmts, mem::take(&mut self.pre_call));
    }

    pub(crate) fn push_pre_assign_stmts(&mut self, prim_stmts: &mut Vec<code::PrimStmt>) {
        push_groups(prim_stmts, mem::take(&mut self.pre_assign));
    }

    pub(crate) fn push_post_assign_stmts(&mut self, prim_stmts: &mut Vec<code::PrimStmt>) {
        push_groups(prim_stmts, mem::take(&mut self.post_assign));
    }

    pub(crate) fn push_post_call_before_goto_stmts(&mut self, prim_stmts: &mut Vec<code::PrimStmt>) {
        push_groups(prim_stmts, mem::take(&mut self.post_call_before_goto));
    }
}

#[derive(Debug, Default)]
pub(crate) struct LocationAnnotationPlan {
    pub pre: Vec<AnnotationGroup>,
    pub expr: Option<code::Annotation>,
    pub post: Vec<AnnotationGroup>,
}

impl LocationAnnotationPlan {
    pub(crate) fn push_pre_stmts(&mut self, prim_stmts: &mut Vec<code::PrimStmt>) {
        push_groups(prim_stmts, mem::take(&mut self.pre));
    }

    pub(crate) fn push_post_stmts(&mut self, prim_stmts: &mut Vec<code::PrimStmt>) {
        push_groups(prim_stmts, mem::take(&mut self.post));
    }

    pub(crate) fn take_pre_stmts(&mut self) -> Vec<code::PrimStmt> {
        groups_to_stmts(mem::take(&mut self.pre))
    }
}

fn push_groups(prim_stmts: &mut Vec<code::PrimStmt>, groups: Vec<AnnotationGroup>) {
    prim_stmts.extend(groups_to_stmts(groups));
}

fn groups_to_stmts(groups: Vec<AnnotationGroup>) -> Vec<code::PrimStmt> {
    groups
        .into_iter()
        .map(|group| code::PrimStmt::Annot {
            a: group.annotations,
            why: group.why,
        })
        .collect()
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    pub(crate) fn prepare_statement_annotation_plan(
        &mut self,
        loc: mir::Location,
        dying_loans: impl ExactSizeIterator<Item = facts::Loan>,
    ) {
        let mut plan = self.annotation_plans.remove(&loc).unwrap_or_default();
        plan.pre.extend(self.generate_endlft_groups(dying_loans));
        self.annotation_plans.insert(loc, plan);
    }

    pub(crate) fn prepare_assignment_annotation_plan(
        &mut self,
        loc: mir::Location,
        rhs: &mir::Rvalue<'tcx>,
        lhs_ty: mir::PlaceTy<'tcx>,
        rhs_ty: ty::Ty<'tcx>,
        lhs_strongly_writeable: bool,
    ) {
        let borrow_annots = regions::assignment::get_assignment_loan_annots(
            &mut self.inclusion_tracker,
            &self.ty_translator,
            loc,
            rhs,
        );

        let composite_annots = regions::composite::get_composite_rvalue_creation_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            &self.ty_translator,
            loc,
            rhs_ty,
        );

        let assignment_annots = regions::assignment::get_assignment_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            &self.ty_translator,
            loc,
            lhs_strongly_writeable,
            lhs_ty,
            rhs_ty,
        );

        let (unconstrained_annots, unconstrained_hints) =
            regions::assignment::make_unconstrained_region_annotations(
                &mut self.inclusion_tracker,
                &self.ty_translator,
                assignment_annots.unconstrained_regions,
                loc,
                Some(rhs),
            );
        for hint in unconstrained_hints {
            self.translated_fn.add_unconstrained_lft_hint(hint);
        }

        let mut plan = self.annotation_plans.remove(&loc).unwrap_or_default();
        plan.pre.push(AnnotationGroup::new(unconstrained_annots, "assignment (unconstrained)"));
        plan.pre.push(AnnotationGroup::new(composite_annots, "composite"));
        plan.pre.push(AnnotationGroup::new(borrow_annots, "borrow"));
        plan.pre.push(AnnotationGroup::new(assignment_annots.new_dyn_inclusions, "assignment"));
        plan.expr = assignment_annots.expr_annot;
        plan.post.push(AnnotationGroup::new(assignment_annots.stmt_annot, "post-assignment"));
        self.annotation_plans.insert(loc, plan);
    }

    pub(crate) fn prepare_terminator_annotation_plan(
        &mut self,
        loc: mir::Location,
        dying_loans: impl ExactSizeIterator<Item = facts::Loan>,
    ) {
        let mut plan = self.annotation_plans.remove(&loc).unwrap_or_default();
        plan.pre.extend(self.generate_endlft_groups(dying_loans));
        self.annotation_plans.insert(loc, plan);
    }

    pub(crate) fn prepare_return_annotation_plan(
        &mut self,
        loc: mir::Location,
        dying_loans: impl ExactSizeIterator<Item = facts::Loan>,
    ) {
        let mut plan = self.annotation_plans.remove(&loc).unwrap_or_default();

        let mut region_folder = regions::TyRegionCollectFolder::new(self.tcx);
        region_folder.fold_ty(self.return_ty);
        let stmt_annots = region_folder
            .get_regions()
            .into_iter()
            .map(|r| code::Annotation::ExtendLft(self.ty_translator.translate_region_var(r)))
            .collect();

        plan.pre.push(AnnotationGroup::new(stmt_annots, "return"));
        plan.pre.extend(self.generate_endlft_groups(dying_loans));
        self.annotation_plans.insert(loc, plan);
    }

    pub(crate) fn prepare_call_annotation_plan(
        &mut self,
        loc: mir::Location,
        call_info: &mut ProcedureInst<'tcx, 'def>,
        destination: &mir::Place<'tcx>,
        output_ty: ty::Ty<'tcx>,
        dying_loans: impl ExactSizeIterator<Item = facts::Loan>,
    ) -> Result<CallAnnotationPlan, TranslationError> {
        let startpoint = self.info.interner.get_point_index(&facts::Point {
            location: loc,
            typ: facts::PointType::Start,
        });

        let classification = regions::calls::compute_call_regions(
            self.tcx,
            &self.inclusion_tracker,
            call_info.method_params,
            loc,
            call_info.num_of_latebounds,
        );

        for (r, c) in &classification.classification {
            match c {
                regions::calls::CallRegionKind::EqR(r2) => {
                    self.inclusion_tracker.add_static_inclusion(*r, *r2, startpoint);
                    self.inclusion_tracker.add_static_inclusion(*r2, *r, startpoint);
                },
                regions::calls::CallRegionKind::Intersection(lfts) => {
                    for r2 in lfts {
                        self.inclusion_tracker.add_static_inclusion(*r2, *r, startpoint);
                    }
                },
            }
        }

        for late in &classification.late_regions {
            let lft = self.format_region(*late);
            call_info.lft_hint.push(lft);
        }
        info!("Call lifetime instantiation (early): {:?}", classification.early_regions);
        info!("Call lifetime instantiation (late): {:?}", classification.late_regions);

        let lhs_ty = self.get_type_of_place(destination);
        let lhs_strongly_writeable = !self.check_place_below_reference(destination);
        let assignment_annots = regions::assignment::get_assignment_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            &self.ty_translator,
            loc,
            lhs_strongly_writeable,
            lhs_ty,
            output_ty,
        );
        info!("assignment annots after call: {assignment_annots:?}");

        let (unconstrained_early_annots, unconstrained_regions) =
            regions::calls::compute_unconstrained_region_annots(
                &mut self.inclusion_tracker,
                &self.ty_translator,
                loc,
                assignment_annots.unconstrained_regions,
                &call_info.mapped_early_regions,
            );

        let (remaining_unconstrained_annots, unconstrained_hints) =
            regions::assignment::make_unconstrained_region_annotations(
                &mut self.inclusion_tracker,
                &self.ty_translator,
                unconstrained_regions,
                loc,
                None,
            );
        for hint in unconstrained_hints {
            self.translated_fn.add_unconstrained_lft_hint(hint);
        }

        let mut call_region_annots = Vec::new();
        for (r, class) in &classification.classification {
            let lft = self.format_region(*r);
            match class {
                regions::calls::CallRegionKind::EqR(r2) => {
                    let lft2 = self.format_region(*r2);
                    call_region_annots.push(code::Annotation::CopyLftName(lft2, lft));
                },
                regions::calls::CallRegionKind::Intersection(rs) => match rs.len() {
                    0 => {
                        return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                            Message::UnsupportedFeature(
                                "RefinedRust does currently not support unconstrained lifetime".to_owned(),
                            ),
                        )));
                    },
                    1 => {
                        if let Some(r2) = rs.iter().next() {
                            let lft2 = self.format_region(*r2);
                            call_region_annots.push(code::Annotation::CopyLftName(lft2, lft));
                        }
                    },
                    _ => {
                        let lfts: Vec<_> = rs.iter().map(|r| self.format_region(*r)).collect();
                        call_region_annots.push(code::Annotation::AliasLftIntersection(lft, lfts));
                    },
                },
            }
        }

        Ok(CallAnnotationPlan {
            pre_call: vec![
                AnnotationGroup::new(call_region_annots, "function_call"),
                AnnotationGroup::new(remaining_unconstrained_annots, "function_call (unconstrained)"),
            ],
            pre_assign: vec![AnnotationGroup::new(
                assignment_annots.new_dyn_inclusions,
                "function_call (assign)",
            )],
            assign_expr: assignment_annots.expr_annot,
            post_assign: vec![
                AnnotationGroup::new(unconstrained_early_annots, "post_function_call (assign, early)"),
                AnnotationGroup::new(assignment_annots.stmt_annot, "post_function_call (assign)"),
            ],
            post_call_before_goto: self.generate_endlft_groups(dying_loans),
        })
    }

    pub(crate) fn prepare_borrow_lifetime_plan(
        &self,
        loc: mir::Location,
        region: ty::Region<'tcx>,
    ) -> BorrowLifetimePlan {
        if let Some(loan) = self.info.get_optional_loan_at_location(loc) {
            let atomic_region = self.info.atomic_region_of_loan(loan);
            return BorrowLifetimePlan {
                lft: self.ty_translator.format_atomic_region(atomic_region),
            };
        }

        info!("Didn't find loan at {:?}; region {:?}", loc, region);
        let region = regions::region_to_region_vid(region);
        BorrowLifetimePlan {
            lft: self.format_region(region),
        }
    }

    pub(crate) fn take_annotation_plan(&mut self, loc: mir::Location) -> LocationAnnotationPlan {
        self.annotation_plans.remove(&loc).unwrap_or_default()
    }

    fn generate_endlft_groups<I>(&self, dying: I) -> Vec<AnnotationGroup>
    where
        I: ExactSizeIterator<Item = facts::Loan>,
    {
        dying
            .map(|d| {
                let lft = self.info.atomic_region_of_loan(d);
                AnnotationGroup::new(
                    vec![code::Annotation::EndLft(self.ty_translator.format_atomic_region(lft))],
                    "endlft",
                )
            })
            .collect()
    }
}
