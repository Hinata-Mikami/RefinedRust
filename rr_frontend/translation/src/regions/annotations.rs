// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, BTreeSet};
use std::mem;

use log::info;
use radium::{code, coq, specs};
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::type_ir::TypeFolder as _;

use super::inclusion_tracker::InclusionTracker;
use super::{assignment, calls, composite, init};
use crate::base::TranslationError;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::{self, PoloniusInfo};
use crate::error::Message;
use crate::types;

pub(crate) struct AnnotationGenerator<'a, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    info: &'a PoloniusInfo<'a, 'tcx>,
    inclusion_tracker: InclusionTracker<'a, 'tcx>,
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'tcx: 'a> AnnotationGenerator<'a, 'tcx> {
    pub(crate) fn new(
        tcx: ty::TyCtxt<'tcx>,
        lifetime_scope: &super::EarlyLateRegionMap<'_>,
        info: &'a PoloniusInfo<'a, 'tcx>,
    ) -> Self {
        Self {
            tcx,
            info,
            inclusion_tracker: init::initialize_inclusion_tracker(lifetime_scope, info),
        }
    }

    pub(crate) fn prepare_initial_universal_arg_constraints(
        &mut self,
        typing_env: ty::TypingEnv<'tcx>,
        sig_args: &[ty::Ty<'tcx>],
        local_args: &[ty::Ty<'tcx>],
    ) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
        init::get_initial_universal_arg_constraints(
            self.tcx,
            typing_env,
            self.info,
            &mut self.inclusion_tracker,
            sig_args,
            local_args,
        )
    }

    pub(crate) fn prepare_initial_universal_arg_annotation_stmts(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        sig_args: &[ty::Ty<'tcx>],
        local_args: &[ty::Ty<'tcx>],
    ) -> Vec<code::PrimStmt> {
        let constraints = self.prepare_initial_universal_arg_constraints(typing_env, sig_args, local_args);
        info!("initial constraints: {:?}", constraints);

        vec![Self::copy_lifetime_constraints_stmt(ty_translator, constraints, "initialization")]
    }

    pub(crate) fn prepare_initial_closure_constraints(
        &mut self,
    ) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
        init::get_initial_closure_constraints(self.info, &mut self.inclusion_tracker)
    }

    pub(crate) fn prepare_initial_closure_annotation_stmts(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
    ) -> Vec<code::PrimStmt> {
        let constraints = self.prepare_initial_closure_constraints();
        info!("initial closure constraints: {:?}", constraints);
        if constraints.is_empty() {
            return Vec::new();
        }

        vec![Self::copy_lifetime_constraints_stmt(ty_translator, constraints, "initialization (closure)")]
    }

    fn copy_lifetime_constraints_stmt(
        ty_translator: &types::LocalTX<'_, 'tcx>,
        constraints: Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)>,
        why: impl Into<String>,
    ) -> code::PrimStmt {
        let annotations = constraints
            .into_iter()
            .map(|(r1, r2)| {
                code::Annotation::CopyLftName(
                    ty_translator.format_atomic_region(r1),
                    ty_translator.format_atomic_region(r2),
                )
            })
            .collect();

        code::PrimStmt::Annot {
            a: annotations,
            why: Some(why.into()),
        }
    }
}

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
    pub late_lft_hints: Vec<specs::Lft>,
    pub unconstrained_lft_hints: Vec<specs::Lft>,
    pub pre_call: Vec<AnnotationGroup>,
    pub pre_assign: Vec<AnnotationGroup>,
    pub assign_expr: Option<code::Annotation>,
    pub post_assign: Vec<AnnotationGroup>,
    pub post_call_before_goto: Vec<AnnotationGroup>,
}

pub(crate) struct CallRegionInputs<'a, 'tcx> {
    pub(crate) method_params: ty::GenericArgsRef<'tcx>,
    pub(crate) num_late_bounds: usize,
    pub(crate) mapped_early_regions: &'a BTreeMap<coq::Ident, usize>,
}

pub(crate) struct CallAssignmentInputs<'tcx> {
    pub(crate) lhs_ty: mir::PlaceTy<'tcx>,
    pub(crate) lhs_strongly_writeable: bool,
    pub(crate) output_ty: ty::Ty<'tcx>,
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

impl<'a, 'tcx: 'a> AnnotationGenerator<'a, 'tcx> {
    pub(crate) fn prepare_statement_annotation_plan(
        &self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        loc: mir::Location,
        predecessors: impl IntoIterator<Item = mir::Location>,
    ) -> LocationAnnotationPlan {
        let dying_loans = self.collect_statement_dying_loans(loc, predecessors);
        let mut plan = LocationAnnotationPlan::default();
        plan.pre.extend(self.generate_endlft_groups(ty_translator, dying_loans.into_iter().rev()));
        plan
    }

    pub(crate) fn collect_terminator_dying_loans(&self, loc: mir::Location) -> Vec<facts::Loan> {
        let dying = self.info.get_dying_loans(loc);
        // Preserve the existing behavior: query zombie loans here, but do not emit EndLft for them.
        let _dying_zombie = self.info.get_dying_zombie_loans(loc);
        BTreeSet::from_iter(dying).into_iter().rev().collect()
    }

    pub(crate) fn prepare_assignment_annotation_plan(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        translated_fn: &mut code::FunctionBuilder<'_>,
        loc: mir::Location,
        rhs: &mir::Rvalue<'tcx>,
        lhs_ty: mir::PlaceTy<'tcx>,
        rhs_ty: ty::Ty<'tcx>,
        lhs_strongly_writeable: bool,
    ) -> LocationAnnotationPlan {
        let borrow_annots =
            assignment::get_assignment_loan_annots(&mut self.inclusion_tracker, ty_translator, loc, rhs);

        let composite_annots = composite::get_composite_rvalue_creation_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            ty_translator,
            loc,
            rhs_ty,
        );

        let assignment_annots = assignment::get_assignment_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            ty_translator,
            loc,
            lhs_strongly_writeable,
            lhs_ty,
            rhs_ty,
        );

        let (unconstrained_annots, unconstrained_hints) = assignment::make_unconstrained_region_annotations(
            &mut self.inclusion_tracker,
            ty_translator,
            assignment_annots.unconstrained_regions,
            loc,
            Some(rhs),
        );
        for hint in unconstrained_hints {
            translated_fn.add_unconstrained_lft_hint(hint);
        }

        let mut plan = LocationAnnotationPlan::default();
        plan.pre.push(AnnotationGroup::new(unconstrained_annots, "assignment (unconstrained)"));
        plan.pre.push(AnnotationGroup::new(composite_annots, "composite"));
        plan.pre.push(AnnotationGroup::new(borrow_annots, "borrow"));
        plan.pre.push(AnnotationGroup::new(assignment_annots.new_dyn_inclusions, "assignment"));
        plan.expr = assignment_annots.expr_annot;
        plan.post.push(AnnotationGroup::new(assignment_annots.stmt_annot, "post-assignment"));
        plan
    }

    pub(crate) fn prepare_terminator_annotation_plan(
        &self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        dying_loans: impl ExactSizeIterator<Item = facts::Loan>,
    ) -> LocationAnnotationPlan {
        let mut plan = LocationAnnotationPlan::default();
        plan.pre.extend(self.generate_endlft_groups(ty_translator, dying_loans));
        plan
    }

    pub(crate) fn prepare_return_annotation_plan(
        &self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        return_ty: ty::Ty<'tcx>,
        dying_loans: impl ExactSizeIterator<Item = facts::Loan>,
    ) -> LocationAnnotationPlan {
        let mut plan = LocationAnnotationPlan::default();

        let mut region_folder = super::TyRegionCollectFolder::new(self.tcx);
        region_folder.fold_ty(return_ty);
        let stmt_annots = region_folder
            .get_regions()
            .into_iter()
            .map(|r| code::Annotation::ExtendLft(ty_translator.translate_region_var(r)))
            .collect();

        plan.pre.push(AnnotationGroup::new(stmt_annots, "return"));
        plan.pre.extend(self.generate_endlft_groups(ty_translator, dying_loans));
        plan
    }

    pub(crate) fn prepare_call_annotation_plan(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        loc: mir::Location,
        call_regions: &CallRegionInputs<'_, 'tcx>,
        assignment: &CallAssignmentInputs<'tcx>,
        dying_loans: impl ExactSizeIterator<Item = facts::Loan>,
    ) -> Result<CallAnnotationPlan, TranslationError> {
        let startpoint = self.info.start_point(loc);

        let classification = calls::compute_call_regions(
            self.tcx,
            &self.inclusion_tracker,
            call_regions.method_params,
            loc,
            call_regions.num_late_bounds,
        );

        for (r, c) in &classification.classification {
            match c {
                calls::CallRegionKind::EqR(r2) => {
                    self.inclusion_tracker.add_static_inclusion(*r, *r2, startpoint);
                    self.inclusion_tracker.add_static_inclusion(*r2, *r, startpoint);
                },
                calls::CallRegionKind::Intersection(lfts) => {
                    for r2 in lfts {
                        self.inclusion_tracker.add_static_inclusion(*r2, *r, startpoint);
                    }
                },
            }
        }

        let late_lft_hints = classification
            .late_regions
            .iter()
            .map(|late| self.format_region(ty_translator, *late))
            .collect();
        info!("Call lifetime instantiation (early): {:?}", classification.early_regions);
        info!("Call lifetime instantiation (late): {:?}", classification.late_regions);

        let assignment_annots = assignment::get_assignment_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            ty_translator,
            loc,
            assignment.lhs_strongly_writeable,
            assignment.lhs_ty,
            assignment.output_ty,
        );
        info!("assignment annots after call: {assignment_annots:?}");

        let (unconstrained_early_annots, unconstrained_regions) = calls::compute_unconstrained_region_annots(
            &mut self.inclusion_tracker,
            ty_translator,
            loc,
            assignment_annots.unconstrained_regions,
            call_regions.mapped_early_regions,
        );

        let (remaining_unconstrained_annots, unconstrained_hints) =
            assignment::make_unconstrained_region_annotations(
                &mut self.inclusion_tracker,
                ty_translator,
                unconstrained_regions,
                loc,
                None,
            );
        let mut call_region_annots = Vec::new();
        for (r, class) in &classification.classification {
            let lft = self.format_region(ty_translator, *r);
            match class {
                calls::CallRegionKind::EqR(r2) => {
                    let lft2 = self.format_region(ty_translator, *r2);
                    call_region_annots.push(code::Annotation::CopyLftName(lft2, lft));
                },
                calls::CallRegionKind::Intersection(rs) => match rs.len() {
                    0 => {
                        return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                            Message::UnsupportedFeature(
                                "RefinedRust does currently not support unconstrained lifetime".to_owned(),
                            ),
                        )));
                    },
                    1 => {
                        if let Some(r2) = rs.iter().next() {
                            let lft2 = self.format_region(ty_translator, *r2);
                            call_region_annots.push(code::Annotation::CopyLftName(lft2, lft));
                        }
                    },
                    _ => {
                        let lfts: Vec<_> = rs.iter().map(|r| self.format_region(ty_translator, *r)).collect();
                        call_region_annots.push(code::Annotation::AliasLftIntersection(lft, lfts));
                    },
                },
            }
        }

        Ok(CallAnnotationPlan {
            late_lft_hints,
            unconstrained_lft_hints: unconstrained_hints,
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
            post_call_before_goto: self.generate_endlft_groups(ty_translator, dying_loans),
        })
    }

    pub(crate) fn prepare_borrow_lifetime_plan(
        &self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        loc: mir::Location,
        region: ty::Region<'tcx>,
    ) -> BorrowLifetimePlan {
        if let Some(loan) = self.info.get_optional_loan_at_location(loc) {
            let atomic_region = self.info.atomic_region_of_loan(loan);
            return BorrowLifetimePlan {
                lft: ty_translator.format_atomic_region(atomic_region),
            };
        }

        info!("Didn't find loan at {:?}; region {:?}", loc, region);
        let region = super::region_to_region_vid(region);
        BorrowLifetimePlan {
            lft: self.format_region(ty_translator, region),
        }
    }

    fn generate_endlft_groups<I>(
        &self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        dying: I,
    ) -> Vec<AnnotationGroup>
    where
        I: ExactSizeIterator<Item = facts::Loan>,
    {
        dying
            .map(|d| {
                let lft = self.info.atomic_region_of_loan(d);
                AnnotationGroup::new(
                    vec![code::Annotation::EndLft(ty_translator.format_atomic_region(lft))],
                    "endlft",
                )
            })
            .collect()
    }

    fn collect_statement_dying_loans(
        &self,
        loc: mir::Location,
        predecessors: impl IntoIterator<Item = mir::Location>,
    ) -> BTreeSet<facts::Loan> {
        let mut dying_loans = BTreeSet::new();
        for predecessor in predecessors {
            let dying_between = self.info.get_loans_dying_between(predecessor, loc, false);
            for loan in &dying_between {
                dying_loans.insert(*loan);
            }

            let dying_between = self.info.get_loans_dying_between(predecessor, loc, true);
            for loan in &dying_between {
                dying_loans.insert(*loan);
            }
        }
        dying_loans
    }

    fn format_region(&self, ty_translator: &types::LocalTX<'_, 'tcx>, r: facts::Region) -> coq::Ident {
        let lft = self.info.mk_atomic_region(r);
        ty_translator.format_atomic_region(lft)
    }
}
