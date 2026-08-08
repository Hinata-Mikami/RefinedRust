// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Function-wide planning of the lifetime annotations inserted into translated MIR.
//!
//! [`AnnotationGenerator`] coordinates Polonius facts, the flow-sensitive [`InclusionTracker`], and
//! the concrete `RefinedRust` annotations needed to replay the borrow checker's safety proof. The
//! analysis is planned before MIR blocks are translated so annotation decisions do not depend on the
//! order in which the translator visits the CFG.
//!
//! # Terminology
//!
//! - A **site** is a MIR point or CFG edge at which a tracker effect occurs or an annotation may be emitted.
//!   Every registered effect retains its site throughout the analysis.
//! - A **planning phase** is a compiler-side stage in which decisions query one fixed set of registered
//!   tracker effects. The first query lazily computes a must-analysis fixed point, called the phase's
//!   **stable state**. No query in that phase may register facts observed by another query in the same phase.
//! - A **batch query** applies one decision procedure to every relevant reachable site using the same stable
//!   state. A subsequent **batch registration** adds all results without querying the tracker; the next query
//!   then computes a new stable state.
//! - A **plan** stores concrete annotations or rendering metadata for later consumption. Preparing a plan
//!   does not mean that its annotations execute during planning.
//!
//! Batching affects only compiler-side analysis order. The registered effects still occur at their
//! original MIR points and edges. For example, call classification is performed for every call before
//! any classification result is registered. Otherwise a later-classified call could observe an
//! earlier-classified call solely because of iteration order.
//!
//! A stable state is distinct from the per-point snapshots documented by `inclusion_tracker`. A
//! stable state is the function-wide fixed point for one set of registered effects. Incoming,
//! pre-shared-reborrow, and pre-dynamic snapshots are intermediate states within the transfer function
//! of each individual MIR point.
//!
//! # Operation Classes
//!
//! Methods are named according to their role in function-wide planning:
//!
//! - `preregister_*` records effects that can be determined without a tracker-dependent annotation decision.
//!   Assignments and calls preregister loans, structural transfers, strong updates, unconstrained-region
//!   definitions, shared-reborrow structure, and dynamic inclusion requirements.
//! - `discover_*` collects structural Polonius information for a later decision. Call discovery, for example,
//!   identifies early, late, new, and output regions without yet choosing their semantic lifetime
//!   definitions.
//! - `classify_*` and `resolve_*` query a stable state. Calls are classified function-wide, and shared
//!   reborrows resolve a known source lifetime without modifying the tracker during the query batch.
//! - `register_*` batch-registers the results of a completed query phase. Registration invalidates the
//!   previous stable state; the next query recomputes it from all effects registered so far.
//! - `prepare_*` constructs concrete plans and rendering metadata from the completed declarations and
//!   resolved results. The `prepare_initial_*` methods are the exception: they both seed initial tracker
//!   relationships and render the corresponding function-entry annotations.
//! - `finalize_*` generates minimal dynamic inclusion annotations. Every dynamic ensure-action has already
//!   been registered function-wide, so finalization can omit an annotation exactly when the inclusion is
//!   guaranteed before that action.
//! - `push_*` and `take_*` consume prepared annotation groups while rendering. These operations do not query
//!   or mutate the inclusion tracker.
//!
//! # Planning Pipeline
//!
//! Annotation planning proceeds as follows:
//!
//! 1. Constructing [`AnnotationGenerator`] seeds function-entry relationships and preregisters
//!    successor-specific loan deaths as edge barriers.
//! 2. Collect every reachable ordinary assignment and preregister all of its tracker-independent effects,
//!    including dynamic inclusion requirements.
//! 3. Discover every reachable ordinary call and preregister its unconditional point and normal-edge effects.
//! 4. Classify every call using one stable state, batch-register all classifications, and prepare the call
//!    plans.
//! 5. Resolve every assignment shared reborrow using one stable state, then batch-register all resolved
//!    source-to-target equalities.
//! 6. Prepare and cache every ordinary assignment plan.
//! 7. Finalize the dynamic annotations in all cached assignment and call plans.
//! 8. Render MIR blocks by consuming cached plans. Block traversal performs no tracker-dependent annotation
//!    planning.
//!
//! The helper modules divide the lower-level work: `init` handles function-entry relationships,
//! `rvalue` handles structural lifetime transfers through rvalues, `assignment` handles writes, loans,
//! shared reborrows, unconstrained regions, and dynamic requirements, and `calls` discovers and
//! classifies call-region instantiations.
//!
//! # Annotation Sites
//!
//! Annotations and related lifetime metadata are needed at these positions:
//!
//! - **Function entry:** universal-to-argument and closure-capture lifetime aliases initialize the named
//!   lifetime map before the body executes.
//! - **Statement and terminator entry:** [`AnnotationGroup`]s end loans that die between predecessor points
//!   and the current statement or terminator.
//! - **Before an ordinary assignment:** [`LocationAnnotationPlan::pre`] initializes unconstrained lifetimes,
//!   performs structural rvalue transfers, starts loans or aliases shared reborrows, and establishes dynamic
//!   inclusions required by a weak update.
//! - **On an assignment expression:** [`LocationAnnotationPlan::expr`] optionally wraps the translated rvalue
//!   with an expression-level annotation required by the update.
//! - **After an ordinary assignment:** [`LocationAnnotationPlan::post`] performs effects such as semantic
//!   lifetime-name copies for strong updates.
//! - **Before a call:** [`CallAnnotationPlan::pre_call`] defines call-instantiation regions and unconstrained
//!   call lifetimes. [`CallAnnotationPlan::pre_assign`] establishes dynamic inclusions needed to write the
//!   call destination.
//! - **On the normal call continuation:** [`CallAnnotationPlan::post_assign`] defines recovered early output
//!   regions and performs the call-result assignment effects. These annotations are not emitted on unwind
//!   paths. `assign_expr` reserves the expression-annotation position for the destination update; ordinary
//!   calls currently require it to be empty.
//! - **On CFG edges:** edge plans end loans only on successors where they die. This covers goto-like
//!   continuations of calls, switches, assertions, drops, false edges, and ordinary gotos.
//! - **Before return:** plans from [`AnnotationGenerator::prepare_return_annotation_plan`] extend the
//!   semantic lifetimes occurring in the returned type.
//! - **Inside borrow expressions:** [`BorrowLifetimePlan`] selects the semantic lifetime name passed to the
//!   translated borrow expression. It is expression metadata rather than an annotation statement.
//! - **In lifetime hints:** call plans carry late-bound lifetime instantiations and unconstrained lifetime
//!   hints for the generated function metadata rather than emitting them as annotation groups.
//!
//! [`LocationAnnotationPlan`] is consumed in `pre`, `expr`, `post` order around one translated MIR
//! assignment. [`CallAnnotationPlan`] separates annotations before the call from effects on its normal
//! continuation. An [`AnnotationGroup`] is rendered as one annotated primitive statement, preserving
//! the required ordering between groups.

use std::collections::{BTreeMap, BTreeSet};
use std::mem;

use log::info;
use radium::{code, coq, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty::RegionExt as _;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::type_ir::TypeFolder as _;

use super::inclusion_tracker::InclusionTracker;
use super::{assignment, calls, init, rvalue};
use crate::base::{PointIndex, Region, TranslationError};
use crate::environment::borrowck::facts;
use crate::environment::mir_mapper::MappingResult;
use crate::environment::polonius_info::{self, PoloniusInfo};
use crate::error::Message;
use crate::types;

/// Plans the lifetime annotations for one MIR body and owns its flow-sensitive inclusion analysis.
///
/// Tracker-independent effects are registered function-wide before tracker-dependent decisions are
/// resolved. The resulting call and location plans can then be rendered without mutating the
/// inclusion tracker, making annotation generation independent of MIR block traversal order.
pub(crate) struct AnnotationGenerator<'a, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    info: &'a PoloniusInfo<'a, 'tcx>,
    mapping: &'a MappingResult,
    inclusion_tracker: InclusionTracker<'a, 'tcx>,
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'tcx: 'a> AnnotationGenerator<'a, 'tcx> {
    pub(crate) fn new(
        tcx: ty::TyCtxt<'tcx>,
        lifetime_scope: &super::EarlyLateRegionMap<'_>,
        info: &'a PoloniusInfo<'a, 'tcx>,
        mapping: &'a MappingResult,
    ) -> Self {
        let mut inclusion_tracker = init::initialize_inclusion_tracker(lifetime_scope, info);
        for (from, to) in info.cfg_edges() {
            for loan in info.get_semantic_loans_dying_between_points(from, to) {
                let region = info.atomic_region_of_loan(loan).get_region();
                inclusion_tracker.add_edge_barrier(region, from, to);
            }
        }
        Self {
            tcx,
            info,
            mapping,
            inclusion_tracker,
        }
    }

    fn source_point_for_target(&self, loc: mir::Location, point_type: facts::PointType) -> facts::Point {
        self.mapping.source_point_for_target_location(loc, point_type).unwrap_or_else(|| {
            panic!("no borrowck Polonius point mapped for target location {loc:?} ({point_type:?})")
        })
    }

    fn point_index_for_target(&self, loc: mir::Location, point_type: facts::PointType) -> facts::PointIndex {
        let source_point = self.source_point_for_target(loc, point_type);
        self.info.get_point(source_point.location, source_point.typ)
    }

    pub(crate) fn start_point_for_target(&self, loc: mir::Location) -> facts::PointIndex {
        self.point_index_for_target(loc, facts::PointType::Start)
    }

    fn mid_point_for_target(&self, loc: mir::Location) -> facts::PointIndex {
        self.point_index_for_target(loc, facts::PointType::Mid)
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
/// A sequence of annotations emitted together as one annotated primitive statement.
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
#[expect(clippy::partial_pub_fields)]
/// Fully prepared annotations and lifetime hints for a function call and its destination write.
///
/// The public fields are consumed by call rendering. Dynamic requirements remain private until
/// function-wide inclusion solving determines the minimal annotations to append to the plan.
pub(crate) struct CallAnnotationPlan {
    pub late_lft_hints: Vec<specs::Lft>,
    pub unconstrained_lft_hints: Vec<specs::Lft>,
    pub pre_call: Vec<AnnotationGroup>,
    pub pre_assign: Vec<AnnotationGroup>,
    pub assign_expr: Option<code::Annotation>,
    pub post_assign: Vec<AnnotationGroup>,
    required_dyn_inclusions: BTreeSet<(Region, Region, PointIndex)>,
}

/// Callee-generic region information needed to discover and classify a call's Polonius regions.
pub(crate) struct CallRegionInputs<'a, 'tcx> {
    pub(crate) source_params: ty::GenericArgsRef<'tcx>,
    pub(crate) resolved_params: ty::GenericArgsRef<'tcx>,
    pub(crate) source_sig: ty::PolyFnSig<'tcx>,
    pub(crate) num_late_bounds: usize,
    pub(crate) mapped_early_regions: &'a BTreeMap<coq::Ident, usize>,
}

/// Information about the destination write performed on a call's normal return edge.
pub(crate) struct CallAssignmentInputs<'tcx> {
    pub(crate) lhs_ty: mir::PlaceTy<'tcx>,
    pub(crate) is_strong_update: bool,
    pub(crate) output_ty: ty::Binder<'tcx, ty::Ty<'tcx>>,
    pub(crate) normal_target: Option<facts::PointIndex>,
}

/// Intermediate call effects collected before constructing a [`CallAnnotationPlan`].
///
/// Discovery first records tracker-independent regions and output information. Classification is
/// filled in during a separate function-wide query phase, after which its effects are registered
/// in a batch so that no call can observe another call merely due to planning order.
pub(crate) struct CallEffectDiscovery<'tcx> {
    regions: calls::CallRegionDiscovery,
    classification: Option<calls::CallRegions>,
    output_ty: ty::Ty<'tcx>,
    unconstrained_regions: BTreeSet<Region>,
    early_region_annots: Vec<code::Annotation>,
}

#[derive(Debug)]
/// The semantic lifetime name selected for a borrow expression.
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
}

#[derive(Debug, Default)]
#[expect(clippy::partial_pub_fields)]
/// Fully prepared annotations surrounding a single MIR location or CFG edge.
///
/// `pre`, `expr`, and `post` are consumed during rendering. Dynamic requirements remain private
/// until they have been solved function-wide and finalized into minimal concrete annotations.
pub(crate) struct LocationAnnotationPlan {
    pub pre: Vec<AnnotationGroup>,
    pub expr: Option<code::Annotation>,
    pub post: Vec<AnnotationGroup>,
    required_dyn_inclusions: BTreeSet<(Region, Region, PointIndex)>,
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
    pub(crate) fn start_point_for_source(&self, loc: mir::Location) -> facts::PointIndex {
        self.info.get_point(loc, facts::PointType::Start)
    }

    pub(crate) fn preregister_strong_assignment(
        &mut self,
        did: DefId,
        loc: mir::Location,
        lhs_ty: ty::Ty<'tcx>,
        rhs_ty: ty::Ty<'tcx>,
    ) -> Result<(), TranslationError> {
        let midpoint = self.mid_point_for_target(loc);
        assignment::preregister_strong_assignment(
            self.tcx,
            &mut self.inclusion_tracker,
            did,
            midpoint,
            lhs_ty,
            rhs_ty,
        )
    }

    pub(crate) fn preregister_assignment_loan(&mut self, loc: mir::Location) {
        let startpoint = self.start_point_for_target(loc);
        let midpoint = self.mid_point_for_target(loc);
        let Some(loan) = self.info.get_optional_loan_at_point(midpoint) else {
            return;
        };
        let region = self.info.atomic_region_of_loan(loan).get_region();
        self.inclusion_tracker.add_known_region(region, startpoint);
        for (source, destination) in self.info.subset_base_at(midpoint) {
            if destination == region {
                self.inclusion_tracker.add_static_inclusion(source, destination, startpoint);
            }
        }
    }

    pub(crate) fn preregister_assignment_effects(
        &mut self,
        did: DefId,
        loc: mir::Location,
        rhs: &mir::Rvalue<'tcx>,
        rhs_ty: ty::Ty<'tcx>,
        rvalue_operand_tys: &[ty::Ty<'tcx>],
        shared_borrow_access_region: Option<ty::Region<'tcx>>,
        lhs_ty: mir::PlaceTy<'tcx>,
        is_strong_update: bool,
    ) -> Result<(), TranslationError> {
        let startpoint = self.start_point_for_target(loc);
        let midpoint = self.mid_point_for_target(loc);
        rvalue::preregister_rvalue_creation(
            self.tcx,
            &mut self.inclusion_tracker,
            did,
            startpoint,
            rhs,
            rhs_ty,
            rvalue_operand_tys,
        )?;
        assignment::preregister_shared_reborrow(
            &mut self.inclusion_tracker,
            rhs,
            startpoint,
            shared_borrow_access_region,
        );
        let unconstrained = assignment::get_new_unconstrained_regions(&self.inclusion_tracker, midpoint);
        assignment::preregister_unconstrained_regions(
            &mut self.inclusion_tracker,
            &unconstrained,
            startpoint,
        );
        let requirements = assignment::get_assignment_dynamic_requirements(
            self.tcx,
            &self.inclusion_tracker,
            midpoint,
            startpoint,
            is_strong_update,
            lhs_ty,
        );
        self.inclusion_tracker.register_dynamic_inclusions(&requirements);
        Ok(())
    }

    pub(crate) fn preregister_call_effects(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        did: DefId,
        loc: mir::Location,
        call_regions: &CallRegionInputs<'_, 'tcx>,
        assignment: &CallAssignmentInputs<'tcx>,
    ) -> Result<CallEffectDiscovery<'tcx>, TranslationError> {
        let startpoint = self.start_point_for_target(loc);
        let midpoint = self.mid_point_for_target(loc);
        let discovery = calls::discover_call_regions(
            self.tcx,
            self.info,
            call_regions.source_params,
            call_regions.resolved_params,
            call_regions.source_sig,
            midpoint,
            call_regions.num_late_bounds,
        );
        for region in &discovery.new_regions {
            self.inclusion_tracker.add_known_region(*region, startpoint);
        }

        let bound_regions: Vec<_> = assignment
            .output_ty
            .bound_vars()
            .iter()
            .enumerate()
            .filter_map(|(index, kind)| matches!(kind, ty::BoundVariableKind::Region(_)).then_some(index))
            .collect();
        if bound_regions.len() != discovery.late_regions_by_bound_var.len()
            || bound_regions
                .iter()
                .any(|bound_var| !discovery.late_regions_by_bound_var.contains_key(bound_var))
        {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!(
                    "could not recover a complete late-bound call instantiation: call specification expects {}, \
                     output has {}, Polonius discovered {} call regions, mapped binders are {:?}",
                    call_regions.num_late_bounds,
                    bound_regions.len(),
                    discovery.late_regions.len(),
                    discovery.late_regions_by_bound_var.keys().collect::<Vec<_>>()
                ),
            ))));
        }
        let (output_ty, _) =
            self.tcx
                .instantiate_bound_regions(assignment.output_ty, &mut |bound: ty::BoundRegion<'tcx>| {
                    let region = discovery.late_regions_by_bound_var[&bound.var.index()];
                    ty::Region::new_var(self.tcx, region.into())
                });

        let unconstrained_regions = if assignment.normal_target.is_some() {
            assignment::get_new_unconstrained_regions(&self.inclusion_tracker, midpoint)
        } else {
            BTreeSet::new()
        };
        let mut remaining_unconstrained = BTreeSet::new();
        let mut recovered_early = Vec::new();
        for region in unconstrained_regions {
            let translated = ty_translator.translate_region_var(region);
            if let Some(index) = call_regions.mapped_early_regions.get(&translated) {
                let scope = ty_translator.scope.borrow();
                let early_region = scope.lifetime_scope.early_regions[*index].unwrap();
                let early_name = scope.lifetime_scope.region_names[&early_region].lft().to_owned();
                recovered_early.push((region, early_region, early_name, translated));
            } else {
                remaining_unconstrained.insert(region);
            }
        }
        assignment::preregister_unconstrained_regions(
            &mut self.inclusion_tracker,
            &remaining_unconstrained,
            startpoint,
        );
        if assignment.normal_target.is_some() {
            let requirements = assignment::get_assignment_dynamic_requirements(
                self.tcx,
                &self.inclusion_tracker,
                midpoint,
                midpoint,
                assignment.is_strong_update,
                assignment.lhs_ty,
            );
            self.inclusion_tracker.register_dynamic_inclusions(&requirements);
        }

        let mut early_region_annots = Vec::new();
        if let Some(target_start) = assignment.normal_target {
            if assignment.is_strong_update {
                assignment::preregister_strong_assignment_on_edge(
                    self.tcx,
                    &mut self.inclusion_tracker,
                    did,
                    midpoint,
                    target_start,
                    assignment.lhs_ty.ty,
                    output_ty,
                )?;
            }
            for (region, early_region, early_name, translated) in recovered_early {
                self.inclusion_tracker.add_edge_pre_barrier(region, midpoint, target_start);
                self.inclusion_tracker.add_edge_known_region(region, midpoint, target_start);
                self.inclusion_tracker.add_edge_static_inclusion(
                    region,
                    early_region,
                    midpoint,
                    target_start,
                );
                self.inclusion_tracker.add_edge_static_inclusion(
                    early_region,
                    region,
                    midpoint,
                    target_start,
                );
                early_region_annots.push(code::Annotation::CopyLftName(early_name, translated));
            }
        }

        Ok(CallEffectDiscovery {
            regions: discovery,
            classification: None,
            output_ty,
            unconstrained_regions: remaining_unconstrained,
            early_region_annots,
        })
    }

    pub(crate) fn classify_call_effects(
        &mut self,
        loc: mir::Location,
        discovery: &mut CallEffectDiscovery<'tcx>,
    ) {
        let midpoint = self.mid_point_for_target(loc);
        discovery.classification = Some(calls::classify_call_regions(
            &mut self.inclusion_tracker,
            midpoint,
            mem::take(&mut discovery.regions),
        ));
    }

    pub(crate) fn resolve_assignment_shared_reborrow(
        &mut self,
        loc: mir::Location,
        rhs: &mir::Rvalue<'tcx>,
        access_region: Option<ty::Region<'tcx>>,
    ) -> Result<Option<(Region, Region, PointIndex)>, TranslationError> {
        let startpoint = self.start_point_for_target(loc);
        Ok(assignment::resolve_shared_reborrow(
            self.tcx,
            &mut self.inclusion_tracker,
            rhs,
            startpoint,
            startpoint,
            access_region,
        )?
        .map(|(source, target)| (source, target, startpoint)))
    }

    pub(crate) fn register_assignment_shared_reborrows(
        &mut self,
        effects: impl IntoIterator<Item = (Region, Region, PointIndex)>,
    ) {
        for (source, target, point) in effects {
            self.inclusion_tracker.add_static_inclusion(source, target, point);
            self.inclusion_tracker.add_static_inclusion(target, source, point);
        }
    }

    pub(crate) fn register_call_classification_effects(
        &mut self,
        loc: mir::Location,
        discovery: &CallEffectDiscovery<'tcx>,
    ) {
        let startpoint = self.start_point_for_target(loc);
        let classification = discovery.classification.as_ref().expect("call effects not classified");
        for (region, class) in &classification.classification {
            self.inclusion_tracker.add_known_region(*region, startpoint);
            match class {
                calls::CallRegionKind::EqR(other) => {
                    self.inclusion_tracker.add_static_inclusion(*region, *other, startpoint);
                    self.inclusion_tracker.add_static_inclusion(*other, *region, startpoint);
                },
                calls::CallRegionKind::Intersection(outlivers) => {
                    for outliver in outlivers {
                        self.inclusion_tracker.add_static_inclusion(*outliver, *region, startpoint);
                    }
                },
            }
        }
    }

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

    pub(crate) fn prepare_cfg_edge_annotation_plan(
        &self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        loc: mir::Location,
        target: mir::BasicBlock,
    ) -> LocationAnnotationPlan {
        let from = self.mid_point_for_target(loc);
        let target_loc = mir::Location {
            block: target,
            statement_index: 0,
        };
        let to = self.start_point_for_target(target_loc);
        let dying = self.info.get_semantic_loans_dying_between_points(from, to);
        let mut plan = LocationAnnotationPlan::default();
        plan.pre.extend(self.generate_endlft_groups(ty_translator, dying.into_iter().rev()));
        plan
    }

    pub(crate) fn prepare_assignment_annotation_plan(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        translated_fn: &mut code::FunctionBuilder<'_>,
        loc: mir::Location,
        rhs: &mir::Rvalue<'tcx>,
        lhs_ty: mir::PlaceTy<'tcx>,
        rhs_ty: ty::Ty<'tcx>,
        rvalue_operand_tys: &[ty::Ty<'tcx>],
        is_strong_update: bool,
        shared_reborrow: Option<(Region, Region)>,
    ) -> Result<LocationAnnotationPlan, TranslationError> {
        let startpoint = self.start_point_for_target(loc);
        let midpoint = self.mid_point_for_target(loc);
        let mut borrow_annots =
            assignment::get_assignment_loan_annots(&self.inclusion_tracker, ty_translator, loc, midpoint);
        borrow_annots.extend(assignment::get_shared_reborrow_annots(
            &self.inclusion_tracker,
            ty_translator,
            shared_reborrow,
        ));

        let rvalue_annots = rvalue::get_rvalue_creation_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            ty_translator,
            startpoint,
            rhs,
            rhs_ty,
            rvalue_operand_tys,
        )?;

        let write_info = assignment::get_assignment_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            ty_translator,
            startpoint,
            midpoint,
            startpoint,
            is_strong_update,
            lhs_ty,
            rhs_ty,
        )?;

        let (unconstrained_annots, unconstrained_hints) = assignment::make_unconstrained_region_annotations(
            &mut self.inclusion_tracker,
            ty_translator,
            write_info.unconstrained_regions,
            startpoint,
            Some(rhs),
        );
        for hint in unconstrained_hints {
            translated_fn.add_unconstrained_lft_hint(hint);
        }

        let mut plan = LocationAnnotationPlan::default();
        plan.pre.push(AnnotationGroup::new(unconstrained_annots, "assignment (unconstrained)"));
        plan.pre.push(AnnotationGroup::new(rvalue_annots, "rvalue"));
        plan.pre.push(AnnotationGroup::new(borrow_annots, "borrow"));
        plan.required_dyn_inclusions = write_info.required_dyn_inclusions;
        plan.expr = write_info.expr_annot;
        plan.post.push(AnnotationGroup::new(write_info.post_write_annots, "post-assignment"));
        Ok(plan)
    }

    pub(crate) fn prepare_return_annotation_plan(
        &self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        return_ty: ty::Ty<'tcx>,
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
        plan
    }

    pub(crate) fn prepare_call_annotation_plan(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        loc: mir::Location,
        assignment: &CallAssignmentInputs<'tcx>,
        mut discovery: CallEffectDiscovery<'tcx>,
    ) -> Result<CallAnnotationPlan, TranslationError> {
        let startpoint = self.start_point_for_target(loc);
        let midpoint = self.mid_point_for_target(loc);

        let classification = discovery.classification.take().expect("call effects not classified");
        let undefined_late_regions = classification.undefined_late_regions();
        if !undefined_late_regions.is_empty() {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!(
                    "call at {loc:?} uses late-bound regions without a semantic lifetime definition: \
                     {undefined_late_regions:?}"
                ),
            ))));
        }

        let (unconstrained_annots, unconstrained_lft_hints) =
            assignment::make_unconstrained_region_annotations(
                &mut self.inclusion_tracker,
                ty_translator,
                discovery.unconstrained_regions,
                startpoint,
                None,
            );

        let late_lft_hints = classification
            .late_regions
            .iter()
            .map(|late| self.format_region(ty_translator, *late))
            .collect();
        info!("Call lifetime instantiation (early): {:?}", classification.early_regions);
        info!("Call lifetime instantiation (late): {:?}", classification.late_regions);

        let write_info = if assignment.normal_target.is_some() {
            assignment::get_assignment_annots(
                self.tcx,
                &mut self.inclusion_tracker,
                ty_translator,
                startpoint,
                midpoint,
                midpoint,
                assignment.is_strong_update,
                assignment.lhs_ty,
                discovery.output_ty,
            )?
        } else {
            assignment::WriteInfo::default()
        };
        info!("write info after call: {write_info:?}");

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
            unconstrained_lft_hints,
            pre_call: vec![
                AnnotationGroup::new(call_region_annots, "function_call"),
                AnnotationGroup::new(unconstrained_annots, "function_call (unconstrained)"),
            ],
            pre_assign: Vec::new(),
            assign_expr: write_info.expr_annot,
            post_assign: vec![
                AnnotationGroup::new(discovery.early_region_annots, "post_function_call (assign, early)"),
                AnnotationGroup::new(write_info.post_write_annots, "post_function_call (assign)"),
            ],
            required_dyn_inclusions: write_info.required_dyn_inclusions,
        })
    }

    pub(crate) fn finalize_assignment_annotation_plan(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        plan: &mut LocationAnnotationPlan,
    ) -> Result<(), TranslationError> {
        let annotations = assignment::generate_dyn_inclusion_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            ty_translator,
            &plan.required_dyn_inclusions,
        )?;
        plan.pre.push(AnnotationGroup::new(annotations, "assignment"));
        Ok(())
    }

    pub(crate) fn finalize_call_annotation_plan(
        &mut self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        plan: &mut CallAnnotationPlan,
    ) -> Result<(), TranslationError> {
        let annotations = assignment::generate_dyn_inclusion_annots(
            self.tcx,
            &mut self.inclusion_tracker,
            ty_translator,
            &plan.required_dyn_inclusions,
        )?;
        plan.pre_assign.push(AnnotationGroup::new(annotations, "function_call (assign)"));
        Ok(())
    }

    pub(crate) fn prepare_borrow_lifetime_plan(
        &self,
        ty_translator: &types::LocalTX<'_, 'tcx>,
        loc: mir::Location,
        region: ty::Region<'tcx>,
    ) -> BorrowLifetimePlan {
        if let Some(loan) = self.info.get_optional_loan_at_point(self.mid_point_for_target(loc)) {
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
        let loc_startpoint = self.start_point_for_target(loc);
        for predecessor in predecessors {
            let pred_midpoint = self.mid_point_for_target(predecessor);
            dying_loans
                .extend(self.info.get_semantic_loans_dying_between_points(pred_midpoint, loc_startpoint));
        }
        dying_loans
    }

    fn format_region(&self, ty_translator: &types::LocalTX<'_, 'tcx>, r: facts::Region) -> coq::Ident {
        let lft = self.info.mk_atomic_region(r);
        ty_translator.format_atomic_region(lft)
    }
}
