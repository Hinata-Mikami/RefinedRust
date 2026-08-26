// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Function-wide orchestration of borrow-checker annotation planning.
//!
//! This module is the boundary between MIR body translation and the region analysis in
//! [`crate::regions`]. It discovers the reachable MIR sites that the renderer will consume, converts
//! dropck MIR assignments to their regionful borrowck representation, and coordinates the planning
//! phases exposed by [`crate::regions::AnnotationGenerator`]. The region module owns the semantic
//! decisions; this module owns body-translation policy and the assignment and call plan caches.
//!
//! Planning must finish before basic blocks are rendered. Consequently, CFG traversal only removes
//! cached plans and cannot change the inclusion analysis through its visitation order.

use std::collections::{BTreeMap, BTreeSet};

use rr_rustc_interface::middle::{mir, ty};

use super::TX;
use crate::base::TranslationError;

/// Regionful information collected for an ordinary MIR assignment before annotation planning.
struct PendingAssignment<'tcx> {
    loc: mir::Location,
    rhs: mir::Rvalue<'tcx>,
    lhs_ty: mir::PlaceTy<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
    rvalue_operand_tys: Vec<ty::Ty<'tcx>>,
    is_strong_update: bool,
    shared_borrow_access_region: Option<ty::Region<'tcx>>,
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Computes the blocks whose statements and calls will later consume prepared plans.
    ///
    /// Calls known to terminate in panic do not reach their nominal successors, but can still reach an
    /// unwind cleanup block. Planning must use the same reachability policy as rendering so dead MIR
    /// cannot introduce unsupported annotation requirements.
    fn reachable_basic_blocks(&self) -> BTreeSet<mir::BasicBlock> {
        let mut pending = vec![mir::START_BLOCK];
        let mut reachable = BTreeSet::new();
        while let Some(bb) = pending.pop() {
            if !reachable.insert(bb) {
                continue;
            }
            let terminator = self.proc.dropck_mir().basic_blocks[bb].terminator();
            let terminates_control_flow = match &terminator.kind {
                mir::TerminatorKind::Call { func, .. } => self.is_call_destination_panic(func),
                _ => false,
            };
            if !terminates_control_flow {
                pending.extend(self.proc.successors(bb));
            }
            let unwind = match &terminator.kind {
                mir::TerminatorKind::Call { unwind, .. }
                | mir::TerminatorKind::Assert { unwind, .. }
                | mir::TerminatorKind::Drop { unwind, .. } => Some(unwind),
                _ => None,
            };
            if let Some(mir::UnwindAction::Cleanup(target)) = unwind {
                pending.push(*target);
            }
        }
        reachable
    }

    /// Prepares and caches every assignment and call annotation plan for the reachable MIR body.
    ///
    /// The ordering implements the function-wide planning phases described by
    /// [`crate::regions::AnnotationGenerator`]:
    ///
    /// 1. Collect reachable assignments and preregister loan issuance at every statement location.
    /// 2. Preregister all tracker-independent assignment effects, including strong-update barriers,
    ///    structural transfers, shared-reborrow structure, and dynamic inclusion requirements.
    /// 3. Discover calls, preregister their unconditional effects, classify every call against one stable
    ///    tracker state, batch-register the classifications, and cache the call plans.
    /// 4. Resolve every shared reborrow against one stable state, then batch-register the resolved aliases so
    ///    no resolution can observe another merely because of iteration order.
    /// 5. Resolve loan supports from immediate and barrier-safe future requirements, filtering against the
    ///    stable set of names available when each loan is initialized.
    /// 6. Construct and cache every ordinary assignment plan after all assignment and call declarations are
    ///    available.
    /// 7. Finalize minimal dynamic inclusion annotations for all cached assignment and call plans.
    ///
    /// Batching changes only compiler-side analysis order: every effect remains attached to its
    /// original MIR point or CFG edge. After this method returns, basic-block translation must only
    /// consume `prepared_assignments` and `prepared_calls`; it must not make tracker-dependent
    /// annotation decisions.
    pub(super) fn prepare_annotations(&mut self) -> Result<(), TranslationError> {
        let reachable_blocks = self.reachable_basic_blocks();
        self.prepare_inline_call_reborrows(&reachable_blocks)?;
        let mut pending_assignments = Vec::new();
        for bb in &reachable_blocks {
            let data = &self.proc.dropck_mir().basic_blocks[*bb];
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let loc = mir::Location {
                    block: *bb,
                    statement_index,
                };
                self.annotations.preregister_assignment_loan(loc);
                if self.is_administrative_alias_stmt(statement)
                    || self.proc.synthetic_drop_borrow_for_assignment(loc).is_some()
                {
                    continue;
                }
                let mir::StatementKind::Assign(assignment) = &statement.kind else {
                    continue;
                };
                let (place, rvalue) = assignment.as_ref();
                if self.is_spec_closure_local(place.local)?.is_some() {
                    continue;
                }
                let lhs_ty = self.proc.region_type_of_place(place);
                let rhs_ty = self.proc.region_type_of_rvalue(loc, rvalue);
                let annotation_rhs = self.proc.source_rvalue_for_target(loc).unwrap_or(rvalue).clone();
                let rvalue_operand_tys = self.proc.region_types_of_rvalue_operands_for_target(loc, rvalue);
                let shared_borrow_access_region =
                    self.proc.shared_borrow_access_region_for_target(loc, rvalue);
                let is_strong_update = !self.check_place_below_reference(place);
                pending_assignments.push(PendingAssignment {
                    loc,
                    rhs: annotation_rhs,
                    lhs_ty,
                    rhs_ty,
                    rvalue_operand_tys,
                    is_strong_update,
                    shared_borrow_access_region,
                });
            }
        }

        let did = self.proc.get_id();
        for assignment in &pending_assignments {
            self.annotations.preregister_assignment_effects(
                did,
                assignment.loc,
                &assignment.rhs,
                assignment.rhs_ty,
                &assignment.rvalue_operand_tys,
                assignment.shared_borrow_access_region,
                assignment.lhs_ty,
                assignment.is_strong_update,
            )?;
            if assignment.is_strong_update {
                self.annotations.preregister_strong_assignment(
                    did,
                    assignment.loc,
                    assignment.lhs_ty.ty,
                    assignment.rhs_ty,
                )?;
            }
        }

        self.prepare_function_calls(&reachable_blocks)?;

        let mut shared_reborrow_effects = Vec::new();
        let mut shared_reborrow_aliases = BTreeMap::new();
        for assignment in &pending_assignments {
            if let Some(effect) = self.annotations.resolve_assignment_shared_reborrow(
                assignment.loc,
                &assignment.rhs,
                assignment.shared_borrow_access_region,
            )? {
                let (source, target, _) = effect;
                assert!(shared_reborrow_aliases.insert(assignment.loc, (source, target)).is_none());
                shared_reborrow_effects.push(effect);
            }
        }
        self.annotations.register_assignment_shared_reborrows(shared_reborrow_effects);
        self.annotations.resolve_assignment_loan_supports();

        for assignment in pending_assignments {
            let plan = self.annotations.prepare_assignment_annotation_plan(
                &self.ty_translator,
                &mut self.translated_fn,
                assignment.loc,
                &assignment.rhs,
                assignment.lhs_ty,
                assignment.rhs_ty,
                &assignment.rvalue_operand_tys,
                assignment.is_strong_update,
                shared_reborrow_aliases.remove(&assignment.loc),
            )?;
            assert!(self.prepared_assignments.insert(assignment.loc, plan).is_none());
        }

        for plan in self.prepared_assignments.values_mut() {
            self.annotations.finalize_assignment_annotation_plan(&self.ty_translator, plan)?;
        }
        for call in self.prepared_calls.values_mut() {
            self.annotations
                .finalize_call_annotation_plan(&self.ty_translator, &mut call.annotation_plan)?;
        }

        Ok(())
    }
}
