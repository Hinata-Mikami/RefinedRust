// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use rr_rustc_interface::data_structures::fx::FxHashMap;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::{self, BasicBlock, Body};
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::span;

use super::types::{NormalizedPlaceElem, PointPhase};
use super::{SourcePoint, TargetLoc, TargetPoint};
use crate::environment::borrowck::facts;
use crate::search;

/// Insert start and mid point mappings for a target location from a phase.
pub(super) fn insert_point_mapping(
    target_points_to_source: &mut FxHashMap<TargetPoint, SourcePoint>,
    target: TargetLoc,
    phase: PointPhase,
) {
    let (target_bb, target_idx) = target;
    let (source, start_source_kind, mid_source_kind) = match phase {
        PointPhase::Direct(source) => (source, facts::PointType::Start, facts::PointType::Mid),
        PointPhase::PreEffect(source) => (source, facts::PointType::Start, facts::PointType::Start),
        PointPhase::PostEffect(source) => (source, facts::PointType::Mid, facts::PointType::Mid),
    };
    let (source_bb, source_idx) = source;

    target_points_to_source
        .insert((target_bb, target_idx, facts::PointType::Start), (source_bb, source_idx, start_source_kind));
    target_points_to_source
        .insert((target_bb, target_idx, facts::PointType::Mid), (source_bb, source_idx, mid_source_kind));
}

/// Compute real predecessor blocks for each basic block in a body.
pub(super) fn compute_predecessors(body: &Body<'_>) -> FxHashMap<BasicBlock, Vec<BasicBlock>> {
    let mut predecessors: FxHashMap<_, Vec<_>> = FxHashMap::default();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for succ in real_targets(data.terminator()) {
            predecessors.entry(succ).or_default().push(bb);
        }
    }
    predecessors
}

/// Return CFG targets excluding unwind-only pseudo-continuations.
pub(super) fn real_targets(terminator: &mir::Terminator<'_>) -> Vec<BasicBlock> {
    match &terminator.kind {
        mir::TerminatorKind::Goto { target }
        | mir::TerminatorKind::Assert { target, .. }
        | mir::TerminatorKind::Drop { target, .. } => vec![*target],
        mir::TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
        mir::TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
        mir::TerminatorKind::FalseEdge { real_target, .. }
        | mir::TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
        mir::TerminatorKind::Yield { resume, .. } => vec![*resume],
        mir::TerminatorKind::InlineAsm { targets, .. } => targets.to_vec(),
        mir::TerminatorKind::CoroutineDrop
        | mir::TerminatorKind::Return
        | mir::TerminatorKind::Unreachable
        | mir::TerminatorKind::UnwindResume
        | mir::TerminatorKind::UnwindTerminate(_)
        | mir::TerminatorKind::TailCall { .. } => vec![],
    }
}

/// Return all successor blocks exposed by a terminator.
pub(super) fn terminator_targets(terminator: &mir::Terminator<'_>) -> Vec<BasicBlock> {
    terminator.successors().collect()
}

/// Return the normal, non-unwind continuation of a terminator when it is unique.
pub(super) const fn normal_successor(terminator: &mir::Terminator<'_>) -> Option<BasicBlock> {
    match &terminator.kind {
        mir::TerminatorKind::Goto { target }
        | mir::TerminatorKind::Assert { target, .. }
        | mir::TerminatorKind::Drop { target, .. }
        | mir::TerminatorKind::FalseEdge {
            real_target: target,
            ..
        }
        | mir::TerminatorKind::FalseUnwind {
            real_target: target,
            ..
        } => Some(*target),
        mir::TerminatorKind::Call { target, .. } => *target,
        _ => None,
    }
}

/// Find the source successor corresponding to a target successor edge.
pub(super) fn matching_source_successor(
    target: &mir::Terminator<'_>,
    target_successor: BasicBlock,
    source: &mir::Terminator<'_>,
) -> Option<BasicBlock> {
    // The mapper aligns predecessor terminators structurally, but their target
    // block numbers differ. Given a target successor edge, pick the analogous
    // source successor edge. We handle only the edge kinds used here: normal
    // continuation and cleanup unwind continuation.
    if normal_successor(target) == Some(target_successor) {
        return normal_successor(source);
    }

    match (&target.kind, &source.kind) {
        (
            mir::TerminatorKind::Assert {
                unwind: unwind_t, ..
            }
            | mir::TerminatorKind::Call {
                unwind: unwind_t, ..
            }
            | mir::TerminatorKind::Drop {
                unwind: unwind_t, ..
            },
            mir::TerminatorKind::Assert {
                unwind: unwind_s, ..
            }
            | mir::TerminatorKind::Call {
                unwind: unwind_s, ..
            }
            | mir::TerminatorKind::Drop {
                unwind: unwind_s, ..
            },
        ) if unwind_target(*unwind_t) == Some(target_successor) => unwind_target(*unwind_s),
        _ => None,
    }
}

/// Collect the explicit values of a switch terminator in order.
pub(super) fn switch_values(targets: &mir::SwitchTargets) -> Vec<u128> {
    targets.iter().map(|(value, _)| value).collect()
}

/// Extract the function `DefId` from a constant function operand.
pub(super) fn operand_fn_def_id(operand: &mir::Operand<'_>) -> Option<DefId> {
    let mir::Operand::Constant(constant) = operand else {
        return None;
    };

    const_fn_def_id(constant)
}

/// Resolve the `DefId` for the lang-level `Drop::drop` method.
pub(super) fn resolve_drop_drop_did(tcx: ty::TyCtxt<'_>) -> Option<DefId> {
    let drop_did = search::try_resolve_did(tcx, &["core", "ops", "drop", "Drop"])?;
    let drop_symbol = span::Symbol::intern("drop");
    let drop_ident = span::Ident::with_dummy_span(drop_symbol);
    tcx.associated_items(drop_did)
        .find_by_ident_and_kind(tcx, drop_ident, ty::AssocTag::Fn, drop_did)
        .map(|item| item.def_id)
}

/// Extract the function `DefId` from a MIR constant operand.
pub(super) fn const_fn_def_id(constant: &mir::ConstOperand<'_>) -> Option<DefId> {
    let ty::TyKind::FnDef(did, _) = constant.const_.ty().kind() else {
        return None;
    };

    Some(*did)
}

/// Compare cast kinds while allowing drop-elaboration pointer-coercion rewrites.
pub(super) fn cast_kind_equiv(target: mir::CastKind, source: mir::CastKind) -> bool {
    // Drop elaboration lowers this pointer coercion to the more primitive
    // `PtrToPtr` cast. Treat them as the same shape for source mapping.
    if matches!(
        (target, source),
        (
            mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::MutToConstPointer, _),
            mir::CastKind::PtrToPtr,
        ) | (
            mir::CastKind::PtrToPtr,
            mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::MutToConstPointer, _),
        )
    ) {
        return true;
    }

    target == source
}

/// Compare aggregate kinds by their mapping-relevant identity.
pub(super) fn aggregate_kind_equiv<'tcx>(
    target: &mir::AggregateKind<'tcx>,
    source: &mir::AggregateKind<'tcx>,
) -> bool {
    match (target, source) {
        // Aggregate generic arguments carry NLL regions in borrowck MIR and erased
        // regions in dropck MIR. For mapping, the ADT identity and variant are the
        // semantic shape we need.
        (
            mir::AggregateKind::Adt(def_id_t, variant_t, _, _, active_field_t),
            mir::AggregateKind::Adt(def_id_s, variant_s, _, _, active_field_s),
        ) => def_id_t == def_id_s && variant_t == variant_s && active_field_t == active_field_s,
        (mir::AggregateKind::Closure(def_id_t, _), mir::AggregateKind::Closure(def_id_s, _))
        | (mir::AggregateKind::Coroutine(def_id_t, _), mir::AggregateKind::Coroutine(def_id_s, _))
        | (
            mir::AggregateKind::CoroutineClosure(def_id_t, _),
            mir::AggregateKind::CoroutineClosure(def_id_s, _),
        ) => def_id_t == def_id_s,
        (mir::AggregateKind::Array(ty_t), mir::AggregateKind::Array(ty_s)) => ty_t == ty_s,
        (mir::AggregateKind::Tuple, mir::AggregateKind::Tuple) => true,
        (mir::AggregateKind::RawPtr(ty_t, mutability_t), mir::AggregateKind::RawPtr(ty_s, mutability_s)) => {
            ty_t == ty_s && mutability_t == mutability_s
        },
        _ => false,
    }
}

/// Convert a MIR place projection element to its normalized representation.
pub(super) const fn normalize_projection_elem(elem: mir::PlaceElem<'_>) -> NormalizedPlaceElem {
    match elem {
        mir::ProjectionElem::Deref => NormalizedPlaceElem::Deref,
        mir::ProjectionElem::Field(field, _) => NormalizedPlaceElem::Field(field.as_usize()),
        mir::ProjectionElem::Index(local) => NormalizedPlaceElem::Index(local),
        mir::ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => NormalizedPlaceElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        },
        mir::ProjectionElem::Subslice { from, to, from_end } => {
            NormalizedPlaceElem::Subslice { from, to, from_end }
        },
        mir::ProjectionElem::Downcast(_, variant_index) => {
            NormalizedPlaceElem::Downcast(variant_index.as_usize())
        },
        mir::ProjectionElem::OpaqueCast(_) => NormalizedPlaceElem::OpaqueCast,
        mir::ProjectionElem::UnwrapUnsafeBinder(_) => NormalizedPlaceElem::UnwrapUnsafeBinder,
    }
}

/// Extract the cleanup target from a MIR unwind action.
pub(super) const fn unwind_target(action: mir::UnwindAction) -> Option<BasicBlock> {
    match action {
        mir::UnwindAction::Cleanup(bb) => Some(bb),
        mir::UnwindAction::Continue | mir::UnwindAction::Unreachable | mir::UnwindAction::Terminate(_) => {
            None
        },
    }
}

/// Count all statement and terminator locations in a body.
pub(super) fn count_locations(body: &Body<'_>) -> usize {
    body.basic_blocks.iter().map(|bb| bb.statements.len() + 1).sum()
}
