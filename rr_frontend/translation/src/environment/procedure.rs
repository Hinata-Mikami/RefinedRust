// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::trace;
use rr_rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{bug, mir, ty};
use rr_rustc_interface::type_ir::TypeFoldable as _;

use crate::environment::mir_mapper::{
    MappingResult, Origin, SyntheticDropBorrow, map_drop_elaborated_to_borrow_checked,
};
use crate::environment::mir_utils::box_deref_alias;
use crate::environment::mir_utils::real_edges::RealEdges;
use crate::environment::{loops, mir_storage};

/// Index of a Basic Block
pub(crate) type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub(crate) struct Procedure<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    proc_def_id: DefId,
    borrowck_mir: &'tcx mir::Body<'tcx>,
    dropck_mir: mir::Body<'tcx>,
    mapping: MappingResult,
    box_deref_aliases: FxHashMap<mir::Local, mir::Place<'tcx>>,
    copy_aliases: FxHashMap<mir::Local, mir::Place<'tcx>>,
    box_materialization_aliases: FxHashMap<mir::Local, mir::Place<'tcx>>,
    real_edges: RealEdges,
    loop_info: loops::ProcedureLoops,
}

struct ErasedRegionDetector<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    found: bool,
}

struct BoxMaterializationUseValidator<'tcx> {
    box_temp: mir::Local,
    raw_temp: mir::Local,
    box_definition: mir::Location,
    raw_definition: mir::Location,
    raw_source: mir::Place<'tcx>,
    valid: bool,
}

impl<'tcx> mir::visit::Visitor<'tcx> for BoxMaterializationUseValidator<'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        if place.local == self.box_temp {
            let is_definition = location == self.box_definition
                && place.projection.is_empty()
                && context.is_place_assignment();
            let is_pointer_extraction = location == self.raw_definition
                && *place == self.raw_source
                && matches!(
                    context,
                    mir::visit::PlaceContext::NonMutatingUse(mir::visit::NonMutatingUseContext::Copy)
                );
            if !is_definition && !is_pointer_extraction {
                self.valid = false;
            }
        }

        // Writes through the raw pointer are uses of its pointee, not redefinitions of the pointer local.
        if place.local == self.raw_temp
            && place.projection.is_empty()
            && context.is_mutating_use()
            && !(location == self.raw_definition && context.is_place_assignment())
        {
            self.valid = false;
        }

        self.super_place(place, context, location);
    }
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for ErasedRegionDetector<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if matches!(r.kind(), ty::RegionKind::ReErased) {
            self.found = true;
        }
        r
    }
}

impl<'tcx> Procedure<'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    pub(crate) fn new(tcx: ty::TyCtxt<'tcx>, proc_def_id: DefId) -> Self {
        trace!("Encoding procedure {:?}", proc_def_id);
        let local_def_id = proc_def_id.expect_local();
        let borrowck_mir = &mir_storage::retrieve_mir_body(tcx, local_def_id).as_ref().unwrap().body;
        let dropck_mir_ref = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
        let dropck_mir_ref = dropck_mir_ref.borrow();
        let mapping = map_drop_elaborated_to_borrow_checked(tcx, borrowck_mir, &dropck_mir_ref);
        let dropck_mir = dropck_mir_ref.clone();
        drop(dropck_mir_ref);

        let box_deref_aliases =
            box_deref_alias::collect_box_deref_aliases(tcx, &dropck_mir).into_iter().collect();
        let copy_aliases = Self::collect_copy_aliases(tcx, borrowck_mir, &dropck_mir);
        let box_materialization_aliases =
            Self::collect_box_materialization_aliases(tcx, borrowck_mir, &dropck_mir);
        let real_edges = RealEdges::new(&dropck_mir);
        let loop_info = loops::ProcedureLoops::new(&dropck_mir, &real_edges);

        Self {
            tcx,
            proc_def_id,
            borrowck_mir,
            dropck_mir,
            mapping,
            box_deref_aliases,
            copy_aliases,
            box_materialization_aliases,
            real_edges,
            loop_info,
        }
    }

    fn collect_copy_aliases(
        tcx: ty::TyCtxt<'tcx>,
        borrowck_mir: &mir::Body<'tcx>,
        dropck_mir: &mir::Body<'tcx>,
    ) -> FxHashMap<mir::Local, mir::Place<'tcx>> {
        let mut copy_aliases = FxHashMap::default();

        for block in dropck_mir.basic_blocks.iter() {
            for stmt in &block.statements {
                let mir::StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (target, rval) = assign.as_ref();
                if !target.projection.is_empty() || borrowck_mir.local_decls.get(target.local).is_some() {
                    continue;
                }

                let mir::Rvalue::Use(mir::Operand::Copy(source) | mir::Operand::Move(source), _) = rval
                else {
                    continue;
                };
                let Some(target_decl) = dropck_mir.local_decls.get(target.local) else {
                    continue;
                };
                if !Self::contains_erased_regions_in(tcx, target_decl.ty) {
                    continue;
                }

                copy_aliases.insert(target.local, *source);
            }
        }

        copy_aliases
    }

    /// Recognize the exact rustc lowering used to expose the pointer of a projected `Box`:
    ///
    /// ```text
    /// _box_tmp = no_retag copy BOX_PLACE
    /// _raw_tmp = copy ((_box_tmp.0).0) as *const T (Transmute)
    /// ```
    ///
    /// Both temporaries must be target-only, the assignments must be consecutive in one block,
    /// `BOX_PLACE` must have the same `Box<T, A>` type and contain a preceding dereference, and
    /// `_box_tmp` may have no other use. `_raw_tmp` remains executable and may be consumed normally,
    /// but it may not be redefined. This deliberately narrow recognition prevents an unrelated
    /// rustc administrative copy from being silently erased.
    ///
    /// Only `_box_tmp` is removed from executable translation. Its sole `_box_tmp.0.0` use is
    /// normalized to `BOX_PLACE.0.0`, allowing the existing transmute lowering to extract the raw
    /// pointer explicitly. `_raw_tmp` remains a real pointer local, so code generation does not need
    /// the removed `MagicBoxDeref` operation.
    fn collect_box_materialization_aliases(
        tcx: ty::TyCtxt<'tcx>,
        borrowck_mir: &mir::Body<'tcx>,
        dropck_mir: &mir::Body<'tcx>,
    ) -> FxHashMap<mir::Local, mir::Place<'tcx>> {
        let mut aliases = FxHashMap::default();

        for (bb, data) in dropck_mir.basic_blocks.iter_enumerated() {
            for (idx, statements) in data.statements.windows(2).enumerate() {
                let [box_copy, raw_alias] = statements else {
                    unreachable!();
                };

                let mir::StatementKind::Assign(box (box_lhs, box_rhs)) = &box_copy.kind else {
                    continue;
                };
                let mir::Rvalue::Use(mir::Operand::Copy(box_source), retag) = box_rhs else {
                    continue;
                };
                if !box_lhs.projection.is_empty()
                    || !retag.no()
                    || borrowck_mir.local_decls.get(box_lhs.local).is_some()
                    || dropck_mir.local_kind(box_lhs.local) != mir::LocalKind::Temp
                    || !box_source.projection.contains(&mir::ProjectionElem::Deref)
                {
                    continue;
                }

                let box_ty = dropck_mir.local_decls[box_lhs.local].ty;
                let ty::TyKind::Adt(box_def, box_args) = box_ty.kind() else {
                    continue;
                };
                if !box_def.is_box() || box_source.ty(&dropck_mir.local_decls, tcx).ty != box_ty {
                    continue;
                }
                let [box_element, _allocator] = box_args.as_slice() else {
                    continue;
                };
                let Some(box_element) = box_element.as_type() else {
                    continue;
                };

                let mir::StatementKind::Assign(box (raw_lhs, raw_rhs)) = &raw_alias.kind else {
                    continue;
                };
                let mir::Rvalue::Cast(
                    mir::CastKind::Transmute,
                    mir::Operand::Copy(raw_source),
                    raw_target_ty,
                ) = raw_rhs
                else {
                    continue;
                };
                if !raw_lhs.projection.is_empty()
                    || raw_lhs.local == box_lhs.local
                    || borrowck_mir.local_decls.get(raw_lhs.local).is_some()
                    || dropck_mir.local_kind(raw_lhs.local) != mir::LocalKind::Temp
                    || dropck_mir.local_decls[raw_lhs.local].ty != *raw_target_ty
                    || raw_source.local != box_lhs.local
                    || raw_source.projection.len() != 2
                    || !raw_source.projection.iter().all(
                        |elem| matches!(elem, mir::ProjectionElem::Field(field, _) if field.as_usize() == 0),
                    )
                    || !matches!(raw_target_ty.kind(), ty::TyKind::RawPtr(inner, ty::Mutability::Not) if *inner == box_element)
                {
                    continue;
                }

                let box_definition = mir::Location {
                    block: bb,
                    statement_index: idx,
                };
                let raw_definition = mir::Location {
                    block: bb,
                    statement_index: idx + 1,
                };
                let mut validator = BoxMaterializationUseValidator {
                    box_temp: box_lhs.local,
                    raw_temp: raw_lhs.local,
                    box_definition,
                    raw_definition,
                    raw_source: *raw_source,
                    valid: true,
                };
                mir::visit::Visitor::visit_body(&mut validator, dropck_mir);
                if !validator.valid {
                    continue;
                }

                aliases.insert(box_lhs.local, *box_source);
            }
        }

        aliases
    }

    #[must_use]
    pub(crate) const fn loop_info(&self) -> &loops::ProcedureLoops {
        &self.loop_info
    }

    /// Get definition ID of the procedure.
    #[must_use]
    pub(crate) const fn get_id(&self) -> DefId {
        self.proc_def_id
    }

    /// Get the borrowck MIR of the procedure.
    #[must_use]
    pub(crate) const fn borrowck_mir(&self) -> &mir::Body<'tcx> {
        self.borrowck_mir
    }

    /// Get the drop-checked MIR used for body translation.
    #[must_use]
    pub(crate) const fn dropck_mir(&self) -> &mir::Body<'tcx> {
        &self.dropck_mir
    }

    /// Get the mapping from drop-checked MIR locations to borrowck MIR locations.
    #[must_use]
    pub(crate) const fn mapping(&self) -> &MappingResult {
        &self.mapping
    }

    /// Rewrite dropck's synthetic raw-pointer `Box` deref aliases back to the
    /// borrowck-level `Box` deref place. This is only used for source-level
    /// typing and location alignment; code generation keeps the raw-pointer
    /// alias explicit and translates its initializer directly.
    pub(crate) fn normalize_box_deref_alias_place(&self, pl: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        let mut normalized = *pl;
        let mut visited = FxHashSet::default();

        while visited.insert(normalized.local) {
            let box_alias = box_deref_alias::normalize_deref_alias_place(self.tcx, &normalized, |local| {
                self.box_deref_aliases.get(&local).copied()
            });
            let materialized = self.normalize_box_materialization_place(&normalized);
            let copied = self.normalize_copy_alias_place(&normalized);
            let next = if box_alias != normalized {
                box_alias
            } else if materialized != normalized {
                materialized
            } else {
                copied
            };
            if next == normalized {
                break;
            }
            normalized = next;
        }

        normalized
    }

    /// Rewrite dereference uses of synthetic `no_retag copy` locals back to the
    /// place they alias. Dropck introduces these around captured mutable refs in
    /// closures, while borrowck MIR keeps using the original projected place.
    pub(crate) fn normalize_copy_alias_place(&self, pl: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        let Some(source) = self.copy_aliases.get(&pl.local) else {
            return *pl;
        };
        if !matches!(pl.projection.first(), Some(mir::ProjectionElem::Deref)) {
            return *pl;
        }

        let mut projection = Vec::with_capacity(source.projection.len() + pl.projection.len());
        projection.extend_from_slice(source.projection);
        projection.extend_from_slice(pl.projection);
        let projection = self.tcx.mk_place_elems(&projection);
        mir::Place {
            local: source.local,
            projection,
        }
    }

    /// Rewrite the sole pointer-field use of a validated synthetic `Box` materialization.
    pub(crate) fn normalize_box_materialization_place(&self, pl: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        let Some(source) = self.box_materialization_aliases.get(&pl.local) else {
            return *pl;
        };

        let mut projection = Vec::with_capacity(source.projection.len() + pl.projection.len());
        projection.extend_from_slice(source.projection);
        projection.extend_from_slice(pl.projection);
        mir::Place {
            local: source.local,
            projection: self.tcx.mk_place_elems(&projection),
        }
    }

    /// Normalize aliases that are safe to erase from executable translation.
    pub(crate) fn normalize_executable_place(&self, pl: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        let mut normalized = *pl;
        let mut visited = FxHashSet::default();

        while visited.insert(normalized.local) {
            let materialized = self.normalize_box_materialization_place(&normalized);
            let copied = self.normalize_copy_alias_place(&normalized);
            let next = if materialized != normalized { materialized } else { copied };
            if next == normalized {
                break;
            }
            normalized = next;
        }

        normalized
    }

    #[must_use]
    pub(crate) fn is_administrative_alias(&self, local: mir::Local) -> bool {
        self.copy_aliases.contains_key(&local) || self.box_materialization_aliases.contains_key(&local)
    }

    #[must_use]
    pub(crate) fn synthetic_drop_borrow_for_assignment(
        &self,
        loc: mir::Location,
    ) -> Option<SyntheticDropBorrow> {
        self.mapping.synthetic_drop_borrow_for_borrow_loc((loc.block, loc.statement_index))
    }

    #[must_use]
    pub(crate) fn synthetic_drop_borrow_for_drop_call(
        &self,
        loc: mir::Location,
    ) -> Option<SyntheticDropBorrow> {
        self.mapping.synthetic_drop_borrow_for_drop_call_loc((loc.block, loc.statement_index))
    }

    #[must_use]
    pub(crate) fn synthetic_drop_borrow_for_local(&self, local: mir::Local) -> Option<SyntheticDropBorrow> {
        self.mapping.synthetic_drop_borrow_for_local(local)
    }

    pub(crate) fn synthetic_drop_borrow_place(
        &self,
        borrow: SyntheticDropBorrow,
    ) -> Option<mir::Place<'tcx>> {
        let (bb, idx) = borrow.borrow_loc();
        let stmt = self.dropck_mir.basic_blocks[bb].statements.get(idx)?;
        let mir::StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        let mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place) = assign.as_ref().1 else {
            return None;
        };
        Some(place)
    }

    pub(crate) fn synthetic_drop_borrow_referent_ty(&self, borrow: SyntheticDropBorrow) -> ty::Ty<'tcx> {
        let place = self.synthetic_drop_borrow_place(borrow).unwrap_or_else(|| {
            bug!("synthetic drop borrow {:?} has no borrow place", borrow.synthetic_ref_local())
        });
        self.region_type_of_place(&place).ty
    }

    #[must_use]
    pub(crate) fn is_unmentioned_synthetic_local(&self, local: mir::Local) -> bool {
        self.borrowck_mir.local_decls.get(local).is_none() && !self.dropck_mir_mentions_local(local)
    }

    fn dropck_mir_mentions_local(&self, local: mir::Local) -> bool {
        self.dropck_mir.basic_blocks.iter().any(|bb| {
            bb.statements.iter().any(|stmt| Self::statement_mentions_local(stmt, local))
                || Self::terminator_mentions_local(bb.terminator(), local)
        })
    }

    fn statement_mentions_local(stmt: &mir::Statement<'tcx>, local: mir::Local) -> bool {
        match &stmt.kind {
            mir::StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.as_ref();
                Self::place_mentions_local(place, local) || Self::rvalue_mentions_local(rvalue, local)
            },
            mir::StatementKind::StorageLive(l) | mir::StatementKind::StorageDead(l) => *l == local,
            mir::StatementKind::FakeRead(box (_, place))
            | mir::StatementKind::PlaceMention(box place)
            | mir::StatementKind::BackwardIncompatibleDropHint {
                place: box place, ..
            } => Self::place_mentions_local(place, local),
            mir::StatementKind::SetDiscriminant { place, .. } => Self::place_mentions_local(place, local),
            mir::StatementKind::AscribeUserType(box (place, _), _) => {
                Self::place_mentions_local(place, local)
            },
            mir::StatementKind::Intrinsic(_)
            | mir::StatementKind::Coverage(_)
            | mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop => false,
        }
    }

    fn terminator_mentions_local(term: &mir::Terminator<'tcx>, local: mir::Local) -> bool {
        match &term.kind {
            mir::TerminatorKind::SwitchInt { discr, .. } => Self::operand_mentions_local(discr, local),
            mir::TerminatorKind::Drop { place, .. } => Self::place_mentions_local(place, local),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                Self::operand_mentions_local(func, local)
                    || args.iter().any(|arg| Self::operand_mentions_local(&arg.node, local))
                    || Self::place_mentions_local(destination, local)
            },
            mir::TerminatorKind::Assert { cond, .. } => Self::operand_mentions_local(cond, local),
            mir::TerminatorKind::InlineAsm { operands, .. } => operands.iter().any(|operand| match operand {
                mir::InlineAsmOperand::In { value, .. } => Self::operand_mentions_local(value, local),
                mir::InlineAsmOperand::Out { place, .. } => {
                    place.as_ref().is_some_and(|place| Self::place_mentions_local(place, local))
                },
                mir::InlineAsmOperand::InOut {
                    in_value,
                    out_place,
                    ..
                } => {
                    Self::operand_mentions_local(in_value, local)
                        || out_place.as_ref().is_some_and(|place| Self::place_mentions_local(place, local))
                },
                mir::InlineAsmOperand::Const { .. }
                | mir::InlineAsmOperand::SymFn { .. }
                | mir::InlineAsmOperand::SymStatic { .. }
                | mir::InlineAsmOperand::Label { .. } => false,
            }),
            mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::Return
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. }
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::TailCall { .. } => false,
        }
    }

    fn rvalue_mentions_local(rvalue: &mir::Rvalue<'tcx>, local: mir::Local) -> bool {
        match rvalue {
            mir::Rvalue::Use(operand, _)
            | mir::Rvalue::Repeat(operand, _)
            | mir::Rvalue::WrapUnsafeBinder(operand, _)
            | mir::Rvalue::UnaryOp(_, operand)
            | mir::Rvalue::Cast(_, operand, _) => Self::operand_mentions_local(operand, local),
            mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Reborrow(_, _, place)
            | mir::Rvalue::Discriminant(place)
            | mir::Rvalue::CopyForDeref(place) => Self::place_mentions_local(place, local),
            mir::Rvalue::BinaryOp(_, operands) => {
                Self::operand_mentions_local(&operands.as_ref().0, local)
                    || Self::operand_mentions_local(&operands.as_ref().1, local)
            },
            mir::Rvalue::Aggregate(_, operands) => {
                operands.iter().any(|operand| Self::operand_mentions_local(operand, local))
            },
            mir::Rvalue::ThreadLocalRef(_) => false,
        }
    }

    fn operand_mentions_local(operand: &mir::Operand<'tcx>, local: mir::Local) -> bool {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => Self::place_mentions_local(place, local),
            mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => false,
        }
    }

    fn place_mentions_local(place: &mir::Place<'tcx>, local: mir::Local) -> bool {
        place.local == local
            || place
                .projection
                .iter()
                .any(|elem| matches!(elem, mir::ProjectionElem::Index(l) if l == local))
    }

    /// Get the typing context.
    #[must_use]
    pub(crate) const fn get_tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    /// Get the predecessors of a basic block.
    #[must_use]
    pub(crate) fn predecessors(&self, bbi: mir::BasicBlock) -> &[mir::BasicBlock] {
        self.real_edges.predecessors(bbi)
    }

    /// Get the successors of a basic block.
    #[must_use]
    pub(crate) fn successors(&self, bbi: mir::BasicBlock) -> &[mir::BasicBlock] {
        self.real_edges.successors(bbi)
    }

    /// Check whether a type still contains erased regions.
    pub(crate) fn contains_erased_regions(&self, ty: ty::Ty<'tcx>) -> bool {
        Self::contains_erased_regions_in(self.tcx, ty)
    }

    fn contains_erased_regions_in(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
        let mut detector = ErasedRegionDetector { tcx, found: false };
        ty.fold_with(&mut detector);
        detector.found
    }

    pub(crate) fn ensure_region_type(
        &self,
        ty: ty::Ty<'tcx>,
        context: impl FnOnce() -> String,
    ) -> ty::Ty<'tcx> {
        if self.contains_erased_regions(ty) {
            bug!("region-sensitive type contains erased regions in {}: {ty:?}", context());
        }
        ty
    }

    /// Get the region-sensitive borrowck type of a local.
    pub(crate) fn region_type_of_local(&self, local: mir::Local) -> ty::Ty<'tcx> {
        if let Some(decl) = self.borrowck_mir.local_decls.get(local) {
            return self.ensure_region_type(decl.ty, || format!("local {local:?}"));
        }

        if let Some(borrow) = self.mapping.synthetic_drop_borrow_for_local(local) {
            let place_ty = self.synthetic_drop_borrow_referent_ty(borrow);
            let ty = self.dropck_mir.local_decls.get(local).map_or_else(
                || bug!("region-sensitive type requested for unknown synthetic drop borrow local {local:?}"),
                |decl| decl.ty,
            );
            let ty::TyKind::Ref(region, _, mutability) = ty.kind() else {
                bug!("synthetic drop borrow local {local:?} has non-reference type: {ty:?}");
            };
            return ty::Ty::new_ref(self.tcx, *region, place_ty, *mutability);
        }

        if let Some(source) = self.copy_aliases.get(&local) {
            return self.region_type_of_place(source).ty;
        }

        // Drop elaboration may introduce administrative locals such as boolean
        // drop flags. They carry no lifetime information, so their dropck shape
        // type is also a valid region-sensitive type as long as it has no erased
        // regions.
        let ty = self.dropck_mir.local_decls.get(local).map_or_else(
            || bug!("region-sensitive type requested for unknown dropck local {local:?}"),
            |decl| decl.ty,
        );
        self.ensure_region_type(ty, || format!("synthetic dropck local {local:?}"))
    }

    /// Get the region-sensitive borrowck type of a target/dropck place.
    pub(crate) fn region_type_of_place(&self, pl: &mir::Place<'tcx>) -> mir::PlaceTy<'tcx> {
        let normalized = self.normalize_box_deref_alias_place(pl);
        let pl = &normalized;
        let mut cur_ty = mir::PlaceTy::from_ty(self.region_type_of_local(pl.local));

        for elem in pl.projection {
            cur_ty = match elem {
                mir::ProjectionElem::Deref => {
                    let ty = cur_ty.ty.builtin_deref(true).unwrap_or_else(|| {
                        bug!("deref projection on non-dereferenceable region-sensitive place type {cur_ty:?}")
                    });
                    mir::PlaceTy::from_ty(ty)
                },
                mir::ProjectionElem::Field(field, _) => mir::PlaceTy::from_ty(
                    mir::PlaceTy::field_ty(self.tcx, cur_ty.ty, cur_ty.variant_index, field).skip_norm_wip(),
                ),
                mir::ProjectionElem::Downcast(_, variant_idx) => mir::PlaceTy {
                    ty: cur_ty.ty,
                    variant_index: Some(variant_idx),
                },
                mir::ProjectionElem::Index(_) | mir::ProjectionElem::ConstantIndex { .. } => {
                    mir::PlaceTy::from_ty(cur_ty.ty.builtin_index().unwrap_or_else(|| {
                        bug!("index projection on non-indexable region-sensitive place type {cur_ty:?}")
                    }))
                },
                mir::ProjectionElem::Subslice { from, to, from_end } => {
                    let ty = match cur_ty.ty.kind() {
                        ty::TyKind::Slice(..) => cur_ty.ty,
                        ty::TyKind::Array(inner, _) if !from_end => {
                            ty::Ty::new_array(self.tcx, *inner, to - from)
                        },
                        ty::TyKind::Array(inner, size) if from_end => {
                            let size = size.try_to_target_usize(self.tcx).unwrap_or_else(|| {
                                bug!("cannot determine array size for region-sensitive subslice projection of {cur_ty:?}")
                            });
                            ty::Ty::new_array(self.tcx, *inner, size - from - to)
                        },
                        _ => {
                            bug!("subslice projection on unsupported region-sensitive place type {cur_ty:?}");
                        },
                    };
                    mir::PlaceTy::from_ty(ty)
                },
                mir::ProjectionElem::OpaqueCast(_) => {
                    bug!("region-sensitive OpaqueCast place typing");
                },
                mir::ProjectionElem::UnwrapUnsafeBinder(_) => {
                    bug!("region-sensitive UnwrapUnsafeBinder place typing");
                },
            };
            self.ensure_region_type(cur_ty.ty, || format!("place {pl:?}"));
        }

        cur_ty
    }

    /// Get the region-sensitive borrowck type of a target/dropck operand.
    pub(crate) fn region_type_of_operand(&self, op: &mir::Operand<'tcx>) -> ty::Ty<'tcx> {
        match op {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self.region_type_of_place(place).ty,
            mir::Operand::Constant(constant) => {
                let ty = constant.const_.ty();
                self.ensure_region_type(ty, || format!("constant operand {op:?}"))
            },
            mir::Operand::RuntimeChecks(_) => {
                bug!("region-sensitive type requested for runtime-check operand {op:?}");
            },
        }
    }

    /// Get the borrowck source statement corresponding to a target/dropck statement location.
    pub(crate) fn source_statement_for_target(&self, loc: mir::Location) -> Option<&mir::Statement<'tcx>> {
        let origin = self.mapping.origin_for_target((loc.block, loc.statement_index))?;
        let (source_block, source_statement_index) = match origin {
            Origin::Source(source) | Origin::FoldedFrom(source) | Origin::SplitFrom(source) => source,
            Origin::Inserted => return None,
        };

        self.borrowck_mir.basic_blocks[source_block].statements.get(source_statement_index)
    }

    /// Get the borrowck source region for a target/dropck borrow rvalue.
    pub(crate) fn source_borrow_region_for_target(&self, loc: mir::Location) -> Option<ty::Region<'tcx>> {
        let source_stmt = self.source_statement_for_target(loc)?;
        let mir::StatementKind::Assign(source_assign) = &source_stmt.kind else {
            return None;
        };
        let mir::Rvalue::Ref(region, _, _) = source_assign.as_ref().1 else {
            return None;
        };
        Some(region)
    }

    /// Get the borrowck source rvalue corresponding to a target/dropck assignment.
    pub(crate) fn source_rvalue_for_target(&self, loc: mir::Location) -> Option<&mir::Rvalue<'tcx>> {
        let source_stmt = self.source_statement_for_target(loc)?;
        let mir::StatementKind::Assign(source_assign) = &source_stmt.kind else {
            return None;
        };
        Some(&source_assign.as_ref().1)
    }

    /// Get the borrowck source aggregate kind corresponding to a target/dropck aggregate rvalue.
    pub(crate) fn source_aggregate_kind_for_target(
        &self,
        loc: mir::Location,
    ) -> Option<&mir::AggregateKind<'tcx>> {
        let mir::Rvalue::Aggregate(kind, _) = self.source_rvalue_for_target(loc)? else {
            return None;
        };
        Some(kind.as_ref())
    }

    /// Get the borrowck source call terminator corresponding to a target/dropck call terminator.
    pub(crate) fn source_call_for_target(&self, loc: mir::Location) -> Option<&mir::Terminator<'tcx>> {
        let origin = self.mapping.origin_for_target((loc.block, loc.statement_index))?;
        let (source_block, source_statement_index) = match origin {
            Origin::Source(source) | Origin::FoldedFrom(source) | Origin::SplitFrom(source) => source,
            Origin::Inserted => return None,
        };

        let source_block_data = &self.borrowck_mir.basic_blocks[source_block];
        if source_statement_index != source_block_data.statements.len() {
            return None;
        }

        let terminator = source_block_data.terminator();
        matches!(terminator.kind, mir::TerminatorKind::Call { .. }).then_some(terminator)
    }

    /// Get the region-sensitive borrowck type of a target/dropck rvalue.
    pub(crate) fn region_type_of_rvalue(&self, loc: mir::Location, rval: &mir::Rvalue<'tcx>) -> ty::Ty<'tcx> {
        if let Some(source_stmt) = self.source_statement_for_target(loc)
            && let mir::StatementKind::Assign(source_assign) = &source_stmt.kind
        {
            let source_rval = &source_assign.as_ref().1;
            let ty = source_rval.ty(&self.borrowck_mir.local_decls, self.tcx);
            return self.ensure_region_type(ty, || format!("source rvalue for target location {loc:?}"));
        }

        let ty = match rval {
            mir::Rvalue::Use(op, _) => self.region_type_of_operand(op),
            mir::Rvalue::Ref(region, borrow_kind, place) => {
                let place_ty = self.region_type_of_place(place).ty;
                let mutability = match borrow_kind {
                    mir::BorrowKind::Shared | mir::BorrowKind::Fake(_) => ty::Mutability::Not,
                    mir::BorrowKind::Mut { .. } => ty::Mutability::Mut,
                };
                ty::Ty::new_ref(self.tcx, *region, place_ty, mutability)
            },
            mir::Rvalue::RawPtr(_, _)
            | mir::Rvalue::BinaryOp(_, _)
            | mir::Rvalue::UnaryOp(_, _)
            | mir::Rvalue::Discriminant(_)
            | mir::Rvalue::Aggregate(_, _)
            | mir::Rvalue::Cast(_, _, _)
            | mir::Rvalue::CopyForDeref(_)
            | mir::Rvalue::Repeat(_, _)
            | mir::Rvalue::ThreadLocalRef(_)
            | mir::Rvalue::Reborrow(_, _, _)
            | mir::Rvalue::WrapUnsafeBinder(_, _) => rval.ty(&self.dropck_mir.local_decls, self.tcx),
        };

        self.ensure_region_type(ty, || format!("target rvalue at {loc:?}"))
    }
}
