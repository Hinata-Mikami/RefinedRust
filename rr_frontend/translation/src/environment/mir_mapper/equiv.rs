// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use rr_rustc_interface::data_structures::fx::FxHashSet;
use rr_rustc_interface::middle::mir::{self, Local};
use rr_rustc_interface::span;

use super::types::*;
use super::util::*;
use super::{Mapper, Origin, SourceLoc};
use crate::environment::mir_utils::box_alias;

impl<'tcx> Mapper<'_, 'tcx> {
    /// Check whether two statements have the same mapping-relevant shape.
    pub(super) fn stmt_equiv(&self, target: &mir::Statement<'tcx>, source: &mir::Statement<'tcx>) -> bool {
        match (&target.kind, &source.kind) {
            (
                mir::StatementKind::Assign(box (lhs_t, rhs_t)),
                mir::StatementKind::Assign(box (lhs_s, rhs_s)),
            ) => self.place_equiv(*lhs_t, *lhs_s) && self.rvalue_equiv(rhs_t, rhs_s),
            (mir::StatementKind::StorageLive(local_t), mir::StatementKind::StorageLive(local_s))
            | (mir::StatementKind::StorageDead(local_t), mir::StatementKind::StorageDead(local_s)) => {
                local_t == local_s
            },
            (mir::StatementKind::FakeRead(fake_read_t), mir::StatementKind::FakeRead(fake_read_s)) => {
                fake_read_t == fake_read_s
            },
            (
                mir::StatementKind::SetDiscriminant {
                    place: place_t,
                    variant_index: variant_t,
                },
                mir::StatementKind::SetDiscriminant {
                    place: place_s,
                    variant_index: variant_s,
                },
            ) => variant_t == variant_s && self.place_equiv(**place_t, **place_s),
            (mir::StatementKind::PlaceMention(place_t), mir::StatementKind::PlaceMention(place_s)) => {
                self.place_equiv(**place_t, **place_s)
            },
            (
                mir::StatementKind::AscribeUserType(place_t, variance_t),
                mir::StatementKind::AscribeUserType(place_s, variance_s),
            ) => {
                variance_t == variance_s
                    && place_t.as_ref().1 == place_s.as_ref().1
                    && self.place_equiv(place_t.as_ref().0, place_s.as_ref().0)
            },
            (mir::StatementKind::Intrinsic(intrinsic_t), mir::StatementKind::Intrinsic(intrinsic_s)) => {
                intrinsic_t == intrinsic_s
            },
            (mir::StatementKind::Coverage(kind_t), mir::StatementKind::Coverage(kind_s)) => kind_t == kind_s,
            (mir::StatementKind::ConstEvalCounter, mir::StatementKind::ConstEvalCounter)
            | (mir::StatementKind::Nop, mir::StatementKind::Nop) => true,
            (
                mir::StatementKind::BackwardIncompatibleDropHint {
                    place: place_t,
                    reason: reason_t,
                },
                mir::StatementKind::BackwardIncompatibleDropHint {
                    place: place_s,
                    reason: reason_s,
                },
            ) => reason_t == reason_s && self.place_equiv(**place_t, **place_s),
            _ => false,
        }
    }

    /// Check whether two terminators have the same mapping-relevant shape.
    pub(super) fn terminator_shape_equiv(
        &self,
        target: &mir::Terminator<'tcx>,
        source: &mir::Terminator<'tcx>,
    ) -> bool {
        use mir::TerminatorKind::{
            Assert, Call, Drop, FalseEdge, FalseUnwind, Goto, Return, SwitchInt, Unreachable, UnwindResume,
            UnwindTerminate,
        };

        match (&target.kind, &source.kind) {
            (Goto { .. }, Goto { .. })
            | (Goto { .. }, FalseEdge { .. })
            | (Goto { .. }, FalseUnwind { .. })
            | (FalseEdge { .. }, Goto { .. })
            | (FalseUnwind { .. }, Goto { .. })
            | (Return, Return)
            | (UnwindResume, UnwindResume)
            | (Unreachable, Unreachable) => true,
            (UnwindTerminate(a), UnwindTerminate(b)) => a == b,
            (
                SwitchInt {
                    discr: discr_t,
                    targets: targets_t,
                },
                SwitchInt {
                    discr: discr_s,
                    targets: targets_s,
                },
            ) => self.operand_equiv(discr_t, discr_s) && switch_values(targets_t) == switch_values(targets_s),
            (
                Assert {
                    cond: cond_t,
                    expected: expected_t,
                    msg: msg_t,
                    ..
                },
                Assert {
                    cond: cond_s,
                    expected: expected_s,
                    msg: msg_s,
                    ..
                },
            ) => {
                expected_t == expected_s
                    && self.operand_equiv(cond_t, cond_s)
                    && self.assert_msg_equiv(msg_t, msg_s)
            },
            (Drop { place: place_t, .. }, Drop { place: place_s, .. }) => {
                self.place_equiv(*place_t, *place_s)
            },
            (
                Call {
                    func: func_t,
                    args: args_t,
                    destination: dest_t,
                    target: target_t,
                    ..
                },
                Call {
                    func: func_s,
                    args: args_s,
                    destination: dest_s,
                    target: target_s,
                    ..
                },
            ) => {
                self.call_core_equiv(func_t, args_t, *dest_t, func_s, args_s, *dest_s)
                    && target_t.is_some() == target_s.is_some()
            },
            _ => false,
        }
    }

    /// Check whether a target statement was inserted by post-borrowck MIR passes.
    pub(super) fn is_inserted_stmt(&self, stmt: &mir::Statement<'tcx>) -> bool {
        match &stmt.kind {
            mir::StatementKind::StorageLive(local) | mir::StatementKind::StorageDead(local) => {
                self.is_synthetic_local(*local)
            },
            mir::StatementKind::Assign(box (lhs, _)) => {
                lhs.projection.is_empty() && self.is_synthetic_local(lhs.local)
            },
            _ => false,
        }
    }

    /// Record metadata for an inserted statement when it introduces an alias.
    pub(super) fn observe_inserted_stmt(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        source_loc: Option<SourceLoc>,
    ) -> Option<Origin> {
        let mir::StatementKind::Assign(box (lhs, rhs)) = &stmt.kind else {
            return None;
        };

        if !lhs.projection.is_empty() || !self.is_synthetic_local(lhs.local) {
            return None;
        }

        if let mir::Rvalue::Use(mir::Operand::Copy(rhs_place) | mir::Operand::Move(rhs_place), _) = rhs {
            self.copy_aliases
                .insert(lhs.local, self.normalize_place_for_flavor(*rhs_place, MirFlavor::Target));
            return None;
        }

        let mir::Rvalue::Cast(
            mir::CastKind::BoxDerefTransmute,
            mir::Operand::Copy(rhs_place) | mir::Operand::Move(rhs_place),
            _,
        ) = rhs
        else {
            return None;
        };

        let box_place = box_alias::box_deref_alias_source_place(self.tcx, self.de, *rhs_place)?;
        let box_place = self.normalize_target_box_place(box_place);

        let split_from = source_loc.filter(|(bb, idx)| {
            self.source_stmt_uses_box_deref(&self.bc.basic_blocks[*bb].statements[*idx], &box_place)
        });

        self.box_deref_aliases.insert(lhs.local, InternalBoxDerefAlias {
            place: box_place,
            source_loc: split_from,
        });

        split_from.map(Origin::SplitFrom)
    }

    /// Normalize a target Box place through administrative copy aliases, including a plain alias-local use.
    fn normalize_target_box_place(&self, place: mir::Place<'tcx>) -> NormalizedPlace {
        let mut normalized = self.normalize_place_for_flavor(place, MirFlavor::Target);
        let mut visited = FxHashSet::default();

        while visited.insert(normalized.local) {
            let Some(alias) = self.copy_aliases.get(&normalized.local) else {
                break;
            };
            let mut projection = alias.projection.clone();
            projection.extend(normalized.projection);
            normalized = NormalizedPlace {
                local: alias.local,
                projection,
            };
        }

        normalized
    }

    /// Check whether a source statement dereferences the given semantic `Box` place.
    pub(super) fn source_stmt_uses_box_deref(
        &self,
        stmt: &mir::Statement<'tcx>,
        box_place: &NormalizedPlace,
    ) -> bool {
        match &stmt.kind {
            mir::StatementKind::Assign(box (_, rhs)) => self.rvalue_uses_box_deref(rhs, box_place),
            mir::StatementKind::SetDiscriminant { place, .. }
            | mir::StatementKind::PlaceMention(place)
            | mir::StatementKind::BackwardIncompatibleDropHint { place, .. } => {
                self.place_uses_box_deref(**place, box_place)
            },
            mir::StatementKind::AscribeUserType(place, _) => {
                self.place_uses_box_deref(place.as_ref().0, box_place)
            },
            _ => false,
        }
    }

    /// Check whether a target statement uses a box-deref alias from a source location.
    pub(super) fn stmt_uses_box_deref_alias(
        &self,
        stmt: &mir::Statement<'tcx>,
        source_loc: SourceLoc,
    ) -> bool {
        match &stmt.kind {
            mir::StatementKind::Assign(box (lhs, rhs)) => {
                self.place_uses_alias_with_origin(*lhs, source_loc)
                    || self.rvalue_uses_alias_with_origin(rhs, source_loc)
            },
            mir::StatementKind::SetDiscriminant { place, .. }
            | mir::StatementKind::PlaceMention(place)
            | mir::StatementKind::BackwardIncompatibleDropHint { place, .. } => {
                self.place_uses_alias_with_origin(**place, source_loc)
            },
            mir::StatementKind::AscribeUserType(place, _) => {
                self.place_uses_alias_with_origin(place.as_ref().0, source_loc)
            },
            _ => false,
        }
    }

    /// Check whether an rvalue dereferences the given semantic `Box` place.
    fn rvalue_uses_box_deref(&self, rvalue: &mir::Rvalue<'tcx>, box_place: &NormalizedPlace) -> bool {
        Self::rvalue_uses_place(rvalue, |place| self.place_uses_box_deref(place, box_place))
    }

    /// Traverse places mentioned by an rvalue and test them with a predicate.
    fn rvalue_uses_place(
        rvalue: &mir::Rvalue<'tcx>,
        mut place_matches: impl FnMut(mir::Place<'tcx>) -> bool,
    ) -> bool {
        match rvalue {
            mir::Rvalue::Use(operand, _)
            | mir::Rvalue::Repeat(operand, _)
            | mir::Rvalue::WrapUnsafeBinder(operand, _)
            | mir::Rvalue::UnaryOp(_, operand)
            | mir::Rvalue::Cast(_, operand, _) => Self::operand_uses_place(operand, &mut place_matches),
            mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Reborrow(_, _, place)
            | mir::Rvalue::Discriminant(place)
            | mir::Rvalue::CopyForDeref(place) => place_matches(*place),
            mir::Rvalue::BinaryOp(_, operands) => {
                Self::operand_uses_place(&operands.as_ref().0, &mut place_matches)
                    || Self::operand_uses_place(&operands.as_ref().1, &mut place_matches)
            },
            mir::Rvalue::Aggregate(_, operands) => {
                operands.iter().any(|operand| Self::operand_uses_place(operand, &mut place_matches))
            },
            mir::Rvalue::ThreadLocalRef(_) => false,
        }
    }

    /// Traverse places mentioned by an operand and test them with a predicate.
    fn operand_uses_place(
        operand: &mir::Operand<'tcx>,
        place_matches: &mut impl FnMut(mir::Place<'tcx>) -> bool,
    ) -> bool {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => place_matches(*place),
            mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => false,
        }
    }

    /// Check whether a source place dereferences the given semantic `Box` place.
    fn place_uses_box_deref(&self, place: mir::Place<'tcx>, box_place: &NormalizedPlace) -> bool {
        let normalized = self.normalize_place_for_flavor(place, MirFlavor::Source);
        normalized.local == box_place.local
            && normalized.projection.starts_with(&box_place.projection)
            && matches!(
                normalized.projection.get(box_place.projection.len()),
                Some(NormalizedPlaceElem::Deref)
            )
    }

    /// Check whether an rvalue uses an alias introduced at the given source location.
    fn rvalue_uses_alias_with_origin(&self, rvalue: &mir::Rvalue<'tcx>, source_loc: SourceLoc) -> bool {
        Self::rvalue_uses_place(rvalue, |place| self.place_uses_alias_with_origin(place, source_loc))
    }

    /// Check whether a place is an alias introduced at the given source location.
    fn place_uses_alias_with_origin(&self, place: mir::Place<'tcx>, source_loc: SourceLoc) -> bool {
        self.box_deref_aliases
            .get(&place.local)
            .is_some_and(|alias| alias.source_loc == Some(source_loc))
    }

    /// Check whether a source statement is erased by cleanup/drop elaboration.
    pub(super) fn is_cleanup_erased_source_stmt(stmt: &mir::Statement<'tcx>) -> bool {
        matches!(
            &stmt.kind,
            mir::StatementKind::AscribeUserType(_, _)
            | mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Coverage(_)
            | mir::StatementKind::Assign(box (_, mir::Rvalue::Ref(_, mir::BorrowKind::Fake(_), _)))
        )
    }

    /// Check whether two operands have the same mapping-relevant shape.
    fn operand_equiv(&self, target: &mir::Operand<'tcx>, source: &mir::Operand<'tcx>) -> bool {
        match (target, source) {
            (mir::Operand::Copy(place_t), mir::Operand::Copy(place_s))
            | (mir::Operand::Move(place_t), mir::Operand::Move(place_s)) => {
                self.place_equiv(*place_t, *place_s)
            },
            (mir::Operand::Constant(const_t), mir::Operand::Constant(const_s)) => {
                self.const_operand_equiv(const_t, const_s)
            },
            (mir::Operand::RuntimeChecks(checks_t), mir::Operand::RuntimeChecks(checks_s)) => {
                checks_t == checks_s
            },
            _ => false,
        }
    }

    /// Check whether two constant operands denote equivalent constants.
    fn const_operand_equiv(
        &self,
        target: &mir::ConstOperand<'tcx>,
        source: &mir::ConstOperand<'tcx>,
    ) -> bool {
        if let (Some(target_did), Some(source_did)) = (const_fn_def_id(target), const_fn_def_id(source)) {
            return target_did == source_did;
        }

        if target.const_ == source.const_ {
            return true;
        }

        let target_ty = target.const_.ty();
        let source_ty = source.const_.ty();
        if target.const_.try_to_scalar() == source.const_.try_to_scalar()
            && self.tcx.erase_and_anonymize_regions(target_ty)
                == self.tcx.erase_and_anonymize_regions(source_ty)
        {
            return true;
        }

        match (target.const_, source.const_) {
            (mir::Const::Val(value_t, ty_t), mir::Const::Val(value_s, ty_s)) => {
                value_t == value_s
                    && self.tcx.erase_and_anonymize_regions(ty_t)
                        == self.tcx.erase_and_anonymize_regions(ty_s)
            },
            _ => false,
        }
    }

    /// Check whether two call function operands denote the same callable.
    pub(super) fn call_func_equiv(&self, target: &mir::Operand<'tcx>, source: &mir::Operand<'tcx>) -> bool {
        match (operand_fn_def_id(target), operand_fn_def_id(source)) {
            (Some(target_did), Some(source_did)) => target_did == source_did,
            _ => self.operand_equiv(target, source),
        }
    }

    /// Check whether the shared function, arguments, and destination of calls match.
    pub(super) fn call_core_equiv(
        &self,
        func_t: &mir::Operand<'tcx>,
        args_t: &[span::Spanned<mir::Operand<'tcx>>],
        dest_t: mir::Place<'tcx>,
        func_s: &mir::Operand<'tcx>,
        args_s: &[span::Spanned<mir::Operand<'tcx>>],
        dest_s: mir::Place<'tcx>,
    ) -> bool {
        self.call_func_equiv(func_t, func_s)
            && args_t.len() == args_s.len()
            && args_t
                .iter()
                .zip(args_s.iter())
                .all(|(arg_t, arg_s)| self.operand_equiv(&arg_t.node, &arg_s.node))
            && self.place_equiv(dest_t, dest_s)
    }

    /// Check whether two assertion messages have the same mapping-relevant shape.
    fn assert_msg_equiv(&self, target: &mir::AssertMessage<'tcx>, source: &mir::AssertMessage<'tcx>) -> bool {
        use mir::AssertKind;

        match (target, source) {
            (
                AssertKind::BoundsCheck {
                    len: len_t,
                    index: index_t,
                },
                AssertKind::BoundsCheck {
                    len: len_s,
                    index: index_s,
                },
            ) => self.operand_equiv(len_t, len_s) && self.operand_equiv(index_t, index_s),
            (AssertKind::Overflow(op_t, lhs_t, rhs_t), AssertKind::Overflow(op_s, lhs_s, rhs_s)) => {
                op_t == op_s && self.operand_equiv(lhs_t, lhs_s) && self.operand_equiv(rhs_t, rhs_s)
            },
            (AssertKind::OverflowNeg(op_t), AssertKind::OverflowNeg(op_s))
            | (AssertKind::DivisionByZero(op_t), AssertKind::DivisionByZero(op_s))
            | (AssertKind::RemainderByZero(op_t), AssertKind::RemainderByZero(op_s))
            | (AssertKind::InvalidEnumConstruction(op_t), AssertKind::InvalidEnumConstruction(op_s)) => {
                self.operand_equiv(op_t, op_s)
            },
            (
                AssertKind::MisalignedPointerDereference {
                    required: required_t,
                    found: found_t,
                },
                AssertKind::MisalignedPointerDereference {
                    required: required_s,
                    found: found_s,
                },
            ) => self.operand_equiv(required_t, required_s) && self.operand_equiv(found_t, found_s),
            (AssertKind::NullPointerDereference, AssertKind::NullPointerDereference) => true,
            (AssertKind::ResumedAfterReturn(kind_t), AssertKind::ResumedAfterReturn(kind_s))
            | (AssertKind::ResumedAfterPanic(kind_t), AssertKind::ResumedAfterPanic(kind_s))
            | (AssertKind::ResumedAfterDrop(kind_t), AssertKind::ResumedAfterDrop(kind_s)) => {
                kind_t == kind_s
            },
            _ => false,
        }
    }

    /// Check whether two rvalues have the same mapping-relevant shape.
    fn rvalue_equiv(&self, target: &mir::Rvalue<'tcx>, source: &mir::Rvalue<'tcx>) -> bool {
        match (target, source) {
            (mir::Rvalue::Use(operand_t, retag_t), mir::Rvalue::Use(operand_s, retag_s)) => {
                retag_t == retag_s && self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::Ref(_, borrow_kind_t, place_t), mir::Rvalue::Ref(_, borrow_kind_s, place_s)) => {
                borrow_kind_t == borrow_kind_s && self.place_equiv(*place_t, *place_s)
            },
            (mir::Rvalue::RawPtr(mutability_t, place_t), mir::Rvalue::RawPtr(mutability_s, place_s)) => {
                mutability_t == mutability_s && self.place_equiv(*place_t, *place_s)
            },
            (
                mir::Rvalue::Reborrow(_, mutability_t, place_t),
                mir::Rvalue::Reborrow(_, mutability_s, place_s),
            ) => mutability_t == mutability_s && self.place_equiv(*place_t, *place_s),
            (mir::Rvalue::BinaryOp(op_t, operands_t), mir::Rvalue::BinaryOp(op_s, operands_s)) => {
                op_t == op_s
                    && self.operand_equiv(&operands_t.as_ref().0, &operands_s.as_ref().0)
                    && self.operand_equiv(&operands_t.as_ref().1, &operands_s.as_ref().1)
            },
            (mir::Rvalue::UnaryOp(op_t, operand_t), mir::Rvalue::UnaryOp(op_s, operand_s)) => {
                op_t == op_s && self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::Discriminant(place_t), mir::Rvalue::Discriminant(place_s))
            | (mir::Rvalue::CopyForDeref(place_t), mir::Rvalue::CopyForDeref(place_s)) => {
                self.place_equiv(*place_t, *place_s)
            },
            (mir::Rvalue::Aggregate(kind_t, operands_t), mir::Rvalue::Aggregate(kind_s, operands_s)) => {
                aggregate_kind_equiv(kind_t.as_ref(), kind_s.as_ref())
                    && operands_t.len() == operands_s.len()
                    && operands_t
                        .iter()
                        .zip(operands_s.iter())
                        .all(|(operand_t, operand_s)| self.operand_equiv(operand_t, operand_s))
            },
            (mir::Rvalue::Cast(kind_t, operand_t, _), mir::Rvalue::Cast(kind_s, operand_s, _)) => {
                cast_kind_equiv(*kind_t, *kind_s) && self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::Repeat(operand_t, len_t), mir::Rvalue::Repeat(operand_s, len_s)) => {
                len_t == len_s && self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::WrapUnsafeBinder(operand_t, _), mir::Rvalue::WrapUnsafeBinder(operand_s, _)) => {
                self.operand_equiv(operand_t, operand_s)
            },
            (mir::Rvalue::ThreadLocalRef(def_id_t), mir::Rvalue::ThreadLocalRef(def_id_s)) => {
                def_id_t == def_id_s
            },
            _ => false,
        }
    }

    /// Check whether a target place corresponds to a source place after normalization.
    pub(super) fn place_equiv(&self, target: mir::Place<'tcx>, source: mir::Place<'tcx>) -> bool {
        self.normalize_place_for_flavor(target, MirFlavor::Target)
            == self.normalize_place_for_flavor(source, MirFlavor::Source)
    }

    /// Normalize a place using source- or target-specific alias rules.
    pub(super) fn normalize_place_for_flavor(
        &self,
        place: mir::Place<'tcx>,
        flavor: MirFlavor,
    ) -> NormalizedPlace {
        match flavor {
            MirFlavor::Source => Self::normalize_source_place(place),
            MirFlavor::Target => self.normalize_place(place),
        }
    }

    /// Normalize a borrowck/source place without target alias rewriting.
    pub(super) fn normalize_source_place(place: mir::Place<'tcx>) -> NormalizedPlace {
        NormalizedPlace {
            local: place.local,
            projection: place.projection.iter().map(normalize_projection_elem).collect(),
        }
    }

    /// Normalize a target place, expanding copy aliases and box-deref aliases.
    pub(super) fn normalize_place(&self, place: mir::Place<'tcx>) -> NormalizedPlace {
        if let Some(alias) = self.box_deref_aliases.get(&place.local)
            && matches!(place.projection.first(), Some(mir::ProjectionElem::Deref))
        {
            let mut projection = alias.place.projection.clone();
            projection.push(NormalizedPlaceElem::Deref);
            projection.extend(place.projection[1..].iter().map(|elem| normalize_projection_elem(*elem)));
            return NormalizedPlace {
                local: alias.place.local,
                projection,
            };
        }

        if let Some(alias) = self.copy_aliases.get(&place.local)
            && matches!(place.projection.first(), Some(mir::ProjectionElem::Deref))
        {
            let mut projection = alias.projection.clone();
            projection.extend(place.projection.iter().map(normalize_projection_elem));
            return NormalizedPlace {
                local: alias.local,
                projection,
            };
        }

        Self::normalize_source_place(place)
    }

    /// Check whether a local exists only in the target/dropck body.
    pub(super) const fn is_synthetic_local(&self, local: Local) -> bool {
        local.as_usize() >= self.source_local_count
    }

    /// Check whether a local is a synthetic boolean local introduced by drop elaboration.
    pub(super) fn is_synthetic_bool_local(&self, local: Local) -> bool {
        self.is_synthetic_local(local) && self.de.local_decls[local].ty.is_bool()
    }
}
