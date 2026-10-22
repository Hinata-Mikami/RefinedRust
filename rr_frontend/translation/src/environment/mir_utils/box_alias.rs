// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use rr_rustc_interface::data_structures::fx::FxHashMap;
use rr_rustc_interface::middle::{mir, ty};

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

/// Recognize the exact rustc lowering used to expose the pointer of a projected `Box`:
///
/// ```text
/// _box_tmp = no_retag copy BOX_PLACE
/// _raw_tmp = copy (_box_tmp.0) as *const T (BoxDerefTransmute)
/// ```
///
/// Both temporaries must be target-only, the assignments must be consecutive in one block,
/// `BOX_PLACE` must have the same `Box<T, A>` type and contain a preceding dereference, and
/// `_box_tmp` may have no other use. `_raw_tmp` remains executable and may be consumed normally,
/// but it may not be redefined. This deliberately narrow recognition prevents an unrelated rustc
/// administrative copy from being silently erased.
///
/// Only `_box_tmp` is removed from executable translation. Its sole `_box_tmp.0` use is
/// normalized to `BOX_PLACE.0`, allowing the existing transmute lowering to extract the raw
/// pointer explicitly. `_raw_tmp` remains a real pointer local.
pub(crate) fn collect_box_materialization_aliases<'tcx>(
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

            let mir::StatementKind::Assign(deref!((box_lhs, box_rhs))) = &box_copy.kind else {
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

            let mir::StatementKind::Assign(deref!((raw_lhs, raw_rhs))) = &raw_alias.kind else {
                continue;
            };
            let mir::Rvalue::Cast(
                mir::CastKind::BoxDerefTransmute,
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
                || raw_source.projection.len() != 1
                || !raw_source
                    .projection
                    .iter()
                    .all(|elem| matches!(elem, mir::ProjectionElem::Field(field, _) if field.as_usize() == 0))
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

/// Collect synthetic raw-pointer aliases introduced for lowered `Box` derefs.
///
/// rustc may lower a semantic `*box_place` into an administrative raw pointer local. The lang-item
/// `Box` uses `BoxDerefTransmute` from its `Unique` field, while the stdlib Box shim uses an ordinary
/// `Transmute` from the nested `NonNull` field:
///
/// ```text
/// _alias = copy (box_place.0) as *const T (BoxDerefTransmute)
/// _alias = copy ((box_place.0).0) as *const T (Transmute)
/// *_alias
/// ```
///
/// The returned map records `_alias -> box_place`. Drop-glue translation uses this for semantic
/// typing of later `*_alias` uses while code generation keeps the alias local explicit.
pub(crate) fn collect_box_deref_aliases<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> HashMap<mir::Local, mir::Place<'tcx>> {
    let mut aliases = HashMap::new();
    for block in body.basic_blocks.iter() {
        for stmt in &block.statements {
            let mir::StatementKind::Assign(deref!((lhs, rhs))) = &stmt.kind else {
                continue;
            };
            if !lhs.projection.is_empty() {
                continue;
            }
            let mir::Rvalue::Cast(kind, mir::Operand::Copy(rhs_place) | mir::Operand::Move(rhs_place), _) =
                rhs
            else {
                continue;
            };

            let Some(box_place) = box_deref_alias_source_place(tcx, body, *kind, *rhs_place) else {
                continue;
            };
            aliases.insert(lhs.local, box_place);
        }
    }
    aliases
}

/// Return the semantic Box place behind a raw-pointer Box deref alias initializer.
pub(crate) fn box_deref_alias_source_place<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    kind: mir::CastKind,
    rhs_place: mir::Place<'tcx>,
) -> Option<mir::Place<'tcx>> {
    let projections = rhs_place.projection.as_ref();
    let internal_field_count = match kind {
        mir::CastKind::BoxDerefTransmute => 1,
        mir::CastKind::Transmute => 2,
        _ => return None,
    };
    let box_projection_len = projections.len().checked_sub(internal_field_count)?;
    let internal_fields = &projections[box_projection_len..];

    // Locate the internal fields from the end so the Box itself may be an arbitrarily projected place.
    if !internal_fields
        .iter()
        .all(|elem| matches!(elem, mir::ProjectionElem::Field(field, _) if field.as_usize() == 0))
    {
        return None;
    }

    // Return only the semantic `Box` place, dropping the internal pointer extraction.
    let projection = tcx.mk_place_elems(&projections[..box_projection_len]);
    let box_place = mir::Place {
        local: rhs_place.local,
        projection,
    };
    box_place.ty(&body.local_decls, tcx).ty.is_box().then_some(box_place)
}

/// Normalize deref uses of an administrative alias local back to the aliased source place.
pub(crate) fn normalize_deref_alias_place<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    place: &mir::Place<'tcx>,
    source_for_alias: impl FnOnce(mir::Local) -> Option<mir::Place<'tcx>>,
) -> mir::Place<'tcx> {
    let Some(source_place) = source_for_alias(place.local) else {
        return *place;
    };
    if !matches!(place.projection.first(), Some(mir::ProjectionElem::Deref)) {
        return *place;
    }

    // Only dereference uses of the alias have `Box` semantics. Plain uses are still the
    // administrative raw-pointer value and should not be rewritten.
    let mut projection = Vec::with_capacity(source_place.projection.len() + place.projection.len());
    projection.extend_from_slice(source_place.projection.as_ref());
    projection.extend_from_slice(place.projection.as_ref());
    let projection = tcx.mk_place_elems(&projection);
    mir::Place {
        local: source_place.local,
        projection,
    }
}
