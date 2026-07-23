// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use rr_rustc_interface::middle::{mir, ty};

/// Collect synthetic raw-pointer aliases introduced for lowered `Box` derefs.
///
/// rustc may lower a semantic `*box_place` into an administrative raw pointer local:
///
/// ```text
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
            let mir::StatementKind::Assign(box (lhs, rhs)) = &stmt.kind else {
                continue;
            };
            if !lhs.projection.is_empty() {
                continue;
            }
            let mir::Rvalue::Cast(
                mir::CastKind::Transmute,
                mir::Operand::Copy(rhs_place) | mir::Operand::Move(rhs_place),
                _,
            ) = rhs
            else {
                continue;
            };

            let Some(box_place) = box_deref_alias_source_place(tcx, body, *rhs_place) else {
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
    rhs_place: mir::Place<'tcx>,
) -> Option<mir::Place<'tcx>> {
    let projections = rhs_place.projection.as_ref();
    let box_projection_len = projections.len().checked_sub(2)?;
    let internal_fields = &projections[box_projection_len..];

    // rustc's raw-pointer alias initializer extracts the stored pointer as two field-0 projections from the
    // semantic `Box`. Locate those fields from the end so the Box itself may be an arbitrarily projected
    // place.
    if !internal_fields
        .iter()
        .all(|elem| matches!(elem, mir::ProjectionElem::Field(field, _) if field.as_usize() == 0))
    {
        return None;
    }

    // Return only the semantic `Box` place, dropping the internal `.0.0` pointer extraction.
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
