// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir` types.
//! copied from prusti-interface/utils.

use std::cmp::Ordering;

use rr_rustc_interface::data_structures::fx::FxHashSet;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_utils::stable_comparator;

/// Expands a place `x.f.g` of type struct into a vector of places for
/// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
/// `without_field` is not `None`, then omits that field from the final
/// vector.
fn expand_struct_place<'tcx>(
    place: mir::Place<'tcx>,
    mir: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    without_field: Option<usize>,
) -> Vec<mir::Place<'tcx>> {
    let mut places: Vec<mir::Place<'tcx>> = Vec::new();
    let typ = place.ty(mir, tcx);
    if !matches!(typ.ty.kind(), ty::Adt(..)) {
        assert!(
            typ.variant_index.is_none(),
            "We have assumed that only enums can have variant_index set. Got {typ:?}."
        );
    }
    match typ.ty.kind() {
        ty::Adt(def, substs) => {
            let variant = typ.variant_index.map_or_else(|| def.non_enum_variant(), |i| def.variant(i));
            for (index, field_def) in variant.fields.iter().enumerate() {
                if Some(index) != without_field {
                    let field_place =
                        tcx.mk_place_field(place, index.into(), field_def.ty(tcx, substs).skip_norm_wip());
                    places.push(field_place);
                }
            }
        },
        ty::Tuple(slice) => {
            for (index, arg) in slice.iter().enumerate() {
                if Some(index) != without_field {
                    let field_place = tcx.mk_place_field(place, index.into(), arg);
                    places.push(field_place);
                }
            }
        },
        ty::Closure(_, substs) => {
            for (index, subst_ty) in substs.as_closure().upvar_tys().iter().enumerate() {
                if Some(index) != without_field {
                    let field_place = tcx.mk_place_field(place, index.into(), subst_ty);
                    places.push(field_place);
                }
            }
        },
        ty::Coroutine(_, substs) => {
            for (index, subst_ty) in substs.as_coroutine().upvar_tys().iter().enumerate() {
                if Some(index) != without_field {
                    let field_place = tcx.mk_place_field(place, index.into(), subst_ty);
                    places.push(field_place);
                }
            }
        },
        ty => unreachable!("ty={:?}", ty),
    }
    places
}

/// Check if the place `potential_prefix` is a prefix of `place`. For example:
///
/// + `is_prefix(x.f, x.f) == true`
/// + `is_prefix(x.f.g, x.f) == true`
/// + `is_prefix(x.f, x.f.g) == false`
pub(crate) fn is_prefix<'tcx>(place: mir::Place<'tcx>, potential_prefix: mir::Place<'tcx>) -> bool {
    if place.local != potential_prefix.local || place.projection.len() < potential_prefix.projection.len() {
        false
    } else {
        place.projection.iter().zip(potential_prefix.projection.iter()).all(|(e1, e2)| e1 == e2)
    }
}

/// Subtract the `subtrahend` place from the `minuend` place. The
/// subtraction is defined as set minus between `minuend` place replaced
/// with a set of places that are unrolled up to the same level as
/// `subtrahend` and the singleton `subtrahend` set. For example,
/// `subtract(x.f, x.f.g.h)` is performed by unrolling `x.f` into
/// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
/// subtracting `{x.f.g.h}` from it, which results into `{x.g, x.h,
/// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`.
pub(crate) fn expand<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    mut minuend: mir::Place<'tcx>,
    subtrahend: mir::Place<'tcx>,
) -> Vec<mir::Place<'tcx>> {
    assert!(is_prefix(subtrahend, minuend), "The minuend must be the prefix of the subtrahend.");
    let mut place_set = Vec::new();
    while minuend.projection.len() < subtrahend.projection.len() {
        let (new_minuend, places) = expand_one_level(mir, tcx, minuend, subtrahend);
        minuend = new_minuend;
        place_set.extend(places);
    }
    place_set
}

/// Expand `current_place` one level down by following the `guide_place`.
/// Returns the new `current_place` and a vector containing other places that
/// could have resulted from the expansion.
fn expand_one_level<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    current_place: mir::Place<'tcx>,
    guide_place: mir::Place<'tcx>,
) -> (mir::Place<'tcx>, Vec<mir::Place<'tcx>>) {
    let index = current_place.projection.len();
    let new_projection =
        tcx.mk_place_elems_from_iter(current_place.projection.iter().chain([guide_place.projection[index]]));
    let new_current_place = mir::Place {
        local: current_place.local,
        projection: new_projection,
    };
    let other_places = match guide_place.projection[index] {
        mir::ProjectionElem::Field(projected_field, _field_ty) => {
            expand_struct_place(current_place, mir, tcx, Some(projected_field.index()))
        },
        mir::ProjectionElem::Deref
        | mir::ProjectionElem::Index(..)
        | mir::ProjectionElem::ConstantIndex { .. }
        | mir::ProjectionElem::Subslice { .. }
        | mir::ProjectionElem::Downcast(..)
        | mir::ProjectionElem::UnwrapUnsafeBinder(..)
        | mir::ProjectionElem::OpaqueCast(..) => vec![],
    };
    (new_current_place, other_places)
}

/// Try to collapse all places in `places` by following the
/// `guide_place`. This function is basically the reverse of
/// `expand_struct_place`.
pub(crate) fn collapse<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    places: &mut FxHashSet<mir::Place<'tcx>>,
    guide_place: mir::Place<'tcx>,
) {
    fn recurse<'tcx>(
        mir: &mir::Body<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
        places: &mut FxHashSet<mir::Place<'tcx>>,
        current_place: mir::Place<'tcx>,
        guide_place: mir::Place<'tcx>,
    ) {
        if current_place != guide_place {
            let (new_current_place, mut expansion) = expand_one_level(mir, tcx, current_place, guide_place);
            recurse(mir, tcx, places, new_current_place, guide_place);
            expansion.push(new_current_place);
            if expansion.iter().all(|place| places.contains(place)) {
                for place in expansion {
                    places.remove(&place);
                }
                places.insert(current_place);
            }
        }
    }
    recurse(mir, tcx, places, guide_place.local.into(), guide_place);
}

/// Comparison of places, using the `tcx`.
pub(crate) fn cmp_place<'tcx>(tcx: ty::TyCtxt<'tcx>, a: &mir::Place<'tcx>, b: &mir::Place<'tcx>) -> Ordering {
    a.local
        .cmp(&b.local)
        .then(a.projection.iter().cmp_by(b.projection, |a, b| cmp_place_elem(tcx, a, b)))
}

const fn place_elem_variant(a: &mir::PlaceElem<'_>) -> u8 {
    match a {
        mir::ProjectionElem::Deref => 0,
        mir::ProjectionElem::Field(..) => 1,
        mir::ProjectionElem::Index(_) => 2,
        mir::ProjectionElem::ConstantIndex { .. } => 3,
        mir::ProjectionElem::Subslice { .. } => 4,
        mir::ProjectionElem::Downcast(..) => 5,
        mir::ProjectionElem::OpaqueCast(_) => 6,
        mir::ProjectionElem::UnwrapUnsafeBinder(_) => 7,
    }
}

fn cmp_place_elem<'tcx>(tcx: ty::TyCtxt<'tcx>, a: mir::PlaceElem<'tcx>, b: mir::PlaceElem<'tcx>) -> Ordering {
    place_elem_variant(&a).cmp(&place_elem_variant(&b)).then_with(|| match (a, b) {
        (mir::ProjectionElem::Deref, mir::ProjectionElem::Deref) => Ordering::Equal,
        (mir::ProjectionElem::Field(idx1, ty1), mir::ProjectionElem::Field(idx2, ty2)) => {
            idx1.cmp(&idx2).then_with(|| stable_comparator(tcx).cmp_ty(ty1, ty2))
        },
        (mir::ProjectionElem::Index(idx1), mir::ProjectionElem::Index(idx2)) => idx1.cmp(&idx2),
        (
            mir::ProjectionElem::ConstantIndex {
                offset: off1,
                min_length: min1,
                from_end: end1,
            },
            mir::ProjectionElem::ConstantIndex {
                offset: off2,
                min_length: min2,
                from_end: end2,
            },
        ) => off1.cmp(&off2).then_with(|| min1.cmp(&min2).then_with(|| end1.cmp(&end2))),
        (
            mir::ProjectionElem::Subslice {
                from: from1,
                to: to1,
                from_end: from_end1,
            },
            mir::ProjectionElem::Subslice {
                from: from2,
                to: to2,
                from_end: from_end2,
            },
        ) => from1.cmp(&from2).then_with(|| to1.cmp(&to2).then_with(|| from_end1.cmp(&from_end2))),
        (mir::ProjectionElem::Downcast(_, idx1), mir::ProjectionElem::Downcast(_, idx2)) => idx1.cmp(&idx2),
        (mir::ProjectionElem::OpaqueCast(ty1), mir::ProjectionElem::OpaqueCast(ty2))
        | (mir::ProjectionElem::UnwrapUnsafeBinder(ty1), mir::ProjectionElem::UnwrapUnsafeBinder(ty2)) => {
            stable_comparator(tcx).cmp_ty(ty1, ty2)
        },
        (_, _) => {
            unreachable!();
        },
    })
}
