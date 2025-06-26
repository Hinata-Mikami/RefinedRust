// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir` types.
//! copied from prusti-interface/utils

use std::cmp::Ordering;

use rr_rustc_interface::data_structures::fx::FxHashSet;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

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
                    let field_place = tcx.mk_place_field(place, index.into(), field_def.ty(tcx, substs));
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
        | mir::ProjectionElem::Subtype(..)
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
        mir::ProjectionElem::Subtype(_) => 8,
    }
}

fn cmp_place_elem<'tcx>(tcx: ty::TyCtxt<'tcx>, a: mir::PlaceElem<'tcx>, b: mir::PlaceElem<'tcx>) -> Ordering {
    place_elem_variant(&a).cmp(&place_elem_variant(&b)).then_with(|| match (a, b) {
        (mir::ProjectionElem::Deref, mir::ProjectionElem::Deref) => Ordering::Equal,
        (mir::ProjectionElem::Field(idx1, ty1), mir::ProjectionElem::Field(idx2, ty2)) => {
            idx1.cmp(&idx2).then_with(|| cmp_ty(tcx, ty1, ty2))
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
        | (mir::ProjectionElem::UnwrapUnsafeBinder(ty1), mir::ProjectionElem::UnwrapUnsafeBinder(ty2))
        | (mir::ProjectionElem::Subtype(ty1), mir::ProjectionElem::Subtype(ty2)) => cmp_ty(tcx, ty1, ty2),
        (_, _) => {
            unreachable!();
        },
    })
}

fn region_discriminant(a: ty::Region<'_>) -> u8 {
    use ty::RegionKind;
    match a.kind() {
        RegionKind::ReEarlyParam(_) => 0,
        RegionKind::ReBound(_, _) => 1,
        RegionKind::ReLateParam(_) => 2,
        RegionKind::ReStatic => 3,
        RegionKind::ReVar(_) => 4,
        RegionKind::RePlaceholder(_) => 5,
        RegionKind::ReErased => 6,
        RegionKind::ReError(_) => 7,
    }
}

fn cmp_region<'tcx>(a: ty::Region<'tcx>, b: ty::Region<'tcx>) -> Ordering {
    region_discriminant(a).cmp(&region_discriminant(b)).then_with(|| {
        use ty::RegionKind;
        match (a.kind(), b.kind()) {
            (RegionKind::ReEarlyParam(a_r), RegionKind::ReEarlyParam(b_r)) => a_r.index.cmp(&b_r.index),
            (RegionKind::ReBound(a_d, a_r), RegionKind::ReBound(b_d, b_r)) => {
                a_d.cmp(&b_d).then(a_r.var.cmp(&b_r.var))
            },
            (RegionKind::ReLateParam(_a_r), RegionKind::ReLateParam(_b_r)) => {
                unimplemented!("compare ReLateParam");
            },
            (RegionKind::ReVar(a_r), RegionKind::ReVar(b_r)) => a_r.index().cmp(&b_r.index()),
            (RegionKind::RePlaceholder(_a_r), RegionKind::RePlaceholder(_b_r)) => {
                unimplemented!("compare RePlaceholder");
            },
            (RegionKind::ReStatic, RegionKind::ReStatic)
            | (RegionKind::ReErased, RegionKind::ReErased)
            | (RegionKind::ReError(_), RegionKind::ReError(_)) => Ordering::Equal,
            _ => {
                unreachable!();
            },
        }
    })
}

fn cmp_const<'tcx>(_tcx: ty::TyCtxt<'tcx>, _a: ty::Const<'tcx>, _b: ty::Const<'tcx>) -> Ordering {
    unimplemented!("compare Const");
}

fn ty_discriminant(ty: ty::Ty<'_>) -> usize {
    use ty::TyKind;
    match ty.kind() {
        TyKind::Bool => 0,
        TyKind::Char => 1,
        TyKind::Int(_) => 2,
        TyKind::Uint(_) => 3,
        TyKind::Float(_) => 4,
        TyKind::Adt(_, _) => 5,
        TyKind::Foreign(_) => 6,
        TyKind::Str => 7,
        TyKind::Array(_, _) => 8,
        TyKind::Slice(_) => 9,
        TyKind::RawPtr(_, _) => 10,
        TyKind::Ref(_, _, _) => 11,
        TyKind::FnDef(_, _) => 12,
        TyKind::FnPtr(..) => 13,
        TyKind::Dynamic(..) => 14,
        TyKind::Closure(_, _) => 15,
        TyKind::CoroutineClosure(_, _) => 16,
        TyKind::Coroutine(_, _) => 17,
        TyKind::CoroutineWitness(_, _) => 18,
        TyKind::Never => 19,
        TyKind::Tuple(_) => 20,
        TyKind::Pat(_, _) => 21,
        TyKind::Alias(_, _) => 22,
        TyKind::Param(_) => 23,
        TyKind::Bound(_, _) => 24,
        TyKind::Placeholder(_) => 25,
        TyKind::Infer(_) => 26,
        TyKind::Error(_) => 27,
        TyKind::UnsafeBinder(_) => 28,
    }
}

fn cmp_defid(tcx: ty::TyCtxt<'_>, a: DefId, b: DefId) -> Ordering {
    let a_hash = tcx.def_path_hash(a);
    let b_hash = tcx.def_path_hash(b);
    a_hash.cmp(&b_hash)
}

fn cmp_ty<'tcx>(tcx: ty::TyCtxt<'tcx>, a: ty::Ty<'tcx>, b: ty::Ty<'tcx>) -> Ordering {
    ty_discriminant(a).cmp(&ty_discriminant(b)).then_with(|| {
        use ty::TyKind;
        match (a.kind(), b.kind()) {
            (TyKind::Int(a_i), TyKind::Int(b_i)) => a_i.cmp(b_i),
            (TyKind::Uint(a_u), TyKind::Uint(b_u)) => a_u.cmp(b_u),
            (TyKind::Float(a_f), TyKind::Float(b_f)) => a_f.cmp(b_f),
            (TyKind::Adt(a_d, a_s), TyKind::Adt(b_d, b_s)) => {
                cmp_defid(tcx, a_d.did(), b_d.did()).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::Foreign(a_d), TyKind::Foreign(b_d)) => cmp_defid(tcx, *a_d, *b_d),
            (TyKind::Array(a_t, a_c), TyKind::Array(b_t, b_c)) => {
                cmp_ty(tcx, *a_t, *b_t).then_with(|| cmp_const(tcx, *a_c, *b_c))
            },
            (TyKind::Pat(..), TyKind::Pat(..)) => {
                unimplemented!("compare Pat");
            },
            (TyKind::Slice(a_t), TyKind::Slice(b_t)) => cmp_ty(tcx, *a_t, *b_t),
            (TyKind::RawPtr(a_t, a_m), TyKind::RawPtr(b_t, b_m)) => {
                cmp_ty(tcx, *a_t, *b_t).then_with(|| a_m.cmp(b_m))
            },
            (TyKind::Ref(a_r, a_t, a_m), TyKind::Ref(b_r, b_t, b_m)) => {
                cmp_region(*a_r, *b_r).then_with(|| cmp_ty(tcx, *a_t, *b_t).then_with(|| a_m.cmp(b_m)))
            },
            (TyKind::FnDef(a_d, a_s), TyKind::FnDef(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::FnPtr(..), TyKind::FnPtr(..)) => {
                unimplemented!("compare FnPtr");
            },
            (TyKind::Dynamic(..), TyKind::Dynamic(..)) => {
                unimplemented!("compare Dynamic");
            },
            (TyKind::Closure(a_d, a_s), TyKind::Closure(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::CoroutineClosure(a_d, a_s), TyKind::CoroutineClosure(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::Coroutine(a_d, a_s), TyKind::Coroutine(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::CoroutineWitness(a_d, a_s), TyKind::CoroutineWitness(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::Tuple(a_t), TyKind::Tuple(b_t)) => {
                a_t.iter().cmp_by(b_t.iter(), |a, b| cmp_ty(tcx, a, b))
            },
            (TyKind::Alias(a_i, a_p), TyKind::Alias(b_i, b_p)) => a_i.cmp(b_i).then_with(|| {
                cmp_defid(tcx, a_p.def_id, b_p.def_id).then_with(|| cmp_arg_refs(tcx, a_p.args, b_p.args))
            }),
            (TyKind::Param(a_p), TyKind::Param(b_p)) => a_p.cmp(b_p),
            (TyKind::Bound(..), TyKind::Bound(..)) => {
                unimplemented!("compare Bound");
            },
            (TyKind::Placeholder(_), TyKind::Placeholder(_)) => {
                unimplemented!("compare Placeholder");
            },
            (TyKind::Infer(_), TyKind::Infer(_)) => {
                unimplemented!("compare Infer");
            },
            (TyKind::Error(_), TyKind::Error(_)) => {
                unimplemented!("compare Error");
            },
            (TyKind::UnsafeBinder(_), TyKind::UnsafeBinder(_)) => {
                unimplemented!("compare UnsafeBinder");
            },
            (TyKind::Bool, TyKind::Bool)
            | (TyKind::Char, TyKind::Char)
            | (TyKind::Str, TyKind::Str)
            | (TyKind::Never, TyKind::Never) => Ordering::Equal,
            _ => {
                unreachable!();
            },
        }
    })
}

const fn generic_arg_kind_variant(a: &ty::GenericArgKind<'_>) -> u8 {
    match a {
        ty::GenericArgKind::Const(_) => 0,
        ty::GenericArgKind::Type(_) => 1,
        ty::GenericArgKind::Lifetime(_) => 2,
    }
}

/// Compare two `GenericArg` deterministically.
/// Should only be called on equal discriminants.
fn cmp_arg_ref<'tcx>(tcx: ty::TyCtxt<'tcx>, a: ty::GenericArg<'tcx>, b: ty::GenericArg<'tcx>) -> Ordering {
    generic_arg_kind_variant(&a.kind())
        .cmp(&generic_arg_kind_variant(&b.kind()))
        .then_with(|| match (a.kind(), b.kind()) {
            (ty::GenericArgKind::Const(c1), ty::GenericArgKind::Const(c2)) => cmp_const(tcx, c1, c2),
            (ty::GenericArgKind::Type(ty1), ty::GenericArgKind::Type(ty2)) => cmp_ty(tcx, ty1, ty2),
            (ty::GenericArgKind::Lifetime(r1), ty::GenericArgKind::Lifetime(r2)) => cmp_region(r1, r2),
            (_, _) => {
                unreachable!("Comparing GenericArg with different discriminant");
            },
        })
}

/// Compare two sequences of `GenericArg`s for the same `DefId`, where the discriminants are pairwise equal.
fn cmp_arg_refs<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    a: &[ty::GenericArg<'tcx>],
    b: &[ty::GenericArg<'tcx>],
) -> Ordering {
    match a.len().cmp(&b.len()) {
        Ordering::Equal => {
            // compare elements
            for (x, y) in a.iter().zip(b.iter()) {
                // the discriminants are the same as the DefId we are calling into is the same
                let xy_cmp = cmp_arg_ref(tcx, *x, *y);
                if xy_cmp != Ordering::Equal {
                    return xy_cmp;
                }
            }
            Ordering::Equal
        },
        o => o,
    }
}
