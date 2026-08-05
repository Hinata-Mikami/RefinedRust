// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides functionality for generating lifetime annotations for composite expressions.

use std::collections::HashSet;

use radium::code;
use rr_rustc_interface::middle::ty;

use crate::environment::borrowck::facts;
use crate::environment::region_folder::*;
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::types;

/// On creating a composite value (e.g. a struct or enum), the composite value gets its own
/// Polonius regions We need to map these regions properly to the respective lifetimes.
pub(crate) fn get_composite_rvalue_creation_annots<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    constraint_point: facts::PointIndex,
    effect_point: facts::PointIndex,
    rhs_ty: ty::Ty<'tcx>,
) -> Vec<code::Annotation> {
    let info = inclusion_tracker.info();
    let regions_of_ty = get_regions_of_ty(tcx, rhs_ty);

    let mut annots = Vec::new();

    for (s1, s2) in info.subset_base_at(constraint_point) {
        let lft1 = info.mk_atomic_region(s1);
        let lft2 = info.mk_atomic_region(s2);

        // a place lifetime is included in a value lifetime
        if lft2.is_value() && lft1.is_place() {
            // make sure it's not due to an assignment constraint
            if regions_of_ty.contains(&s2) && !info.has_subset_base_at(s2, s1, constraint_point) {
                // we enforce this inclusion by setting the lifetimes to be equal
                inclusion_tracker.add_static_inclusion(s1, s2, effect_point);
                inclusion_tracker.add_static_inclusion(s2, s1, effect_point);

                let annot = code::Annotation::CopyLftName(
                    ty_translator.format_atomic_region(lft1),
                    ty_translator.format_atomic_region(lft2),
                );
                annots.push(annot);
            }
        }
    }
    annots
}

/// Get the regions appearing in a type.
fn get_regions_of_ty<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> HashSet<facts::Region> {
    let mut regions = HashSet::new();
    let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
        ty::RegionKind::ReVar(rv) => {
            regions.insert(rv.into());
            r
        },
        _ => r,
    };
    let mut folder = RegionFolder::new(tcx, &mut clos);
    folder.fold_ty(ty);
    regions
}
