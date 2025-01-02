// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Get trait requirements of objects.

use std::cmp::Ordering;

use log::{info, trace};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::{shims, utils};

/// Get non-trivial trait requirements of a `ParamEnv`,
/// ordered deterministically.
pub fn get_nontrivial<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    in_trait_decl: Option<DefId>,
) -> Vec<ty::TraitRef<'tcx>> {
    let mut trait_refs = Vec::new();
    trace!(
        "Enter get_nontrivial_trait_requirements with param_env = {param_env:?}, in_trait_decl = {in_trait_decl:?}"
    );

    let clauses = param_env.caller_bounds();
    for cl in clauses {
        let cl_kind = cl.kind();
        let cl_kind = cl_kind.skip_binder();

        // only look for trait predicates for now
        if let ty::ClauseKind::Trait(trait_pred) = cl_kind {
            // We ignore negative polarities for now
            if trait_pred.polarity == ty::ImplPolarity::Positive {
                let trait_ref = trait_pred.trait_ref;

                // filter Sized, Copy, Send, Sync?
                if Some(true) == is_builtin_trait(tcx, trait_ref.def_id) {
                    continue;
                }

                // this is a nontrivial requirement
                trait_refs.push(trait_ref);
            }
        }
    }

    // Make sure the order is stable across compilations
    trait_refs.sort_by(|a, b| cmp_trait_ref(tcx, in_trait_decl, a, b));

    trace!("Leave get_nontrivial_trait_requirements with trait_refs = {trait_refs:?}");

    trait_refs
}

/// Check if this is a built-in trait
fn is_builtin_trait(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let sized_did = utils::try_resolve_did(tcx, &["core", "marker", "Sized"])?;

    // TODO: for these, should instead require the primitive encoding of our Coq formalization
    let send_did = utils::try_resolve_did(tcx, &["core", "marker", "Send"])?;
    let sync_did = utils::try_resolve_did(tcx, &["core", "marker", "Sync"])?;
    let copy_did = utils::try_resolve_did(tcx, &["core", "marker", "Copy"])?;

    // used for closures
    let tuple_did = utils::try_resolve_did(tcx, &["core", "marker", "Tuple"])?;

    Some(
        trait_did == sized_did
            || trait_did == copy_did
            || trait_did == tuple_did
            || trait_did == send_did
            || trait_did == sync_did,
    )
}

/// Compare two `GenericArg` deterministically.
/// Should only be called on equal discriminants.
fn cmp_arg_ref<'tcx>(tcx: ty::TyCtxt<'tcx>, a: ty::GenericArg<'tcx>, b: ty::GenericArg<'tcx>) -> Ordering {
    match (a.unpack(), b.unpack()) {
        (ty::GenericArgKind::Const(c1), ty::GenericArgKind::Const(c2)) => c1.cmp(&c2),
        (ty::GenericArgKind::Type(ty1), ty::GenericArgKind::Type(ty2)) => {
            // we should make sure that this always orders the Self instance first.
            match (ty1.kind(), ty2.kind()) {
                (ty::TyKind::Param(p1), ty::TyKind::Param(p2)) => p1.cmp(p2),
                (ty::TyKind::Param(p1), _) => Ordering::Less,
                (_, _) => ty1.cmp(&ty2),
            }
        },
        (ty::GenericArgKind::Lifetime(r1), ty::GenericArgKind::Lifetime(r2)) => r1.cmp(&r2),
        (_, _) => {
            unreachable!("Comparing GenericArg with different discriminant");
        },
    }
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

/// Compare two `TraitRef`s deterministically, giving a
/// consistent order that is stable across compilations.
fn cmp_trait_ref<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    in_trait_decl: Option<DefId>,
    a: &ty::TraitRef<'tcx>,
    b: &ty::TraitRef<'tcx>,
) -> Ordering {
    // if one of them is the self trait, that should be smaller.
    if let Some(trait_did) = in_trait_decl {
        if a.def_id == trait_did && a.args[0].expect_ty().is_param(0) {
            return Ordering::Less;
        }
        if b.def_id == trait_did && b.args[0].expect_ty().is_param(0) {
            return Ordering::Greater;
        }
    }

    let path_a = shims::flat::get_cleaned_def_path(tcx, a.def_id);
    let path_b = shims::flat::get_cleaned_def_path(tcx, b.def_id);
    let path_cmp = path_a.cmp(&path_b);
    info!("cmp_trait_ref: comparing paths {path_a:?} and {path_b:?}");

    if path_cmp == Ordering::Equal {
        let args_a = a.args.as_slice();
        let args_b = b.args.as_slice();
        cmp_arg_refs(tcx, args_a, args_b)
    } else {
        path_cmp
    }
}
