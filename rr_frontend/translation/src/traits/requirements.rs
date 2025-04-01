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

use crate::environment::Environment;
use crate::{search, shims};

/// Determine the origin of a trait obligation.
/// `surrounding_reqs` are the requirements of a surrounding impl or decl.
fn determine_origin_of_trait_requirement<'tcx>(
    did: DefId,
    tcx: ty::TyCtxt<'tcx>,
    surrounding_reqs: &Option<Vec<ty::TraitRef<'tcx>>>,
    req: ty::TraitRef<'tcx>,
) -> radium::TyParamOrigin {
    if let Some(surrounding_reqs) = surrounding_reqs {
        let in_trait_decl = tcx.trait_of_item(did);

        if surrounding_reqs.contains(&req) {
            if in_trait_decl.is_some() {
                return radium::TyParamOrigin::SurroundingTrait;
            }
            return radium::TyParamOrigin::SurroundingImpl;
        }
    }
    radium::TyParamOrigin::Direct
}

/// Meta information of a trait requirement.
#[derive(Debug)]
pub struct TraitReqMeta<'tcx> {
    pub trait_ref: ty::TraitRef<'tcx>,
    pub bound_regions: Vec<ty::BoundRegionKind>,
    pub binders: ty::Binder<'tcx, ()>,
    pub origin: radium::TyParamOrigin,
    pub is_used_in_self_trait: bool,
    pub is_self_in_trait_decl: bool,
}

/// Get the trait requirements of a [did], also determining their origin relative to the [did].
/// The requirements are sorted in a way that is stable across compilations.
pub fn get_trait_requirements_with_origin<'tcx>(
    env: &Environment<'tcx>,
    did: DefId,
) -> Vec<TraitReqMeta<'tcx>> {
    trace!("Enter get_trait_requirements_with_origin for did={did:?}");
    let param_env: ty::ParamEnv<'tcx> = env.tcx().param_env(did);

    // Are we declaring the scope of a trait?
    let is_trait = env.tcx().is_trait(did);

    // Determine whether we are declaring the scope of a trait method or trait impl method
    let in_trait_decl = env.tcx().trait_of_item(did);
    let in_trait_impl = env.trait_impl_of_method(did);

    // if this has a surrounding scope, get the requirements declared on that, so that we can
    // determine the origin of this requirement below
    let surrounding_reqs = if let Some(trait_did) = in_trait_decl {
        let trait_param_env = env.tcx().param_env(trait_did);
        Some(get_nontrivial(env.tcx(), trait_param_env, None).into_iter().map(|(x, _, _)| x).collect())
    } else if let Some(impl_did) = in_trait_impl {
        let impl_param_env = env.tcx().param_env(impl_did);
        Some(get_nontrivial(env.tcx(), impl_param_env, None).into_iter().map(|(x, _, _)| x).collect())
    } else {
        None
    };

    let clauses = param_env.caller_bounds();
    info!("Caller bounds: {:?}", clauses);

    let in_trait_decl = if is_trait { Some(did) } else { in_trait_decl };
    let requirements = get_nontrivial(env.tcx(), param_env, in_trait_decl);
    let mut annotated_requirements = Vec::new();

    for (trait_ref, bound_regions, binders) in requirements {
        // check if we are in the process of translating a trait decl
        let is_self = trait_ref.args[0].as_type().unwrap().is_param(0);
        let mut is_used_in_self_trait = false;
        if let Some(trait_decl_did) = in_trait_decl {
            // is this a reference to the trait we are currently declaring
            let is_use_of_self_trait = trait_decl_did == trait_ref.def_id;

            if is_use_of_self_trait && is_self {
                // This is the self assumption of the trait we are currently implementing
                // For a function spec in a trait decl, we remember this, as we do not require
                // a quantified spec for the Self trait.
                is_used_in_self_trait = true;
            }
        }

        // we are processing the Self requirement in the scope of a trait declaration, so skip this.
        let is_self_in_trait_decl = is_trait && is_used_in_self_trait && is_self;

        let origin = determine_origin_of_trait_requirement(did, env.tcx(), &surrounding_reqs, trait_ref);
        info!("Determined origin of requirement {trait_ref:?} as {origin:?}");

        let req = TraitReqMeta {
            trait_ref,
            bound_regions,
            binders,
            origin,
            is_used_in_self_trait,
            is_self_in_trait_decl,
        };
        annotated_requirements.push(req);
    }

    trace!(
        "Leave get_trait_requirements_with_origin for did={did:?} with annotated_requirements={annotated_requirements:?}"
    );
    annotated_requirements
}

/// Get non-trivial trait requirements of a `ParamEnv`,
/// ordered deterministically.
pub fn get_nontrivial<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    in_trait_decl: Option<DefId>,
) -> Vec<(ty::TraitRef<'tcx>, Vec<ty::BoundRegionKind>, ty::Binder<'tcx, ()>)> {
    let mut trait_refs = Vec::new();
    trace!(
        "Enter get_nontrivial_trait_requirements with param_env = {param_env:?}, in_trait_decl = {in_trait_decl:?}"
    );

    let clauses = param_env.caller_bounds();
    for cl in clauses {
        let cl_kind = cl.kind();

        let mut bound_regions = Vec::new();
        let bound_vars = cl_kind.bound_vars();
        for v in bound_vars {
            match v {
                ty::BoundVariableKind::Region(r) => {
                    bound_regions.push(r);
                },
                _ => {
                    unimplemented!("do not support higher-ranked bounds for non-lifetimes");
                },
            }
        }

        // keep the binders around
        let binders = cl_kind.rebind(());

        // TODO: maybe problematic
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
                trait_refs.push((trait_ref, bound_regions, binders));
            }
        }
    }

    // Make sure the order is stable across compilations
    trait_refs.sort_by(|(a, _, _), (b, _, _)| cmp_trait_ref(tcx, in_trait_decl, a, b));

    trace!("Leave get_nontrivial_trait_requirements with trait_refs = {trait_refs:?}");

    trait_refs
}

/// Check if this is a built-in trait
fn is_builtin_trait(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let sized_did = search::try_resolve_did(tcx, &["core", "marker", "Sized"])?;

    // TODO: for these, should instead require the primitive encoding of our Coq formalization
    let send_did = search::try_resolve_did(tcx, &["core", "marker", "Send"])?;
    let sync_did = search::try_resolve_did(tcx, &["core", "marker", "Sync"])?;
    let copy_did = search::try_resolve_did(tcx, &["core", "marker", "Copy"])?;

    // used for closures
    let tuple_did = search::try_resolve_did(tcx, &["core", "marker", "Tuple"])?;

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
