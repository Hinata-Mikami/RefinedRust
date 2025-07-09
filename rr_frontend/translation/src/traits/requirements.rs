// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Get trait requirements of objects.

use log::{info, trace};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::environment::Environment;
use crate::{search, traits};

/// Determine the origin of a trait obligation.
/// `surrounding_reqs` are the requirements of a surrounding impl or decl.
#[expect(clippy::ref_option)]
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
pub(crate) struct TraitReqMeta<'tcx> {
    pub trait_ref: ty::TraitRef<'tcx>,
    pub bound_regions: Vec<ty::BoundRegionKind>,
    pub binders: ty::Binder<'tcx, ()>,
    pub origin: radium::TyParamOrigin,
    pub is_used_in_self_trait: bool,
    pub is_self_in_trait_decl: bool,
    // for the ordered associated types, an optional constraint
    pub assoc_constraints: Vec<Option<ty::Ty<'tcx>>>,
}

/// Get the trait requirements of a [did], also determining their origin relative to the [did].
/// The requirements are sorted in a way that is stable across compilations.
pub(crate) fn get_trait_requirements_with_origin<'tcx>(
    env: &Environment<'tcx>,
    did: DefId,
) -> Vec<TraitReqMeta<'tcx>> {
    trace!("Enter get_trait_requirements_with_origin for did={did:?}");
    let typing_env: ty::TypingEnv<'tcx> = ty::TypingEnv::post_analysis(env.tcx(), did);

    // Are we declaring the scope of a trait?
    let is_trait = env.tcx().is_trait(did);

    // Determine whether we are declaring the scope of a trait method or trait impl method
    let in_trait_decl = env.tcx().trait_of_item(did);
    let in_trait_impl = env.trait_impl_of_method(did);

    // if this has a surrounding scope, get the requirements declared on that, so that we can
    // determine the origin of this requirement below
    let surrounding_reqs = if let Some(trait_did) = in_trait_decl {
        let trait_param_env = env.tcx().param_env(trait_did);
        Some(
            get_nontrivial(env, trait_did, trait_param_env, None)
                .into_iter()
                .map(|(x, _, _)| x)
                .collect(),
        )
    } else if let Some(impl_did) = in_trait_impl {
        let impl_param_env = env.tcx().param_env(impl_did);
        Some(
            get_nontrivial(env, impl_did, impl_param_env, None)
                .into_iter()
                .map(|(x, _, _)| x)
                .collect(),
        )
    } else {
        None
    };

    let clauses = typing_env.param_env.caller_bounds();
    info!("Caller bounds: {:?}", clauses);

    let in_trait_decl = if is_trait { Some(did) } else { in_trait_decl };
    let requirements = get_nontrivial(env, did, typing_env.param_env, in_trait_decl);
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

        let assoc_constraints = traits::get_trait_assoc_constraints(env, typing_env, trait_ref);

        let req = TraitReqMeta {
            trait_ref,
            bound_regions,
            binders,
            origin,
            is_used_in_self_trait,
            is_self_in_trait_decl,
            assoc_constraints,
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
pub(crate) fn get_nontrivial<'tcx>(
    env: &Environment<'tcx>,
    for_did: DefId,
    param_env: ty::ParamEnv<'tcx>,
    in_trait_decl: Option<DefId>,
) -> Vec<(ty::TraitRef<'tcx>, Vec<ty::BoundRegionKind>, ty::Binder<'tcx, ()>)> {
    let mut trait_refs = Vec::new();
    trace!(
        "Enter get_nontrivial_trait_requirements with for_did={for_did:?}, param_env = {param_env:?}, in_trait_decl = {in_trait_decl:?}"
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
            if trait_pred.polarity == ty::PredicatePolarity::Positive {
                let trait_ref = trait_pred.trait_ref;

                // filter Sized, Copy, Send, Sync?
                if Some(true) == is_builtin_trait(env.tcx(), trait_ref.def_id) {
                    continue;
                }

                // this is a nontrivial requirement
                trait_refs.push((trait_ref, bound_regions, binders));
            }
        }
    }

    // Make sure the order is stable across compilations
    trait_refs.sort_by(|(a, _, _), (b, _, _)| traits::cmp_trait_ref(env, in_trait_decl, a, b));

    trace!("Leave get_nontrivial_trait_requirements with for_did={for_did:?}, trait_refs = {trait_refs:?}");

    trait_refs
}

/// Check if this is a built-in trait
fn is_builtin_trait(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let sized_did = search::try_resolve_did(tcx, &["core", "marker", "Sized"])?;

    // used for closures
    let tuple_did = search::try_resolve_did(tcx, &["core", "marker", "Tuple"])?;

    Some(trait_did == sized_did || trait_did == tuple_did)
}
