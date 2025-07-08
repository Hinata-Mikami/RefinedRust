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
}

/// Get the trait requirements of a [did], also determining their origin relative to the [did].
/// The requirements are sorted in a way that is stable across compilations.
pub(crate) fn get_trait_requirements_with_origin<'tcx>(
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

    let clauses = param_env.caller_bounds();
    info!("Caller bounds: {:?}", clauses);

    let in_trait_decl = if is_trait { Some(did) } else { in_trait_decl };
    let requirements = get_nontrivial(env, did, param_env, in_trait_decl);
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
    trait_refs.sort_by(|(a, _, _), (b, _, _)| cmp_trait_ref(env, in_trait_decl, a, b));

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

fn cmp_const<'tcx>(_env: &Environment<'tcx>, _a: ty::Const<'tcx>, _b: ty::Const<'tcx>) -> Ordering {
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

fn cmp_defid(env: &Environment<'_>, a: DefId, b: DefId) -> Ordering {
    // NOTE: This definition is problematic if we are defining shims.
    // The relative order of shims to each other may not be the same as the relative order of the
    // actual objects to each other.

    let a_did = shims::flat::get_external_did_for_did(env, a).unwrap_or(a);
    let b_did = shims::flat::get_external_did_for_did(env, b).unwrap_or(b);

    let a_hash = env.tcx().def_path_hash(a_did);
    let b_hash = env.tcx().def_path_hash(b_did);
    a_hash.cmp(&b_hash)
}

fn cmp_ty<'tcx>(env: &Environment<'tcx>, a: ty::Ty<'tcx>, b: ty::Ty<'tcx>) -> Ordering {
    ty_discriminant(a).cmp(&ty_discriminant(b)).then_with(|| {
        use ty::TyKind;
        match (a.kind(), b.kind()) {
            (TyKind::Int(a_i), TyKind::Int(b_i)) => a_i.cmp(b_i),
            (TyKind::Uint(a_u), TyKind::Uint(b_u)) => a_u.cmp(b_u),
            (TyKind::Float(a_f), TyKind::Float(b_f)) => a_f.cmp(b_f),
            (TyKind::Adt(a_d, a_s), TyKind::Adt(b_d, b_s)) => {
                cmp_defid(env, a_d.did(), b_d.did()).then_with(|| cmp_arg_refs(env, a_s, b_s))
            },
            (TyKind::Foreign(a_d), TyKind::Foreign(b_d)) => cmp_defid(env, *a_d, *b_d),
            (TyKind::Array(a_t, a_c), TyKind::Array(b_t, b_c)) => {
                cmp_ty(env, *a_t, *b_t).then_with(|| cmp_const(env, *a_c, *b_c))
            },
            (TyKind::Pat(..), TyKind::Pat(..)) => {
                unimplemented!("compare Pat");
            },
            (TyKind::Slice(a_t), TyKind::Slice(b_t)) => cmp_ty(env, *a_t, *b_t),
            (TyKind::RawPtr(a_t, a_m), TyKind::RawPtr(b_t, b_m)) => {
                cmp_ty(env, *a_t, *b_t).then_with(|| a_m.cmp(b_m))
            },
            (TyKind::Ref(a_r, a_t, a_m), TyKind::Ref(b_r, b_t, b_m)) => {
                cmp_region(*a_r, *b_r).then_with(|| cmp_ty(env, *a_t, *b_t).then_with(|| a_m.cmp(b_m)))
            },
            (TyKind::FnDef(a_d, a_s), TyKind::FnDef(b_d, b_s)) => {
                cmp_defid(env, *a_d, *b_d).then_with(|| cmp_arg_refs(env, a_s, b_s))
            },
            (TyKind::FnPtr(..), TyKind::FnPtr(..)) => {
                unimplemented!("compare FnPtr");
            },
            (TyKind::Dynamic(..), TyKind::Dynamic(..)) => {
                unimplemented!("compare Dynamic");
            },
            (TyKind::Closure(a_d, a_s), TyKind::Closure(b_d, b_s)) => {
                cmp_defid(env, *a_d, *b_d).then_with(|| cmp_arg_refs(env, a_s, b_s))
            },
            (TyKind::CoroutineClosure(a_d, a_s), TyKind::CoroutineClosure(b_d, b_s)) => {
                cmp_defid(env, *a_d, *b_d).then_with(|| cmp_arg_refs(env, a_s, b_s))
            },
            (TyKind::Coroutine(a_d, a_s), TyKind::Coroutine(b_d, b_s)) => {
                cmp_defid(env, *a_d, *b_d).then_with(|| cmp_arg_refs(env, a_s, b_s))
            },
            (TyKind::CoroutineWitness(a_d, a_s), TyKind::CoroutineWitness(b_d, b_s)) => {
                cmp_defid(env, *a_d, *b_d).then_with(|| cmp_arg_refs(env, a_s, b_s))
            },
            (TyKind::Tuple(a_t), TyKind::Tuple(b_t)) => {
                a_t.iter().cmp_by(b_t.iter(), |a, b| cmp_ty(env, a, b))
            },
            (TyKind::Alias(a_i, a_p), TyKind::Alias(b_i, b_p)) => a_i.cmp(b_i).then_with(|| {
                cmp_defid(env, a_p.def_id, b_p.def_id).then_with(|| cmp_arg_refs(env, a_p.args, b_p.args))
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

/// Compare two `GenericArg` deterministically.
/// Should only be called on equal discriminants.
fn cmp_arg_ref<'tcx>(env: &Environment<'tcx>, a: ty::GenericArg<'tcx>, b: ty::GenericArg<'tcx>) -> Ordering {
    match (a.kind(), b.kind()) {
        (ty::GenericArgKind::Const(c1), ty::GenericArgKind::Const(c2)) => cmp_const(env, c1, c2),
        (ty::GenericArgKind::Type(ty1), ty::GenericArgKind::Type(ty2)) => {
            // we should make sure that this always orders the Self instance first.
            match (ty1.kind(), ty2.kind()) {
                (ty::TyKind::Param(p1), ty::TyKind::Param(p2)) => p1.cmp(p2),
                (ty::TyKind::Param(_), _) => Ordering::Less,
                (_, _) => cmp_ty(env, ty1, ty2),
            }
        },
        (ty::GenericArgKind::Lifetime(r1), ty::GenericArgKind::Lifetime(r2)) => cmp_region(r1, r2),
        (_, _) => {
            unreachable!("Comparing GenericArg with different discriminant");
        },
    }
}

/// Compare two sequences of `GenericArg`s for the same `DefId`, where the discriminants are pairwise equal.
fn cmp_arg_refs<'tcx>(
    env: &Environment<'tcx>,
    a: &[ty::GenericArg<'tcx>],
    b: &[ty::GenericArg<'tcx>],
) -> Ordering {
    match a.len().cmp(&b.len()) {
        Ordering::Equal => {
            // compare elements
            for (x, y) in a.iter().zip(b.iter()) {
                // the discriminants are the same as the DefId we are calling into is the same
                let xy_cmp = cmp_arg_ref(env, *x, *y);
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
    env: &Environment<'tcx>,
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

    //let path_a = shims::flat::get_cleaned_def_path(tcx, a.def_id);
    //let path_b = shims::flat::get_cleaned_def_path(tcx, b.def_id);
    //let path_cmp = path_a.cmp(&path_b);
    //info!("cmp_trait_ref: comparing paths {path_a:?} and {path_b:?}");

    let path_cmp = cmp_defid(env, a.def_id, b.def_id);

    path_cmp.then_with(|| {
        let args_a = a.args.as_slice();
        let args_b = b.args.as_slice();
        cmp_arg_refs(env, args_a, args_b)
    })
}
