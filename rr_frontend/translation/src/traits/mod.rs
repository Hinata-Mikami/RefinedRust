// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cmp::Ordering;
use std::collections::HashMap;

use derive_more::Display;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::environment::Environment;
use crate::shims;

pub(crate) mod registry;
pub(crate) mod requirements;
pub(crate) mod resolution;

#[derive(Debug, Clone, Display)]
pub(crate) enum Error<'tcx> {
    /// This `DefId` is not a trait
    #[display("The given `DefId` {:?} is not a trait", _0)]
    NotATrait(DefId),

    /// This `DefId` is not an impl of a trait
    #[display("The given `DefId` {:?} is not a trait implementation", _0)]
    NotATraitImpl(DefId),

    /// This closure does not implement the closure trait
    #[display("Did not find trait impl of {:?} for closure {:?}", _1, _0)]
    NotAClosureTraitImpl(DefId, ty::ClosureKind),

    /// This `DefId` does not represent a closure trait, when it was expected to.
    #[display("This DefId does not represent a closure trait {:?}", _0)]
    NotAClosureTrait(DefId),

    /// The trait for this closure kind could not be found
    #[display("Could not find the trait for closure kind {:?}", _0)]
    CouldNotFindClosureTrait(ty::ClosureKind),

    /// This `DefId` is not a trait method
    #[display("The given `DefId` {:?} is not a trait method", _0)]
    NotATraitMethod(DefId),

    /// This `DefId` is not an assoc type
    #[display("The given `DefId` {:?} is not an associated type", _0)]
    NotAnAssocType(DefId),

    /// We encountered an associated constant
    #[display("Associated constants are not supported")]
    AssocConstNotSupported,

    /// This trait already exists
    #[display("This trait {:?} already has been registered", _0)]
    TraitAlreadyExists(DefId),

    /// This trait impl already exists
    #[display("This trait impl {:?} already has been registered", _0)]
    ImplAlreadyExists(DefId),

    /// This closure trait impl already exists
    #[display("This closure ({:?}, {:?}) already has been registered", _0, _1)]
    ClosureImplAlreadyExists(DefId, ty::ClosureKind),

    /// Trait hasn't been registered yet but is used
    #[display("This trait {:?} has not been registered yet", _0)]
    UnregisteredTrait(DefId),

    /// Trait impl hasn't been registered yet but is used
    #[display("This trait impl {:?} has not been registered yet", _0)]
    UnregisteredImpl(DefId),

    /// Cannot find this trait instance in the local environment
    #[display("An instance for this trait {:?} cannot by found with generic args {:?}", _0, _1)]
    UnknownLocalInstance(DefId, ty::GenericArgsRef<'tcx>),

    #[display("An error occurred when parsing the specification of the trait {:?}: {:?}", _0, _1)]
    TraitSpec(DefId, String),

    #[display("An error occurred when parsing the specification of the trait impl {:?}: {:?}", _0, _1)]
    TraitImplSpec(DefId, String),
}

pub(crate) type TraitResult<'tcx, T> = Result<T, Error<'tcx>>;

/// Given a particular reference to a trait, get the associated type constraints for this trait reference.
pub(crate) fn get_trait_assoc_constraints<'tcx>(
    env: &Environment<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
) -> Vec<Option<ty::Ty<'tcx>>> {
    let mut assoc_ty_map = HashMap::new();

    // TODO: check if caller_bounds does the right thing for implied bounds
    let clauses = typing_env.param_env.caller_bounds();
    for cl in clauses {
        let cl_kind = cl.kind();
        let cl_kind = cl_kind.skip_binder();

        // only look for trait predicates for now
        if let ty::ClauseKind::Projection(proj) = cl_kind
            && trait_ref.def_id == proj.trait_def_id(env.tcx())
            && trait_ref.args == proj.projection_term.args
        {
            // same trait and same args
            let idx = env.get_trait_associated_type_index(proj.def_id()).unwrap();
            let ty = proj.term.as_type().unwrap();
            assoc_ty_map.insert(idx, ty);
        }
    }

    let assoc_tys = env.get_trait_assoc_types(trait_ref.def_id);
    assoc_tys
        .into_iter()
        .enumerate()
        .map(|(idx, _)| assoc_ty_map.get(&idx).copied())
        .collect()
}

/// Sort associated items of a trait in a stable way.
pub(crate) fn sort_assoc_items<'tcx>(
    env: &Environment<'tcx>,
    items: &'tcx ty::AssocItems,
) -> Vec<&'tcx ty::AssocItem> {
    let mut items: Vec<_> = items.in_definition_order().collect();
    items.sort_by(|a, b| cmp_defid(env, a.def_id, b.def_id));

    items
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
    // NOTE: The relative order of shims to each other may not be the same as the relative order of the
    // actual objects to each other. Therefore, use the export order.
    let a_did = shims::flat::get_external_did_for_did(env, a).unwrap_or(a);
    let b_did = shims::flat::get_external_did_for_did(env, b).unwrap_or(b);

    //let a_path = env.tcx().def_path(a_did);
    let a_str = env.tcx().def_path_str(a_did);
    let b_str = env.tcx().def_path_str(b_did);

    a_str.cmp(&b_str)

    //let a_hash = env.tcx().def_path_hash(a_did);
    //let b_hash = env.tcx().def_path_hash(b_did);
    //a_hash.cmp(&b_hash)
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
    // if one of them is the self trait, that should be greater (at the end, after its
    // dependencies).
    if let Some(trait_did) = in_trait_decl {
        if a.def_id == trait_did && a.args[0].expect_ty().is_param(0) {
            return Ordering::Greater;
        }
        if b.def_id == trait_did && b.args[0].expect_ty().is_param(0) {
            return Ordering::Less;
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
