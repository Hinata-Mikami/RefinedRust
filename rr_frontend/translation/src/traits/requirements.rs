// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Get trait requirements of objects.

use log::{info, trace};
use radium::specs;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty::{self, TypeFoldable as _, TypeSuperFoldable as _};
use rr_rustc_interface::type_ir::{ClausePolarity, Upcast as _};

use crate::base::TranslationError;
use crate::error::Message;
use crate::{environment, rustcmp, search, traits};

type TraitRequirement<'tcx> =
    (ty::TraitRef<'tcx>, Vec<ty::BoundRegionKind<'tcx>>, ty::Binder<'tcx, ()>, specs::TyParamOrigin, bool);

pub(crate) type ProjectionEquality<'tcx> = (DefId, ty::GenericArgsRef<'tcx>, ty::Ty<'tcx>);

struct CollectedRequirements<'tcx> {
    requirements: Vec<TraitRequirement<'tcx>>,
    clauses: Vec<ty::Clause<'tcx>>,
}

/// Meta information of a trait requirement.
#[derive(Debug)]
pub(crate) struct TraitReqMeta<'tcx> {
    pub trait_ref: ty::TraitRef<'tcx>,
    pub bound_regions: Vec<ty::BoundRegionKind<'tcx>>,
    pub binders: ty::Binder<'tcx, ()>,
    pub origin: specs::TyParamOrigin,
    pub is_used_in_self_trait: bool,
    pub is_self_in_trait_decl: bool,
    pub is_assoc_bound: bool,
    // for the ordered associated types, an optional constraint
    pub assoc_constraints: Vec<Option<ty::Ty<'tcx>>>,
}

/// Get the trait requirements of a [did], also determining their origin relative to the [did].
/// The requirements are sorted in a way that is stable across compilations.
pub(crate) fn get_trait_requirements_with_origin<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    did: DefId,
) -> Result<Vec<TraitReqMeta<'tcx>>, TranslationError> {
    trace!("Enter get_trait_requirements_with_origin for did={did:?}");
    let typing_env: ty::TypingEnv<'tcx> = ty::TypingEnv::post_analysis(tcx, did);

    // Are we declaring the scope of a trait?
    let is_trait = tcx.is_trait(did);

    // Determine whether we are declaring the scope of a trait method or trait impl method
    let in_trait_decl = tcx.trait_of_assoc(did);

    let clauses = typing_env.param_env.caller_bounds().collect::<Vec<_>>();
    info!("Caller bounds: {:?}", clauses);

    let in_trait_decl = if is_trait { Some(did) } else { in_trait_decl };
    let collected = get_nontrivial(tcx, did, typing_env.param_env, in_trait_decl)?;
    let mut annotated_requirements = Vec::new();

    for (trait_ref, bound_regions, binders, origin, is_assoc_bound) in collected.requirements {
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

        info!("Determined origin of requirement {trait_ref:?} as {origin:?}");

        let assoc_constraints =
            traits::get_trait_assoc_constraints(tcx, collected.clauses.iter().copied(), trait_ref);

        let req = TraitReqMeta {
            trait_ref,
            bound_regions,
            binders,
            origin,
            is_used_in_self_trait,
            is_self_in_trait_decl,
            is_assoc_bound,
            assoc_constraints,
        };
        annotated_requirements.push(req);
    }

    trace!(
        "Leave get_trait_requirements_with_origin for did={did:?} with annotated_requirements={annotated_requirements:?}"
    );
    Ok(annotated_requirements)
}

/// Determine the origin of a clause.
fn determine_origin_of_clause<'tcx>(
    did: DefId,
    tcx: ty::TyCtxt<'tcx>,
    surrounding_reqs: Option<&Vec<ty::Clause<'tcx>>>,
    req: ty::Clause<'tcx>,
) -> specs::TyParamOrigin {
    if let Some(surrounding_reqs) = surrounding_reqs {
        let in_trait_decl = tcx.trait_of_assoc(did);

        if surrounding_reqs.contains(&req) {
            if in_trait_decl.is_some() {
                return specs::TyParamOrigin::SurroundingTrait;
            }
            return specs::TyParamOrigin::SurroundingImpl;
        }
    }
    specs::TyParamOrigin::Direct
}

/// Get clauses for a `DefId` together with their origin.
pub(crate) fn get_clauses_with_origin<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    for_did: DefId,
    param_env: ty::ParamEnv<'tcx>,
) -> Vec<(ty::Clause<'tcx>, specs::TyParamOrigin)> {
    let clauses = param_env.caller_bounds();

    // Determine whether we are declaring the scope of a trait method or trait impl method
    let in_trait_decl = tcx.trait_of_assoc(for_did);
    let in_trait_impl = environment::trait_impl_of_method(tcx, for_did);

    // if this has a surrounding scope, get the requirements declared on that, so that we can
    // determine the origin of this requirement below
    let surrounding_reqs = if let Some(trait_did) = in_trait_decl {
        let trait_param_env = tcx.param_env(trait_did);
        Some(trait_param_env.caller_bounds().collect())
    } else if let Some(impl_did) = in_trait_impl {
        let impl_param_env = tcx.param_env(impl_did);
        Some(impl_param_env.caller_bounds().collect())
    } else {
        None
    };

    let mut clauses_with_origin = Vec::new();
    for cl in clauses {
        let origin = determine_origin_of_clause(for_did, tcx, surrounding_reqs.as_ref(), cl);
        clauses_with_origin.push((cl, origin));
    }

    trace!("determined clauses with origin for {for_did:?} as {clauses_with_origin:?}");

    clauses_with_origin
}

/// Get non-trivial trait requirements of a `ParamEnv`,
/// ordered deterministically.
fn get_nontrivial<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    for_did: DefId,
    param_env: ty::ParamEnv<'tcx>,
    in_trait_decl: Option<DefId>,
) -> Result<CollectedRequirements<'tcx>, TranslationError> {
    let clauses_with_origin = get_clauses_with_origin(tcx, for_did, param_env);
    let mut clauses: Vec<_> = clauses_with_origin.iter().map(|(clause, _)| *clause).collect();
    let mut trait_refs = Vec::new();
    let mut canonical_trait_refs = Vec::new();
    let mut parents = Vec::new();
    trace!(
        "Enter get_nontrivial_trait_requirements with for_did={for_did:?}, param_env = {param_env:?}, in_trait_decl = {in_trait_decl:?}"
    );

    for (cl, origin) in clauses_with_origin {
        if let Some(requirement) = trait_requirement_from_clause(tcx, cl, origin, false) {
            let canonical_trait_ref =
                normalize_trait_ref_with_projection_equalities(tcx, requirement.0, &clauses);
            push_requirement_if_new(
                &mut trait_refs,
                &mut canonical_trait_refs,
                &mut parents,
                requirement,
                canonical_trait_ref,
                None,
            );
        }
    }

    let mut current = 0;
    while current < trait_refs.len() {
        let (trait_ref, _, binders, origin, is_assoc_bound) = trait_refs[current].clone();
        let trait_clauses = instantiated_trait_clauses(tcx, trait_ref, binders, is_assoc_bound);
        clauses.extend(trait_clauses.iter().map(|(clause, _)| *clause));
        for requirement in &mut canonical_trait_refs {
            requirement.0 = normalize_trait_ref_with_projection_equalities(tcx, requirement.0, &clauses);
        }

        for (clause, clause_is_assoc_bound) in trait_clauses {
            let Some(requirement) =
                trait_requirement_from_clause(tcx, clause, origin, is_assoc_bound || clause_is_assoc_bound)
            else {
                continue;
            };
            let canonical_trait_ref =
                normalize_trait_ref_with_projection_equalities(tcx, requirement.0, &clauses);
            if contains_requirement(&canonical_trait_refs, canonical_trait_ref, requirement.2) {
                continue;
            }
            let mut ancestor = Some(current);
            let mut matching_ancestors = 0;
            while let Some(idx) = ancestor {
                if canonical_trait_refs[idx].0.def_id == canonical_trait_ref.def_id {
                    matching_ancestors += 1;
                }
                ancestor = parents[idx];
            }
            // Permit one repeated trait constructor so projection equalities can close finite
            // fixed points such as `Try`/`Residual`. A third occurrence on the active path means
            // unfolding is still growing and cannot produce a finite encoding.
            if matching_ancestors >= 2 {
                return Err(TranslationError::ErrorReported(tcx.dcx().span_err(
                    tcx.def_span(for_did),
                    Message::UnsupportedFeature(
                        "cyclic associated type trait requirements do not have a finite unfolding".to_owned(),
                    ),
                )));
            }
            push_requirement_if_new(
                &mut trait_refs,
                &mut canonical_trait_refs,
                &mut parents,
                requirement,
                canonical_trait_ref,
                Some(current),
            );
        }
        current += 1;
    }

    let defn_order = order_requirements(tcx, in_trait_decl, &trait_refs);

    trace!("Leave get_nontrivial_trait_requirements with for_did={for_did:?}, trait_refs = {defn_order:?}");

    Ok(CollectedRequirements {
        requirements: defn_order,
        clauses,
    })
}

fn instantiated_trait_clauses<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    binders: ty::Binder<'tcx, ()>,
    include_supertraits: bool,
) -> Vec<(ty::Clause<'tcx>, bool)> {
    let mut clauses = Vec::new();
    if include_supertraits {
        clauses.extend(
            ty::elaborate::supertraits(tcx, binders.rebind(trait_ref))
                .skip(1)
                .map(|supertrait| (supertrait.upcast(tcx), false)),
        );
    }

    for assoc_did in environment::get_trait_assoc_types(tcx, trait_ref.def_id) {
        for &(bound, _) in tcx.explicit_item_bounds(assoc_did).skip_binder() {
            // `instantiate_supertrait` composes the outer requirement binder with binders
            // introduced by the associated bound and shifts their indices accordingly.
            let bound = bound.instantiate_supertrait(tcx, binders.rebind(trait_ref));
            clauses.push((bound, true));
        }
    }
    clauses
}

struct ProjectionEqualityFolder<'a, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    equalities: &'a [ProjectionEquality<'tcx>],
    active: Vec<ty::AliasTy<'tcx>>,
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for ProjectionEqualityFolder<'_, 'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        let ty = t.super_fold_with(self);
        let ty::TyKind::Alias(_, alias) = ty.kind() else {
            return ty;
        };
        let ty::AliasTyKind::Projection { def_id } = alias.kind else {
            return ty;
        };
        if self.active.contains(alias) {
            return ty;
        }

        self.active.push(*alias);
        let replacement = (0..self.equalities.len()).find_map(|idx| {
            let (projection_did, args, replacement) = self.equalities[idx];
            let args = args.fold_with(self);
            (projection_did == def_id && args == alias.args).then_some(replacement)
        });

        let Some(replacement) = replacement else {
            self.active.pop();
            return ty;
        };
        let replacement = replacement.fold_with(self);
        self.active.pop();
        replacement
    }
}

fn normalize_trait_ref_with_projection_equalities<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    clauses: &[ty::Clause<'tcx>],
) -> ty::TraitRef<'tcx> {
    let equalities = clauses
        .iter()
        .filter_map(|clause| {
            let clause_kind = clause.kind();
            if !clause_kind.bound_vars().is_empty() {
                return None;
            }
            let ty::ClauseKind::Projection(projection) = clause_kind.skip_binder() else {
                return None;
            };
            Some((projection.def_id(), projection.projection_term.args, projection.term.as_type()?))
        })
        .collect::<Vec<_>>();
    normalize_trait_ref(tcx, trait_ref, &equalities)
}

pub(crate) fn normalize_trait_ref<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    equalities: &[ProjectionEquality<'tcx>],
) -> ty::TraitRef<'tcx> {
    trait_ref.fold_with(&mut ProjectionEqualityFolder {
        tcx,
        equalities,
        active: Vec::new(),
    })
}

fn trait_requirement_from_clause<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    cl: ty::Clause<'tcx>,
    origin: specs::TyParamOrigin,
    is_assoc_bound: bool,
) -> Option<TraitRequirement<'tcx>> {
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
        if trait_pred.polarity == ClausePolarity::Positive {
            let trait_ref = trait_pred.trait_ref;

            // filter Sized, Copy, Send, Sync?
            if Some(true) == is_builtin_trait(tcx, trait_ref.def_id) {
                return None;
            }

            return Some((trait_ref, bound_regions, binders, origin, is_assoc_bound));
        }
    }
    None
}

fn contains_requirement<'tcx>(
    requirements: &[TraitRequirement<'tcx>],
    trait_ref: ty::TraitRef<'tcx>,
    binders: ty::Binder<'tcx, ()>,
) -> bool {
    requirements.iter().any(|(existing_trait_ref, _, existing_binders, _, _)| {
        existing_trait_ref == &trait_ref && *existing_binders == binders
    })
}

fn push_requirement_if_new<'tcx>(
    requirements: &mut Vec<TraitRequirement<'tcx>>,
    canonical_requirements: &mut Vec<TraitRequirement<'tcx>>,
    parents: &mut Vec<Option<usize>>,
    requirement: TraitRequirement<'tcx>,
    canonical_trait_ref: ty::TraitRef<'tcx>,
    parent: Option<usize>,
) {
    if !contains_requirement(canonical_requirements, canonical_trait_ref, requirement.2) {
        let mut canonical_requirement = requirement.clone();
        canonical_requirement.0 = canonical_trait_ref;
        requirements.push(requirement);
        canonical_requirements.push(canonical_requirement);
        parents.push(parent);
    }
}

fn order_requirements<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    in_trait_decl: Option<DefId>,
    requirements: &[TraitRequirement<'tcx>],
) -> Vec<TraitRequirement<'tcx>> {
    fn is_current_trait_self_requirement(
        in_trait_decl: Option<DefId>,
        requirement: &TraitRequirement<'_>,
    ) -> bool {
        in_trait_decl.is_some_and(|trait_did| {
            requirement.0.def_id == trait_did && requirement.0.args[0].expect_ty().is_param(0)
        })
    }

    fn visit<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        in_trait_decl: Option<DefId>,
        requirements: &[TraitRequirement<'tcx>],
        idx: usize,
        visiting: &mut [bool],
        visited: &mut [bool],
        ordered: &mut Vec<TraitRequirement<'tcx>>,
    ) {
        if visited[idx] {
            return;
        }
        // Canonically finite requirement cycles are supported by pre-registering all trait-use
        // cells before they are filled. Growing cycles are rejected during collection above.
        if visiting[idx] {
            return;
        }
        visiting[idx] = true;

        let deps = trait_get_deps(tcx, requirements[idx].0.def_id);
        let mut dep_indices: Vec<_> = requirements
            .iter()
            .enumerate()
            .filter_map(|(dep_idx, requirement)| {
                (deps.contains(&requirement.0.def_id)
                    && !is_current_trait_self_requirement(in_trait_decl, requirement))
                .then_some(dep_idx)
            })
            .collect();
        dep_indices.sort_by(|a, b| {
            rustcmp::cmp_trait_ref(tcx, in_trait_decl, &requirements[*a].0, &requirements[*b].0)
        });
        for dep_idx in dep_indices {
            visit(tcx, in_trait_decl, requirements, dep_idx, visiting, visited, ordered);
        }

        visiting[idx] = false;
        visited[idx] = true;
        ordered.push(requirements[idx].clone());
    }

    let mut indices: Vec<_> = (0..requirements.len()).collect();
    indices
        .sort_by(|a, b| rustcmp::cmp_trait_ref(tcx, in_trait_decl, &requirements[*a].0, &requirements[*b].0));
    let (indices, self_indices): (Vec<_>, Vec<_>) = indices
        .into_iter()
        .partition(|idx| !is_current_trait_self_requirement(in_trait_decl, &requirements[*idx]));
    let mut visiting = vec![false; requirements.len()];
    let mut visited = vec![false; requirements.len()];
    let mut ordered = Vec::new();
    for idx in indices.into_iter().chain(self_indices) {
        visit(tcx, in_trait_decl, requirements, idx, &mut visiting, &mut visited, &mut ordered);
    }
    ordered
}

fn trait_get_deps(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Vec<DefId> {
    let param_env = tcx.param_env(trait_did);
    let clauses = param_env.caller_bounds();

    let mut deps = Vec::new();
    for cl in clauses {
        let cl_kind = cl.kind();
        let cl_kind = cl_kind.skip_binder();

        // only look for trait predicates for now
        if let ty::ClauseKind::Trait(trait_pred) = cl_kind {
            // We ignore negative polarities for now
            if trait_pred.polarity == ClausePolarity::Positive {
                let trait_ref = trait_pred.trait_ref;
                if trait_ref.def_id != trait_did {
                    deps.push(trait_ref.def_id);
                }
            }
        }
    }

    for assoc_did in environment::get_trait_assoc_types(tcx, trait_did) {
        for &(clause, _) in tcx.explicit_item_bounds(assoc_did).skip_binder() {
            let ty::ClauseKind::Trait(trait_pred) = clause.kind().skip_binder() else {
                continue;
            };
            if trait_pred.polarity == ClausePolarity::Positive && trait_pred.trait_ref.def_id != trait_did {
                deps.push(trait_pred.trait_ref.def_id);
            }
        }
    }

    deps
}

/// Check if this is a built-in trait
fn is_builtin_trait(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let sized_did = search::try_resolve_did(tcx, &["core", "marker", "Sized"])?;
    let meta_sized_did = search::try_resolve_did(tcx, &["core", "marker", "MetaSized"])?;
    //let pointee_sized_did = search::try_resolve_did(tcx, &["core", "marker", "PointeeSized"])?;

    // used for closures
    let tuple_did = search::try_resolve_did(tcx, &["core", "marker", "Tuple"])?;

    // Used for const. I suppose for us const is irrelevant, and this feature is extremely
    // underdocumented, so just ignore it.
    let destruct_did = search::try_resolve_did(tcx, &["core", "marker", "Destruct"])?;

    // For us all Metadata is () right now.
    let pointee_did = search::try_resolve_did(tcx, &["core", "ptr", "Pointee"])?;

    // Everything is Thin.
    let thin_did = search::try_resolve_did(tcx, &["core", "ptr", "metadata", "Thin"])?;

    Some(
        trait_did == sized_did
            || trait_did == tuple_did
            || trait_did == meta_sized_did
            || trait_did == destruct_did
            || trait_did == pointee_did
            || trait_did == thin_did,
    )
}
