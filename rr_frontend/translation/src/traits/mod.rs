// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::{environment, rustcmp, search};

pub(crate) mod registry;
pub(crate) mod requirements;
pub(crate) mod resolution;

pub(crate) fn raise_unknown_local_instance<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    trait_did: DefId,
    args: ty::GenericArgsRef<'tcx>,
) -> ! {
    tcx.dcx().span_bug(
        tcx.def_span(trait_did),
        format!("could not find local instance for trait with generic args {args:?}"),
    )
}

pub(crate) fn raise_not_a_trait(tcx: ty::TyCtxt<'_>, did: DefId) -> ! {
    tcx.dcx().span_bug(tcx.def_span(did), "expected trait, found non-trait item")
}

pub(crate) fn raise_not_a_trait_impl(tcx: ty::TyCtxt<'_>, did: DefId) -> ! {
    tcx.dcx().span_bug(tcx.def_span(did), "expected trait impl, found non-trait impl item")
}

pub(crate) fn raise_not_a_closure_trait(tcx: ty::TyCtxt<'_>, did: DefId) -> ! {
    tcx.dcx()
        .span_bug(tcx.def_span(did), "expected closure trait, found non-closure trait item")
}

pub(crate) fn raise_could_not_find_closure_trait(tcx: ty::TyCtxt<'_>, kind: ty::ClosureKind) -> ! {
    tcx.dcx().bug(format!("could not resolve lang-item closure trait for kind {kind:?}"))
}

pub(crate) fn raise_not_a_trait_method(tcx: ty::TyCtxt<'_>, did: DefId) -> ! {
    tcx.dcx()
        .span_bug(tcx.def_span(did), "expected trait method, found non-trait method item")
}

pub(crate) fn raise_not_an_assoc_type(tcx: ty::TyCtxt<'_>, did: DefId) -> ! {
    tcx.dcx()
        .span_bug(tcx.def_span(did), "expected associated type, found different associated item")
}

pub(crate) fn raise_assoc_const_not_supported(tcx: ty::TyCtxt<'_>) -> ! {
    tcx.dcx()
        .bug("associated constants in trait translation should have been rejected earlier")
}

pub(crate) fn raise_trait_already_exists(tcx: ty::TyCtxt<'_>, did: DefId) -> ! {
    tcx.dcx().span_bug(tcx.def_span(did), "trait shim already registered")
}

pub(crate) fn raise_impl_already_exists(tcx: ty::TyCtxt<'_>, did: DefId) -> ! {
    tcx.dcx().span_bug(tcx.def_span(did), "trait impl shim already registered")
}

pub(crate) fn raise_closure_impl_already_exists(
    tcx: ty::TyCtxt<'_>,
    closure_did: DefId,
    closure_kind: ty::ClosureKind,
) -> ! {
    tcx.dcx().span_bug(
        tcx.def_span(closure_did),
        format!("closure impl already registered for {closure_did:?} with kind {closure_kind:?}"),
    )
}

/// Given a particular reference to a trait, get the associated type constraints for this trait reference.
pub(crate) fn get_trait_assoc_constraints<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
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
            && trait_ref.def_id == proj.trait_def_id(tcx)
            && trait_ref.args == proj.projection_term.args
        {
            // same trait and same args
            let idx = environment::get_trait_associated_type_index(tcx, proj.def_id()).unwrap();
            let ty = proj.term.as_type().unwrap();
            assoc_ty_map.insert(idx, ty);
        }
    }

    let assoc_tys = environment::get_trait_assoc_types(tcx, trait_ref.def_id);
    assoc_tys
        .into_iter()
        .enumerate()
        .map(|(idx, _)| assoc_ty_map.get(&idx).copied())
        .collect()
}

/// Sort associated items of a trait in a stable way.
pub(crate) fn sort_assoc_items<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    items: &'tcx ty::AssocItems,
) -> Vec<&'tcx ty::AssocItem> {
    let mut items: Vec<_> = items.in_definition_order().collect();
    items.sort_by(|a, b| rustcmp::cmp_defid(tcx, a.def_id, b.def_id));

    items
}

/// Check if this is a derive trait that does not need spec annotations to implement.
pub(crate) fn is_derive_trait_with_no_annotations(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let copy_did = search::try_resolve_did(tcx, &["core", "marker", "Copy"])?;
    let clone_did = search::try_resolve_did(tcx, &["core", "clone", "Clone"])?;
    let debug_did = search::try_resolve_did(tcx, &["core", "fmt", "Debug"])?;

    Some(trait_did == copy_did || trait_did == clone_did || trait_did == debug_did)
}

/// Check if this is a derive trait that needs spec annotations to implement.
pub(crate) fn is_derive_trait_with_annotations(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let eq_did = search::try_resolve_did(tcx, &["core", "cmp", "Eq"])?;
    let partial_eq_did = search::try_resolve_did(tcx, &["core", "cmp", "PartialEq"])?;
    let ord_did = search::try_resolve_did(tcx, &["core", "cmp", "Ord"])?;
    let partial_ord_did = search::try_resolve_did(tcx, &["core", "cmp", "PartialOrd"])?;

    Some(
        trait_did == eq_did
            || trait_did == partial_eq_did
            || trait_did == ord_did
            || trait_did == partial_ord_did,
    )
}
