// These functions have been adapted from Miri (https://github.com/rust-lang/miri/blob/31fb32e49f42df19b45baccb6aa80c3d726ed6d5/src/helpers.rs#L48) under the MIT license.

//! Utility functions for finding Rust source objects.

use std::collections::HashMap;
use std::mem;

use log::info;
use rr_rustc_interface::middle::{metadata, ty};
use rr_rustc_interface::{hir, span};

use crate::{types, unification};

/// Gets an instance for a path.
/// Taken from Miri <https://github.com/rust-lang/miri/blob/31fb32e49f42df19b45baccb6aa80c3d726ed6d5/src/helpers.rs#L48>.
pub fn try_resolve_did_direct<T>(tcx: ty::TyCtxt<'_>, path: &[T]) -> Option<hir::def_id::DefId>
where
    T: AsRef<str>,
{
    tcx.crates(())
        .iter()
        .find(|&&krate| tcx.crate_name(krate).as_str() == path[0].as_ref())
        .and_then(|krate| {
            let krate = hir::def_id::DefId {
                krate: *krate,
                index: hir::def_id::CRATE_DEF_INDEX,
            };

            let mut items: &[metadata::ModChild] = tcx.module_children(krate);
            let mut path_it = path.iter().skip(1).peekable();

            while let Some(segment) = path_it.next() {
                for item in mem::take(&mut items) {
                    let item: &metadata::ModChild = item;
                    if item.ident.name.as_str() == segment.as_ref() {
                        if path_it.peek().is_none() {
                            return Some(item.res.def_id());
                        }

                        items = tcx.module_children(item.res.def_id());
                        break;
                    }
                }
            }
            None
        })
}

pub fn try_resolve_did<T>(tcx: ty::TyCtxt<'_>, path: &[T]) -> Option<hir::def_id::DefId>
where
    T: AsRef<str>,
{
    if let Some(did) = try_resolve_did_direct(tcx, path) {
        return Some(did);
    }

    // if the first component is "std", try if we can replace it with "alloc" or "core"
    if path[0].as_ref() == "std" {
        let mut components: Vec<_> = path.iter().map(|x| x.as_ref().to_owned()).collect();
        components[0] = "core".to_owned();
        if let Some(did) = try_resolve_did_direct(tcx, &components) {
            return Some(did);
        }
        // try "alloc"
        components[0] = "alloc".to_owned();
        try_resolve_did_direct(tcx, &components)
    } else {
        None
    }
}

/// Try to resolve the `DefId` of an implementation of a trait for a particular type.
/// Note that this does not, in general, find a unique solution, in case there are complex things
/// with different where clauses going on.
pub fn try_resolve_trait_impl_did<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    trait_did: hir::def_id::DefId,
    trait_args: &[Option<ty::GenericArg<'tcx>>],
    for_type: ty::Ty<'tcx>,
) -> Option<hir::def_id::DefId> {
    // get all impls of this trait
    let impls: &ty::trait_def::TraitImpls = tcx.trait_impls_of(trait_did);

    if let ty::TyKind::Param(_) = for_type.kind() {
        // this is a blanket impl
        let defs = impls.blanket_impls();
        info!("found blanket implementations: {:?}", defs);

        let mut solution = None;
        for did in defs {
            let impl_ref: Option<ty::EarlyBinder<ty::TraitRef<'_>>> = tcx.impl_trait_ref(did);
            // now we need to get the constraints and see if we can unify them
            // TODO: come up with algorithm for that
            // - I guess we need to unify the type variables here.
            // - I'm assuming all type variables are open (this should be true -- all variables need to be
            //   universally quantified)
            // - I can just compute a mapping of indices to TyParam
            // - and check that it remains consistent.
            // Then I have an output mapping, and can check if the where clauses are satisfied for
            // that mapping
            if let Some(impl_ref) = impl_ref {
                let impl_ref = types::normalize_in_function(*did, tcx, impl_ref.skip_binder()).unwrap();

                let this_impl_args = impl_ref.args;
                // filter by the generic instantiation for the trait
                info!("found impl with args {:?}", this_impl_args);
                // args has self at position 0 and generics of the trait at position 1..

                // check if the generic argument types match up
                let mut unification_map = HashMap::new();
                if !unification::args_unify_types(
                    &this_impl_args.as_slice()[1..],
                    trait_args,
                    &mut unification_map,
                ) {
                    continue;
                }

                // TODO check if the where clauses match up

                info!("found impl {:?}", impl_ref);
                if solution.is_some() {
                    println!(
                        "Warning: Ambiguous resolution for impl of trait {:?} on type {:?}; solution {:?} but found also {:?}",
                        trait_did,
                        for_type,
                        solution.unwrap(),
                        impl_ref.def_id,
                    );
                } else {
                    solution = Some(*did);
                }
            }
        }

        solution
    } else {
        let mut unification_map = HashMap::new();

        // this is a non-blanket impl
        let simplified_type =
            ty::fast_reject::simplify_type(tcx, for_type, ty::fast_reject::TreatParams::AsCandidateKey)?;
        let defs = impls.non_blanket_impls().get(&simplified_type)?;
        info!("found non-blanket implementations: {:?}", defs);

        let mut solution = None;
        for did in defs {
            let impl_self_ty: ty::Ty<'tcx> = tcx.type_of(did).instantiate_identity();
            let impl_self_ty = types::normalize_in_function(*did, tcx, impl_self_ty).unwrap();

            // check if this is an implementation for the right type
            if unification::unify_types(for_type, impl_self_ty, &mut unification_map) {
                let impl_ref: Option<ty::EarlyBinder<ty::TraitRef<'_>>> = tcx.impl_trait_ref(did);

                if let Some(impl_ref) = impl_ref {
                    let impl_ref = types::normalize_in_function(*did, tcx, impl_ref.skip_binder()).unwrap();

                    let this_impl_args = impl_ref.args;
                    // filter by the generic instantiation for the trait
                    info!("found impl with args {:?}", this_impl_args);
                    // args has self at position 0 and generics of the trait at position 1..

                    // check if the generic argument types match up
                    let mut unification_map = unification_map.clone();
                    if !unification::args_unify_types(
                        &this_impl_args.as_slice()[1..],
                        trait_args,
                        &mut unification_map,
                    ) {
                        continue;
                    }

                    info!("found impl {:?}", impl_ref);
                    if solution.is_some() {
                        println!(
                            "Warning: Ambiguous resolution for impl of trait {:?} on type {:?}; solution {:?} but found also {:?}",
                            trait_did,
                            for_type,
                            solution.unwrap(),
                            impl_ref.def_id,
                        );
                    } else {
                        solution = Some(*did);
                    }
                }
            }
        }
        solution
    }
}

/// Try to resolve the `DefId` of a method in an implementation of a trait for a particular type.
/// Note that this does not, in general, find a unique solution, in case there are complex things
/// with different where clauses going on.
pub fn try_resolve_trait_method_did<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    trait_did: hir::def_id::DefId,
    trait_args: &[Option<ty::GenericArg<'tcx>>],
    method_name: &str,
    for_type: ty::Ty<'tcx>,
) -> Option<hir::def_id::DefId> {
    // get all impls of this trait
    let impls: &ty::trait_def::TraitImpls = tcx.trait_impls_of(trait_did);

    let simplified_type =
        ty::fast_reject::simplify_type(tcx, for_type, ty::fast_reject::TreatParams::AsCandidateKey)?;
    let defs = impls.non_blanket_impls().get(&simplified_type)?;
    info!("found implementations: {:?}", impls);

    let mut unification_map = HashMap::new();

    let mut solution = None;
    for did in defs {
        let impl_self_ty: ty::Ty<'tcx> = tcx.type_of(did).instantiate_identity();
        let impl_self_ty = types::normalize_in_function(*did, tcx, impl_self_ty).unwrap();

        // check if this is an implementation for the right type
        if unification::unify_types(for_type, impl_self_ty, &mut unification_map) {
            let impl_ref: Option<ty::EarlyBinder<ty::TraitRef<'_>>> = tcx.impl_trait_ref(did);

            if let Some(impl_ref) = impl_ref {
                let impl_ref = types::normalize_in_function(*did, tcx, impl_ref.skip_binder()).unwrap();

                let this_impl_args = impl_ref.args;
                // filter by the generic instantiation for the trait
                info!("found impl with args {:?}", this_impl_args);
                // args has self at position 0 and generics of the trait at position 1..

                // check if the generic argument types match up
                let mut unification_map = unification_map.clone();
                if !unification::args_unify_types(
                    &this_impl_args.as_slice()[1..],
                    trait_args,
                    &mut unification_map,
                ) {
                    continue;
                }

                let impl_assoc_items: &ty::AssocItems = tcx.associated_items(did);
                // find the right item
                if let Some(item) = impl_assoc_items.find_by_name_and_kind(
                    tcx,
                    span::symbol::Ident::from_str(method_name),
                    ty::AssocKind::Fn,
                    trait_did,
                ) {
                    info!("found impl {:?} with item {:?}", impl_ref, item);
                    if solution.is_some() {
                        println!(
                            "Warning: Ambiguous resolution for method {method_name} of trait {:?} on type {:?}; solution {:?} but found also {:?}",
                            trait_did,
                            for_type,
                            solution.unwrap(),
                            item.def_id
                        );
                    } else {
                        solution = Some(item.def_id);
                    }
                }
            }
        }
    }

    solution
}

/// Try to get a defid of a method at the given path.
/// This does not handle trait methods.
/// This also does not handle overlapping method definitions/specialization well.
pub fn try_resolve_method_did_direct<T>(tcx: ty::TyCtxt<'_>, path: &[T]) -> Option<hir::def_id::DefId>
where
    T: AsRef<str>,
{
    tcx.crates(())
        .iter()
        .find(|&&krate| tcx.crate_name(krate).as_str() == path[0].as_ref())
        .and_then(|krate| {
            let krate = hir::def_id::DefId {
                krate: *krate,
                index: hir::def_id::CRATE_DEF_INDEX,
            };

            let mut items: &[metadata::ModChild] = tcx.module_children(krate);
            let mut path_it = path.iter().skip(1).peekable();

            while let Some(segment) = path_it.next() {
                //info!("items to look at: {:?}", items);
                for item in mem::take(&mut items) {
                    let item: &metadata::ModChild = item;

                    if item.ident.name.as_str() != segment.as_ref() {
                        continue;
                    }

                    info!("taking path: {:?}", segment.as_ref());
                    if path_it.peek().is_none() {
                        return Some(item.res.def_id());
                    }

                    // just the method remaining
                    if path_it.len() != 1 {
                        items = tcx.module_children(item.res.def_id());
                        break;
                    }

                    let did: hir::def_id::DefId = item.res.def_id();
                    let impls: &[hir::def_id::DefId] = tcx.inherent_impls(did);
                    info!("trying to find method among impls {:?}", impls);

                    let find = path_it.next().unwrap();
                    for impl_did in impls {
                        //let ty = tcx.type_of(*impl_did);
                        //info!("type of impl: {:?}", ty);
                        let items: &ty::AssocItems = tcx.associated_items(impl_did);
                        //info!("items here: {:?}", items);
                        // TODO more robust error handling if there are multiple matches.
                        for item in items.in_definition_order() {
                            //info!("comparing: {:?} with {:?}", item.name.as_str(), find);
                            if item.name.as_str() == find.as_ref() {
                                return Some(item.def_id);
                            }
                        }
                        //info!("impl items: {:?}", items);
                    }

                    //info!("inherent impls for {:?}: {:?}", did, impls);
                    return None;
                }
            }

            None
        })
}

pub fn try_resolve_method_did<T>(tcx: ty::TyCtxt<'_>, path: &[T]) -> Option<hir::def_id::DefId>
where
    T: AsRef<str>,
{
    if let Some(did) = try_resolve_method_did_direct(tcx, path) {
        return Some(did);
    }

    // if the first component is "std", try if we can replace it with "alloc" or "core"
    if path[0].as_ref() == "std" {
        let mut components: Vec<_> = path.iter().map(|x| x.as_ref().to_owned()).collect();
        components[0] = "core".to_owned();
        if let Some(did) = try_resolve_method_did_direct(tcx, &components) {
            return Some(did);
        }
        // try "alloc"
        components[0] = "alloc".to_owned();
        try_resolve_method_did_direct(tcx, &components)
    } else {
        None
    }
}
