//! Interface for resolving trait requirements using `rustc`'s trait resolution.
use std::collections::HashMap;

/// Inspired by (in terms of rustc APIs used) by
/// <https://github.com/xldenis/creusot/blob/9d8b1822cd0c43154a6d5d4d05460be56710399c/creusot/src/translation/traits.rs>
use log::{info, trace};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::infer::infer::TyCtxtInferExt as _;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TypeVisitableExt as _;
use rr_rustc_interface::{middle, trait_selection};
use trait_selection::{infer, solve};

//use trait_selection::traits::{self, normalize::NormalizeExt};
use crate::regions::arg_folder;
use crate::regions::region_bi_folder::RegionBiFolder;

/// Normalize a type in the given environment.
pub(crate) fn normalize_type<'tcx, T>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: T,
) -> Result<T, Vec<trait_selection::traits::FulfillmentError<'tcx>>>
where
    T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
{
    // TODO: should we normalize like this also below?
    let infer_ctx: infer::InferCtxt<'tcx> = tcx
        .infer_ctxt()
        .with_next_trait_solver(true)
        .ignoring_regions()
        .build(typing_env.typing_mode);

    let obligation_cause = middle::traits::ObligationCause::dummy();
    let at = infer_ctx.at(&obligation_cause, typing_env.param_env);

    solve::deeply_normalize(at, ty)

    //trait_selection::traits::fully_normalize(
    //&infer_ctx,
    //middle::traits::ObligationCause::dummy(),
    //param_env,
    //ty,
    //)
}

/// Resolve an implementation of a trait using codegen candidate selection.
/// `did` can be the id of a trait, or the id of an associated item of a trait.
pub(crate) fn resolve_impl_source<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    did: DefId,
    substs: ty::GenericArgsRef<'tcx>,
    below_binders: ty::Binder<'tcx, ()>,
) -> Option<trait_selection::traits::ImplSource<'tcx, ()>> {
    // we erase regions, because candidate selection cannot deal with open region variables
    trace!("args before erasing: {substs:?}");
    let erased_substs = tcx.normalize_erasing_regions(typing_env, substs);
    //let erased_substs = normalize_type(tcx, typing_env, substs).unwrap();
    trace!("erased args: {erased_substs:?}");
    let erased_substs = arg_folder::relabel_late_bounds(erased_substs, tcx);
    trace!("erased args: {erased_substs:?}");

    // Check if the `did` is an associated item
    let trait_ref = if let Some(item) = tcx.opt_associated_item(did) {
        match item.container {
            ty::AssocItemContainer::Trait => {
                // this is part of a trait declaration
                ty::TraitRef::new(tcx, item.container_id(tcx), erased_substs)
            },
            ty::AssocItemContainer::Impl => {
                // this is part of an implementation of a trait
                tcx.impl_trait_ref(item.container_id(tcx))?.instantiate(tcx, erased_substs)
            },
        }
    } else {
        // Otherwise, check if it's a reference to a trait itself
        if tcx.is_trait(did) {
            ty::TraitRef::new(tcx, did, erased_substs)
        } else {
            return None;
        }
    };

    trace!("selecting codegen candidate for {trait_ref:?}");
    let res = tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref)).ok()?;
    Some(recover_lifetimes_for_impl_source(tcx, typing_env, substs, res, below_binders))
}

fn recover_lifetimes_for_impl_source<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    substs: ty::GenericArgsRef<'tcx>,
    impl_source: &'tcx trait_selection::traits::ImplSource<'tcx, ()>,
    below_binders: ty::Binder<'tcx, ()>,
) -> trait_selection::traits::ImplSource<'tcx, ()> {
    match impl_source {
        trait_selection::traits::ImplSource::UserDefined(impl_data) => {
            let impl_did = impl_data.impl_def_id;
            let impl_args = impl_data.args;

            trace!("resolved to impl {impl_did:?} with args {impl_args:?}");

            // enumerate regions in args since they were erased before
            let (enumerated_impl_args, num_regions) = arg_folder::relabel_erased_regions(impl_args, tcx);

            trace!("re-enumerated impl args: {enumerated_impl_args:?}");

            if num_regions == 0 {
                return impl_source.to_owned();
            }

            // instantiate the trait with the impl args; the subject is the trait below the impl's binders
            let subject = tcx.impl_subject(impl_did);
            let subject = subject.skip_binder();
            let subject = arg_folder::instantiate_open(subject, tcx, enumerated_impl_args.as_slice());

            let ty::ImplSubject::Trait(subject_ref) = subject else {
                unreachable!();
            };

            // impl_args are the args of the trait, instantiated with the re-enumerated args of the resolved
            // impl required_args are the args of the trait that we were expecting, still
            // containing the right regions Find an instantiation of `impl_args`'s regions by
            // comparing them.
            let impl_args = subject_ref.args;
            let required_args = substs;
            trace!("implementing trait {:?} for args {:?}", subject_ref.def_id, impl_args);
            trace!("mapping regions from {required_args:?} to {impl_args:?}");

            // normalize both args first, taking into account the late bound binders
            // TODO: actually, this seems to have problem if we have to normalize an alias
            // involving region variables.
            // Is there some way to teach the resolution about region variables in scope?
            let bound_impl_args = below_binders.rebind(impl_args);
            let impl_args = normalize_type(tcx, typing_env, bound_impl_args).unwrap();
            let impl_args = impl_args.skip_binder();

            trace!("normalized impl_args = {impl_args:?}");

            let bound_required_args = below_binders.rebind(required_args);
            let required_args = normalize_type(tcx, typing_env, bound_required_args).unwrap();
            let required_args = required_args.skip_binder();

            trace!("normalized required = {required_args:?}");

            // find the mapping
            let mut mapper = RegionMapper {
                tcx,
                typing_env,
                map: HashMap::new(),
            };
            mapper.map_generic_args(impl_args, required_args);
            let region_map = mapper.get_result(num_regions);
            trace!("recovered region map: {region_map:?}");

            // then instantiate the enumerated_impl_args with the mapping, recovering the
            // propertly-instantiated args for the resolved `impl`
            let renamed_impl_args = arg_folder::rename_region_vids(enumerated_impl_args, tcx, region_map);

            let new_data = trait_selection::traits::ImplSourceUserDefinedData {
                impl_def_id: impl_did,
                args: renamed_impl_args,
                nested: impl_data.nested.clone(),
            };
            trait_selection::traits::ImplSource::UserDefined(new_data)
        },
        trait_selection::traits::ImplSource::Param(_) => {
            // TODO?
            impl_source.to_owned()
        },
        trait_selection::traits::ImplSource::Builtin(_, _) => impl_source.to_owned(),
    }
}

struct RegionMapper<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    map: HashMap<ty::RegionVid, ty::Region<'tcx>>,
}
impl<'tcx> RegionMapper<'tcx> {
    fn get_result(mut self, num_regions: usize) -> Vec<ty::Region<'tcx>> {
        let mut res = Vec::new();
        for i in 0..num_regions {
            let r = self.map.remove(&ty::RegionVid::from(i)).unwrap();
            res.push(r);
        }
        res
    }
}
impl<'tcx> RegionBiFolder<'tcx> for RegionMapper<'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn typing_env(&self) -> &ty::TypingEnv<'tcx> {
        &self.typing_env
    }

    fn map_regions(&mut self, r1: ty::Region<'tcx>, r2: ty::Region<'tcx>) {
        if let ty::RegionKind::ReVar(v1) = r1.kind() {
            assert!(!self.map.contains_key(&v1));

            self.map.insert(v1, r2);
        }
    }
}

// Design for type unification:
// - we get a trait_ref, typing_env and the resolved ImplSource.
// - the impl args have erased lifetimes.
// - given the impl args, compute the corresponding trait args
// - can lifetime args appear in impl args that are not also mentioned in trait args? no, probably not. Maybe
//   'static..
//   + so I can make a fairly simple structural traversal, I guess.
//   + How do I know which variable to map to what? maybe I need to give all erased variables a fresh name
//     first. then backtranslate then compare and compute mapping

/// Resolve a reference to a trait using codegen trait selection.
/// `did` should be the id of a trait.
pub(crate) fn resolve_trait<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    did: DefId,
    substs: ty::GenericArgsRef<'tcx>,
    below_binders: ty::Binder<'tcx, ()>,
) -> Option<(DefId, ty::GenericArgsRef<'tcx>, TraitResolutionKind)> {
    if tcx.is_trait(did) {
        let impl_source = resolve_impl_source(tcx, typing_env, did, substs, below_binders);
        info!("trait impl_source for {:?}: {:?}", did, impl_source);
        match impl_source? {
            trait_selection::traits::ImplSource::UserDefined(impl_data) => {
                Some((impl_data.impl_def_id, impl_data.args, TraitResolutionKind::UserDefined))
            },
            trait_selection::traits::ImplSource::Param(_) => Some((did, substs, TraitResolutionKind::Param)),
            trait_selection::traits::ImplSource::Builtin(impl_source, _) => {
                trace!("resolve_trait: found Builtin {impl_source:?}");
                match *substs[0].as_type().unwrap().kind() {
                    // try to get the body
                    ty::Closure(closure_def_id, closure_substs) => {
                        Some((closure_def_id, closure_substs, TraitResolutionKind::Closure))
                    },
                    _ => unimplemented!(),
                }
            },
        }
    } else {
        None
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum TraitResolutionKind {
    Param,
    UserDefined,
    Closure,
}

/// Resolve a reference to a trait item using codegen trait selection.
/// `did` should be the id of a trait item.
pub(crate) fn resolve_assoc_item<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    did: DefId,
    substs: ty::GenericArgsRef<'tcx>,
    below_binders: ty::Binder<'tcx, ()>,
) -> Option<(DefId, ty::GenericArgsRef<'tcx>, TraitResolutionKind)> {
    let assoc = tcx.opt_associated_item(did)?;

    /*
    // If we're given an associated item that is already on an instance,
    // we don't need to resolve at all!
    //
    // FIXME: not true given specialization!
    if let AssocItemContainer::ImplContainer = assoc.container {
        return None;
    }
    */

    let trait_ref = ty::TraitRef::from_assoc(tcx, tcx.trait_of_assoc(did).unwrap(), substs);

    let impl_source = resolve_impl_source(tcx, typing_env, did, substs, below_binders)?;
    info!("trait impl_source for {:?}: {:?}", did, impl_source);

    match impl_source {
        trait_selection::traits::ImplSource::UserDefined(impl_data) => {
            // this is a user-defined trait, and we found the right impl
            // now map back to the item we were looking for
            let trait_did = tcx.trait_id_of_impl(impl_data.impl_def_id).unwrap();
            let trait_def: &'tcx ty::TraitDef = tcx.trait_def(trait_did);

            // Find the id of the actual associated method we will be running
            let ancestors = trait_def.ancestors(tcx, impl_data.impl_def_id).unwrap();
            // find the item we were looking for
            let leaf_def = ancestors.leaf_def(tcx, assoc.def_id).unwrap_or_else(|| {
                panic!("{:?} not found in {:?}", assoc, impl_data.impl_def_id);
            });

            if !leaf_def.is_final() && trait_ref.still_further_specializable() {
                // return the original id to call
                return Some((did, substs, TraitResolutionKind::UserDefined));
            }

            // Translate the original substitution into one on the selected impl method

            let typing_env = typing_env.with_post_analysis_normalized(tcx);
            let infcx = tcx.infer_ctxt().build(typing_env.typing_mode);

            let substs = substs.rebase_onto(tcx, trait_did, impl_data.args);
            let substs = trait_selection::traits::translate_args(
                &infcx,
                typing_env.param_env,
                impl_data.impl_def_id,
                substs,
                leaf_def.defining_node,
            );
            let leaf_substs = substs;
            //let leaf_substs = infcx.tcx.erase_regions(substs);

            Some((leaf_def.item.def_id, leaf_substs, TraitResolutionKind::UserDefined))
        },
        trait_selection::traits::ImplSource::Param(_) => Some((did, substs, TraitResolutionKind::Param)),
        trait_selection::traits::ImplSource::Builtin(_, _) =>
        // the 0-th parameter should be self
        // if this is a closure, we want to call that closure
        {
            match *substs[0].as_type().unwrap().kind() {
                // try to get the body
                ty::Closure(closure_def_id, closure_substs) => {
                    Some((closure_def_id, closure_substs, TraitResolutionKind::Closure))
                },
                _ => unimplemented!(),
            }
        },
    }
}
