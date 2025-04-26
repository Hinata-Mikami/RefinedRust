// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use derive_more::Display;
use rr_rustc_interface::hir;
use rr_rustc_interface::middle::ty;

use crate::environment::Environment;

pub mod region_bi_folder;
pub mod registry;
pub mod requirements;
pub mod resolution;

#[derive(Debug, Clone, Display)]
pub enum Error<'tcx> {
    /// This DefId is not a trait
    #[display("The given DefId {:?} is not a trait", _0)]
    NotATrait(hir::def_id::DefId),
    /// This DefId is not an impl of a trait
    #[display("The given DefId {:?} is not a trait implementation", _0)]
    NotATraitImpl(hir::def_id::DefId),
    /// This DefId is not a trait method
    #[display("The given DefId {:?} is not a trait method", _0)]
    NotATraitMethod(hir::def_id::DefId),
    /// This DefId is not an assoc type
    #[display("The given DefId {:?} is not an associated type", _0)]
    NotAnAssocType(hir::def_id::DefId),
    /// This trait already exists
    #[display("This trait {:?} already has been registered", _0)]
    TraitAlreadyExists(hir::def_id::DefId),
    /// This trait impl already exists
    #[display("This trait impl {:?} already has been registered", _0)]
    ImplAlreadyExists(hir::def_id::DefId),
    /// Trait hasn't been registered yet but is used
    #[display("This trait {:?} has not been registered yet", _0)]
    UnregisteredTrait(hir::def_id::DefId),
    /// Trait impl hasn't been registered yet but is used
    #[display("This trait impl {:?} has not been registered yet", _0)]
    UnregisteredImpl(hir::def_id::DefId),
    /// Cannot find this trait instance in the local environment
    #[display("An instance for this trait {:?} cannot by found with generic args {:?}", _0, _1)]
    UnknownLocalInstance(hir::def_id::DefId, ty::GenericArgsRef<'tcx>),
    #[display("An error occurred when parsing the specification of the trait {:?}: {:?}", _0, _1)]
    TraitSpec(hir::def_id::DefId, String),
    #[display("An error occurred when parsing the specification of the trait impl {:?}: {:?}", _0, _1)]
    TraitImplSpec(hir::def_id::DefId, String),
    /// Unknown error
    #[display("Unknown Error")]
    Unknown,
}
pub type TraitResult<'tcx, T> = Result<T, Error<'tcx>>;

/// Given a particular reference to a trait, get the associated type constraints for this trait reference.
pub fn get_trait_assoc_constraints<'tcx>(
    env: &Environment<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
) -> HashMap<String, ty::Ty<'tcx>> {
    let mut assoc_ty_map = HashMap::new();

    // TODO: check if caller_bounds does the right thing for implied bounds
    let clauses = param_env.caller_bounds();
    for cl in clauses {
        let cl_kind = cl.kind();
        let cl_kind = cl_kind.skip_binder();

        // only look for trait predicates for now
        if let ty::ClauseKind::Projection(proj) = cl_kind {
            if trait_ref.def_id == proj.trait_def_id(env.tcx()) && trait_ref.args == proj.projection_ty.args {
                // same trait and same args
                let name = env.get_assoc_item_name(proj.def_id()).unwrap();
                let ty = proj.term.ty().unwrap();
                assoc_ty_map.insert(name, ty);
            }
        }
    }
    assoc_ty_map
}
