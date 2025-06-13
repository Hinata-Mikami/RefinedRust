// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides a flat representation of types that is stable across compilations.

use log::info;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::span;
use serde::{Deserialize, Serialize};

use crate::spec_parsers::{get_export_as_attr, ExportAs, RustPath};
use crate::{attrs, search, Environment};

/// An item path that receives generic arguments.
#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
pub struct PathWithArgs {
    path: Vec<String>,
    /// An encoding of the `GenericArgs` for this definition.
    /// This is `Some(ty)` if:
    /// - the argument represents a type (not a constant or region)
    /// - and the arg is not the trivial identity arg (in case of ADTs)
    args: Vec<Option<Type>>,
}

impl PathWithArgs {
    pub fn to_item<'tcx>(&self, tcx: ty::TyCtxt<'tcx>) -> Option<(DefId, Vec<Option<ty::GenericArg<'tcx>>>)> {
        let did = search::try_resolve_did(tcx, self.path.as_slice())?;

        let mut ty_args = Vec::new();

        for arg in &self.args {
            if let Some(arg) = arg {
                let ty = arg.to_type(tcx)?;
                ty_args.push(Some(ty::GenericArg::from(ty)));
            } else {
                ty_args.push(None);
            }
        }

        Some((did, ty_args))
    }

    /// `args` should be normalized already.
    pub fn from_item<'tcx>(
        env: &Environment<'tcx>,
        did: DefId,
        args: &[ty::GenericArg<'tcx>],
    ) -> Option<Self> {
        let path = get_export_path_for_did(env, did);
        let mut flattened_args = Vec::new();
        info!("flattening args {args:?} for did {did:?}");
        for arg in args {
            if let Some(ty) = arg.as_type() {
                let flattened_ty = convert_ty_to_flat_type(env, ty)?;
                flattened_args.push(Some(flattened_ty));
            } else {
                flattened_args.push(None);
            }
        }
        Some(Self {
            path: path.path.path,
            args: flattened_args,
        })
    }
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "ty::IntTy")]
pub enum IntTyDef {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}
#[derive(Serialize, Deserialize)]
#[serde(remote = "ty::UintTy")]
pub enum UintTyDef {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
/// A "flattened" representation of types that should be suitable serialized storage, and should be
/// stable enough to resolve to the same actual type across compilations.
/// Currently mostly geared to our trait resolution needs.
pub enum Type {
    /// Path + generic args
    /// empty args represents the identity substitution
    Adt(PathWithArgs),
    #[serde(with = "IntTyDef")]
    Int(ty::IntTy),
    #[serde(with = "UintTyDef")]
    Uint(ty::UintTy),
    Char,
    Bool,
    Param(u32),
    // TODO: more cases
}

impl Type {
    /// Try to convert a flat type to a type.
    pub fn to_type<'tcx>(&self, tcx: ty::TyCtxt<'tcx>) -> Option<ty::Ty<'tcx>> {
        match self {
            Self::Adt(path_with_args) => {
                let (did, flat_args) = path_with_args.to_item(tcx)?;

                let ty: ty::EarlyBinder<ty::Ty<'tcx>> = tcx.type_of(did);
                let ty::TyKind::Adt(_, args) = ty.skip_binder().kind() else {
                    return None;
                };

                // build substitution
                let mut substs = Vec::new();
                for (ty_arg, flat_arg) in args.iter().zip(flat_args.into_iter()) {
                    match ty_arg.kind() {
                        ty::GenericArgKind::Type(_) => {
                            if let Some(flat_arg) = flat_arg {
                                substs.push(flat_arg);
                            }
                        },
                        _ => {
                            substs.push(ty_arg);
                        },
                    }
                }

                // substitute
                info!("substituting {:?} with {:?}", ty, substs);
                let subst_ty = if substs.is_empty() {
                    ty.instantiate_identity()
                } else {
                    ty.instantiate(tcx, substs.as_slice())
                };

                Some(subst_ty)
            },
            Self::Bool => Some(tcx.mk_ty_from_kind(ty::TyKind::Bool)),
            Self::Char => Some(tcx.mk_ty_from_kind(ty::TyKind::Char)),
            Self::Int(it) => Some(tcx.mk_ty_from_kind(ty::TyKind::Int(it.to_owned()))),
            Self::Uint(it) => Some(tcx.mk_ty_from_kind(ty::TyKind::Uint(it.to_owned()))),
            Self::Param(idx) => {
                // use a dummy. For matching with the procedures from `unification.rs`, we only
                // need the indices to be consistent.
                let param = ty::ParamTy::new(*idx, span::Symbol::intern("dummy"));
                let kind = ty::TyKind::Param(param);
                Some(tcx.mk_ty_from_kind(kind))
            },
        }
    }
}

/// Try to convert a type to a flat type. Assumes the type has been normalized already.
pub fn convert_ty_to_flat_type<'tcx>(env: &Environment<'tcx>, ty: ty::Ty<'tcx>) -> Option<Type> {
    match ty.kind() {
        ty::TyKind::Adt(def, args) => {
            let did = def.did();
            // TODO: if this is downcast to a variant, this might not work
            let path_with_args = PathWithArgs::from_item(env, did, args.as_slice())?;
            Some(Type::Adt(path_with_args))
        },
        ty::TyKind::Bool => Some(Type::Bool),
        ty::TyKind::Char => Some(Type::Char),
        ty::TyKind::Int(it) => Some(Type::Int(it.to_owned())),
        ty::TyKind::Uint(it) => Some(Type::Uint(it.to_owned())),
        ty::TyKind::Param(p) => Some(Type::Param(p.index)),
        _ => None,
    }
}

pub fn get_cleaned_def_path(tcx: ty::TyCtxt<'_>, did: DefId) -> Vec<String> {
    let def_path = tcx.def_path_str(did);
    // we clean this up a bit and segment it
    let mut components = Vec::new();
    for i in def_path.split("::") {
        if i.starts_with('<') && i.ends_with('>') {
            // this is a generic specialization, skip
            continue;
        }
        components.push(i.to_owned());
    }
    info!("split def path {:?} to {:?}", def_path, components);

    components
}

/// Get the path we should export an item at.
pub fn get_export_path_for_did(env: &Environment, did: DefId) -> ExportAs {
    let attrs = env.get_attributes(did);

    if attrs::has_tool_attr(attrs, "export_as") {
        let filtered_attrs = attrs::filter_for_tool(attrs);

        return get_export_as_attr(filtered_attrs.as_slice()).unwrap();
    }

    // Check for an annotation on the surrounding impl
    if let Some(impl_did) = env.tcx().impl_of_method(did) {
        let attrs = env.get_attributes(impl_did);

        if attrs::has_tool_attr(attrs, "export_as") {
            let filtered_attrs = attrs::filter_for_tool(attrs);
            let mut path_prefix = get_export_as_attr(filtered_attrs.as_slice()).unwrap();

            // push the last component of this path
            //let def_path = env.tcx().def_path(did);
            let mut this_path = get_cleaned_def_path(env.tcx(), did);
            path_prefix.path.path.push(this_path.pop().unwrap());

            return path_prefix;
        }
    }

    let mut basic_path = get_cleaned_def_path(env.tcx(), did);
    // lets check if this is in the current crate, in that case add the current crate prefix
    if did.as_local().is_some() {
        let crate_name = env.tcx().crate_name(span::def_id::LOCAL_CRATE);
        basic_path.insert(0, crate_name.as_str().to_owned());
    }
    ExportAs {
        path: RustPath { path: basic_path },
        as_method: false,
    }
}
