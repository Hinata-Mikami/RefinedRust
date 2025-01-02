// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utilities for translating region information.

use std::collections::{BTreeMap, HashMap, HashSet};

use derive_more::{Constructor, Debug};
use log::{info, warn};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::tcx::PlaceTy;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::{Ty, TyCtxt, TyKind, TypeFoldable};
use ty::TypeSuperFoldable;

use crate::arg_folder::ty_instantiate;
use crate::base::{self, Region};
use crate::environment::polonius_info::{self, PoloniusInfo};
use crate::environment::Environment;

/// A `TypeFolder` that finds all regions occurring in a type.
pub struct TyRegionCollectFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    regions: HashSet<Region>,
}
impl<'tcx> TyRegionCollectFolder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        TyRegionCollectFolder {
            tcx,
            regions: HashSet::new(),
        }
    }

    pub fn get_regions(self) -> HashSet<Region> {
        self.regions
    }
}
impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for TyRegionCollectFolder<'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    // TODO: handle the case that we pass below binders
    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if let ty::RegionKind::ReVar(r) = r.kind() {
            self.regions.insert(r);
        }

        r
    }
}

/// Collect all the regions appearing in a type.
pub fn find_region_variables_of_place_type<'tcx>(
    env: &Environment<'tcx>,
    ty: PlaceTy<'tcx>,
) -> HashSet<Region> {
    let mut collector = TyRegionCollectFolder::new(env.tcx());
    if ty.variant_index.is_some() {
        panic!("find_region_variables_of_place_type: don't support enums");
    }

    ty.ty.fold_with(&mut collector);
    collector.get_regions()
}

/// Data structure that maps early and late region indices inside functions to Polonius regions.
#[derive(Constructor, Clone, Debug, Default)]
pub struct EarlyLateRegionMap {
    // maps indices of early and late regions to Polonius region ids
    pub early_regions: Vec<Option<ty::RegionVid>>,
    pub late_regions: Vec<ty::RegionVid>,

    // maps Polonius region ids to names
    pub region_names: BTreeMap<ty::RegionVid, radium::Lft>,

    // maps source-level universal lifetime names to region ids
    pub lft_names: HashMap<String, ty::RegionVid>,
}
impl EarlyLateRegionMap {
    /// Lookup a Polonius region with a given kind.
    pub fn lookup_region_with_kind(
        &self,
        k: polonius_info::UniversalRegionKind,
        r: Region,
    ) -> Option<radium::UniversalLft> {
        match k {
            polonius_info::UniversalRegionKind::Function => Some(radium::UniversalLft::Function),
            polonius_info::UniversalRegionKind::Static => Some(radium::UniversalLft::Static),

            polonius_info::UniversalRegionKind::Local => {
                self.lookup_region(r).map(|x| radium::UniversalLft::Local(x.to_owned()))
            },

            polonius_info::UniversalRegionKind::External => {
                self.lookup_region(r).map(|x| radium::UniversalLft::External(x.to_owned()))
            },
        }
    }

    pub fn lookup_region(&self, region: ty::RegionVid) -> Option<&radium::Lft> {
        self.region_names.get(&region)
    }

    pub fn lookup_early_region(&self, idx: usize) -> Option<&radium::Lft> {
        let ovid = self.early_regions.get(idx)?;
        let vid = ovid.as_ref()?;
        self.lookup_region(*vid)
    }

    pub fn lookup_late_region(&self, idx: usize) -> Option<&radium::Lft> {
        let vid = self.late_regions.get(idx)?;
        self.lookup_region(*vid)
    }
}

/// Format the Coq representation of an atomic region.
pub fn format_atomic_region_direct(
    r: &polonius_info::AtomicRegion,
    scope: Option<&EarlyLateRegionMap>,
) -> String {
    match r {
        polonius_info::AtomicRegion::Loan(_, r) => format!("llft{}", r.index()),
        polonius_info::AtomicRegion::PlaceRegion(r) => format!("plft{}", r.index()),
        polonius_info::AtomicRegion::Unknown(r) => format!("vlft{}", r.index()),

        polonius_info::AtomicRegion::Universal(_, r) => {
            let Some(scope) = scope else {
                return format!("ulft{}", r.index());
            };

            let Some(s) = scope.lookup_region(*r) else {
                return format!("ulft{}", r.index());
            };

            s.to_string()
        },
    }
}

/// Process the signature of a function by instantiating the region variables with their
/// Polonius variables.
/// Returns the argument and return type signature instantiated in this way.
/// Moreover, returns a `EarlyLateRegionMap` that contains the mapping of indices to Polonius
/// region variables.
pub fn replace_fnsig_args_with_polonius_vars<'tcx>(
    env: &Environment<'tcx>,
    params: &[ty::GenericArg<'tcx>],
    sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
) -> (Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>, EarlyLateRegionMap) {
    // a mapping of Polonius region IDs to names
    let mut universal_lifetimes = BTreeMap::new();
    let mut lifetime_names = HashMap::new();

    let mut region_substitution_early: Vec<Option<ty::RegionVid>> = Vec::new();

    // we create a substitution that replaces early bound regions with their Polonius
    // region variables
    let mut subst_early_bounds: Vec<ty::GenericArg<'tcx>> = Vec::new();
    let mut num_early_bounds = 0;
    for a in params {
        if let ty::GenericArgKind::Lifetime(r) = a.unpack() {
            // skip over 0 = static
            let next_id = ty::RegionVid::from_u32(num_early_bounds + 1);
            let revar = ty::Region::new_var(env.tcx(), next_id);
            num_early_bounds += 1;
            subst_early_bounds.push(ty::GenericArg::from(revar));

            region_substitution_early.push(Some(next_id));

            match *r {
                ty::RegionKind::ReEarlyBound(r) => {
                    let name = base::strip_coq_ident(r.name.as_str());
                    universal_lifetimes.insert(next_id, format!("ulft_{}", name));
                    lifetime_names.insert(name, next_id);
                },
                _ => {
                    universal_lifetimes.insert(next_id, format!("ulft_{}", num_early_bounds));
                },
            }
        } else {
            subst_early_bounds.push(*a);
            region_substitution_early.push(None);
        }
    }
    let subst_early_bounds = env.tcx().mk_args(&subst_early_bounds);

    info!("Computed early region map {region_substitution_early:?}");

    // add names for late bound region variables
    let mut num_late_bounds = 0;
    let mut region_substitution_late = Vec::new();
    for b in sig.bound_vars() {
        let next_id = ty::RegionVid::from_u32(num_early_bounds + num_late_bounds + 1);

        let ty::BoundVariableKind::Region(r) = b else {
            continue;
        };

        region_substitution_late.push(next_id);

        match r {
            ty::BoundRegionKind::BrNamed(_, sym) => {
                let mut region_name = base::strip_coq_ident(sym.as_str());
                if region_name == "_" {
                    region_name = next_id.as_usize().to_string();
                    universal_lifetimes.insert(next_id, format!("ulft_{}", region_name));
                } else {
                    universal_lifetimes.insert(next_id, format!("ulft_{}", region_name));
                    lifetime_names.insert(region_name, next_id);
                }
            },
            ty::BoundRegionKind::BrAnon(_) => {
                universal_lifetimes.insert(next_id, format!("ulft_{}", next_id.as_usize()));
            },
            _ => (),
        }

        num_late_bounds += 1;
    }

    // replace late-bound region variables by re-enumerating them in the same way as the MIR
    // type checker does (that this happens in the same way is important to make the names
    // line up!)
    let mut next_index = num_early_bounds + 1; // skip over one additional due to static
    let mut folder = |_| {
        let cur_index = next_index;
        next_index += 1;
        ty::Region::new_var(env.tcx(), ty::RegionVid::from_u32(cur_index))
    };
    let (late_sig, _late_region_map) = env.tcx().replace_late_bound_regions(sig, &mut folder);

    // replace early bound variables
    let inputs: Vec<_> = late_sig
        .inputs()
        .iter()
        .map(|ty| ty_instantiate(*ty, env.tcx(), subst_early_bounds))
        .collect();

    let output = ty_instantiate(late_sig.output(), env.tcx(), subst_early_bounds);

    info!("Computed late region map {region_substitution_late:?}");

    let region_map = EarlyLateRegionMap::new(
        region_substitution_early,
        region_substitution_late,
        universal_lifetimes,
        lifetime_names,
    );
    (inputs, output, region_map)
}
