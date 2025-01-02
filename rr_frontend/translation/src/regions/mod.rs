// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utilities for translating region information.

use std::cell::{OnceCell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write;

use derive_more::{Constructor, Debug};
use log::{info, trace, warn};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::tcx::PlaceTy;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::{Ty, TyCtxt, TyKind, TypeFoldable};
use ty::TypeSuperFoldable;

use crate::base::*;
use crate::environment::polonius_info::{self, PoloniusInfo};
use crate::environment::Environment;
use crate::spec_parsers::parse_utils::ParamLookup;
use crate::trait_registry::{self, Error, GenericTraitUse, TraitRegistry, TraitResult};

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

/// Data structure that maps early and late region indices to Polonius regions.
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
