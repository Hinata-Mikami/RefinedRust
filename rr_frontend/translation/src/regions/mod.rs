// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utilities for translating region information.

mod arg_folder;
pub mod assignment;
pub mod calls;
pub mod composite;
pub mod inclusion_tracker;
pub mod init;

use std::collections::{BTreeMap, HashMap, HashSet};

use derive_more::{Constructor, Debug};
use log::{info, warn};
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TyCtxt;
use ty::TypeSuperFoldable;

use crate::base::Region;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info;

/// Collect all the regions appearing in a type.
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

    pub fn translate_atomic_region(&self, r: &polonius_info::AtomicRegion) -> radium::Lft {
        format_atomic_region_direct(r, Some(self))
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

pub fn region_to_region_vid(r: ty::Region<'_>) -> facts::Region {
    match r.kind() {
        ty::RegionKind::ReVar(vid) => vid,
        _ => panic!(),
    }
}

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
