// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utilities for translating region information.

pub mod arg_folder;
pub mod assignment;
pub mod calls;
pub mod composite;
pub mod inclusion_tracker;
pub mod init;
pub mod region_bi_folder;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use derive_more::{Constructor, Debug};
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TypeSuperFoldable as _;

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info;

/// Collect all the regions appearing in a type.
/// Data structure that maps early and late region indices inside functions to Polonius regions.
#[derive(Constructor, Clone, Debug, Default)]
pub struct EarlyLateRegionMap {
    // maps indices of early and late regions to Polonius region ids
    pub early_regions: Vec<Option<facts::Region>>,
    pub late_regions: Vec<Vec<facts::Region>>,

    // maps Polonius region ids to names
    pub region_names: BTreeMap<facts::Region, radium::Lft>,

    // maps source-level universal lifetime names to region ids
    pub lft_names: HashMap<String, facts::Region>,
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
        }
    }

    pub fn lookup_region(&self, region: facts::Region) -> Option<&radium::Lft> {
        self.region_names.get(&region)
    }

    pub fn lookup_early_region(&self, idx: usize) -> Option<&radium::Lft> {
        let ovid = self.early_regions.get(idx)?;
        let vid = ovid.as_ref()?;
        self.lookup_region(*vid)
    }

    pub fn lookup_late_region(&self, idx: usize, var: usize) -> Option<&radium::Lft> {
        let binder = self.late_regions.get(idx)?;
        let vid = binder.get(var)?;
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
        polonius_info::AtomicRegion::PlaceRegion(r, uc) => {
            if *uc {
                format!("puclft{}", r.index())
            } else {
                format!("plft{}", r.index())
            }
        },
        polonius_info::AtomicRegion::Unknown(r, uc) => {
            if *uc {
                format!("vuclft{}", r.index())
            } else {
                format!("vlft{}", r.index())
            }
        },
        polonius_info::AtomicRegion::Universal(k, r) => {
            if matches!(k, polonius_info::UniversalRegionKind::Static) {
                return "static".to_owned();
            }

            let Some(scope) = scope else {
                return format!("ulft{}", r.index());
            };

            let Some(s) = scope.lookup_region(*r) else {
                return format!("ulft{}", r.index());
            };

            s.to_owned()
        },
    }
}

pub fn region_to_region_vid(r: ty::Region<'_>) -> facts::Region {
    if let ty::RegionKind::ReVar(vid) = r.kind() {
        vid.into()
    } else {
        panic!()
    }
}

/// A `TypeFolder` that finds all regions occurring in a type.
pub struct TyRegionCollectFolder<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    regions: BTreeSet<Region>,
}

impl<'tcx> TyRegionCollectFolder<'tcx> {
    pub const fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        TyRegionCollectFolder {
            tcx,
            regions: BTreeSet::new(),
        }
    }

    pub fn get_regions(self) -> BTreeSet<Region> {
        self.regions
    }
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for TyRegionCollectFolder<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    // TODO: handle the case that we pass below binders
    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if let ty::RegionKind::ReVar(r) = r.kind() {
            self.regions.insert(r.into());
        }

        r
    }
}
