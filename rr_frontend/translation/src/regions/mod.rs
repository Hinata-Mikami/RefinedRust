// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utilities for translating region information.

pub(crate) mod arg_folder;
pub(crate) mod assignment;
pub(crate) mod calls;
pub(crate) mod composite;
pub(crate) mod inclusion_tracker;
pub(crate) mod init;
pub(crate) mod region_bi_folder;

use std::collections::{BTreeMap, BTreeSet, HashMap, btree_map};

use derive_more::{Constructor, Debug};
use radium::{coq, specs};
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TypeSuperFoldable as _;

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info;

/// Collect all the regions appearing in a type.
/// Data structure that maps early and late region indices inside functions to Polonius regions.
#[derive(Constructor, Clone, Debug, Default)]
pub(crate) struct EarlyLateRegionMap {
    // Maps indices of early and late regions to Polonius region ids.
    // For closures, this does not include the lifetimes for the captures.
    pub early_regions: Vec<Option<facts::Region>>,
    pub late_regions: Vec<Vec<facts::Region>>,

    pub closure_regions: Vec<facts::Region>,

    // Maps Polonius region ids to names.
    // This map is the ground truth of what eventually gets added to the generated Rocq
    // representation.
    // In particular, it contains the mapping of closure capture lifetimes.
    pub region_names: BTreeMap<facts::Region, specs::Lft>,

    // Maps source-level universal lifetime names to region ids.
    pub lft_names: HashMap<String, facts::Region>,
}

impl EarlyLateRegionMap {
    /// Lookup a Polonius region with a given kind.
    pub(crate) fn lookup_region_with_kind(
        &self,
        k: polonius_info::UniversalRegionKind,
        r: Region,
    ) -> Option<specs::UniversalLft> {
        match k {
            polonius_info::UniversalRegionKind::Function => Some(specs::UniversalLft::Function),
            polonius_info::UniversalRegionKind::Static => Some(specs::UniversalLft::Static),

            polonius_info::UniversalRegionKind::Local => {
                self.lookup_region(r).map(|x| specs::UniversalLft::Local(x.to_owned()))
            },
        }
    }

    pub(crate) fn lookup_region(&self, region: facts::Region) -> Option<&specs::Lft> {
        self.region_names.get(&region)
    }

    pub(crate) fn lookup_early_region(&self, idx: usize) -> Option<&specs::Lft> {
        let ovid = self.early_regions.get(idx)?;
        let vid = ovid.as_ref()?;
        self.lookup_region(*vid)
    }

    pub(crate) fn lookup_late_region(&self, idx: usize, var: usize) -> Option<&specs::Lft> {
        let binder = self.late_regions.get(idx)?;
        let vid = binder.get(var)?;
        self.lookup_region(*vid)
    }

    pub(crate) fn translate_atomic_region(&self, r: polonius_info::AtomicRegion) -> specs::Lft {
        format_atomic_region_direct(r, Some(self))
    }

    /// Make sure that a region for a closure capture is registered.
    pub(crate) fn ensure_closure_region(&mut self, r: polonius_info::AtomicRegion) {
        if let btree_map::Entry::Vacant(e) = self.region_names.entry(r.get_region()) {
            let name = format_atomic_region_direct(r, None);
            e.insert(name);

            self.closure_regions.push(r.get_region());
        }
    }
}

/// Format the Coq representation of an atomic region.
pub(crate) fn format_atomic_region_direct(
    r: polonius_info::AtomicRegion,
    scope: Option<&EarlyLateRegionMap>,
) -> specs::Lft {
    let (prefix, index) = match r {
        polonius_info::AtomicRegion::Loan(r) => ("l", r.index()),
        polonius_info::AtomicRegion::PlaceRegion(r, uc) => (if uc { "puc" } else { "p" }, r.index()),
        polonius_info::AtomicRegion::Unknown(r, uc) => (if uc { "vuc" } else { "v" }, r.index()),
        polonius_info::AtomicRegion::Universal(k, r) => {
            if matches!(k, polonius_info::UniversalRegionKind::Static) {
                return coq::Ident::new("static");
            }

            if let Some(scope) = scope
                && let Some(s) = scope.lookup_region(r)
            {
                return s.clone();
            }

            ("u", r.index())
        },
    };

    coq::Ident::new(format!("{}lft{}", prefix, index))
}

pub(crate) fn region_to_region_vid(r: ty::Region<'_>) -> facts::Region {
    if let ty::RegionKind::ReVar(vid) = r.kind() { vid.into() } else { panic!() }
}

/// A `TypeFolder` that finds all regions occurring in a type.
pub(crate) struct TyRegionCollectFolder<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    regions: BTreeSet<Region>,
}

impl<'tcx> TyRegionCollectFolder<'tcx> {
    pub(crate) const fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        TyRegionCollectFolder {
            tcx,
            regions: BTreeSet::new(),
        }
    }

    pub(crate) fn get_regions(self) -> BTreeSet<Region> {
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
