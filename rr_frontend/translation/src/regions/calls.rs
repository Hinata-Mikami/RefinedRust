// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides functionality for generating lifetime annotations for calls.

use std::collections::{BTreeMap, BTreeSet};

use derive_more::Debug;
use log::{info, warn};
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::RegionExt as _;

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info;
use crate::environment::region_folder::*;
use crate::regions::inclusion_tracker::InclusionTracker;

// solve the constraints for the new_regions
// we first identify what kinds of constraints these new regions are subject to
#[derive(Debug)]
pub(crate) enum CallRegionKind {
    // this is just an intersection of local regions.
    Intersection(BTreeSet<Region>),
    // this is equal to a specific region
    EqR(Region),
}

pub(crate) struct CallRegions {
    pub early_regions: Vec<Region>,
    pub late_regions: Vec<Region>,
    pub classification: BTreeMap<Region, CallRegionKind>,
    pub new_regions: BTreeSet<Region>,
}

#[derive(Default)]
#[expect(clippy::partial_pub_fields)]
pub(crate) struct CallRegionDiscovery {
    pub early_regions: Vec<Region>,
    pub late_regions: Vec<Region>,
    pub late_regions_by_bound_var: BTreeMap<usize, Region>,
    pub new_regions: BTreeSet<Region>,
    relevant_constraints: Vec<(Region, Region)>,
}

fn late_region_binder_order(sig: ty::PolyFnSig<'_>) -> Vec<usize> {
    sig.bound_vars()
        .iter()
        .enumerate()
        .filter_map(|(index, kind)| matches!(kind, ty::BoundVariableKind::Region(_)).then_some(index))
        .collect()
}

/// Reproduce the order in which rustc allocates inference variables while instantiating the
/// signature. This need not be the order of entries in `bound_vars`.
fn late_region_allocation_order<'tcx>(tcx: ty::TyCtxt<'tcx>, sig: ty::PolyFnSig<'tcx>) -> Vec<usize> {
    let mut allocation_order = Vec::new();
    let mut next_region = 0;
    let (_, _) = tcx.instantiate_bound_regions(sig, &mut |bound: ty::BoundRegion<'tcx>| {
        allocation_order.push(bound.var.index());
        let region = ty::Region::new_var(tcx, ty::RegionVid::from_usize(next_region));
        next_region += 1;
        region
    });
    allocation_order
}

fn is_contiguous(regions: &[Region]) -> bool {
    regions.windows(2).all(|pair| pair[0].as_u32() + 1 == pair[1].as_u32())
}

fn map_allocated_regions_to_binders(
    binder_order: &[usize],
    allocation_order: &[usize],
    regions: &[Region],
) -> Option<(Vec<Region>, BTreeMap<usize, Region>)> {
    if allocation_order.len() != regions.len() || binder_order.len() != regions.len() {
        return None;
    }

    let allocated: BTreeMap<_, _> = allocation_order.iter().copied().zip(regions.iter().copied()).collect();
    let by_bound_var: BTreeMap<_, _> = binder_order
        .iter()
        .copied()
        .map(|bound_var| allocated.get(&bound_var).copied().map(|region| (bound_var, region)))
        .collect::<Option<_>>()?;
    let ordered = binder_order.iter().map(|bound_var| by_bound_var[bound_var]).collect();
    Some((ordered, by_bound_var))
}

/// Compute instantiations for the lifetime parameters of a function.
/// Each of the lifetimes in the function's signature has one Polonius inference variable at the
/// call site, and we need to find an instantiation for these.
/// `substs` are the substitutions for the early-bound regions
pub(crate) fn discover_call_regions<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    info: &polonius_info::PoloniusInfo<'_, 'tcx>,
    substs: &[ty::GenericArg<'tcx>],
    resolved_substs: &[ty::GenericArg<'tcx>],
    sig: ty::PolyFnSig<'tcx>,
    midpoint: facts::PointIndex,
    num_expected_late_bounds: usize,
) -> CallRegionDiscovery {
    let mut early_regions = Vec::new();
    for a in substs.iter().chain(resolved_substs) {
        if let ty::GenericArgKind::Lifetime(r) = a.kind()
            && let ty::RegionKind::ReVar(r) = r.kind()
            && !early_regions.contains(&r.into())
        {
            early_regions.push(r.into());
        }
    }
    info!("call args: {substs:?}");
    info!("call region instantiations (early): {:?}", early_regions);

    // this is a hack to identify the inference variables introduced for the
    // call's late-bound universals.
    // TODO: Can we get this information in a less hacky way?
    // One approach: compute the early + late bound regions for a given DefId, similarly to how
    // we do it when starting to translate a function
    // Problem: this doesn't give a straightforward way to compute their instantiation

    // now find all the regions that appear in type parameters we instantiate.
    // These are regions that the callee doesn't know about.
    let mut generic_regions: BTreeSet<facts::Region> = BTreeSet::new();
    let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
        ty::RegionKind::ReVar(rv) => {
            generic_regions.insert(rv.into());
            r
        },
        _ => r,
    };

    for a in substs.iter().chain(resolved_substs) {
        if let ty::GenericArgKind::Type(c) = a.kind() {
            let mut folder = RegionFolder::new(tcx, &mut clos);
            folder.fold_ty(c);
        }
    }
    info!("Regions of generic args: {:?}", generic_regions);

    // go over all region constraints initiated at this location
    let new_constraints = info.get_new_subset_constraints_at_point(midpoint);
    let mut new_regions = BTreeSet::new();
    let mut relevant_constraints = Vec::new();
    for (r1, r2) in &new_constraints {
        if matches!(info.get_region_kind(*r1), polonius_info::RegionKind::Unknown(_)) {
            // this is probably a inference variable for the call
            new_regions.insert(*r1);
            relevant_constraints.push((*r1, *r2));
        }
        if matches!(info.get_region_kind(*r2), polonius_info::RegionKind::Unknown(_)) {
            new_regions.insert(*r2);
            relevant_constraints.push((*r1, *r2));
        }
    }
    // first sort this to enable cycle resolution
    let mut new_regions_sorted: Vec<Region> = new_regions.iter().copied().collect();
    new_regions_sorted.sort();
    info!("new regions: {new_regions_sorted:?}");
    info!("relevant constraints: {relevant_constraints:?}");

    let candidates: Vec<_> = new_regions_sorted
        .iter()
        .copied()
        .filter(|region| !early_regions.contains(region) && !generic_regions.contains(region))
        .collect();
    let binder_order = late_region_binder_order(sig);
    let allocation_order = late_region_allocation_order(tcx, sig);
    let num_source_late_bounds = binder_order.len();
    if num_source_late_bounds != num_expected_late_bounds {
        warn!(
            "call signature and specification disagree on late-bound region count: \
             signature={num_source_late_bounds}, specification={num_expected_late_bounds}"
        );
    }

    // rustc allocates the late-bound inference variables as one run before creating the other
    // inference variables used to normalize and check the call. Prefer reconstructing that run,
    // but retain the previous heuristic for calls where the Polonius constraints do not expose it.
    let strict_regions = candidates.get(..num_source_late_bounds).filter(|regions| {
        candidates.len() == num_source_late_bounds
            && allocation_order.len() == num_source_late_bounds
            && is_contiguous(regions)
    });
    let (late_regions, late_regions_by_bound_var) = if let Some(regions) = strict_regions {
        let (ordered, by_bound_var) =
            map_allocated_regions_to_binders(&binder_order, &allocation_order, regions)
                .expect("strict call-region reconstruction has matching binder and allocation counts");
        info!(
            "reconstructed call late regions from rustc allocation order: {allocation_order:?} -> {ordered:?}"
        );
        (ordered, by_bound_var)
    } else {
        let mut late_regions = candidates;
        // Elided lifetimes in trait impl arguments can appear as extra late-bound regions on the
        // impl method even though they behave like early-bound regions. Preserve the best-effort
        // workaround of removing such regions when they equal an early-bound region.
        // See https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/work_items/25.
        if late_regions.len() > num_source_late_bounds {
            late_regions.retain(|x| {
                !early_regions.iter().any(|y| {
                    relevant_constraints.contains(&(*x, *y)) && relevant_constraints.contains(&(*y, *x))
                })
            });
        }
        late_regions.truncate(num_source_late_bounds);
        let (late_regions, by_bound_var) =
            map_allocated_regions_to_binders(&binder_order, &allocation_order, &late_regions).unwrap_or_else(
                || {
                    let by_bound_var =
                        binder_order.iter().copied().zip(late_regions.iter().copied()).collect();
                    (late_regions, by_bound_var)
                },
            );
        warn!(
            "falling back to heuristic call-region instantiation: expected={num_expected_late_bounds}, \
             binders={binder_order:?}, allocation_order={allocation_order:?}, candidates={late_regions:?}"
        );
        (late_regions, by_bound_var)
    };
    info!("computed late regions: {:?}, expected: {num_expected_late_bounds:?}", late_regions.len());
    info!("call region instantiations (late): {:?}", late_regions);

    CallRegionDiscovery {
        early_regions,
        late_regions,
        late_regions_by_bound_var,
        new_regions,
        relevant_constraints,
    }
}

pub(crate) fn classify_call_regions(
    incl_tracker: &mut InclusionTracker<'_, '_>,
    midpoint: facts::PointIndex,
    discovery: CallRegionDiscovery,
) -> CallRegions {
    let CallRegionDiscovery {
        early_regions,
        late_regions,
        new_regions,
        relevant_constraints,
        ..
    } = discovery;
    let mut new_regions_sorted: Vec<_> = new_regions.iter().copied().collect();
    new_regions_sorted.sort();

    // Notes:
    // - if two of the call regions need to be equal due to constraints on the function, we define the one
    //   with the larger id in terms of the other one
    // - we ignore unidirectional subset constraints between call regions (these do not help in finding a
    //   solution if we take the transitive closure beforehand)
    // - if a call region needs to be equal to a local region, we directly define it in terms of the local
    //   region
    // - otherwise, it will be an intersection of local regions
    let mut new_regions_classification = BTreeMap::new();
    // compute transitive closure of constraints
    let relevant_constraints = polonius_info::compute_transitive_closure(relevant_constraints);
    for r in &new_regions_sorted {
        for (r1, r2) in &relevant_constraints {
            if *r2 != *r {
                continue;
            }
            // reflexive constraints do not help us, of course.
            if *r1 == *r2 {
                continue;
            }
            // r1 should be known or a new region
            if !incl_tracker.is_region_known_before_dynamic(*r1, midpoint) && !new_regions.contains(r1) {
                // this is a constraint that won't help us
                continue;
            }

            // i.e. (flipping it around when we are talking about lifetimes),
            // r needs to be a sublft of r1
            if relevant_constraints.contains(&(*r2, *r1)) {
                // if r1 is also a new region and r2 is ordered before it, we will
                // just define r1 in terms of r2
                if new_regions.contains(r1) && r2.as_u32() < r1.as_u32() {
                    continue;
                }
                // need an equality constraint
                new_regions_classification.insert(*r2, CallRegionKind::EqR(*r1));
                // do not consider the rest of the constraints as r is already
                // fully specified
                break;
            }

            // the intersection also needs to contain r1
            if new_regions.contains(r1) {
                // we do not need this constraint, since we already computed the
                // transitive closure.
                continue;
            }

            let kind = new_regions_classification
                .entry(*r)
                .or_insert(CallRegionKind::Intersection(BTreeSet::new()));

            let CallRegionKind::Intersection(s) = kind else {
                unreachable!();
            };

            s.insert(*r1);
        }
    }
    info!("call arg classification: {:?}", new_regions_classification);

    CallRegions {
        early_regions,
        late_regions,
        classification: new_regions_classification,
        new_regions,
    }
}

impl CallRegions {
    fn has_definition(&self, region: Region, visiting: &mut BTreeSet<Region>) -> bool {
        if !self.new_regions.contains(&region) {
            return true;
        }
        if !visiting.insert(region) {
            return false;
        }

        let defined = match self.classification.get(&region) {
            Some(CallRegionKind::EqR(source)) => self.has_definition(*source, visiting),
            Some(CallRegionKind::Intersection(sources)) => {
                !sources.is_empty() && sources.iter().all(|source| self.has_definition(*source, visiting))
            },
            None => false,
        };
        visiting.remove(&region);
        defined
    }

    pub(crate) fn undefined_late_regions(&self) -> Vec<Region> {
        self.late_regions
            .iter()
            .copied()
            .filter(|region| !self.has_definition(*region, &mut BTreeSet::new()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_allocation_order_to_binder_order() {
        let allocated = [Region::from_usize(30), Region::from_usize(31)];
        let (ordered, by_bound_var) = map_allocated_regions_to_binders(&[0, 1], &[1, 0], &allocated).unwrap();

        assert_eq!(ordered, [Region::from_usize(31), Region::from_usize(30)]);
        assert_eq!(by_bound_var[&0], Region::from_usize(31));
        assert_eq!(by_bound_var[&1], Region::from_usize(30));
    }

    #[test]
    fn detects_undefined_late_region() {
        let late = Region::from_usize(1);
        let regions = CallRegions {
            early_regions: Vec::new(),
            late_regions: vec![late],
            classification: BTreeMap::new(),
            new_regions: BTreeSet::from([late]),
        };

        assert_eq!(regions.undefined_late_regions(), [late]);
    }
}
