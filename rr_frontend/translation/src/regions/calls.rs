// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides functionality for generating lifetime annotations for calls.

use std::collections::{HashMap, HashSet};

use derive_more::Debug;
use log::info;
use rr_rustc_interface::middle::ty::TypeFolder;
use rr_rustc_interface::middle::{mir, ty};

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::{polonius_info, Environment};
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::types;

// solve the constraints for the new_regions
// we first identify what kinds of constraints these new regions are subject to
#[derive(Debug)]
pub enum CallRegionKind {
    // this is just an intersection of local regions.
    Intersection(HashSet<Region>),
    // this is equal to a specific region
    EqR(Region),
}

pub struct CallRegions {
    pub early_regions: Vec<Region>,
    pub late_regions: Vec<Region>,
    pub classification: HashMap<Region, CallRegionKind>,
}

// `substs` are the substitutions for the early-bound regions
pub fn compute_call_regions<'tcx>(
    env: &Environment<'tcx>,
    incl_tracker: &InclusionTracker<'_, '_>,
    substs: &[ty::GenericArg<'tcx>],
    loc: mir::Location,
) -> CallRegions {
    let info = incl_tracker.info();

    let midpoint = info.interner.get_point_index(&facts::Point {
        location: loc,
        typ: facts::PointType::Mid,
    });

    let mut early_regions = Vec::new();
    for a in substs {
        if let ty::GenericArgKind::Lifetime(r) = a.unpack() {
            if let ty::RegionKind::ReVar(r) = r.kind() {
                early_regions.push(r);
            }
        }
    }
    info!("call region instantiations (early): {:?}", early_regions);

    // this is a hack to identify the inference variables introduced for the
    // call's late-bound universals.
    // TODO: Can we get this information in a less hacky way?
    // One approach: compute the early + late bound regions for a given DefId, similarly to how
    // we do it when starting to translate a function
    // Problem: this doesn't give a straightforward way to compute their instantiation

    // now find all the regions that appear in type parameters we instantiate.
    // These are regions that the callee doesn't know about.
    let mut generic_regions = HashSet::new();
    let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
        ty::RegionKind::ReVar(rv) => {
            generic_regions.insert(rv);
            r
        },
        _ => r,
    };

    for a in substs {
        if let ty::GenericArgKind::Type(c) = a.unpack() {
            let mut folder = ty::fold::RegionFolder::new(env.tcx(), &mut clos);
            folder.fold_ty(c);
        }
    }
    info!("Regions of generic args: {:?}", generic_regions);

    // go over all region constraints initiated at this location
    let new_constraints = info.get_new_subset_constraints_at_point(midpoint);
    let mut new_regions = HashSet::new();
    let mut relevant_constraints = Vec::new();
    for (r1, r2) in &new_constraints {
        if matches!(info.get_region_kind(*r1), polonius_info::RegionKind::Unknown) {
            // this is probably a inference variable for the call
            new_regions.insert(*r1);
            relevant_constraints.push((*r1, *r2));
        }
        if matches!(info.get_region_kind(*r2), polonius_info::RegionKind::Unknown) {
            new_regions.insert(*r2);
            relevant_constraints.push((*r1, *r2));
        }
    }
    // first sort this to enable cycle resolution
    let mut new_regions_sorted: Vec<Region> = new_regions.iter().copied().collect();
    new_regions_sorted.sort();

    // identify the late-bound regions
    let mut late_regions = Vec::new();
    for r in &new_regions_sorted {
        // only take the ones which are not early bound and
        // which are not due to a generic (the callee doesn't care about generic regions)
        if !early_regions.contains(r) && !generic_regions.contains(r) {
            late_regions.push(*r);
        }
    }
    info!("call region instantiations (late): {:?}", late_regions);

    // Notes:
    // - if two of the call regions need to be equal due to constraints on the function, we define the one
    //   with the larger id in terms of the other one
    // - we ignore unidirectional subset constraints between call regions (these do not help in finding a
    //   solution if we take the transitive closure beforehand)
    // - if a call region needs to be equal to a local region, we directly define it in terms of the local
    //   region
    // - otherwise, it will be an intersection of local regions
    let mut new_regions_classification = HashMap::new();
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
                .or_insert(CallRegionKind::Intersection(HashSet::new()));

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
    }
}

/// Compute annotations for recovering unconstrained regions.
pub fn compute_unconstrained_region_annots<'tcx>(
    env: &Environment<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    loc: mir::Location,
    unconstrained_regions: HashSet<facts::Region>,
    early_region_map: &HashMap<String, usize>,
) -> Result<(Vec<radium::Annotation>, HashSet<facts::Region>), TranslationError<'tcx>> {
    let info = inclusion_tracker.info();
    let midpoint = info.interner.get_point_index(&facts::Point {
        location: loc,
        typ: facts::PointType::Mid,
    });

    let mut remaining_regions = HashSet::new();

    let mut unconstrained_annotations = Vec::new();
    for r in unconstrained_regions {
        let translated_region = ty_translator.translate_region_var(r)?;
        if let Some(early_region_idx) = early_region_map.get(&translated_region) {
            let scope = ty_translator.scope.borrow();

            let early_lft_vid = scope.lifetime_scope.early_regions[*early_region_idx].unwrap();
            let early_lft_name = &scope.lifetime_scope.region_names[&early_lft_vid];
            unconstrained_annotations
                .push(radium::Annotation::CopyLftName(early_lft_name.to_owned(), translated_region));

            inclusion_tracker.add_static_inclusion(r, early_lft_vid, midpoint);
            inclusion_tracker.add_static_inclusion(early_lft_vid, r, midpoint);
        } else {
            remaining_regions.insert(r);
        }
    }
    Ok((unconstrained_annotations, remaining_regions))
}
