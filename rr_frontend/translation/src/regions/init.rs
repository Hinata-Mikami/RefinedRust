// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides functionality for generating initial lifetime constraints.

use std::collections::{BTreeMap, HashMap};

use log::info;
use rr_rustc_interface::middle::{mir, ty};

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::{polonius_info, Environment};
use crate::regions::arg_folder::instantiate_open;
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::regions::region_bi_folder::RegionBiFolder;
use crate::regions::EarlyLateRegionMap;
use crate::traits::resolution;

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
                ty::RegionKind::ReEarlyParam(r) => {
                    let name = strip_coq_ident(r.name.as_str());
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
                let mut region_name = strip_coq_ident(sym.as_str());
                if region_name == "_" {
                    region_name = next_id.as_usize().to_string();
                    universal_lifetimes.insert(next_id, format!("ulft_{}", region_name));
                } else {
                    universal_lifetimes.insert(next_id, format!("ulft_{}", region_name));
                    lifetime_names.insert(region_name, next_id);
                }
            },
            ty::BoundRegionKind::BrAnon => {
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
    let (late_sig, _late_region_map) = env.tcx().instantiate_bound_regions(sig, &mut folder);

    // replace early bound variables
    let inputs: Vec<_> = late_sig
        .inputs()
        .iter()
        .map(|ty| instantiate_open(*ty, env.tcx(), subst_early_bounds))
        .collect();

    let output = instantiate_open(late_sig.output(), env.tcx(), subst_early_bounds);

    info!("Computed late region map {region_substitution_late:?}");

    let region_map = EarlyLateRegionMap::new(
        region_substitution_early,
        vec![region_substitution_late],
        universal_lifetimes,
        lifetime_names,
    );
    (inputs, output, region_map)
}

/// At the start of the function, there's a universal (placeholder) region for reference argument.
/// These get subsequently relabeled.
/// Given the relabeled region, find the original placeholder region.
pub fn find_placeholder_region_for(r: ty::RegionVid, info: &PoloniusInfo) -> Option<ty::RegionVid> {
    let root_location = mir::Location {
        block: mir::BasicBlock::from_u32(0),
        statement_index: 0,
    };
    let root_point = info.interner.get_point_index(&facts::Point {
        location: root_location,
        typ: facts::PointType::Start,
    });

    for (r1, r2, p) in &info.borrowck_in_facts.subset_base {
        let k1 = info.get_region_kind(*r1);
        if *p == root_point && *r2 == r && matches!(k1, polonius_info::RegionKind::Universal(_)) {
            info!("find placeholder region for: {:?} ⊑ {:?} = r = {:?}", r1, r2, r);
            return Some(*r1);
        }
    }
    None
}

/// Filter the "interesting" constraints between universal lifetimes that need to hold
/// (this does not include the constraints that need to hold for all universal lifetimes,
/// e.g. that they outlive the function lifetime and are outlived by 'static).
pub fn get_relevant_universal_constraints<'a>(
    lifetime_scope: &EarlyLateRegionMap,
    inclusion_tracker: &mut InclusionTracker,
    info: &'a PoloniusInfo<'a, '_>,
) -> Vec<(radium::UniversalLft, radium::UniversalLft)> {
    let input_facts = &info.borrowck_in_facts;
    let placeholder_subset = &input_facts.known_placeholder_subset;

    let root_location = mir::Location {
        block: mir::BasicBlock::from_u32(0),
        statement_index: 0,
    };
    let root_point = info.interner.get_point_index(&facts::Point {
        location: root_location,
        typ: facts::PointType::Start,
    });

    let mut universal_constraints = Vec::new();

    for (r1, r2) in placeholder_subset {
        if let polonius_info::RegionKind::Universal(uk1) = info.get_region_kind(*r1) {
            if let polonius_info::RegionKind::Universal(uk2) = info.get_region_kind(*r2) {
                // if LHS is static, ignore.
                if uk1 == polonius_info::UniversalRegionKind::Static {
                    continue;
                }
                // if RHS is the function lifetime, ignore
                if uk2 == polonius_info::UniversalRegionKind::Function {
                    continue;
                }

                let to_universal = || {
                    let x = lifetime_scope.lookup_region_with_kind(uk1, *r2)?;
                    let y = lifetime_scope.lookup_region_with_kind(uk2, *r1)?;
                    Some((x, y))
                };
                // else, add this constraint
                // for the purpose of this analysis, it is fine to treat it as a dynamic inclusion
                if let Some((x, y)) = to_universal() {
                    inclusion_tracker.add_dynamic_inclusion(*r1, *r2, root_point);
                    universal_constraints.push((x, y));
                };
            }
        }
    }
    universal_constraints
}

/// Get additional constraints between capture places and value lifetimes that hold at the
/// beginning of the closure.
pub fn get_initial_closure_constraints<'a>(
    info: &'a PoloniusInfo<'a, '_>,
    inclusion_tracker: &mut InclusionTracker<'a, '_>,
) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
    let input_facts = &info.borrowck_in_facts;

    let root_location = mir::Location {
        block: mir::BasicBlock::from_u32(0),
        statement_index: 0,
    };
    let root_point = info.interner.get_point_index(&facts::Point {
        location: root_location,
        typ: facts::PointType::Mid,
    });

    let mut closure_constraints = Vec::new();

    for (r1, r2, p) in &input_facts.subset_base {
        if *p == root_point && input_facts.subset_base.contains(&(*r2, *r1, *p)) {
            let lft1 = info.mk_atomic_region(*r1);
            let lft2 = info.mk_atomic_region(*r2);

            if lft1.is_place() && lft2.is_value() {
                inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
                inclusion_tracker.add_static_inclusion(*r2, *r1, root_point);

                closure_constraints.push((lft1, lft2));
            }
        }
    }
    closure_constraints
}

/// Determine initial constraints between universal regions and local place regions.
/// Returns an initial mapping for the name map that initializes place regions of arguments
/// with universals.
/// We structurally compare the regions in the function signature args `sig_args` with the regions
/// in the body's `local_args`.
pub fn get_initial_universal_arg_constraints<'a, 'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    info: &'a PoloniusInfo<'a, 'tcx>,
    inclusion_tracker: &mut InclusionTracker<'a, 'tcx>,
    sig_args: &[ty::Ty<'tcx>],
    local_args: &[ty::Ty<'tcx>],
) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
    info!("computing initial universal constraints for {sig_args:?} and {local_args:?}");

    // Polonius generates a base subset constraint uregion ⊑ pregion.
    // We turn that into pregion = uregion, as we do strong updates at the top-level.
    assert!(sig_args.len() == local_args.len());

    // compute the mapping
    let mut unifier = InitialPoloniusUnifier::new();
    for (a1, a2) in local_args.iter().zip(sig_args.iter()) {
        let a1_normalized = resolution::normalize_type(tcx, param_env, *a1).unwrap();
        let a2_normalized = resolution::normalize_type(tcx, param_env, *a2).unwrap();
        unifier.map_tys(a1_normalized, a2_normalized);
    }

    // add the inclusions to the inclusion tracker

    let root_location = mir::Location {
        block: mir::BasicBlock::from_u32(0),
        statement_index: 0,
    };
    let root_point = info.interner.get_point_index(&facts::Point {
        location: root_location,
        typ: facts::PointType::Start,
    });

    let mut initial_arg_mapping = Vec::new();
    for (l, s) in unifier.get_result() {
        inclusion_tracker.add_static_inclusion(s, l, root_point);
        inclusion_tracker.add_static_inclusion(l, s, root_point);

        let lft1 = info.mk_atomic_region(l);
        let lft2 = info.mk_atomic_region(s);
        initial_arg_mapping.push((lft2, lft1));
    }

    initial_arg_mapping
}

pub struct InitialPoloniusUnifier {
    mapping: HashMap<Region, Region>,
}
impl InitialPoloniusUnifier {
    pub fn new() -> Self {
        Self {
            mapping: HashMap::new(),
        }
    }

    pub fn get_result(self) -> HashMap<Region, Region> {
        self.mapping
    }
}
impl<'tcx> RegionBiFolder<'tcx> for InitialPoloniusUnifier {
    fn map_regions(&mut self, r1: ty::Region<'tcx>, r2: ty::Region<'tcx>) {
        if let ty::RegionKind::ReVar(l1) = *r1 {
            if let ty::RegionKind::ReVar(l2) = *r2 {
                if let Some(l22) = self.mapping.get(&l1) {
                    assert_eq!(l2, *l22);
                } else {
                    self.mapping.insert(l1, l2);
                }
            }
        }
    }
}
