// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
use std::iter;

use log::info;

use crate::base::*;
use crate::environment::polonius_info::{self, PoloniusInfo};

#[derive(Clone, Copy, Debug)]
pub(crate) enum DynamicInclusion {
    /// Emit `ExtendLft` for the contained region when the reverse inclusion is static.
    ExtendLft(polonius_info::AtomicRegion),
    /// Emit `DynIncludeLft` for the two contained semantic lifetime names.
    IncludeLft(polonius_info::AtomicRegion, polonius_info::AtomicRegion),
}

#[derive(Debug)]
pub(crate) struct MutualDynamicInclusion {
    pub r1: Region,
    pub r2: Region,
    pub point: PointIndex,
}

type Inclusion<R> = (R, R);

struct GuaranteedStates<R, P> {
    /// Regions guaranteed to have semantic lifetime names after predecessor-edge effects, but
    /// before the point-local barrier and all point-local effects.
    incoming_known_regions: BTreeMap<P, BTreeSet<R>>,
    /// Inclusions after the point-local barrier and ordinary static effects, but before structural
    /// shared-reborrow effects. This snapshot prevents a shared reborrow from justifying itself.
    pre_shared_reborrow_inclusions: BTreeMap<P, BTreeSet<Inclusion<R>>>,
    /// Known regions at the same phase as `pre_shared_reborrow_inclusions`.
    pre_shared_reborrow_known_regions: BTreeMap<P, BTreeSet<R>>,
    /// Inclusions after structural shared-reborrow effects, but before dynamic ensure-actions.
    /// Dynamic annotation minimality is decided from this snapshot.
    pre_dynamic_inclusions: BTreeMap<P, BTreeSet<Inclusion<R>>>,
    /// Known regions at the same phase as `pre_dynamic_inclusions`.
    pre_dynamic_known_regions: BTreeMap<P, BTreeSet<R>>,
    /// Inclusions guaranteed after every point-local effect, including dynamic ensure-actions.
    inclusions: BTreeMap<P, BTreeSet<Inclusion<R>>>,
    /// Regions guaranteed to have semantic lifetime names after every point-local effect.
    known_regions: BTreeMap<P, BTreeSet<R>>,
}

impl<R, P> Default for GuaranteedStates<R, P> {
    fn default() -> Self {
        Self {
            incoming_known_regions: BTreeMap::new(),
            pre_shared_reborrow_inclusions: BTreeMap::new(),
            pre_shared_reborrow_known_regions: BTreeMap::new(),
            pre_dynamic_inclusions: BTreeMap::new(),
            pre_dynamic_known_regions: BTreeMap::new(),
            inclusions: BTreeMap::new(),
            known_regions: BTreeMap::new(),
        }
    }
}

/// Compute facts guaranteed to hold at each phase of every CFG point.
///
/// Transfer order is edge pre-barriers, edge additions, edge barriers, point-local barriers,
/// ordinary static/known effects, structural shared-reborrow effects, and finally dynamic
/// ensure-actions. At joins, only facts present on every incoming edge are retained. Initializing
/// non-root points with the finite universe of possible facts computes the greatest fixed point
/// required by a must analysis. Entry points instead start with `entry_inclusions`, modeling the
/// implicit function-entry predecessor so that backedges cannot establish facts on first entry.
fn compute_guaranteed_states_with_dynamic<R, P>(
    cfg_edges: impl IntoIterator<Item = (P, P)>,
    entry_points: impl IntoIterator<Item = P>,
    entry_inclusions: impl IntoIterator<Item = (R, R)>,
    static_inclusions: impl IntoIterator<Item = (R, R, P)>,
    shared_reborrow_static_inclusions: impl IntoIterator<Item = (R, R, P)>,
    dynamic_inclusions: impl IntoIterator<Item = (R, R, P)>,
    known_regions: impl IntoIterator<Item = (R, P)>,
    shared_reborrow_known_regions: impl IntoIterator<Item = (R, P)>,
    barriers: impl IntoIterator<Item = (R, P)>,
    edge_pre_barriers: impl IntoIterator<Item = (R, P, P)>,
    edge_barriers: impl IntoIterator<Item = (R, P, P)>,
    edge_inclusions: impl IntoIterator<Item = (R, R, P, P)>,
    edge_known_regions: impl IntoIterator<Item = (R, P, P)>,
) -> GuaranteedStates<R, P>
where
    R: Copy + Ord,
    P: Copy + Ord,
{
    let cfg_edges: Vec<_> = cfg_edges.into_iter().collect();
    let entry_points: BTreeSet<_> = entry_points.into_iter().collect();
    let mut entry_inclusions: BTreeSet<_> = entry_inclusions.into_iter().collect();
    close_transitively(&mut entry_inclusions);
    let entry_known: BTreeSet<_> = entry_inclusions.iter().flat_map(|(r1, r2)| [*r1, *r2]).collect();
    let mut local_static_inclusions: BTreeMap<P, BTreeSet<Inclusion<R>>> = BTreeMap::new();
    let mut local_shared_reborrow_static_inclusions: BTreeMap<P, BTreeSet<Inclusion<R>>> = BTreeMap::new();
    let mut local_dynamic_inclusions: BTreeMap<P, BTreeSet<Inclusion<R>>> = BTreeMap::new();
    let mut local_known: BTreeMap<P, BTreeSet<R>> = BTreeMap::new();
    let mut local_shared_reborrow_known: BTreeMap<P, BTreeSet<R>> = BTreeMap::new();
    let mut barriers_by_point: BTreeMap<P, BTreeSet<R>> = BTreeMap::new();
    let mut pre_barriers_by_edge: BTreeMap<(P, P), BTreeSet<R>> = BTreeMap::new();
    let mut barriers_by_edge: BTreeMap<(P, P), BTreeSet<R>> = BTreeMap::new();
    let mut inclusions_by_edge: BTreeMap<(P, P), BTreeSet<Inclusion<R>>> = BTreeMap::new();
    let mut known_by_edge: BTreeMap<(P, P), BTreeSet<R>> = BTreeMap::new();
    let mut predecessors: BTreeMap<P, BTreeSet<P>> = BTreeMap::new();
    let mut points = BTreeSet::new();

    for (from, to) in cfg_edges {
        points.insert(from);
        points.insert(to);
        predecessors.entry(to).or_default().insert(from);
        predecessors.entry(from).or_default();
    }
    for (r1, r2, point) in static_inclusions {
        points.insert(point);
        local_static_inclusions.entry(point).or_default().insert((r1, r2));
        local_known.entry(point).or_default().extend([r1, r2]);
    }
    for (r1, r2, point) in shared_reborrow_static_inclusions {
        points.insert(point);
        local_shared_reborrow_static_inclusions.entry(point).or_default().insert((r1, r2));
    }
    for (r1, r2, point) in dynamic_inclusions {
        points.insert(point);
        local_dynamic_inclusions.entry(point).or_default().insert((r1, r2));
    }
    for (region, point) in known_regions {
        points.insert(point);
        local_known.entry(point).or_default().insert(region);
    }
    for (region, point) in shared_reborrow_known_regions {
        points.insert(point);
        local_shared_reborrow_known.entry(point).or_default().insert(region);
    }
    for (region, point) in barriers {
        points.insert(point);
        barriers_by_point.entry(point).or_default().insert(region);
    }
    for (region, from, to) in edge_barriers {
        points.extend([from, to]);
        barriers_by_edge.entry((from, to)).or_default().insert(region);
    }
    for (region, from, to) in edge_pre_barriers {
        points.extend([from, to]);
        pre_barriers_by_edge.entry((from, to)).or_default().insert(region);
    }
    for (r1, r2, from, to) in edge_inclusions {
        points.extend([from, to]);
        inclusions_by_edge.entry((from, to)).or_default().insert((r1, r2));
        known_by_edge.entry((from, to)).or_default().extend([r1, r2]);
    }
    for (region, from, to) in edge_known_regions {
        points.extend([from, to]);
        known_by_edge.entry((from, to)).or_default().insert(region);
    }

    let mut possible_inclusions: BTreeSet<_> = local_static_inclusions
        .values()
        .chain(local_shared_reborrow_static_inclusions.values())
        .chain(local_dynamic_inclusions.values())
        .chain(inclusions_by_edge.values())
        .flat_map(|inclusions| inclusions.iter().copied())
        .collect();
    possible_inclusions.extend(&entry_inclusions);
    close_transitively(&mut possible_inclusions);
    let possible_known = local_known
        .values()
        .chain(local_shared_reborrow_known.values())
        .chain(known_by_edge.values())
        .flat_map(|regions| regions.iter().copied())
        .chain(
            local_dynamic_inclusions
                .values()
                .flat_map(|inclusions| inclusions.iter().flat_map(|(r1, r2)| [*r1, *r2])),
        )
        .collect::<BTreeSet<_>>();

    let mut states = GuaranteedStates::default();
    for point in &points {
        if !entry_points.contains(point) && predecessors.get(point).is_some_and(|preds| !preds.is_empty()) {
            states.incoming_known_regions.insert(*point, possible_known.clone());
            states.pre_shared_reborrow_inclusions.insert(*point, possible_inclusions.clone());
            states.pre_shared_reborrow_known_regions.insert(*point, possible_known.clone());
            states.pre_dynamic_inclusions.insert(*point, possible_inclusions.clone());
            states.pre_dynamic_known_regions.insert(*point, possible_known.clone());
            states.inclusions.insert(*point, possible_inclusions.clone());
            states.known_regions.insert(*point, possible_known.clone());
        } else {
            states.incoming_known_regions.insert(*point, BTreeSet::new());
            states.pre_shared_reborrow_inclusions.insert(*point, BTreeSet::new());
            states.pre_shared_reborrow_known_regions.insert(*point, BTreeSet::new());
            states.pre_dynamic_inclusions.insert(*point, BTreeSet::new());
            states.pre_dynamic_known_regions.insert(*point, BTreeSet::new());
            states.inclusions.insert(*point, BTreeSet::new());
            states.known_regions.insert(*point, BTreeSet::new());
        }
    }

    loop {
        let mut changed = false;
        for point in &points {
            let preds = predecessors.get(point).into_iter().flatten().copied();
            let (incoming_inclusions, incoming_known) = if entry_points.contains(point) {
                // This is the implicit function-entry predecessor. Backedges to the entry block
                // must be joined with its empty state rather than replacing it.
                (entry_inclusions.clone(), entry_known.clone())
            } else {
                (
                    intersect_predecessors(
                        preds.clone(),
                        *point,
                        &states.inclusions,
                        &inclusions_by_edge,
                        &pre_barriers_by_edge,
                        &barriers_by_edge,
                        |(r1, r2), killed| !killed.contains(r1) && !killed.contains(r2),
                        close_transitively,
                    ),
                    intersect_predecessors(
                        preds,
                        *point,
                        &states.known_regions,
                        &known_by_edge,
                        &pre_barriers_by_edge,
                        &barriers_by_edge,
                        |region, killed| !killed.contains(region),
                        |_| {},
                    ),
                )
            };

            let mut point_inclusions = incoming_inclusions;
            let mut point_known = incoming_known.clone();
            if let Some(killed) = barriers_by_point.get(point) {
                point_inclusions.retain(|(r1, r2)| !killed.contains(r1) && !killed.contains(r2));
                point_known.retain(|region| !killed.contains(region));
            }
            if let Some(local) = local_static_inclusions.get(point) {
                point_inclusions.extend(local);
                close_transitively(&mut point_inclusions);
            }
            if let Some(local) = local_known.get(point) {
                point_known.extend(local);
            }
            let pre_shared_reborrow_inclusions = point_inclusions.clone();
            let pre_shared_reborrow_known = point_known.clone();
            if let Some(local) = local_shared_reborrow_static_inclusions.get(point) {
                point_inclusions.extend(local);
                close_transitively(&mut point_inclusions);
                point_known.extend(local.iter().flat_map(|(r1, r2)| [*r1, *r2]));
            }
            if let Some(local) = local_shared_reborrow_known.get(point) {
                point_known.extend(local);
            }
            let pre_dynamic_inclusions = point_inclusions.clone();
            let pre_dynamic_known = point_known.clone();
            if let Some(local) = local_dynamic_inclusions.get(point) {
                point_inclusions.extend(local);
                close_transitively(&mut point_inclusions);
                point_known.extend(local.iter().flat_map(|(r1, r2)| [*r1, *r2]));
            }

            if states.incoming_known_regions.get(point) != Some(&incoming_known) {
                states.incoming_known_regions.insert(*point, incoming_known);
                changed = true;
            }
            if states.pre_shared_reborrow_inclusions.get(point) != Some(&pre_shared_reborrow_inclusions) {
                states.pre_shared_reborrow_inclusions.insert(*point, pre_shared_reborrow_inclusions);
                changed = true;
            }
            if states.pre_dynamic_inclusions.get(point) != Some(&pre_dynamic_inclusions) {
                states.pre_dynamic_inclusions.insert(*point, pre_dynamic_inclusions);
                changed = true;
            }
            if states.pre_shared_reborrow_known_regions.get(point) != Some(&pre_shared_reborrow_known) {
                states.pre_shared_reborrow_known_regions.insert(*point, pre_shared_reborrow_known);
                changed = true;
            }
            if states.pre_dynamic_known_regions.get(point) != Some(&pre_dynamic_known) {
                states.pre_dynamic_known_regions.insert(*point, pre_dynamic_known);
                changed = true;
            }
            if states.inclusions.get(point) != Some(&point_inclusions) {
                states.inclusions.insert(*point, point_inclusions);
                changed = true;
            }
            if states.known_regions.get(point) != Some(&point_known) {
                states.known_regions.insert(*point, point_known);
                changed = true;
            }
        }
        if !changed {
            return states;
        }
    }
}

#[cfg(test)]
fn compute_guaranteed_states<R, P>(
    cfg_edges: impl IntoIterator<Item = (P, P)>,
    inclusions: impl IntoIterator<Item = (R, R, P)>,
    known_regions: impl IntoIterator<Item = (R, P)>,
    barriers: impl IntoIterator<Item = (R, P)>,
    edge_pre_barriers: impl IntoIterator<Item = (R, P, P)>,
    edge_barriers: impl IntoIterator<Item = (R, P, P)>,
    edge_inclusions: impl IntoIterator<Item = (R, R, P, P)>,
    edge_known_regions: impl IntoIterator<Item = (R, P, P)>,
) -> GuaranteedStates<R, P>
where
    R: Copy + Ord,
    P: Copy + Ord,
{
    compute_guaranteed_states_with_dynamic(
        cfg_edges,
        [],
        [],
        inclusions,
        iter::empty(),
        iter::empty(),
        known_regions,
        iter::empty(),
        barriers,
        edge_pre_barriers,
        edge_barriers,
        edge_inclusions,
        edge_known_regions,
    )
}

fn intersect_predecessors<T, R, P>(
    predecessors: impl IntoIterator<Item = P>,
    point: P,
    states: &BTreeMap<P, BTreeSet<T>>,
    additions: &BTreeMap<(P, P), BTreeSet<T>>,
    pre_barriers: &BTreeMap<(P, P), BTreeSet<R>>,
    barriers: &BTreeMap<(P, P), BTreeSet<R>>,
    retain: impl Fn(&T, &BTreeSet<R>) -> bool,
    finalize: impl Fn(&mut BTreeSet<T>),
) -> BTreeSet<T>
where
    T: Copy + Ord,
    R: Ord,
    P: Copy + Ord,
{
    let mut predecessors = predecessors.into_iter();
    let Some(first) = predecessors.next() else {
        return BTreeSet::new();
    };
    let edge_state = |predecessor| {
        let mut state = states.get(&predecessor).cloned().unwrap_or_default();
        if let Some(killed) = pre_barriers.get(&(predecessor, point)) {
            state.retain(|fact| retain(fact, killed));
        }
        if let Some(added) = additions.get(&(predecessor, point)) {
            state.extend(added);
            finalize(&mut state);
        }
        if let Some(killed) = barriers.get(&(predecessor, point)) {
            state.retain(|fact| retain(fact, killed));
        }
        state
    };
    let mut intersection = edge_state(first);
    for predecessor in predecessors {
        let state = edge_state(predecessor);
        intersection.retain(|fact| state.contains(fact));
    }
    intersection
}

fn close_transitively<R>(inclusions: &mut BTreeSet<Inclusion<R>>)
where
    R: Copy + Ord,
{
    loop {
        let current: Vec<_> = inclusions.iter().copied().collect();
        let mut changed = false;
        for (r1, r2) in &current {
            for (s1, r3) in &current {
                if r2 == s1 {
                    changed |= inclusions.insert((*r1, *r3));
                }
            }
        }
        if !changed {
            return;
        }
    }
}

/// Tracks inclusions guaranteed to hold in the flow-sensitive `RefinedRust` context at each point.
/// Static and dynamically established inclusions are kept separate because they require different
/// annotations, but both use the same must-dataflow semantics.
pub(crate) struct InclusionTracker<'a, 'tcx> {
    /// Polonius facts and CFG used to solve the registered effects.
    info: &'a PoloniusInfo<'a, 'tcx>,
    /// Static inclusions supplied by the implicit function-entry predecessor. These include
    /// universal and argument-region relationships and are visible before the first MIR effect.
    entry_static_incl_base: Vec<(Region, Region)>,
    /// Unconditional point-local static inclusions. They are applied after the point barrier and
    /// make both endpoint lifetime names known.
    static_incl_base: Vec<(Region, Region, PointIndex)>,
    /// Structural access-to-target inclusions established by shared reborrows. They are applied
    /// only after shared-reborrow decisions so they cannot define their own source or target.
    shared_reborrow_static_incl_base: Vec<(Region, Region, PointIndex)>,
    /// Dynamic inclusion requirements. Each acts as an order-independent ensure-action: it emits
    /// an annotation only if absent before this phase, but guarantees the inclusion afterward.
    dynamic_incl_base: Vec<(Region, Region, PointIndex)>,
    /// Point-local definitions of semantic lifetime names established before shared reborrows.
    known_region_base: Vec<(Region, PointIndex)>,
    /// Lifetime names initialized by shared-reborrow annotations. They become known after the
    /// shared-reborrow decision and are visible to later effects and CFG points.
    shared_reborrow_known_region_base: Vec<(Region, PointIndex)>,
    /// Point-local strong-update kills, applied before all point-local additions.
    barriers: Vec<(Region, PointIndex)>,
    /// Edge-local kills applied before edge additions. These model overwriting the old edge state
    /// while still allowing the edge operation to define a replacement value.
    edge_pre_barriers: Vec<(Region, PointIndex, PointIndex)>,
    /// Edge-local kills applied after edge additions, notably lifetime deaths on that edge.
    edge_barriers: Vec<(Region, PointIndex, PointIndex)>,
    /// Static inclusions established only while traversing a particular CFG edge. Their endpoints
    /// also become known on that edge.
    edge_static_incl_base: Vec<(Region, Region, PointIndex, PointIndex)>,
    /// Semantic lifetime names initialized only while traversing a particular CFG edge.
    edge_known_region_base: Vec<(Region, PointIndex, PointIndex)>,
    /// Cached must-states excluding dynamic ensure-actions.
    static_states: Option<GuaranteedStates<Region, PointIndex>>,
    /// Cached must-states including every registered effect.
    full_states: Option<GuaranteedStates<Region, PointIndex>>,
}

impl<'a, 'tcx: 'a> InclusionTracker<'a, 'tcx> {
    pub(crate) const fn new(info: &'a PoloniusInfo<'a, 'tcx>) -> Self {
        Self {
            info,
            entry_static_incl_base: Vec::new(),
            static_incl_base: Vec::new(),
            shared_reborrow_static_incl_base: Vec::new(),
            dynamic_incl_base: Vec::new(),
            known_region_base: Vec::new(),
            shared_reborrow_known_region_base: Vec::new(),
            barriers: Vec::new(),
            edge_pre_barriers: Vec::new(),
            edge_barriers: Vec::new(),
            edge_static_incl_base: Vec::new(),
            edge_known_region_base: Vec::new(),
            static_states: None,
            full_states: None,
        }
    }

    pub(crate) const fn info(&self) -> &'a PoloniusInfo<'a, 'tcx> {
        self.info
    }

    /// Register an unconditional point-local static inclusion `r1 ⊑ r2`.
    pub(crate) fn add_static_inclusion(&mut self, r1: Region, r2: Region, point: PointIndex) {
        self.static_incl_base.push((r1, r2, point));
        self.static_states = None;
        self.full_states = None;
    }

    /// Register `r1 ⊑ r2` in the implicit function-entry predecessor state.
    pub(crate) fn add_entry_static_inclusion(&mut self, r1: Region, r2: Region) {
        self.entry_static_incl_base.push((r1, r2));
        self.static_states = None;
        self.full_states = None;
    }

    /// Register a structural shared-reborrow inclusion after the pre-shared snapshot.
    pub(crate) fn add_shared_reborrow_static_inclusion(&mut self, r1: Region, r2: Region, point: PointIndex) {
        self.shared_reborrow_static_incl_base.push((r1, r2, point));
        self.static_states = None;
        self.full_states = None;
    }

    /// Register a dynamic ensure-action requiring `r1 ⊑ r2` at `point`.
    pub(crate) fn add_dynamic_inclusion(&mut self, r1: Region, r2: Region, point: PointIndex) {
        self.dynamic_incl_base.push((r1, r2, point));
        self.full_states = None;
    }

    /// Register that `region` has a semantic lifetime name after ordinary effects at `point`.
    pub(crate) fn add_known_region(&mut self, region: Region, point: PointIndex) {
        self.known_region_base.push((region, point));
        self.static_states = None;
        self.full_states = None;
    }

    /// Register a name initialized by the shared-reborrow effect at `point`.
    pub(crate) fn add_shared_reborrow_known_region(&mut self, region: Region, point: PointIndex) {
        self.shared_reborrow_known_region_base.push((region, point));
        self.static_states = None;
        self.full_states = None;
    }

    /// Kill all knowledge involving `region` before applying effects at `point`.
    pub(crate) fn add_barrier(&mut self, region: Region, point: PointIndex) {
        self.barriers.push((region, point));
        self.static_states = None;
        self.full_states = None;
    }

    /// Kill all knowledge involving `region` while transferring state along `from -> to`.
    pub(crate) fn add_edge_barrier(&mut self, region: Region, from: PointIndex, to: PointIndex) {
        self.edge_barriers.push((region, from, to));
        self.static_states = None;
        self.full_states = None;
    }

    /// Kill knowledge involving `region` before additions on the edge `from -> to`.
    pub(crate) fn add_edge_pre_barrier(&mut self, region: Region, from: PointIndex, to: PointIndex) {
        self.edge_pre_barriers.push((region, from, to));
        self.static_states = None;
        self.full_states = None;
    }

    /// Establish `r1 ⊑ r2` only on the edge `from -> to`.
    pub(crate) fn add_edge_static_inclusion(
        &mut self,
        r1: Region,
        r2: Region,
        from: PointIndex,
        to: PointIndex,
    ) {
        self.edge_static_incl_base.push((r1, r2, from, to));
        self.static_states = None;
        self.full_states = None;
    }

    /// Register a semantic lifetime name initialized only on the edge `from -> to`.
    pub(crate) fn add_edge_known_region(&mut self, region: Region, from: PointIndex, to: PointIndex) {
        self.edge_known_region_base.push((region, from, to));
        self.static_states = None;
        self.full_states = None;
    }

    fn recompute_static(&mut self) {
        self.static_states = Some(compute_guaranteed_states_with_dynamic(
            self.info.cfg_edges(),
            [self.info.entry_point()],
            self.entry_static_incl_base.iter().copied(),
            self.static_incl_base.iter().copied(),
            self.shared_reborrow_static_incl_base.iter().copied(),
            [],
            self.known_region_base.iter().copied(),
            self.shared_reborrow_known_region_base.iter().copied(),
            self.barriers.iter().copied(),
            self.edge_pre_barriers.iter().copied(),
            self.edge_barriers.iter().copied(),
            self.edge_static_incl_base.iter().copied(),
            self.edge_known_region_base.iter().copied(),
        ));
    }

    pub(crate) fn recompute(&mut self) {
        self.full_states = Some(compute_guaranteed_states_with_dynamic(
            self.info.cfg_edges(),
            [self.info.entry_point()],
            self.entry_static_incl_base.iter().copied(),
            self.static_incl_base.iter().copied(),
            self.shared_reborrow_static_incl_base.iter().copied(),
            self.dynamic_incl_base.iter().copied(),
            self.known_region_base.iter().copied(),
            self.shared_reborrow_known_region_base.iter().copied(),
            self.barriers.iter().copied(),
            self.edge_pre_barriers.iter().copied(),
            self.edge_barriers.iter().copied(),
            self.edge_static_incl_base.iter().copied(),
            self.edge_known_region_base.iter().copied(),
        ));
    }

    pub(crate) fn is_region_known_before_dynamic(&mut self, region: Region, point: PointIndex) -> bool {
        if self.full_states.is_none() {
            self.recompute();
        }
        self.full_states
            .as_ref()
            .and_then(|states| states.pre_dynamic_known_regions.get(&point))
            .is_some_and(|regions| regions.contains(&region))
    }

    pub(crate) fn is_region_known_before_effects(&mut self, region: Region, point: PointIndex) -> bool {
        if self.full_states.is_none() {
            self.recompute();
        }
        self.full_states
            .as_ref()
            .and_then(|states| states.incoming_known_regions.get(&point))
            .is_some_and(|regions| regions.contains(&region))
    }

    pub(crate) fn is_region_known_before_shared_reborrow(
        &mut self,
        region: Region,
        point: PointIndex,
    ) -> bool {
        if self.full_states.is_none() {
            self.recompute();
        }
        self.full_states
            .as_ref()
            .and_then(|states| states.pre_shared_reborrow_known_regions.get(&point))
            .is_some_and(|regions| regions.contains(&region))
    }

    pub(crate) fn check_inclusion_before_shared_reborrow(
        &mut self,
        r1: Region,
        r2: Region,
        point: PointIndex,
    ) -> bool {
        if self.full_states.is_none() {
            self.recompute();
        }
        self.full_states
            .as_ref()
            .and_then(|states| states.pre_shared_reborrow_inclusions.get(&point))
            .is_some_and(|inclusions| inclusions.contains(&(r1, r2)))
    }

    pub(crate) fn regions_included_in_before_dynamic(
        &mut self,
        region: Region,
        point: PointIndex,
    ) -> BTreeSet<Region> {
        if self.full_states.is_none() {
            self.recompute();
        }
        self.full_states
            .as_ref()
            .and_then(|states| states.pre_dynamic_inclusions.get(&point))
            .into_iter()
            .flatten()
            .filter_map(|(source, destination)| (*destination == region).then_some(*source))
            .collect()
    }

    pub(crate) fn check_static_inclusion(&mut self, r1: Region, r2: Region, point: PointIndex) -> bool {
        if r1 == r2 {
            return true;
        }
        if self.static_states.is_none() {
            self.recompute_static();
        }
        self.static_states
            .as_ref()
            .and_then(|states| states.inclusions.get(&point))
            .is_some_and(|inclusions| inclusions.contains(&(r1, r2)))
    }

    fn generate_dyn_inclusion(
        &mut self,
        stmt_annots: &mut Vec<DynamicInclusion>,
        inclusions: &mut BTreeSet<Inclusion<Region>>,
        r1: Region,
        r2: Region,
        point: PointIndex,
    ) -> Result<(), MutualDynamicInclusion> {
        if r1 == r2 || inclusions.contains(&(r1, r2)) {
            return Ok(());
        }

        if self.check_static_inclusion(r2, r1, point) {
            // TODO: recover the syntactic inclusion path instead of assuming r1 ⊑ₗ [r2].
            stmt_annots.push(DynamicInclusion::ExtendLft(self.info.mk_atomic_region(r1)));
        } else {
            if inclusions.contains(&(r2, r1)) {
                return Err(MutualDynamicInclusion { r1, r2, point });
            }
            // Lifetime annotations use the opposite orientation from Polonius origins.
            stmt_annots.push(DynamicInclusion::IncludeLft(
                self.info.mk_atomic_region(r2),
                self.info.mk_atomic_region(r1),
            ));
        }
        inclusions.insert((r1, r2));
        close_transitively(inclusions);
        Ok(())
    }

    pub(crate) fn register_dynamic_inclusions(&mut self, incls: &BTreeSet<(Region, Region, PointIndex)>) {
        for (r1, r2, point) in incls {
            self.add_dynamic_inclusion(*r1, *r2, *point);
        }
    }

    pub(crate) fn generate_dyn_inclusions(
        &mut self,
        incls: &BTreeSet<(Region, Region, PointIndex)>,
    ) -> Result<Vec<DynamicInclusion>, MutualDynamicInclusion> {
        info!("Generating dynamic inclusions {:?}", incls);
        if self.full_states.is_none() {
            self.recompute();
        }
        let mut inclusions_by_point: BTreeMap<_, _> = incls
            .iter()
            .map(|(_, _, point)| {
                let inclusions = self
                    .full_states
                    .as_ref()
                    .and_then(|states| states.pre_dynamic_inclusions.get(point))
                    .cloned()
                    .unwrap_or_default();
                (*point, inclusions)
            })
            .collect();
        let mut stmt_annots = Vec::new();

        // RefinedRust cannot establish equality by adding two dynamic inclusions. Reject the pair
        // before generating either annotation; a statically known direction is handled by
        // `ExtendLft` below and is therefore supported.
        for (r1, r2, point) in incls {
            if r1 < r2
                && incls.contains(&(*r2, *r1, *point))
                && !inclusions_by_point[point].contains(&(*r1, *r2))
                && !inclusions_by_point[point].contains(&(*r2, *r1))
            {
                return Err(MutualDynamicInclusion {
                    r1: *r1,
                    r2: *r2,
                    point: *point,
                });
            }
        }

        for (r1, r2, point) in incls {
            self.generate_dyn_inclusion(
                &mut stmt_annots,
                inclusions_by_point.get_mut(point).unwrap(),
                *r1,
                *r2,
                *point,
            )?;
        }

        Ok(stmt_annots)
    }
}

#[cfg(test)]
mod tests {
    use super::{compute_guaranteed_states, compute_guaranteed_states_with_dynamic};

    #[test]
    fn dynamic_requirements_do_not_justify_themselves() {
        let states = compute_guaranteed_states_with_dynamic(
            [(0, 1), (1, 1)],
            [],
            [],
            [],
            [],
            [('a', 'b', 1)],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(!states.pre_dynamic_inclusions[&1].contains(&('a', 'b')));
        assert!(states.inclusions[&1].contains(&('a', 'b')));
    }

    #[test]
    fn upstream_dynamic_requirements_suppress_redundant_annotations() {
        let states = compute_guaranteed_states_with_dynamic(
            [(0, 1), (1, 2)],
            [],
            [],
            [],
            [],
            [('a', 'b', 1), ('a', 'b', 2)],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(!states.pre_dynamic_inclusions[&1].contains(&('a', 'b')));
        assert!(states.pre_dynamic_inclusions[&2].contains(&('a', 'b')));
    }

    #[test]
    fn dynamic_requirements_are_joined_as_must_facts() {
        let edges = [(0, 1), (0, 2), (1, 3), (2, 3)];
        let one_branch = compute_guaranteed_states_with_dynamic(
            edges,
            [],
            [],
            [],
            [],
            [('a', 'b', 1)],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(!one_branch.pre_dynamic_inclusions[&3].contains(&('a', 'b')));

        let both_branches = compute_guaranteed_states_with_dynamic(
            edges,
            [],
            [],
            [],
            [],
            [('a', 'b', 1), ('a', 'b', 2)],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(both_branches.pre_dynamic_inclusions[&3].contains(&('a', 'b')));
    }

    #[test]
    fn local_initialization_is_absent_from_incoming_known_state() {
        let states = compute_guaranteed_states_with_dynamic(
            [(0, 1), (1, 2)],
            [],
            [],
            [],
            [],
            [],
            [('a', 1)],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(!states.incoming_known_regions[&1].contains(&'a'));
        assert!(states.known_regions[&1].contains(&'a'));
        assert!(states.incoming_known_regions[&2].contains(&'a'));
    }

    #[test]
    fn explicit_entry_starts_empty_even_with_a_backedge() {
        let states = compute_guaranteed_states_with_dynamic(
            [(0, 1), (1, 0)],
            [0],
            [],
            [],
            [],
            [('a', 'b', 1)],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(!states.pre_dynamic_inclusions[&0].contains(&('a', 'b')));
        assert!(!states.pre_dynamic_inclusions[&1].contains(&('a', 'b')));
    }

    #[test]
    fn entry_inclusions_are_visible_before_first_statement_effects() {
        let states = compute_guaranteed_states_with_dynamic(
            [(0, 1), (1, 0)],
            [0],
            [('u', 'p')],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
        );

        assert!(states.pre_dynamic_inclusions[&0].contains(&('u', 'p')));
        assert!(states.incoming_known_regions[&0].contains(&'u'));
        assert!(states.incoming_known_regions[&0].contains(&'p'));
    }

    #[test]
    fn shared_reborrow_initialization_does_not_justify_itself() {
        let states = compute_guaranteed_states_with_dynamic(
            [(0, 1)],
            [0],
            [],
            [],
            [('l', 'r', 0), ('r', 'l', 0)],
            [],
            [('l', 0)],
            [('r', 0)],
            [],
            [],
            [],
            [],
            [],
        );

        assert!(states.pre_shared_reborrow_known_regions[&0].contains(&'l'));
        assert!(!states.pre_shared_reborrow_known_regions[&0].contains(&'r'));
        assert!(states.known_regions[&0].contains(&'r'));
        assert!(states.inclusions[&0].contains(&('l', 'r')));
        assert!(states.incoming_known_regions[&1].contains(&'r'));
    }

    #[test]
    fn dynamic_registration_order_does_not_change_solved_states() {
        let solve = |requirements| {
            compute_guaranteed_states_with_dynamic(
                [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)],
                [0],
                [],
                [],
                [],
                requirements,
                [],
                [],
                [],
                [],
                [],
                [],
                [],
            )
        };
        let forward = solve([('a', 'b', 1), ('a', 'b', 2), ('b', 'c', 3), ('a', 'c', 4)]);
        let reverse = solve([('a', 'c', 4), ('b', 'c', 3), ('a', 'b', 2), ('a', 'b', 1)]);

        assert_eq!(forward.pre_dynamic_inclusions, reverse.pre_dynamic_inclusions);
        assert_eq!(forward.inclusions, reverse.inclusions);
        assert_eq!(forward.pre_dynamic_known_regions, reverse.pre_dynamic_known_regions);
        assert_eq!(forward.known_regions, reverse.known_regions);
    }

    #[test]
    fn joins_keep_only_inclusions_guaranteed_by_every_predecessor() {
        let states = compute_guaranteed_states(
            [(0, 1), (0, 2), (1, 3), (2, 3)],
            [('a', 'b', 1)],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(states.inclusions[&1].contains(&('a', 'b')));
        assert!(!states.inclusions[&3].contains(&('a', 'b')));

        let states = compute_guaranteed_states(
            [(0, 1), (0, 2), (1, 3), (2, 3)],
            [('a', 'b', 1), ('a', 'b', 2)],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(states.inclusions[&3].contains(&('a', 'b')));
    }

    #[test]
    fn joins_compare_transitively_closed_states() {
        let states = compute_guaranteed_states(
            [(0, 1), (0, 2), (1, 3), (2, 3)],
            [('a', 'b', 1), ('b', 'c', 1), ('a', 'c', 2)],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(states.inclusions[&3].contains(&('a', 'c')));
        assert!(!states.inclusions[&3].contains(&('a', 'b')));
    }

    #[test]
    fn backedge_facts_do_not_leak_to_the_first_loop_iteration() {
        let states = compute_guaranteed_states(
            [(0, 1), (1, 2), (2, 1), (1, 3)],
            [('a', 'b', 2)],
            [],
            [],
            [],
            [],
            [],
            [],
        );
        assert!(!states.inclusions[&1].contains(&('a', 'b')));
        assert!(states.inclusions[&2].contains(&('a', 'b')));
        assert!(!states.inclusions[&3].contains(&('a', 'b')));
    }

    #[test]
    fn barriers_kill_incoming_facts_but_not_point_local_effects() {
        let states = compute_guaranteed_states(
            [(0, 1), (1, 2), (2, 3)],
            [('a', 'b', 0), ('c', 'a', 0), ('d', 'a', 2)],
            [],
            [('a', 2)],
            [],
            [],
            [],
            [],
        );
        assert!(!states.inclusions[&2].contains(&('a', 'b')));
        assert!(!states.inclusions[&2].contains(&('c', 'a')));
        assert!(states.inclusions[&2].contains(&('d', 'a')));
        assert!(states.inclusions[&3].contains(&('d', 'a')));
        assert!(states.known_regions[&2].contains(&'a'));
    }

    #[test]
    fn known_regions_are_flow_sensitive() {
        let states =
            compute_guaranteed_states([(0, 1), (0, 2), (1, 3), (2, 3)], [], [('a', 1)], [], [], [], [], []);
        assert!(states.known_regions[&1].contains(&'a'));
        assert!(!states.known_regions[&3].contains(&'a'));
    }

    #[test]
    fn edge_barriers_kill_only_the_affected_predecessor_state() {
        let states = compute_guaranteed_states(
            [(0, 1), (0, 2), (1, 3), (2, 3)],
            [('a', 'b', 0)],
            [('a', 0)],
            [],
            [],
            [('a', 1, 3)],
            [],
            [],
        );
        assert!(states.inclusions[&2].contains(&('a', 'b')));
        assert!(!states.inclusions[&3].contains(&('a', 'b')));
        assert!(!states.known_regions[&3].contains(&'a'));
    }

    #[test]
    fn edge_additions_apply_only_to_the_selected_successor() {
        let states = compute_guaranteed_states([(0, 1), (0, 2)], [], [], [], [], [], [('a', 'b', 0, 1)], [(
            'c', 0, 1,
        )]);
        assert!(states.inclusions[&1].contains(&('a', 'b')));
        assert!(states.known_regions[&1].contains(&'c'));
        assert!(!states.inclusions[&2].contains(&('a', 'b')));
        assert!(!states.known_regions[&2].contains(&'c'));
    }

    #[test]
    fn edge_additions_are_not_promoted_to_shared_successor_facts() {
        let states = compute_guaranteed_states([(0, 2), (1, 2)], [], [], [], [], [], [('a', 'b', 0, 2)], [(
            'c', 0, 2,
        )]);
        assert!(!states.inclusions[&2].contains(&('a', 'b')));
        assert!(!states.known_regions[&2].contains(&'c'));
    }

    #[test]
    fn edge_barriers_apply_after_edge_additions() {
        let states =
            compute_guaranteed_states([(0, 1)], [], [], [], [], [('a', 0, 1)], [('a', 'b', 0, 1)], [(
                'a', 0, 1,
            )]);
        assert!(!states.inclusions[&1].contains(&('a', 'b')));
        assert!(!states.known_regions[&1].contains(&'a'));
    }

    #[test]
    fn edge_pre_barriers_apply_before_edge_additions() {
        let states = compute_guaranteed_states(
            [(0, 1)],
            [('c', 'a', 0)],
            [('a', 0)],
            [],
            [('a', 0, 1)],
            [],
            [('a', 'b', 0, 1)],
            [('a', 0, 1)],
        );
        assert!(!states.inclusions[&1].contains(&('c', 'a')));
        assert!(states.inclusions[&1].contains(&('a', 'b')));
        assert!(states.known_regions[&1].contains(&'a'));
    }
}
