// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, BTreeSet};

use log::info;

use crate::base::*;
use crate::environment::polonius_info::{self, PoloniusInfo};

pub(crate) enum DynamicInclusion {
    ExtendLft(polonius_info::AtomicRegion),
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
    inclusions: BTreeMap<P, BTreeSet<Inclusion<R>>>,
    known_regions: BTreeMap<P, BTreeSet<R>>,
}

impl<R, P> Default for GuaranteedStates<R, P> {
    fn default() -> Self {
        Self {
            inclusions: BTreeMap::new(),
            known_regions: BTreeMap::new(),
        }
    }
}

/// Compute facts guaranteed to hold after each CFG point.
///
/// Point-local barriers are applied to the incoming state before point-local effects. At joins,
/// only facts present on every incoming edge are retained. Initializing non-root points with the
/// finite universe of possible facts computes the greatest fixed point required by a must
/// analysis, while roots start with the empty state.
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
    let cfg_edges: Vec<_> = cfg_edges.into_iter().collect();
    let mut local_inclusions: BTreeMap<P, BTreeSet<Inclusion<R>>> = BTreeMap::new();
    let mut local_known: BTreeMap<P, BTreeSet<R>> = BTreeMap::new();
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
    for (r1, r2, point) in inclusions {
        points.insert(point);
        local_inclusions.entry(point).or_default().insert((r1, r2));
        local_known.entry(point).or_default().extend([r1, r2]);
    }
    for (region, point) in known_regions {
        points.insert(point);
        local_known.entry(point).or_default().insert(region);
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

    let mut possible_inclusions = local_inclusions
        .values()
        .chain(inclusions_by_edge.values())
        .flat_map(|inclusions| inclusions.iter().copied())
        .collect();
    close_transitively(&mut possible_inclusions);
    let possible_known = local_known
        .values()
        .chain(known_by_edge.values())
        .flat_map(|regions| regions.iter().copied())
        .collect::<BTreeSet<_>>();

    let mut states = GuaranteedStates::default();
    for point in &points {
        if predecessors.get(point).is_some_and(|preds| !preds.is_empty()) {
            states.inclusions.insert(*point, possible_inclusions.clone());
            states.known_regions.insert(*point, possible_known.clone());
        } else {
            states.inclusions.insert(*point, BTreeSet::new());
            states.known_regions.insert(*point, BTreeSet::new());
        }
    }

    loop {
        let mut changed = false;
        for point in &points {
            let preds = predecessors.get(point).into_iter().flatten().copied();
            let mut point_inclusions = intersect_predecessors(
                preds.clone(),
                *point,
                &states.inclusions,
                &inclusions_by_edge,
                &pre_barriers_by_edge,
                &barriers_by_edge,
                |(r1, r2), killed| !killed.contains(r1) && !killed.contains(r2),
                close_transitively,
            );
            let mut point_known = intersect_predecessors(
                preds,
                *point,
                &states.known_regions,
                &known_by_edge,
                &pre_barriers_by_edge,
                &barriers_by_edge,
                |region, killed| !killed.contains(region),
                |_| {},
            );

            if let Some(killed) = barriers_by_point.get(point) {
                point_inclusions.retain(|(r1, r2)| !killed.contains(r1) && !killed.contains(r2));
                point_known.retain(|region| !killed.contains(region));
            }
            if let Some(local) = local_inclusions.get(point) {
                point_inclusions.extend(local);
                close_transitively(&mut point_inclusions);
            }
            if let Some(local) = local_known.get(point) {
                point_known.extend(local);
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
    info: &'a PoloniusInfo<'a, 'tcx>,
    static_incl_base: Vec<(Region, Region, PointIndex)>,
    dynamic_incl_base: Vec<(Region, Region, PointIndex)>,
    known_region_base: Vec<(Region, PointIndex)>,
    barriers: Vec<(Region, PointIndex)>,
    edge_pre_barriers: Vec<(Region, PointIndex, PointIndex)>,
    edge_barriers: Vec<(Region, PointIndex, PointIndex)>,
    edge_static_incl_base: Vec<(Region, Region, PointIndex, PointIndex)>,
    edge_known_region_base: Vec<(Region, PointIndex, PointIndex)>,
    static_states: Option<GuaranteedStates<Region, PointIndex>>,
    full_states: Option<GuaranteedStates<Region, PointIndex>>,
}

impl<'a, 'tcx: 'a> InclusionTracker<'a, 'tcx> {
    pub(crate) const fn new(info: &'a PoloniusInfo<'a, 'tcx>) -> Self {
        Self {
            info,
            static_incl_base: Vec::new(),
            dynamic_incl_base: Vec::new(),
            known_region_base: Vec::new(),
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

    pub(crate) fn add_static_inclusion(&mut self, r1: Region, r2: Region, point: PointIndex) {
        self.static_incl_base.push((r1, r2, point));
        self.static_states = None;
        self.full_states = None;
    }

    pub(crate) fn add_dynamic_inclusion(&mut self, r1: Region, r2: Region, point: PointIndex) {
        self.dynamic_incl_base.push((r1, r2, point));
        self.full_states = None;
    }

    pub(crate) fn add_known_region(&mut self, region: Region, point: PointIndex) {
        self.known_region_base.push((region, point));
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

    pub(crate) fn add_edge_pre_barrier(&mut self, region: Region, from: PointIndex, to: PointIndex) {
        self.edge_pre_barriers.push((region, from, to));
        self.static_states = None;
        self.full_states = None;
    }

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

    pub(crate) fn add_edge_known_region(&mut self, region: Region, from: PointIndex, to: PointIndex) {
        self.edge_known_region_base.push((region, from, to));
        self.static_states = None;
        self.full_states = None;
    }

    fn recompute_static(&mut self) {
        self.static_states = Some(compute_guaranteed_states(
            self.info.cfg_edges(),
            self.static_incl_base.iter().copied(),
            self.known_region_base.iter().copied(),
            self.barriers.iter().copied(),
            self.edge_pre_barriers.iter().copied(),
            self.edge_barriers.iter().copied(),
            self.edge_static_incl_base.iter().copied(),
            self.edge_known_region_base.iter().copied(),
        ));
    }

    pub(crate) fn recompute(&mut self) {
        let inclusions = self.static_incl_base.iter().chain(&self.dynamic_incl_base).copied();
        self.full_states = Some(compute_guaranteed_states(
            self.info.cfg_edges(),
            inclusions,
            self.known_region_base.iter().copied(),
            self.barriers.iter().copied(),
            self.edge_pre_barriers.iter().copied(),
            self.edge_barriers.iter().copied(),
            self.edge_static_incl_base.iter().copied(),
            self.edge_known_region_base.iter().copied(),
        ));
    }

    pub(crate) fn check_inclusion(&mut self, r1: Region, r2: Region, point: PointIndex) -> bool {
        if r1 == r2 {
            return true;
        }
        if self.full_states.is_none() {
            self.recompute();
        }
        self.full_states
            .as_ref()
            .and_then(|states| states.inclusions.get(&point))
            .is_some_and(|inclusions| inclusions.contains(&(r1, r2)))
    }

    pub(crate) fn is_region_known(&mut self, region: Region, point: PointIndex) -> bool {
        if self.full_states.is_none() {
            self.recompute();
        }
        self.full_states
            .as_ref()
            .and_then(|states| states.known_regions.get(&point))
            .is_some_and(|regions| regions.contains(&region))
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
        r1: Region,
        r2: Region,
        point: PointIndex,
    ) -> Result<(), MutualDynamicInclusion> {
        if self.check_inclusion(r1, r2, point) {
            return Ok(());
        }

        if self.check_static_inclusion(r2, r1, point) {
            self.add_dynamic_inclusion(r1, r2, point);
            // TODO: recover the syntactic inclusion path instead of assuming r1 ⊑ₗ [r2].
            stmt_annots.push(DynamicInclusion::ExtendLft(self.info.mk_atomic_region(r1)));
        } else {
            if self.check_inclusion(r2, r1, point) {
                return Err(MutualDynamicInclusion { r1, r2, point });
            }
            self.add_dynamic_inclusion(r1, r2, point);
            // Lifetime annotations use the opposite orientation from Polonius origins.
            stmt_annots.push(DynamicInclusion::IncludeLft(
                self.info.mk_atomic_region(r2),
                self.info.mk_atomic_region(r1),
            ));
        }
        Ok(())
    }

    pub(crate) fn generate_dyn_inclusions(
        &mut self,
        incls: &BTreeSet<(Region, Region, PointIndex)>,
    ) -> Result<Vec<DynamicInclusion>, MutualDynamicInclusion> {
        info!("Generating dynamic inclusions {:?}", incls);
        let mut stmt_annots = Vec::new();

        // RefinedRust cannot establish equality by adding two dynamic inclusions. Reject the pair
        // before generating either annotation; a statically known direction is handled by
        // `ExtendLft` below and is therefore supported.
        for (r1, r2, point) in incls {
            if r1 < r2
                && incls.contains(&(*r2, *r1, *point))
                && !self.check_inclusion(*r1, *r2, *point)
                && !self.check_inclusion(*r2, *r1, *point)
            {
                return Err(MutualDynamicInclusion {
                    r1: *r1,
                    r2: *r2,
                    point: *point,
                });
            }
        }

        for (r1, r2, point) in incls {
            self.generate_dyn_inclusion(&mut stmt_annots, *r1, *r2, *point)?;
        }

        Ok(stmt_annots)
    }
}

#[cfg(test)]
mod tests {
    use super::compute_guaranteed_states;

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
