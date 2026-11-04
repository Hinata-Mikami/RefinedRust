// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cmp;
use std::collections::{BTreeMap, BTreeSet};

use rr_rustc_interface::errors::ErrorGuaranteed;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::{borrowck, polonius_engine};
use rr_rustc_utils::normalize_def_path_str;
use topological_sort::TopologicalSort;

use crate::shims;

/// Strip symbols from an identifier to be compatible with Coq.
/// In particular things like ' or ::.
pub(crate) fn strip_coq_ident(s: &str) -> String {
    String::from(s)
        .replace('\'', "")
        .replace("::", "_")
        .replace('&', "REF")
        .replace("()", "unit")
        .replace(|c: char| !(c.is_alphanumeric() || c == '_'), "")
}

pub(crate) type Region = <borrowck::consumers::RustcFacts as polonius_engine::FactTypes>::Origin;
pub(crate) type PointIndex = <borrowck::consumers::RustcFacts as polonius_engine::FactTypes>::Point;

fn normalize_logical_path_segment(seg: &str) -> String {
    if matches!(seg, "core" | "alloc" | "std") { "std".to_owned() } else { seg.to_owned() }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct LogicalDefKey {
    pub path: Vec<String>,
    pub as_method: bool,
}

impl LogicalDefKey {
    pub(crate) fn new(tcx: ty::TyCtxt<'_>, did: DefId) -> Self {
        let export_path = shims::flat::get_export_path_for_did(tcx, did);
        let path = export_path
            .path
            .path
            .into_iter()
            .enumerate()
            .map(|(idx, seg)| if idx == 0 { normalize_logical_path_segment(&seg) } else { seg })
            .collect();

        Self {
            path,
            as_method: export_path.as_method,
        }
    }
}

/// Ordered `DefId`s by their logical/export path.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct OrderedDefId {
    pub def_id: DefId,
    pub logical_key: LogicalDefKey,
    pub normalized_def_path: String,
}

impl OrderedDefId {
    pub(crate) fn new(tcx: ty::TyCtxt<'_>, did: DefId) -> Self {
        let logical_key = LogicalDefKey::new(tcx, did);
        let normalized_def_path = normalize_def_path_str(&tcx.def_path_str(did));
        Self {
            def_id: did,
            logical_key,
            normalized_def_path,
        }
    }
}

impl Ord for OrderedDefId {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.logical_key
            .cmp(&other.logical_key)
            .then_with(|| self.normalized_def_path.cmp(&other.normalized_def_path))
            .then_with(|| {
                self.def_id
                    .krate
                    .cmp(&other.def_id.krate)
                    .then_with(|| self.def_id.index.cmp(&other.def_id.index))
            })
    }
}

impl PartialOrd<Self> for OrderedDefId {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn compute_def_sccs(deps: &BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>>) -> Vec<Vec<OrderedDefId>> {
    struct TarjanState {
        next_index: usize,
        stack: Vec<OrderedDefId>,
        indices: BTreeMap<OrderedDefId, usize>,
        lowlinks: BTreeMap<OrderedDefId, usize>,
        on_stack: BTreeSet<OrderedDefId>,
        components: Vec<Vec<OrderedDefId>>,
    }

    fn strong_connect(
        node: &OrderedDefId,
        graph: &BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>>,
        state: &mut TarjanState,
    ) {
        let index = state.next_index;
        state.next_index += 1;
        state.indices.insert(node.clone(), index);
        state.lowlinks.insert(node.clone(), index);
        state.stack.push(node.clone());
        state.on_stack.insert(node.clone());

        if let Some(successors) = graph.get(node) {
            for successor in successors {
                if !state.indices.contains_key(successor) {
                    strong_connect(successor, graph, state);
                    let lowlink = state.lowlinks[node].min(state.lowlinks[successor]);
                    state.lowlinks.insert(node.clone(), lowlink);
                } else if state.on_stack.contains(successor) {
                    let lowlink = state.lowlinks[node].min(state.indices[successor]);
                    state.lowlinks.insert(node.clone(), lowlink);
                }
            }
        }

        if state.lowlinks[node] == state.indices[node] {
            let mut component = Vec::new();
            loop {
                let component_node = state.stack.pop().unwrap();
                state.on_stack.remove(&component_node);
                let is_root = component_node == *node;
                component.push(component_node);
                if is_root {
                    break;
                }
            }
            state.components.push(component);
        }
    }

    let mut graph: BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>> = BTreeMap::new();
    for (did, referenced_dids) in deps {
        graph.entry(did.clone()).or_default();
        for did2 in referenced_dids {
            graph.entry(did2.clone()).or_default().insert(did.clone());
            graph.entry(did.clone()).or_default();
        }
    }

    let mut state = TarjanState {
        next_index: 0,
        stack: Vec::new(),
        indices: BTreeMap::new(),
        lowlinks: BTreeMap::new(),
        on_stack: BTreeSet::new(),
        components: Vec::new(),
    };

    for node in graph.keys() {
        if !state.indices.contains_key(node) {
            strong_connect(node, &graph, &mut state);
        }
    }

    state.components
}

/// Order definitions topologically, preserving strongly connected components.
pub(crate) fn order_def_sccs_with_deps(
    _tcx: ty::TyCtxt<'_>,
    deps: &BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>>,
) -> Vec<Vec<DefId>> {
    let components = compute_def_sccs(deps);
    let mut component_by_node = BTreeMap::new();
    for (idx, component) in components.iter().enumerate() {
        for node in component {
            component_by_node.insert(node.clone(), idx);
        }
    }

    let mut topo: TopologicalSort<usize> = TopologicalSort::new();
    for idx in 0..components.len() {
        topo.insert(idx);
    }
    for (did, referenced_dids) in deps {
        let did_component = component_by_node[did];
        for did2 in referenced_dids {
            let dep_component = component_by_node[did2];
            if dep_component != did_component {
                topo.add_dependency(dep_component, did_component);
            }
        }
    }

    let defs: BTreeSet<OrderedDefId> = deps.keys().cloned().collect();
    let mut defn_order = Vec::new();
    while !topo.is_empty() {
        let mut next = topo.pop_all();
        next.sort_by(|a, b| {
            let mut a_defs: Vec<&OrderedDefId> =
                components[*a].iter().filter(|did| defs.contains(*did)).collect();
            let mut b_defs: Vec<&OrderedDefId> =
                components[*b].iter().filter(|did| defs.contains(*did)).collect();
            a_defs.sort();
            b_defs.sort();
            a_defs.cmp(&b_defs)
        });

        for component_idx in next {
            let mut component_defs: Vec<_> =
                components[component_idx].iter().filter(|did| defs.contains(*did)).cloned().collect();
            component_defs.sort();
            if !component_defs.is_empty() {
                defn_order.push(component_defs.into_iter().map(|did| did.def_id).collect());
            }
        }
    }

    defn_order
}

/// Order ADT definitions topologically.
pub(crate) fn order_defs_with_deps(
    tcx: ty::TyCtxt<'_>,
    deps: &BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>>,
) -> Vec<DefId> {
    for (did, referenced_dids) in deps {
        if referenced_dids.contains(did) {
            panic!("RefinedRust does not currently support mutually recursive types");
        }
    }

    let ordered = order_def_sccs_with_deps(tcx, deps);
    let mut defn_order = Vec::new();
    for component in ordered {
        if component.len() > 1 {
            panic!("RefinedRust does not currently support mutually recursive types");
        }
        defn_order.extend(component);
    }

    defn_order
}

/// Error type used for the MIR to Caesium translation.
#[derive(Clone, Debug)]
pub(crate) enum TranslationError {
    ErrorReported(ErrorGuaranteed),

    Tainted(ErrorGuaranteed),
}
