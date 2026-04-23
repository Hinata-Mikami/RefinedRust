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

pub(crate) fn normalize_def_path_str(def_path: &str) -> String {
    let mut segments = def_path.split("::");
    if let Some(seg) = segments.next()
        && matches!(seg, "core" | "alloc" | "std")
    {
        return format!("std::{}", segments.collect::<Vec<_>>().join("::"));
    }
    def_path.to_owned()
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

pub(crate) fn sort_def_ids(tcx: ty::TyCtxt<'_>, dids: &mut [DefId]) {
    dids.sort_by(|a, b| {
        LogicalDefKey::new(tcx, *a)
            .cmp(&LogicalDefKey::new(tcx, *b))
            .then_with(|| {
                normalize_def_path_str(&tcx.def_path_str(*a))
                    .cmp(&normalize_def_path_str(&tcx.def_path_str(*b)))
            })
            .then_with(|| a.krate.cmp(&b.krate).then_with(|| a.index.cmp(&b.index)))
    });
}

/// Order ADT definitions topologically.
pub(crate) fn order_defs_with_deps(
    tcx: ty::TyCtxt<'_>,
    deps: &BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>>,
) -> Vec<DefId> {
    let mut topo = TopologicalSort::new();
    let mut defs = BTreeSet::new();

    //info!("Ordering ADT defs: {deps:?}");

    for (did, referenced_dids) in deps {
        defs.insert(did);
        topo.insert(did.def_id);
        for did2 in referenced_dids {
            topo.add_dependency(did2.def_id, did.def_id);
        }
    }

    let mut defn_order = Vec::new();
    while !topo.is_empty() {
        let mut next = topo.pop_all();
        // sort these by lexicographic order
        sort_def_ids(tcx, &mut next);

        if next.is_empty() {
            // dependency cycle detected
            // TODO
            panic!("RefinedRust does not currently support mutually recursive types");
        }
        // only track actual definitions
        defn_order.extend(next.into_iter().filter(|x| defs.contains(&OrderedDefId::new(tcx, *x))));
    }

    defn_order
}

/// Error type used for the MIR to Caesium translation.
#[derive(Clone, Debug)]
pub(crate) enum TranslationError {
    ErrorReported(ErrorGuaranteed),

    Tainted(ErrorGuaranteed),
}
