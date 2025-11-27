// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cmp;
use std::collections::{BTreeMap, BTreeSet};

use derive_more::Display;
use rr_rustc_interface::errors::ErrorGuaranteed;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::hir::definitions::DefPathHash;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::{borrowck, polonius_engine};
use topological_sort::TopologicalSort;

use crate::environment::borrowck::facts;
use crate::traits;

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

/// Ordered `DefId`s, ordered by their `DefPathHash`, which should be stable across compilations.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct OrderedDefId {
    pub def_id: DefId,
    pub def_path_hash: DefPathHash,
}

impl OrderedDefId {
    pub(crate) fn new(tcx: ty::TyCtxt<'_>, did: DefId) -> Self {
        let def_path_hash = tcx.def_path_hash(did);
        Self {
            def_id: did,
            def_path_hash,
        }
    }
}

impl Ord for OrderedDefId {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.def_path_hash.cmp(&other.def_path_hash).then_with(|| {
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
        let hash_a = tcx.def_path_hash(*a);
        let hash_b = tcx.def_path_hash(*b);
        hash_a.cmp(&hash_b)
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
//TODO: add location info based on Span
#[derive(Clone, Debug, Display)]
pub(crate) enum TranslationError<'tcx> {
    #[display("Unsupported Feature: {}", description)]
    UnsupportedFeature { description: String },

    #[display("Unsupported Type: {}", description)]
    UnsupportedType { description: String },

    #[display("Recursive type does not have an invariant: {:?}", _0)]
    RecursiveTypeWithoutInvariant(DefId),

    #[display("Unimplemented Case: {}", description)]
    Unimplemented { description: String },

    #[display("Invalid Layout")]
    InvalidLayout,

    #[display("Unknown Variable: {}", _0)]
    UnknownVar(String),

    #[display("Unknown Error: {}", _0)]
    UnknownError(String),

    #[display("Fatal Error: {}", _0)]
    FatalError(String),

    #[display("Attribute is ill-formed: {}", _0)]
    AttributeError(String),

    #[display("Configured attribute-parser is unknown: {}", _0)]
    UnknownAttributeParser(String),

    #[display("Unknown procedure: {}", _0)]
    UnknownProcedure(String),

    #[display("Unknown early region: {:?}", _0)]
    UnknownEarlyRegion(ty::EarlyParamRegion),

    #[display("Unknown late region (outside function): (binder {}, var {})", _0, _1)]
    UnknownLateRegionOutsideFunction(usize, usize),

    #[display("Unknown late region: (binder {}, var {})", _0, _1)]
    UnknownLateRegion(usize, usize),

    #[display("Cannot translate placeholder region")]
    PlaceholderRegion,

    #[display("Cannot translate unknown region: {:?}", _0)]
    UnknownRegion(ty::Region<'tcx>),

    #[display("Encountered Polonius region outside function: {:?}", _0)]
    PoloniusRegionOutsideFunction(facts::Region),

    #[display("Cannot translate Polonius region: {:?}", _0)]
    UnknownPoloniusRegion(facts::Region),

    #[display("Trait could not be resolved: {}", _0)]
    TraitResolution(String),

    #[display("Trait translation failed: {}", _0)]
    TraitTranslation(traits::Error<'tcx>),

    #[display("Procedure could not be registered: {}", _0)]
    ProcedureRegistry(String),

    #[display("Could not parse loop spec: {}", _0)]
    LoopSpec(String),

    #[display("Incomplete specification for trait impl {:?}", _0)]
    IncompleteTraitImplSpec(DefId),

    #[display("Error reported")]
    ErrorReported(ErrorGuaranteed),
}

impl<'tcx> From<traits::Error<'tcx>> for TranslationError<'tcx> {
    fn from(x: traits::Error<'tcx>) -> Self {
        Self::TraitTranslation(x)
    }
}

impl From<ErrorGuaranteed> for TranslationError<'_> {
    fn from(x: ErrorGuaranteed) -> Self {
        Self::ErrorReported(x)
    }
}
