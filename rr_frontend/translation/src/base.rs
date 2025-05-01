// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use derive_more::Display;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{borrowck, polonius_engine};

use crate::environment::borrowck::facts;
use crate::traits;

/// Strip symbols from an identifier to be compatible with Coq.
/// In particular things like ' or ::.
pub fn strip_coq_ident(s: &str) -> String {
    String::from(s)
        .replace('\'', "")
        .replace("::", "_")
        .replace(|c: char| !(c.is_alphanumeric() || c == '_'), "")
}

pub type Region = <borrowck::consumers::RustcFacts as polonius_engine::FactTypes>::Origin;
pub type PointIndex = <borrowck::consumers::RustcFacts as polonius_engine::FactTypes>::Point;

/// Error type used for the MIR to Caesium translation.
//TODO: add location info based on Span
#[derive(Clone, Debug, Display)]
pub enum TranslationError<'tcx> {
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

    #[display("Loan was not found at location {:?}", _0)]
    LoanNotFound(mir::Location),

    #[display("Attribute is ill-formed: {}", _0)]
    AttributeError(String),

    #[display("Configured attribute-parser is unknown: {}", _0)]
    UnknownAttributeParser(String),

    #[display("Unknown procedure: {}", _0)]
    UnknownProcedure(String),

    #[display("Unknown early region: {:?}", _0)]
    UnknownEarlyRegion(ty::EarlyBoundRegion),

    #[display("Unknown late region (outside function): (binder {}, var {})", _0, _1)]
    UnknownLateRegionOutsideFunction(usize, usize),

    #[display("Unknown late region: (binder {}, var {})", _0, _1)]
    UnknownLateRegion(usize, usize),

    #[display("Cannot translate placeholder region")]
    PlaceholderRegion(),

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

    #[display("Lookup in a dummy scope: {}", _0)]
    DummyScope(String),

    #[display("Could not parse loop spec: {}", _0)]
    LoopSpec(String),
}

impl<'tcx> From<traits::Error<'tcx>> for TranslationError<'tcx> {
    fn from(x: traits::Error<'tcx>) -> Self {
        Self::TraitTranslation(x)
    }
}
