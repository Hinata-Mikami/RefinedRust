// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use derive_more::Display;
use rr_rustc_interface::errors::DiagMessage;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::{base, procedures, traits};

#[expect(dead_code)]
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub(crate) enum Message<'tcx> {
    #[display("No assumption is allowed, but this function is annotated with `#[rr::{}]`", _0)]
    NoAssumptionAllowed(procedures::Mode),

    #[display("Unknown ADT: {:?}", _0)]
    UnknownAdt(DefId),

    #[display("ADT shim was overridden for {:?}", _0)]
    OverriddenAdtShim(DefId),

    #[display("Cannot translate unknown region: {:?}", _0)]
    UnknownRegion(ty::Region<'tcx>),

    #[display("Cannot translate placeholder region")]
    PlaceholderRegion,

    #[display("Unknown early region: {:?}", _0)]
    UnknownEarlyRegion(ty::EarlyParamRegion),

    #[display("Unknown late region: (binder {}, var {})", _0, _1)]
    UnknownLateRegion(usize, usize),

    #[display("Unknown late region (outside function): (binder {}, var {})", _0, _1)]
    UnknownLateRegionOutsideFunction(usize, usize),

    #[display("Cannot translate Polonius region: {:?}", _0)]
    UnknownPoloniusRegion(base::Region),

    #[display("Unknown generic parameter: {}", _0)]
    UnknownGenericParam(String),

    #[display("No refinement annotated for field {}", _0)]
    MissingFieldRefinement(String),

    #[display("generate_adt_shim_use called for unknown adt shim {:?}", _0)]
    UnknownAdtShim(DefId),

    #[display("Could not get field {} of {}", _0, _1)]
    UnknownField(String, String),

    #[display("Expected a structlike type: {}", _0)]
    ExpectedStructlike(String),

    #[display("Unsupported feature: {}", _0)]
    UnsupportedFeature(String),

    #[display("Unsupported type: {}", _0)]
    UnsupportedType(String),

    #[display("ADT downcast on non-enum type")]
    AdtDowncastOnNonEnumType,

    #[display("Expected SwitchInt discriminator to have integer type")]
    SwitchIntOnNonIntegerType,

    #[display("Configured attribute-parser is unknown: {}", _0)]
    UnknownAttributeParser(String),

    #[display("Unknown function kind")]
    UnknownFunctionKind,

    #[display("Expected an FnDef type")]
    ExpectedFnDefType,

    #[display("Unknown variable: {}", _0)]
    UnknownVar(String),

    #[display("Unknown procedure: {}", _0)]
    UnknownProcedure(String),

    #[display("Procedure could not be registered: {}", _0)]
    ProcedureRegistry(String),

    #[display("Did not find a registered static: {}", _0)]
    MissingRegisteredStatic(String),

    #[display("Could not find local for return value")]
    MissingReturnValueLocal,

    #[display("Unimplemented case: {}", _0)]
    Unimplemented(String),

    #[display("Invalid layout")]
    InvalidLayout,

    #[display("Trait resolution failed: {}", _0)]
    TraitResolution(String),

    #[display("Cannot take offset of {}", _0)]
    OffsetOnUnsupportedType(String),

    #[display("Recursive type does not have an invariant: {:?}", _0)]
    RecursiveTypeWithoutInvariant(DefId),

    #[display("Application of UnOp::Not to non-{{Int, Bool}}")]
    UnOpNotOnUnsupportedType,

    #[display("Attribute is ill-formed: {}", _0)]
    AttributeError(String),

    #[display("Failed to parse struct invariant spec: {}", _0)]
    StructInvariantSpecParse(String),

    #[display("Failed to parse field specification: {}", _0)]
    FieldSpecParseError(String),

    #[display("Failed to const-evaluate discriminant: {}", _0)]
    DiscriminantConstEval(String),

    #[display("Failed to parse enum spec: {}", _0)]
    EnumSpecParse(String),

    #[display("Failed to parse `refine_as` enum annotation: {}", _0)]
    EnumRefineAsParse(String),

    #[display("Could not parse loop spec: {}", _0)]
    LoopSpec(String),

    #[display("Trait translation failed: {}", _0)]
    TraitTranslation(traits::Error<'tcx>),
}

impl<'tcx> From<traits::Error<'tcx>> for Message<'tcx> {
    fn from(x: traits::Error<'tcx>) -> Self {
        Self::TraitTranslation(x)
    }
}

impl From<Message<'_>> for DiagMessage {
    fn from(msg: Message<'_>) -> Self {
        Self::Str(format!("[RefinedRust] {}", msg).into())
    }
}
