// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use derive_more::Display;
use rr_rustc_interface::errors::DiagMessage;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::spec_parsers::const_attr_parser::ParserError as ConstParserError;
use crate::spec_parsers::crate_attr_parser::ParserError as CrateParserError;
use crate::spec_parsers::enum_spec_parser::ParserError as EnumParserError;
use crate::spec_parsers::loop_attr_parser::ParserError as LoopParserError;
use crate::spec_parsers::module_attr_parser::ParserError as ModuleParserError;
use crate::spec_parsers::struct_spec_parser::ParserError as StructParserError;
use crate::spec_parsers::trait_attr_parser::ParserError as TraitParserError;
use crate::spec_parsers::trait_impl_attr_parser::ParserError as TraitImplParserError;
use crate::{base, procedures};

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

    #[display("Skipping function due to `#[rr::skip]`")]
    SkipWarn,

    #[display("Skipping function due to `#[rr::skip]` on enclosing impl")]
    SkipOnImplWarn,

    #[display("Skipping function due to previous failure: {}", _0)]
    SkippedDueToPreviousFailure(String),

    #[display("Skipping trait impl due to previous failure: {:?}", _0)]
    SkippedTraitImplDueToPreviousFailure(DefId),

    #[display("Failed to parse struct invariant spec: {}", _0)]
    StructInvariantSpecParse(StructParserError),

    #[display("Failed to parse field specification: {}", _0)]
    FieldSpecParseError(StructParserError),

    #[display("Failed to parse const specification: {}", _0)]
    ConstSpecParse(ConstParserError),

    #[display("Failed to parse crate specification: {}", _0)]
    CrateSpecParse(CrateParserError),

    #[display("Failed to parse module specification: {}", _0)]
    ModuleSpecParse(ModuleParserError),

    #[display("Failed to parse trait impl specification: {}", _0)]
    TraitImplSpecParse(TraitImplParserError),

    #[display("Failed to parse trait specification: {}", _0)]
    TraitSpecParse(TraitParserError),

    #[display("Failed to parse enum spec: {}", _0)]
    EnumSpecParse(EnumParserError),

    #[display("Failed to parse `refine_as` enum annotation: {}", _0)]
    EnumRefineAsParse(EnumParserError),

    #[display("Could not parse loop spec: {}", _0)]
    LoopSpec(LoopParserError),

    #[display("An error occurred when parsing the specification of the trait impl {:?}: {:?}", _0, _1)]
    TraitImplSpec(DefId, String),

    #[display("Trait {:?} has not been registered with RefinedRust yet", _0)]
    TraitNotRegisteredWithRefinedRust(DefId),

    #[display(
        "Closure impl for {:?} with kind {:?} has not been registered with RefinedRust yet; add a specification for it?",
        _0,
        _1
    )]
    ClosureImplNotRegisteredWithRefinedRust(DefId, ty::ClosureKind),

    #[display("This trait impl {:?} of {:?} has not been registered yet", _0, _1)]
    UnregisteredImpl(DefId, DefId),

    #[display("Incomplete specification for trait impl {:?}", _0)]
    IncompleteTraitImplSpec(DefId),
}

impl From<Message<'_>> for DiagMessage {
    fn from(msg: Message<'_>) -> Self {
        Self::Str(format!("[RefinedRust] {}", msg).into())
    }
}
