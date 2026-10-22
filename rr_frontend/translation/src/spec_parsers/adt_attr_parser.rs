// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Parsing for ADT-level attributes that control generated ADT obligations.
//!
//! These are intentionally narrower than the existing function-level modes. For now the only
//! supported ADT obligation target is `drop_glue`, as in `#[rr::skip(drop_glue)]`,
//! `#[rr::trust_me(drop_glue)]`, and `#[rr::only_spec(drop_glue)]`.

use attribute_parse::{MToken, parse};
use derive_more::Display;
use rr_rustc_interface::hir;
use rr_rustc_interface::span::Span;

use crate::attrs;
use crate::spec_parsers::SpannedError;
use crate::spec_parsers::parse_utils::{attr_args_tokens, str_err};

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum AdtDropGlueMode {
    /// Generate and prove virtual drop glue normally.
    Prove,
    /// Generate the virtual drop-glue spec/code, but trust its proof obligation.
    TrustMe,
    /// Generate only the virtual drop-glue spec, but no code or proof obligation.
    OnlySpec,
    /// Do not register virtual drop glue for this ADT at all.
    Skip,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub(crate) enum ParserError {
    #[display("{}", _0)]
    Parse(String),
    #[display("bare rr::trust_me is not supported on ADTs")]
    BareTrustMe,
    #[display("bare rr::only_spec is not supported on ADTs")]
    BareOnlySpec,
    #[display("unsupported ADT obligation target `{}`; expected `drop_glue`", _0)]
    UnsupportedTarget(String),
    #[display("conflicting drop_glue modes on ADT; use only one of skip, trust_me, or only_spec")]
    ConflictingDropGlueModes,
}

const fn spanned_error(span: Span, err: ParserError) -> SpannedError<ParserError> {
    SpannedError { err, span }
}

fn parse_err(span: Span, err: parse::Error) -> SpannedError<ParserError> {
    spanned_error(span, ParserError::Parse(str_err(err)))
}

fn parse_adt_drop_glue_targets(attr: &hir::AttrItem) -> Result<Vec<String>, SpannedError<ParserError>> {
    // Bare `skip` remains the broad ADT skip; bare assumed modes have no ADT-wide meaning.
    if matches!(attr.args, hir::AttrArgs::Empty) {
        return Ok(Vec::new());
    }

    let buffer = parse::Buffer::new(&attr_args_tokens(&attr.args));
    let targets: parse::Punctuated<parse::Ident, MToken![,]> =
        parse::Punctuated::parse_separated_nonempty(&buffer, &()).map_err(|err| parse_err(attr.span, err))?;

    Ok(targets.into_iter().map(parse::Ident::value).collect())
}

pub(crate) fn get_adt_drop_glue_mode(
    attr_items: &[&hir::AttrItem],
) -> Result<AdtDropGlueMode, SpannedError<ParserError>> {
    // Default to proving drop glue unless an ADT-specific mode overrides it.
    let mut mode = AdtDropGlueMode::Prove;

    for attr in attr_items {
        let Some(name) = attrs::get_tool_attr_name(attr) else {
            continue;
        };
        if name != "skip" && name != "trust_me" && name != "only_spec" {
            continue;
        }

        let targets = parse_adt_drop_glue_targets(attr)?;
        if targets.is_empty() {
            // A bare `#[rr::skip]` skips all ADT obligations, including drop glue.
            if name == "skip" {
                return Ok(AdtDropGlueMode::Skip);
            }
            if name == "trust_me" {
                return Err(spanned_error(attr.span, ParserError::BareTrustMe));
            }
            return Err(spanned_error(attr.span, ParserError::BareOnlySpec));
        }

        for target in targets {
            if target != "drop_glue" {
                return Err(spanned_error(attr.span, ParserError::UnsupportedTarget(target)));
            }

            // Multiple identical annotations are harmless, but mixing modes is ambiguous.
            match (name, mode) {
                ("skip", AdtDropGlueMode::Prove) => mode = AdtDropGlueMode::Skip,
                ("trust_me", AdtDropGlueMode::Prove) => mode = AdtDropGlueMode::TrustMe,
                ("only_spec", AdtDropGlueMode::Prove) => mode = AdtDropGlueMode::OnlySpec,
                ("skip", AdtDropGlueMode::Skip)
                | ("trust_me", AdtDropGlueMode::TrustMe)
                | ("only_spec", AdtDropGlueMode::OnlySpec) => {},
                _ => return Err(spanned_error(attr.span, ParserError::ConflictingDropGlueModes)),
            }
        }
    }

    Ok(mode)
}

pub(crate) fn has_non_drop_glue_adt_attr(attr_items: &[&hir::AttrItem]) -> bool {
    // Used by derived-trait discovery: targeted drop-glue attrs should not make unrelated derived
    // trait obligations look annotated.
    attr_items
        .iter()
        .filter_map(|attr| attrs::get_tool_attr_name(attr))
        .any(|name| name != "skip" && name != "trust_me" && name != "only_spec")
}
