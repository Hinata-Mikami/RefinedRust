// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use attribute_parse::parse;
use derive_more::Display;
use radium::coq;
use rr_rustc_interface::hir;
use rr_rustc_interface::span::Span;

use crate::spec_parsers::SpannedError;
use crate::spec_parsers::parse_utils::{self, attr_args_tokens, str_err};

#[derive(Clone, Debug, Eq, PartialEq, Display)]
pub(crate) enum ParserError {
    #[display("parse error: {}", _0)]
    Parse(String),
    #[display("multiple rr::coq_prefix attributes have been provided")]
    DuplicatePrefix,
    #[display("multiple rr::package attributes have been provided")]
    DuplicatePackage,
    #[display("unknown attribute for crate specification: {}", _0)]
    UnknownAttribute(String),
}

const fn spanned_error(span: Span, err: ParserError) -> SpannedError<ParserError> {
    SpannedError { err, span }
}

fn parse_err(span: Span, err: parse::Error) -> SpannedError<ParserError> {
    spanned_error(span, ParserError::Parse(str_err(err)))
}

/// Parse attributes on a crate.
/// Permitted attributes:
/// - `rr::import("A.B.C`", "D"), which will import the Coq path "A.B.C.D"
pub(crate) trait CrateAttrParser {
    fn parse_crate_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
        span: Span,
    ) -> Result<CrateAttrs, SpannedError<ParserError>>;
}

#[derive(Clone, Debug)]
pub(crate) struct CrateAttrs {
    pub exports: Vec<coq::module::Export>,
    pub prefix: Option<String>,
    pub includes: BTreeMap<String, Span>,
    pub export_includes: BTreeMap<String, Span>,
    pub package: Option<String>,
}

pub(crate) struct VerboseCrateAttrParser;

impl VerboseCrateAttrParser {
    pub(crate) const fn new() -> Self {
        Self {}
    }
}

impl CrateAttrParser for VerboseCrateAttrParser {
    fn parse_crate_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
        span: Span,
    ) -> Result<CrateAttrs, SpannedError<ParserError>> {
        let mut exports: Vec<coq::module::Export> = Vec::new();
        let mut includes: BTreeMap<String, Span> = BTreeMap::new();
        let mut export_includes: BTreeMap<String, Span> = BTreeMap::new();
        let mut prefix: Option<String> = None;
        let mut package: Option<String> = None;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;
            let attr_span = it.span;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
            match seg.as_str() {
                "import" => {
                    let path: parse_utils::CoqExportModule =
                        buffer.parse(&()).map_err(|e| parse_err(attr_span, e))?;
                    exports.push(path.into());
                },
                "include" => {
                    let name: parse::LitStr = buffer.parse(&()).map_err(|e| parse_err(attr_span, e))?;
                    let name = name.value();
                    includes.entry(name).or_insert(attr_span);
                },
                "export_include" => {
                    let name: parse::LitStr = buffer.parse(&()).map_err(|e| parse_err(attr_span, e))?;
                    let name = name.value();
                    export_includes.entry(name).or_insert(attr_span);
                },
                "coq_prefix" => {
                    let path: parse::LitStr = buffer.parse(&()).map_err(|e| parse_err(attr_span, e))?;
                    if prefix.is_some() {
                        return Err(spanned_error(span, ParserError::DuplicatePrefix));
                    }
                    prefix = Some(path.value().clone());
                },
                "package" => {
                    let path: parse::LitStr = buffer.parse(&()).map_err(|e| parse_err(attr_span, e))?;
                    if package.is_some() {
                        return Err(spanned_error(span, ParserError::DuplicatePackage));
                    }
                    package = Some(path.value().clone());
                },
                _ => {
                    return Err(spanned_error(span, ParserError::UnknownAttribute(format!("{:?}", args))));
                },
            }
        }

        Ok(CrateAttrs {
            exports,
            prefix,
            includes,
            export_includes,
            package,
        })
    }
}
