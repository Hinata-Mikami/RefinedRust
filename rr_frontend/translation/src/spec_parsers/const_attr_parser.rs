// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use attribute_parse::parse;
use derive_more::Display;
use rr_rustc_interface::hir;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::span::Span;

use crate::spec_parsers::SpannedError;
use crate::spec_parsers::parse_utils::{attr_args_tokens, str_err};

#[derive(Clone, Debug, Eq, PartialEq, Display)]
pub(crate) enum ParserError {
    #[display("parse error: {}", _0)]
    Parse(String),
    #[display("name attribute has already been specified")]
    DuplicateName,
    #[display("unknown attribute for const specification: {}", _0)]
    UnknownAttribute(String),
    #[display("no name attribute specified on const")]
    MissingName,
}

const fn spanned_error(span: Span, err: ParserError) -> SpannedError<ParserError> {
    SpannedError { err, span }
}

fn parse_err(span: Span, err: parse::Error) -> SpannedError<ParserError> {
    spanned_error(span, ParserError::Parse(str_err(err)))
}

/// Parse attributes on a const.
/// Permitted attributes:
/// - `rr::name("x`"), which will introduce the name x to refer to the const in other specs
pub(crate) trait ConstAttrParser {
    fn parse_const_attrs<'a>(
        &'a mut self,
        did: LocalDefId,
        span: Span,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<ConstAttrs, SpannedError<ParserError>>;
}

#[derive(Clone, Debug)]
pub(crate) struct ConstAttrs {
    pub name: String,
}

pub(crate) struct VerboseConstAttrParser;

impl VerboseConstAttrParser {
    pub(crate) const fn new() -> Self {
        Self {}
    }
}

impl ConstAttrParser for VerboseConstAttrParser {
    fn parse_const_attrs<'a>(
        &'a mut self,
        _did: LocalDefId,
        span: Span,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<ConstAttrs, SpannedError<ParserError>> {
        let mut name: Option<String> = None;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));

            match seg.as_str() {
                "name" => {
                    let parsed_name: parse::LitStr =
                        buffer.parse(&()).map_err(|e| parse_err(buffer.pos().unwrap(), e))?;
                    if name.is_some() {
                        return Err(spanned_error(span, ParserError::DuplicateName));
                    }
                    name = Some(parsed_name.value());
                },
                _ => {
                    return Err(spanned_error(span, ParserError::UnknownAttribute(format!("{:?}", args))));
                },
            }
        }

        let Some(name) = name else {
            return Err(spanned_error(span, ParserError::MissingName));
        };

        Ok(ConstAttrs { name })
    }
}
