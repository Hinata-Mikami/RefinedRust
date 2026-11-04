// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use attribute_parse::parse;
use radium::coq;
use rr_rustc_interface::hir;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::span::Span;

use crate::spec_parsers::SpannedError;
use crate::spec_parsers::parse_utils::{self, attr_args_tokens, str_err};

#[derive(Clone, Eq, PartialEq, Debug, derive_more::Display)]
pub(crate) enum ParserError {
    #[display("{}", _0)]
    Parse(String),
    #[display("unknown attribute for module specification: {:?}", _0)]
    UnknownAttribute(String),
}

const fn spanned_error(span: Span, err: ParserError) -> SpannedError<ParserError> {
    SpannedError { err, span }
}

fn parse_err(span: Span, err: parse::Error) -> SpannedError<ParserError> {
    spanned_error(span, ParserError::Parse(str_err(err)))
}

/// Parse attributes on a module.
/// Permitted attributes:
/// - `rr::import("A.B.C`", "D"), which will import the Coq path "A.B.C.D"
pub(crate) trait ModuleAttrParser {
    fn parse_module_attrs<'a>(
        &'a mut self,
        did: LocalDefId,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<ModuleAttrs, SpannedError<ParserError>>;
}

#[derive(Clone, Debug)]
pub(crate) struct ModuleAttrs {
    pub exports: Vec<coq::module::Export>,
    pub includes: BTreeMap<String, Span>,
    pub export_includes: BTreeMap<String, Span>,
}

pub(crate) struct VerboseModuleAttrParser;

impl VerboseModuleAttrParser {
    pub(crate) const fn new() -> Self {
        Self {}
    }
}

impl ModuleAttrParser for VerboseModuleAttrParser {
    fn parse_module_attrs<'a>(
        &'a mut self,
        _did: LocalDefId,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<ModuleAttrs, SpannedError<ParserError>> {
        let mut exports: Vec<coq::module::Export> = Vec::new();
        let mut includes: BTreeMap<String, Span> = BTreeMap::new();
        let mut export_includes: BTreeMap<String, Span> = BTreeMap::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
            let span = it.span;
            match seg.as_str() {
                "import" => {
                    let path: parse_utils::CoqExportModule =
                        buffer.parse(&()).map_err(|err| parse_err(span, err))?;
                    exports.push(path.into());
                },
                "include" => {
                    let name: parse::LitStr = buffer.parse(&()).map_err(|err| parse_err(span, err))?;
                    let name = name.value();
                    includes.entry(name).or_insert(span);
                },
                "export_include" => {
                    let name: parse::LitStr = buffer.parse(&()).map_err(|err| parse_err(span, err))?;
                    let name = name.value();
                    export_includes.entry(name).or_insert(span);
                },
                _ => {
                    return Err(spanned_error(span, ParserError::UnknownAttribute(format!("{:?}", args))));
                },
            }
        }

        Ok(ModuleAttrs {
            exports,
            includes,
            export_includes,
        })
    }
}
