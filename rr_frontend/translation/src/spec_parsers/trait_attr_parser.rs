// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{HashMap, HashSet};

use attribute_parse::{MToken, parse};
use derive_more::Constructor;
use radium::specs;
use rr_rustc_interface::hir;
use rr_rustc_interface::span::Span;

use crate::spec_parsers::SpannedError;
use crate::spec_parsers::parse_utils::{
    IdentOrTerm, ParamLookup, RRCoqType, RustPath, RustPathElem, attr_args_tokens, str_err,
};

#[derive(Clone, Eq, PartialEq, Debug, derive_more::Display)]
pub(crate) enum ParserError {
    #[display("{}", _0)]
    Parse(String),
    #[display("rr::external_attrs specified, but rr::exists has been previously specified")]
    ExternalAttrsAfterExists,
    #[display("rr::exists specified, but rr::external_attrs has been previously specified")]
    ExistsAfterExternalAttrs,
    #[display("attribute {} has been declared multiple times", _0)]
    DuplicateAttribute(String),
    #[display("rr::semantic has been declared multiple times")]
    DuplicateSemanticInterp,
    #[display("unknown attribute for trait specification: {:?}", _0)]
    UnknownAttribute(String),
}

const fn spanned_error(span: Span, err: ParserError) -> SpannedError<ParserError> {
    SpannedError { err, span }
}

fn parse_err(span: Span, err: parse::Error) -> SpannedError<ParserError> {
    spanned_error(span, ParserError::Parse(str_err(err)))
}

/// Parse attributes on a trait.
/// Permitted attributes:
/// - `rr::exists("x" : "Prop")`, which will declare a specification attribute "x" of the given type "Prop"
pub(crate) trait TraitAttrParser {
    fn parse_trait_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<TraitAttrs, SpannedError<ParserError>>;
}

/// Extends an existing scope with additional literals of attributes parsed so far.
#[derive(Constructor)]
struct TraitAttrScope<'a, T> {
    inner_scope: &'a T,
    // spec attrs that were parsed so far mapped to the record item name
    literals: HashMap<String, String>,
}

impl<'def, T: ParamLookup<'def>> ParamLookup<'def> for TraitAttrScope<'_, T> {
    fn lookup_ty_param(&self, path: &RustPath) -> Option<specs::Type<'def>> {
        self.inner_scope.lookup_ty_param(path)
    }

    fn lookup_lft(&self, lft: &str) -> Option<&specs::LftParam> {
        self.inner_scope.lookup_lft(lft)
    }

    fn lookup_literal(&self, path: &RustPath) -> Option<String> {
        if path.len() == 1 {
            let RustPathElem::AssocItem(it) = &path[0];
            if let Some(lit) = self.literals.get(it) {
                return Some(lit.to_owned());
            }
        }
        self.inner_scope.lookup_literal(path)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct TraitAttrs {
    pub attrs: specs::traits::SpecAttrsDecl,
}

pub(crate) struct VerboseTraitAttrParser<'a, T, F> {
    scope: TraitAttrScope<'a, T>,
    make_record_id: F,
}

impl<'a, 'def, T: ParamLookup<'def>, F> VerboseTraitAttrParser<'a, T, F>
where
    F: Fn(&str) -> String,
{
    pub(crate) fn new(scope: &'a T, make_record_id: F) -> Self {
        let scope = TraitAttrScope::new(scope, HashMap::new());
        Self {
            scope,
            make_record_id,
        }
    }
}

impl<'def, T: ParamLookup<'def>, F> TraitAttrParser for VerboseTraitAttrParser<'_, T, F>
where
    F: Fn(&str) -> String,
{
    fn parse_trait_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<TraitAttrs, SpannedError<ParserError>> {
        let mut trait_attrs = Vec::new();
        let mut used_attrs = HashSet::new();

        let mut external_attrs = false;
        let mut semantic_interp = None;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
            let span = it.span;

            match seg.as_str() {
                "external_attrs" => {
                    if !trait_attrs.is_empty() {
                        return Err(spanned_error(span, ParserError::ExternalAttrsAfterExists));
                    }
                    external_attrs = true;
                },
                "exists" => {
                    if external_attrs {
                        return Err(spanned_error(span, ParserError::ExistsAfterExternalAttrs));
                    }
                    let parsed_name: IdentOrTerm = buffer.parse(&()).map_err(|err| parse_err(span, err))?;
                    buffer.parse::<_, MToken![:]>(&()).map_err(|err| parse_err(span, err))?;
                    // add the new identifier to the scope
                    self.scope.literals.insert(
                        parsed_name.to_string(),
                        self.make_record_id.call((&parsed_name.to_string(),)),
                    );
                    let parsed_type: RRCoqType =
                        buffer.parse(&self.scope).map_err(|err| parse_err(span, err))?;
                    if !used_attrs.insert(parsed_name.to_string()) {
                        return Err(spanned_error(
                            span,
                            ParserError::DuplicateAttribute(parsed_name.to_string()),
                        ));
                    }
                    trait_attrs.push((parsed_name.to_string(), parsed_type.ty));
                },
                "semantic" => {
                    let parsed_term: parse::LitStr =
                        buffer.parse(&self.scope).map_err(|err| parse_err(span, err))?;
                    let (lit, _) = self.scope.process_coq_literal(&parsed_term.value());

                    if semantic_interp.is_some() {
                        return Err(spanned_error(span, ParserError::DuplicateSemanticInterp));
                    }
                    semantic_interp = Some(lit);
                },
                "nondependent" | "export_as" => (),
                _ => {
                    return Err(spanned_error(span, ParserError::UnknownAttribute(format!("{:?}", args))));
                },
            }
        }

        let attrs = if external_attrs { None } else { Some(trait_attrs) };
        Ok(TraitAttrs {
            attrs: specs::traits::SpecAttrsDecl::new(attrs, semantic_interp),
        })
    }
}

/// Get all the trait attrs declared on a trait with `rr::exists`, without validating them yet.
pub(crate) fn get_declared_trait_attrs(
    attrs: &[&hir::AttrItem],
) -> Result<Vec<String>, SpannedError<ParserError>> {
    let mut trait_attrs = Vec::new();

    for &it in attrs {
        let path_segs = &it.path.segments;

        let Some(seg) = path_segs.get(1) else {
            continue;
        };

        let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
        let span = it.span;

        if "exists" == seg.as_str() {
            let parsed_name: IdentOrTerm = buffer.parse(&()).map_err(|err| parse_err(span, err))?;
            let parsed_name = parsed_name.to_string();
            buffer.parse::<_, MToken![:]>(&()).map_err(|err| parse_err(span, err))?;
            trait_attrs.push(parsed_name);
        } else if "external_attrs" == seg.as_str() {
            let params: parse::Punctuated<parse::LitStr, MToken![,]> =
                parse::Punctuated::<_, _>::parse_terminated(&buffer, &())
                    .map_err(|err| parse_err(span, err))?;
            for it in params {
                trait_attrs.push(it.value());
            }
        }
    }

    Ok(trait_attrs)
}
