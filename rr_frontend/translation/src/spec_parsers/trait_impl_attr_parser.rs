// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use attribute_parse::MToken;
use attribute_parse::parse::{self, Parse as _, Peek as _};
use radium::{coq, specs};
use rr_rustc_interface::hir;
use rr_rustc_interface::span::Span;

use crate::spec_parsers::SpannedError;
use crate::spec_parsers::parse_utils::{
    IdentOrTerm, ParamLookup, RRCoqContextItem, attr_args_tokens, str_err,
};

#[derive(Clone, Eq, PartialEq, Debug, derive_more::Display)]
pub(crate) enum ParserError {
    #[display("{}", _0)]
    Parse(String),
    #[display("unknown macro {} in trait attribute instantiation", _0)]
    UnknownMacro(String),
    #[display("attribute {} has been instantiated multiple times", _0)]
    DuplicateInstantiation(String),
    #[display("unknown attribute for trait impl specification: {:?}", _0)]
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
/// - `rr::instantiate("x" := "True")`, which will instantiate a specification attribute "x" to a given term
///   "True"
/// - `rr::derive_instantiate`, similar, but on an ADT with a `derive` attribute
/// - `rr::context` for specifying extra context items
pub(crate) trait TraitImplAttrParser {
    fn parse_trait_impl_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<TraitImplAttrs, SpannedError<ParserError>>;

    fn parse_derive_trait_impl_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<TraitImplAttrs, SpannedError<ParserError>>;
}

#[derive(Clone, Debug)]
pub(crate) struct TraitImplAttrs {
    pub(crate) attrs: specs::traits::SpecAttrsInst,
    pub(crate) context_items: coq::binder::BinderList,
}

impl TraitImplAttrs {
    pub(crate) fn filter_for_attrs(
        &self,
        required: &[String],
    ) -> Result<specs::traits::SpecAttrsInst, String> {
        let mut out = BTreeMap::new();

        for attr in required {
            if let Some(a) = self.attrs.attrs.get(attr) {
                out.insert(attr.to_owned(), a.to_owned());
            } else {
                return Err(attr.to_owned());
            }
        }

        Ok(specs::traits::SpecAttrsInst::new(out))
    }
}

pub(crate) struct VerboseTraitImplAttrParser<'a, T> {
    scope: &'a T,
}

impl<'a, 'def, T: ParamLookup<'def>> VerboseTraitImplAttrParser<'a, T> {
    pub(crate) const fn new(scope: &'a T) -> Self {
        Self { scope }
    }

    fn parse_instantiate(
        &self,
        buffer: &parse::Buffer,
        span: Span,
    ) -> Result<(String, specs::traits::SpecAttrInst), SpannedError<ParserError>> {
        let parsed_name: IdentOrTerm = buffer.parse(&self.scope).map_err(|err| parse_err(span, err))?;
        buffer.parse::<_, MToken![:]>(&self.scope).map_err(|err| parse_err(span, err))?;
        buffer.parse::<_, MToken![=]>(&self.scope).map_err(|err| parse_err(span, err))?;

        let inst = if parse::Pound::peek(buffer) {
            buffer.parse::<_, MToken![#]>(&()).map_err(|err| parse_err(span, err))?;
            let macro_cmd: parse::Ident = buffer.parse(&()).map_err(|err| parse_err(span, err))?;
            if &macro_cmd.value() != "proof" {
                return Err(spanned_error(span, ParserError::UnknownMacro(macro_cmd.value())));
            }

            let parsed_term: parse::LitStr = buffer.parse(self.scope).map_err(|err| parse_err(span, err))?;
            let (parsed_term, _) = self.scope.process_coq_literal(&parsed_term.value());

            specs::traits::SpecAttrInst::Proof(parsed_term)
        } else {
            // if this is delimited, just enter the delimiter
            let buffer =
                if let Some(stream) = buffer.peek_delimited() { &parse::Buffer::new(stream) } else { buffer };

            let parsed_term: parse::LitStr = buffer.parse(self.scope).map_err(|err| parse_err(span, err))?;
            let (parsed_term, _) = self.scope.process_coq_literal(&parsed_term.value());
            let term = coq::term::Term::Literal(parsed_term);

            specs::traits::SpecAttrInst::Term(term)
        };
        Ok((parsed_name.to_string(), inst))
    }
}

impl<'def, T: ParamLookup<'def>> TraitImplAttrParser for VerboseTraitImplAttrParser<'_, T> {
    fn parse_trait_impl_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<TraitImplAttrs, SpannedError<ParserError>> {
        let mut trait_attrs = BTreeMap::new();
        let mut context_items = Vec::new();

        for &it in attrs {
            let path_segs = &it.path.segments;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
            let span = it.span;

            match seg.as_str() {
                "instantiate" => {
                    let (parsed_name, inst) = self.parse_instantiate(&buffer, span)?;
                    if trait_attrs.insert(parsed_name.clone(), inst).is_some() {
                        return Err(spanned_error(span, ParserError::DuplicateInstantiation(parsed_name)));
                    }
                },
                "context" => {
                    let context_item =
                        RRCoqContextItem::parse(&buffer, self.scope).map_err(|err| parse_err(span, err))?;
                    let param = context_item.into();
                    context_items.push(param);
                },
                "export_as" | "only_spec" | "trust_me" | "skip" | "verify" => (),
                _ => {
                    return Err(spanned_error(span, ParserError::UnknownAttribute(format!("{:?}", it.path))));
                },
            }
        }

        Ok(TraitImplAttrs {
            attrs: specs::traits::SpecAttrsInst::new(trait_attrs),
            context_items: coq::binder::BinderList::new(context_items),
        })
    }

    fn parse_derive_trait_impl_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<TraitImplAttrs, SpannedError<ParserError>> {
        let mut trait_attrs = BTreeMap::new();
        let mut context_items = Vec::new();

        for &it in attrs {
            let path_segs = &it.path.segments;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
            let span = it.span;

            match seg.as_str() {
                "derive_instantiate" => {
                    let (parsed_name, inst) = self.parse_instantiate(&buffer, span)?;
                    if trait_attrs.insert(parsed_name.clone(), inst).is_some() {
                        return Err(spanned_error(span, ParserError::DuplicateInstantiation(parsed_name)));
                    }
                },
                "context" => {
                    let context_item =
                        RRCoqContextItem::parse(&buffer, self.scope).map_err(|err| parse_err(span, err))?;
                    let param = context_item.into();
                    context_items.push(param);
                },
                _ => (),
            }
            // rest is handled by the ADT spec parser
        }

        Ok(TraitImplAttrs {
            attrs: specs::traits::SpecAttrsInst::new(trait_attrs),
            context_items: coq::binder::BinderList::new(context_items),
        })
    }
}
