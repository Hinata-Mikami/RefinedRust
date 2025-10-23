// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use attribute_parse::MToken;
use attribute_parse::parse::{self, Peek as _};
use radium::{coq, specs};
use rr_rustc_interface::hir;

use crate::spec_parsers::parse_utils::{IdentOrTerm, ParamLookup, attr_args_tokens, str_err};

/// Parse attributes on a trait.
/// Permitted attributes:
/// - `rr::instantiate("x" := "True")`, which will instantiate a specification attribute "x" to a given term
///   "True"
pub(crate) trait TraitImplAttrParser {
    fn parse_trait_impl_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<TraitImplAttrs, String>;
}

#[derive(Clone, Debug)]
pub(crate) struct TraitImplAttrs {
    pub attrs: specs::traits::SpecAttrsInst,
}

pub(crate) struct VerboseTraitImplAttrParser<'a, T> {
    scope: &'a T,
}

impl<'a, T> VerboseTraitImplAttrParser<'a, T> {
    pub(crate) const fn new(scope: &'a T) -> Self {
        Self { scope }
    }
}

impl<'def, T: ParamLookup<'def>> TraitImplAttrParser for VerboseTraitImplAttrParser<'_, T> {
    fn parse_trait_impl_attrs<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<TraitImplAttrs, String> {
        let mut trait_attrs = BTreeMap::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));

            match seg.name.as_str() {
                "instantiate" => {
                    let parsed_name: IdentOrTerm = buffer.parse(&self.scope).map_err(str_err)?;
                    buffer.parse::<_, MToken![:]>(&self.scope).map_err(str_err)?;
                    buffer.parse::<_, MToken![=]>(&self.scope).map_err(str_err)?;

                    let inst = if parse::Pound::peek(&buffer) {
                        buffer.parse::<_, MToken![#]>(&()).map_err(str_err)?;
                        let macro_cmd: parse::Ident = buffer.parse(&()).map_err(str_err)?;
                        if &macro_cmd.value() != "proof" {
                            return Err(format!(
                                "unknown macro {} in trait attribute instantiation",
                                macro_cmd.value()
                            ));
                        }

                        let parsed_term: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                        let (parsed_term, _) = self.scope.process_coq_literal(&parsed_term.value());

                        specs::traits::SpecAttrInst::Proof(parsed_term)
                    } else {
                        // if this is delimited, just enter the delimiter
                        let buffer = if let Some(stream) = buffer.peek_delimited() {
                            parse::Buffer::new(stream)
                        } else {
                            buffer
                        };

                        let parsed_term: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                        let (parsed_term, _) = self.scope.process_coq_literal(&parsed_term.value());
                        let term = coq::term::Term::Literal(parsed_term);

                        specs::traits::SpecAttrInst::Term(term)
                    };
                    if trait_attrs.insert(parsed_name.to_string(), inst).is_some() {
                        return Err(format!("attribute {parsed_name} has been instantiated multiple times"));
                    }
                },
                "export_as" | "only_spec" | "trust_me" => (),
                _ => {
                    return Err(format!("unknown attribute for trait impl specification: {:?}", args));
                },
            }
        }

        Ok(TraitImplAttrs {
            attrs: specs::traits::SpecAttrsInst::new(trait_attrs),
        })
    }
}
