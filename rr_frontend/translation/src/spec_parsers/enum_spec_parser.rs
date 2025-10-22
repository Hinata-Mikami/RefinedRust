// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use attribute_parse::{MToken, parse};
use parse::Peek as _;
use radium::{coq, specs};
use rr_rustc_interface::hir;

use crate::spec_parsers::parse_utils::{ParamLookup, attr_args_tokens, str_err};

/// An attribute spec parser handles the parsing of the attributes of the whole enum and relevant
/// attributes on the variants at once.
///
/// Supported attributes for the whole enum:
/// - `rr::refined_by`: specifies the refinement type
///
/// Supported attributes for the enum variants:
/// - `rr::pattern`: specifies the Coq pattern of the refinement type that matches this variant
/// - `rr::refinement`: specifies the refinement of the struct for this variant in the scope introduced by the
///   pattern. Can be omitted if the variant does not have any fields.
pub(crate) trait EnumSpecParser {
    fn parse_enum_spec<'a>(
        &'a mut self,
        ty_name: &str,
        attrs: &'a [&'a hir::AttrItem],
        variant_attrs: &[Vec<&'a hir::AttrItem>],
    ) -> Result<specs::enums::Spec, String>;
}

#[derive(Debug)]
pub(crate) struct EnumPattern {
    pub pat: String,
    pub args: Vec<String>,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for EnumPattern {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        // parse the pattern
        let pat: parse::LitStr = stream.parse(meta)?;
        let (pat, _) = meta.process_coq_literal(&pat.value());

        let args: Vec<String> = if parse::Dollar::peek(stream) {
            // optionally parse args
            stream.parse::<_, MToken![$]>(meta)?;

            // parse a sequence of args
            let parsed_args: parse::Punctuated<parse::LitStr, MToken![,]> =
                parse::Punctuated::<_, _>::parse_terminated(stream, meta)?;

            parsed_args
                .into_iter()
                .map(|s| {
                    let (arg, _) = meta.process_coq_literal(&s.value());
                    arg
                })
                .collect()
        } else {
            Vec::new()
        };

        Ok(Self { pat, args })
    }
}

pub(crate) struct VerboseEnumSpecParser<'a, T> {
    scope: &'a T,
}

impl<'a, 'def, T: ParamLookup<'def>> VerboseEnumSpecParser<'a, T> {
    pub(crate) const fn new(scope: &'a T) -> Self {
        Self { scope }
    }
}

impl<'def, T: ParamLookup<'def>> EnumSpecParser for VerboseEnumSpecParser<'_, T> {
    fn parse_enum_spec<'a>(
        &'a mut self,
        ty_name: &str,
        attrs: &'a [&'a hir::AttrItem],
        variant_attrs: &[Vec<&'a hir::AttrItem>],
    ) -> Result<specs::enums::Spec, String> {
        let mut variant_patterns: Vec<(String, Vec<String>, String)> = Vec::new();
        let mut rfn_type = None;
        let mut is_partial = false;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
            match seg.name.as_str() {
                "refined_by" => {
                    let ty: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                    let (rt_processed, _) = self.scope.process_coq_literal(ty.value().as_str());
                    rfn_type = Some(rt_processed);
                },
                "partial" => {
                    is_partial = true;
                },
                "export_as" => {},
                _ => {
                    return Err(format!("unknown attribute for enum specification: {:?}", args));
                },
            }
        }

        // parse the variant patterns
        for attrs in variant_attrs {
            let mut pattern = None;
            let mut refinement = None;
            for &it in attrs {
                let path_segs = &it.path.segments;

                let Some(seg) = path_segs.get(1) else {
                    continue;
                };

                let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
                let name = seg.name.as_str();
                match name {
                    "pattern" => {
                        let pat: EnumPattern = buffer.parse(self.scope).map_err(str_err)?;
                        pattern = Some(pat);
                    },
                    "refinement" => {
                        let rfn: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                        let (rfn_processed, _) = self.scope.process_coq_literal(rfn.value().as_str());
                        refinement = Some(rfn_processed);
                    },
                    _ => {
                        // skip and ignore other attributes, they may be part of struct specs
                    },
                }
            }

            if let Some(pattern) = pattern {
                let refinement = refinement.unwrap_or_else(|| "*[]".to_owned());
                variant_patterns.push((pattern.pat, pattern.args, refinement));
            }
        }

        let Some(rfn_type) = rfn_type else {
            return Err(format!("No refined_by clause provided for enum {:?}", ty_name));
        };

        let rfn_type = coq::term::Type::Literal(rfn_type);

        Ok(specs::enums::Spec {
            rfn_type,
            variant_patterns,
            is_partial,
        })
    }
}

/// Parse the arguments of a `rr::refine_as` annotation.
/// Returns the optional specified name.
pub(crate) fn parse_enum_refine_as(attrs: &hir::AttrArgs) -> Result<Option<String>, String> {
    let buffer = parse::Buffer::new(&attr_args_tokens(attrs));

    if matches!(attrs, hir::AttrArgs::Empty) {
        Ok(None)
    } else {
        let name: parse::LitStr = buffer.parse(&()).map_err(str_err)?;
        Ok(Some(name.value()))
    }
}
