// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use attribute_parse::{parse, MToken};
use parse::Peek as _;
use radium::{coq, specs};
use rr_rustc_interface::ast;

use crate::spec_parsers::parse_utils::{str_err, ParamLookup};

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
pub trait EnumSpecParser {
    fn parse_enum_spec<'a>(
        &'a mut self,
        ty_name: &str,
        attrs: &'a [&'a ast::ast::AttrItem],
        variant_attrs: &[Vec<&'a ast::ast::AttrItem>],
    ) -> Result<specs::EnumSpec, String>;
}

#[derive(Debug)]
pub struct EnumPattern {
    pub pat: String,
    pub args: Vec<String>,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for EnumPattern {
    fn parse(stream: parse::Stream, meta: &T) -> parse::Result<Self> {
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

#[expect(clippy::module_name_repetitions)]
pub struct VerboseEnumSpecParser<'a, T> {
    scope: &'a T,
}

impl<'a, 'def, T: ParamLookup<'def>> VerboseEnumSpecParser<'a, T> {
    pub const fn new(scope: &'a T) -> Self {
        Self { scope }
    }
}

impl<'b, 'def, T: ParamLookup<'def>> EnumSpecParser for VerboseEnumSpecParser<'b, T> {
    fn parse_enum_spec<'a>(
        &'a mut self,
        ty_name: &str,
        attrs: &'a [&'a ast::ast::AttrItem],
        variant_attrs: &[Vec<&'a ast::ast::AttrItem>],
    ) -> Result<specs::EnumSpec, String> {
        let mut variant_patterns: Vec<(String, Vec<String>, String)> = Vec::new();
        let mut rfn_type = None;
        let mut xt_type = None;
        let mut is_partial = false;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&it.args.inner_tokens());
            match seg.ident.name.as_str() {
                "refined_by" => {
                    let ty: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                    let (rt_processed, _) = self.scope.process_coq_literal(ty.value().as_str());
                    let (xt_processed, _) = self.scope.process_coq_literal_xt(ty.value().as_str(), true);
                    rfn_type = Some(rt_processed);
                    xt_type = Some(xt_processed.replace("place_rfn", ""));
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

                let buffer = parse::Buffer::new(&it.args.inner_tokens());
                match seg.ident.name.as_str() {
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
                        // skip and ignore other attributes
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
        let Some(xt_type) = xt_type else {
            return Err(format!("No refined_by clause provided for enum {:?}", ty_name));
        };

        let xt_type = coq::term::Type::Literal(xt_type);
        let rfn_type = coq::term::Type::Literal(rfn_type);
        let xt_injection = format!("(@xmap ({xt_type}) ({rfn_type}) _)");

        Ok(specs::EnumSpec {
            rfn_type,
            xt_type,
            xt_injection,
            variant_patterns,
            is_partial,
        })
    }
}

/// Parse the arguments of a `rr::refine_as` annotation.
/// Returns the optional specified name.
pub fn parse_enum_refine_as(attrs: &ast::ast::AttrArgs) -> Result<Option<String>, String> {
    let buffer = parse::Buffer::new(&attrs.inner_tokens());

    if matches!(attrs, ast::ast::AttrArgs::Empty) {
        Ok(None)
    } else {
        let name: parse::LitStr = buffer.parse(&()).map_err(str_err)?;
        Ok(Some(name.value()))
    }
}
