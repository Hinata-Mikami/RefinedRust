// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashSet;

use attribute_parse::{parse, MToken};
use parse::{Parse, Peek};
use radium::{coq, specs, term};
use rr_rustc_interface::ast::ast::AttrItem;
use rr_rustc_interface::hir::def_id::LocalDefId;

use crate::spec_parsers::parse_utils::*;

/// Parse attributes on a const.
/// Permitted attributes:
/// TODO
pub trait LoopAttrParser {
    fn parse_loop_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<radium::LoopSpec, String>;
}

/// Representation of the `IProps` that can appear in a requires or ensures clause.
enum MetaIProp {
    /// #[rr::requires("..")] or #[rr::requires("Ha" : "..")]
    Pure(String, Option<String>),
    /// #[rr::requires(#iris "..")]
    Iris(specs::IProp),
    /// #[rr::requires(#type "l" : "rfn" @ "ty")]
    Type(specs::TyOwnSpec),
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for MetaIProp {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        if parse::Pound::peek(input) {
            input.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = input.parse(meta)?;
            match macro_cmd.value().as_str() {
                "type" => {
                    let loc_str: parse::LitStr = input.parse(meta)?;
                    let (loc_str, mut annot_meta) = meta.process_coq_literal(&loc_str.value());

                    input.parse::<_, MToken![:]>(meta)?;

                    let rfn_str: parse::LitStr = input.parse(meta)?;
                    let (rfn_str, annot_meta2) = meta.process_coq_literal(&rfn_str.value());

                    annot_meta.join(&annot_meta2);

                    input.parse::<_, MToken![@]>(meta)?;

                    let type_str: parse::LitStr = input.parse(meta)?;
                    let (type_str, annot_meta3) = meta.process_coq_literal(&type_str.value());
                    annot_meta.join(&annot_meta3);

                    let spec = specs::TyOwnSpec::new(loc_str, rfn_str, type_str, false, annot_meta);
                    Ok(Self::Type(spec))
                },
                "iris" => {
                    let prop: IProp = input.parse(meta)?;
                    Ok(Self::Iris(prop.into()))
                },
                _ => Err(parse::Error::OtherErr(
                    input.pos().unwrap(),
                    format!("invalid macro command: {:?}", macro_cmd.value()),
                )),
            }
        } else {
            let name_or_prop_str: parse::LitStr = input.parse(meta)?;
            if parse::Colon::peek(input) {
                // this is a name
                let name_str = name_or_prop_str.value();

                input.parse::<_, MToken![:]>(meta)?;

                let pure_prop: parse::LitStr = input.parse(meta)?;
                let (pure_str, _annot_meta) = meta.process_coq_literal(&pure_prop.value());
                // TODO: should we use annot_meta?

                Ok(Self::Pure(pure_str, Some(name_str)))
            } else {
                // this is a
                let (lit, _) = meta.process_coq_literal(&name_or_prop_str.value());
                Ok(Self::Pure(lit, None))
            }
        }
    }
}

impl From<MetaIProp> for specs::IProp {
    fn from(meta: MetaIProp) -> Self {
        match meta {
            MetaIProp::Pure(p, name) => match name {
                None => Self::Pure(p),
                Some(n) => Self::PureWithName(p, n),
            },
            MetaIProp::Iris(p) => p,
            MetaIProp::Type(spec) => {
                let lit = spec.fmt_owned("π");
                Self::Atom(lit)
            },
        }
    }
}

/// Invariant variable refinement declaration
struct InvVar {
    local: String,
    rfn: String,
}
impl<'def, T: ParamLookup<'def>> parse::Parse<T> for InvVar {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        let local_str: parse::LitStr = input.parse(meta)?;
        let local_str = local_str.value();

        input.parse::<_, MToken![:]>(meta)?;

        let rfn_str: parse::LitStr = input.parse(meta)?;
        let (rfn_str, _) = meta.process_coq_literal(&rfn_str.value());

        Ok(Self {
            local: local_str,
            rfn: rfn_str,
        })
    }
}

#[allow(clippy::module_name_repetitions)]
pub struct VerboseLoopAttrParser<'def, 'a, T> {
    locals: Vec<(String, radium::LocalKind, bool, radium::Type<'def>)>,
    scope: &'a T,
}

impl<'def, 'a, T: ParamLookup<'def>> VerboseLoopAttrParser<'def, 'a, T> {
    pub const fn new(
        locals: Vec<(String, radium::LocalKind, bool, radium::Type<'def>)>,
        scope: &'a T,
    ) -> Self {
        Self { locals, scope }
    }
}

impl<'def, 'a, T: ParamLookup<'def>> LoopAttrParser for VerboseLoopAttrParser<'def, 'a, T> {
    fn parse_loop_attrs<'b>(&'b mut self, attrs: &'b [&'b AttrItem]) -> Result<radium::LoopSpec, String> {
        let mut invariant: Vec<specs::IProp> = Vec::new();
        let mut inv_vars: Vec<InvVar> = Vec::new();
        let mut inv_var_set: HashSet<String> = HashSet::new();
        let mut existentials: Vec<coq::binder::Binder> = Vec::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&it.args.inner_tokens());

            match seg.ident.name.as_str() {
                "exists" => {
                    let params = RRParams::parse(&buffer, self.scope).map_err(str_err)?;
                    for param in params.params {
                        existentials.push(param.into());
                    }
                },
                "inv" => {
                    let parsed_iprop: MetaIProp = buffer.parse(self.scope).map_err(str_err)?;
                    invariant.push(parsed_iprop.into());
                },
                "inv_var" => {
                    let parsed_inv_var: InvVar = buffer.parse(self.scope).map_err(str_err)?;
                    inv_var_set.insert(parsed_inv_var.local.clone());
                    inv_vars.push(parsed_inv_var);
                },
                "ignore" => {
                    // ignore, this is the spec closure annotation
                },
                _ => {
                    return Err(format!("unknown attribute for loop specification: {:?}", args));
                },
            }
        }

        // now assemble the actual invariant
        // we split the local variables into three sets:
        // - named and definitely initialized variables, which we can use in the invariant
        // - named and maybe uninitialized variables, which we can not use in the invariant. Their type is
        //   preserved across the loop.
        // - compiler temporaries, which are required to be uninitialized. (NOTE: if we have mutable
        //   references around, this means that we need to extract observations and properly use their
        //   equalities)

        // binders that the invariant is parametric in
        let mut rfn_binders = Vec::new();

        // proposition for unknown locals
        let mut uninit_locals_prop: Vec<specs::IProp> = Vec::new();

        // track locals
        let mut inv_locals: Vec<String> = Vec::new();
        let mut uninit_locals: Vec<String> = Vec::new();
        let mut preserved_locals: Vec<String> = Vec::new();

        // get locals
        for (name, kind, initialized, ty) in &self.locals {
            // get the refinement type
            let mut rfn_ty = ty.get_rfn_type();
            let ty_st: specs::SynType = ty.into();
            // wrap it in place_rfn, since we reason about places
            rfn_ty = term::RefinedRustType::PlaceRfn(Box::new(rfn_ty)).into();

            let local_name = kind.mk_local_name(name);

            if *kind == radium::LocalKind::CompilerTemp {
                let pred = format!("{local_name} ◁ₗ[π, Owned false] .@ (◁ uninit {ty_st})");
                uninit_locals_prop.push(specs::IProp::Atom(pred));

                uninit_locals.push(local_name);
            } else if *initialized && inv_var_set.contains(name) {
                inv_locals.push(local_name);

                rfn_binders.push(coq::binder::Binder::new(Some(name.to_owned()), rfn_ty));
            } else {
                preserved_locals.push(local_name);
            }
        }

        // add constraints on refinements
        let mut var_invariants = Vec::new();
        for inv_var in inv_vars {
            var_invariants.push(specs::IProp::Pure(format!("{} = {}", inv_var.local, inv_var.rfn)));
        }

        var_invariants.extend(invariant);
        var_invariants.extend(uninit_locals_prop);

        let prop_body = specs::IProp::Sep(var_invariants);
        let prop_body = specs::IProp::Exists(existentials, Box::new(prop_body));

        let pred = radium::IPropPredicate::new(rfn_binders, prop_body);
        Ok(radium::LoopSpec::new(pred, inv_locals, preserved_locals, uninit_locals))
    }
}
