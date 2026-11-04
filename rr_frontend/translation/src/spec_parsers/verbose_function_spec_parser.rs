// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;
use std::mem;

use attribute_parse::{MToken, parse};
use log::info;
use parse::{Parse, Peek as _};
use radium::{coq, fmt_list, model, push_str_list, specs};
use rr_rustc_interface::hir;
use rr_rustc_interface::middle::hir::place;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::span::{DUMMY_SP, Span};

use crate::spec_parsers::SpannedError;
use crate::spec_parsers::parse_utils::{
    CoqLiteralError, IProp, IdentOrTerm, LiteralTypeWithRef, ParamLookup, Projection, Projections,
    RRCoqContextItem, RRParam, RRParams, RustPath, RustPlace, attr_args_tokens, str_err,
};

pub(crate) const COMMON_FUNCTION_SPEC_ATTRS: &[&str] = &[
    "params",
    "args",
    "returns",
    "requires",
    "ensures",
    "observe",
    "capture",
    "exists",
    "tactics",
    "unsafe_elctx",
    "context",
    "verify",
    "ok",
    "instantiate",
    "may_unwind_if",
];

pub(crate) const FUNCTION_SPEC_ATTRS: &[&str] = &[
    "code_shim",
    "export_as",
    "inline",
    "only_spec",
    "raw_mut_self",
    "verify",
    "trust_me",
    "use_panic_abort",
    "ensures_on_unwind",
];

pub(crate) const CLOSURE_SPEC_ATTRS: &[&str] =
    &["capture", "only_spec", "verify", "trust_me", "use_panic_abort"];

pub(crate) struct ClosureMetaInfo<'a, 'tcx, 'def> {
    /// the closure kind
    pub kind: ty::ClosureKind,
    /// capture information
    pub captures: &'tcx [&'tcx ty::CapturedPlace<'tcx>],
    /// the translated types of the captures, including the surrounding reference if captured by-ref.
    /// Needs to be in same order as `captures`
    pub capture_tys: &'a [specs::Type<'def>],
    /// the lifetime of the closure, if kind is `Fn` or `FnMut`
    pub closure_lifetime: Option<specs::Lft>,
}

#[derive(Clone, Eq, PartialEq, Debug, derive_more::Display)]
pub(crate) enum ParserError {
    #[display("{}", _0)]
    Parse(String),
    #[display("{}", _0)]
    AntiQuotation(CoqLiteralError),
    #[display("could not find name")]
    CouldNotFindName,
    #[display("expected {} function arguments, found a different count", _0)]
    WrongFunctionArgumentCount(usize),
    #[display("linktime assumptions are not allowed on closures")]
    LinktimeAssumptionsNotAllowedOnClosures,
    #[display("non-pure requires clause after rr::ok")]
    NonPureRequiresClauseAfterOk,
    #[display("non-pure ensures clause after rr::ok")]
    NonPureEnsuresClauseAfterOk,
    #[display("Did not expect postcondition {:?} for by-value capture", _0)]
    DidNotExpectPostconditionForByValueCapture(String),
    #[display("Closure captures ByUse, which is not supported")]
    ClosureCapturesByUseNotSupported,
    AmbiguousCapture(String),
    #[display("specified rr::returns and rr::ok at the same time")]
    SpecifiedReturnsAndOkAtSameTime,
    #[display("unknown closure attribute: {}", _0)]
    UnknownClosureAttribute(String),
    #[display("unknown function attribute: {}", _0)]
    UnknownFunctionAttribute(String),
    #[display("{}", _0)]
    Builder(String),
}

const fn spanned_error(span: Span, err: ParserError) -> SpannedError<ParserError> {
    SpannedError { err, span }
}

fn parse_err(span: Span, err: parse::Error) -> SpannedError<ParserError> {
    spanned_error(span, ParserError::Parse(str_err(err)))
}

pub(crate) struct ClosureSpecInfo {
    // the encoded pre and postconditions
    pub params_encoded: coq::term::Term,
    pub pre_encoded: coq::term::Term,
    pub post_encoded: coq::term::Term,
    pub post_mut_encoded: coq::term::Term,
    pub unwind_condition_encoded: coq::term::Term,
}
impl ClosureSpecInfo {
    fn new_from_parsed_spec<'def>(
        parsed_spec: &ParsedSpecInfo<'def>,
        parsed_captures: &ParsedClosureSpecInfo<'def>,
        extra_params: Vec<coq::binder::Binder>,
        extra_existentials: Vec<coq::binder::Binder>,
    ) -> Self {
        // TODO for the closure spec parser:
        // - disallow attributes that we cannot fit into this
        // - disallow overriding types
        //
        // Pre ext_params self args :=
        //  ∃ params, ext_params = *[...] ∧ self = # (pre_rfn) ∧ args = *[ $# args_patterns ] ∧ precond
        //
        // Post ext_params self args ret :=
        // ∃ params, ext_params = *[...] ∧ self = # (pre_rfn) ∧ args = *[ $# args_patterns ] ∧
        //  ∃ ex, ret = $# ret_pattern ∧ postcond ∧
        //      (observes for the mutable captures?)
        //
        // PostMut ext_params self args ret self' :=
        // ∃ params, ext_params = *[...] ∧ self = # (pre_rfn) ∧ args = *[ $# args_patterns ] ∧
        //  ∃ ex, ret = $# ret_pattern ∧ postcond ∧
        //    self' = post_pattern
        //

        // get all the params that will be a part of the `Params` type
        let ext_params = coq::binder::BinderList::new(
            parsed_spec.params.iter().filter_map(|(x, b)| b.then_some(x.0.clone())).collect(),
        );
        let ext_params_tys: Vec<_> = ext_params.0.iter().map(|x| x.get_type().unwrap().to_owned()).collect();
        let ext_params_ty = coq::term::Type::UserDefined(model::Type::PList(
            "id".to_owned(),
            ext_params_tys,
            "Type".to_owned(),
        ));

        let params_var = "_params";
        let params_binder = coq::binder::Binder::new(Some(params_var.to_owned()), ext_params_ty.clone());

        let self_var = "_self";
        let self_binder = coq::binder::Binder::new(Some(self_var.to_owned()), coq::term::RocqType::Infer);
        let args_var = "_args";
        let args_binder = coq::binder::Binder::new(Some(args_var.to_owned()), coq::term::RocqType::Infer);
        let ret_var = "_ret";
        let ret_binder = coq::binder::Binder::new(Some(ret_var.to_owned()), coq::term::RocqType::Infer);
        let self_post_var = "_self_post";
        let self_post_binder =
            coq::binder::Binder::new(Some(self_post_var.to_owned()), coq::term::RocqType::Infer);

        // params for the captures and the main spec
        let all_params = coq::binder::BinderList::new(
            parsed_spec
                .params
                .iter()
                .map(|(x, _)| x.0.clone())
                .chain(parsed_captures.params.iter().cloned())
                .chain(extra_params)
                .collect(),
        );
        let pre_self_rfn_clause = format!("{self_var} = ({})", parsed_captures.closure_self_rfn);
        let pre_args_rfn_clause = if parsed_spec.args.is_empty() {
            format!("{args_var} = tt")
        } else {
            format!("{args_var} = *[ {} ]", fmt_list!(&parsed_spec.args, "; ", |x| { x.1.clone() }))
        };

        // the clause for destructuring the external params
        let ext_params_rfn_clause =
            format!("{params_var} = *[ {} ]", fmt_list!(&ext_params.0, "; ", |x| { x.get_name() }));

        let all_existentials = coq::binder::BinderList::new(
            parsed_spec.existentials.iter().map(|x| x.0.clone()).chain(extra_existentials).collect(),
        );

        let ret_term = if let Some(ret) = &parsed_spec.ret { &ret.1 } else { "tt" };
        let post_ret_rfn_clause = format!("{ret_var} = ({ret_term})");

        // one variant for the PostMut predicate
        let mut post_ex_clauses_mut: Vec<coq::iris::IProp> =
            parsed_spec.postconditions.iter().map(|x| x.clone().into()).collect();
        post_ex_clauses_mut.insert(
            0,
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(post_ret_rfn_clause.clone()))),
        );
        // one for the Post predicate, which also contains the individual observations on FnOnce captures
        let mut post_ex_clauses: Vec<coq::iris::IProp> = parsed_spec
            .postconditions
            .iter()
            .map(|x| x.clone().into())
            .chain(parsed_captures.postconditions.iter().map(|x| x.clone().into()))
            .collect();
        post_ex_clauses
            .insert(0, coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(post_ret_rfn_clause))));

        let post_self_rfn_clause = format!("{self_post_var} = ({})", parsed_captures.closure_self_post_rfn);
        post_ex_clauses_mut
            .push(coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(post_self_rfn_clause))));

        let tid_binder = coq::binder::Binder::new(
            Some("π".to_owned()),
            coq::term::RocqType::UserDefined(model::Type::ThreadId),
        );

        let unwind_condition_encoded = if parsed_spec.unwind_conditions.is_empty() {
            coq::term::Term::Lambda(
                coq::binder::BinderList::new(vec![
                    self_binder.clone(),
                    params_binder.clone(),
                    args_binder.clone(),
                ]),
                Box::new(coq::term::Term::Literal("False".to_owned())),
            )
        } else {
            let unwind_condition = if parsed_spec.unwind_conditions.len() == 1 {
                parsed_spec.unwind_conditions[0].clone()
            } else {
                coq::term::Term::Infix("∨".to_owned(), parsed_spec.unwind_conditions.clone())
            };
            let unwind_condition = coq::term::Term::Exists(
                all_params.clone(),
                Box::new(coq::term::Term::Infix("∧".to_owned(), vec![
                    coq::term::Term::Literal(ext_params_rfn_clause.clone()),
                    coq::term::Term::Literal(pre_self_rfn_clause.clone()),
                    coq::term::Term::Literal(pre_args_rfn_clause.clone()),
                    unwind_condition,
                ])),
            );
            coq::term::Term::Lambda(
                coq::binder::BinderList::new(vec![
                    self_binder.clone(),
                    params_binder.clone(),
                    args_binder.clone(),
                ]),
                Box::new(unwind_condition),
            )
        };

        // assemble precondition
        let mut pre_clauses: Vec<coq::iris::IProp> =
            parsed_spec.preconditions.iter().map(|x| x.clone().into()).collect();
        pre_clauses.insert(
            0,
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(pre_self_rfn_clause.clone()))),
        );
        pre_clauses.insert(
            0,
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(pre_args_rfn_clause.clone()))),
        );
        pre_clauses.insert(
            0,
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(ext_params_rfn_clause.clone()))),
        );
        // make sure it's in goal shape
        pre_clauses.push(coq::iris::IProp::True);
        let pre = coq::iris::IProp::Exists(all_params.clone(), Box::new(coq::iris::IProp::Sep(pre_clauses)));
        let pre = pre.purify();
        let pre_encoded = coq::term::Term::Lambda(
            coq::binder::BinderList::new(vec![
                tid_binder.clone(),
                params_binder.clone(),
                self_binder.clone(),
                args_binder.clone(),
            ]),
            Box::new(coq::term::Term::UserDefined(model::Term::IProp(pre))),
        );

        // assemble postcondition
        let post_ex_clause = coq::iris::IProp::Exists(
            all_existentials.clone(),
            Box::new(coq::iris::IProp::Sep(post_ex_clauses)),
        );
        let post_clauses = vec![
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(ext_params_rfn_clause.clone()))),
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(pre_self_rfn_clause.clone()))),
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(pre_args_rfn_clause.clone()))),
            post_ex_clause,
            // make sure it's in goal shape
            coq::iris::IProp::True,
        ];
        let post =
            coq::iris::IProp::Exists(all_params.clone(), Box::new(coq::iris::IProp::Sep(post_clauses)));
        let post = post.purify();
        let post_encoded = coq::term::Term::Lambda(
            coq::binder::BinderList::new(vec![
                tid_binder.clone(),
                params_binder.clone(),
                self_binder.clone(),
                args_binder.clone(),
                ret_binder.clone(),
            ]),
            Box::new(coq::term::Term::UserDefined(model::Term::IProp(post))),
        );

        // assemble postmut
        let post_mut_ex_clause =
            coq::iris::IProp::Exists(all_existentials, Box::new(coq::iris::IProp::Sep(post_ex_clauses_mut)));
        let post_mut_clauses = vec![
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(ext_params_rfn_clause))),
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(pre_self_rfn_clause))),
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(pre_args_rfn_clause))),
            post_mut_ex_clause,
            // make sure it's in goal shape
            coq::iris::IProp::True,
        ];
        let post_mut =
            coq::iris::IProp::Exists(all_params, Box::new(coq::iris::IProp::Sep(post_mut_clauses)));
        let post_mut = post_mut.purify();
        let post_mut_encoded = coq::term::Term::Lambda(
            coq::binder::BinderList::new(vec![
                tid_binder,
                params_binder,
                self_binder,
                args_binder,
                self_post_binder,
                ret_binder,
            ]),
            Box::new(coq::term::Term::UserDefined(model::Term::IProp(post_mut))),
        );

        // Note: make sure to mangle the arg names of the generated lambdas, so we don't collide
        // with names in the specification (e.g. ret)
        Self {
            params_encoded: coq::term::RocqTerm::Type(Box::new(ext_params_ty)),
            pre_encoded,
            post_encoded,
            post_mut_encoded,
            unwind_condition_encoded,
        }
    }
}

pub(crate) trait FunctionSpecParser<'def> {
    /// Parse a set of attributes into a function spec.
    /// The implementation can assume the `attrs` to be prefixed by the tool prefix (e.g. `rr`) and
    /// that it does not need to deal with any other attributes.
    fn parse_function_spec<'a>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
        builder: &'a mut specs::functions::LiteralSpecBuilder<'def>,
    ) -> Result<(), SpannedError<ParserError>>;

    /// Parse a set of attributes into a closure spec.
    /// The implementation can assume the `attrs` to be prefixed by the tool prefix (e.g. `rr`) and
    /// that it does not need to deal with any other attributes.
    fn parse_closure_spec<'a, F>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
        builder: &'a mut specs::functions::LiteralSpecBuilder<'def>,
        closure_meta: ClosureMetaInfo<'_, '_, 'def>,
        make_tuple: F,
    ) -> Result<ClosureSpecInfo, SpannedError<ParserError>>
    where
        F: FnMut(Vec<specs::Type<'def>>) -> specs::Type<'def>;
}

/// A sequence of refinements with optional types, e.g.
/// `"42" @ "int i32", "1337", "(a, b)"`
#[derive(Debug)]
struct RRArgs {
    args: Vec<LiteralTypeWithRef>,
}

impl<'def, T: ParamLookup<'def>> Parse<T> for RRArgs {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let args: parse::Punctuated<LiteralTypeWithRef, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(stream, meta)?;
        Ok(Self {
            args: args.into_iter().collect(),
        })
    }
}

fn compute_projection(proj: &place::Place<'_>) -> Projections {
    let mut projections = Vec::new();
    let mut cur_ty = proj.base_ty;
    for x in &proj.projections {
        match x.kind {
            place::ProjectionKind::Deref => {
                projections.push(Projection::Deref);
            },
            place::ProjectionKind::Field(field, variant) => {
                if let ty::TyKind::Adt(def, _) = cur_ty.kind() {
                    let variant_def = def.variant(variant);
                    let field_def = variant_def.fields.get(field).unwrap();
                    let field_name = field_def.name.as_str();
                    projections.push(Projection::Field(field_name.to_owned()));
                } else {
                    unimplemented!("closure capture of Field, but this is not an ADT");
                }
            },
            _ => {
                unimplemented!("unsupported capture via projection {:?}", x.kind);
            },
        }
        cur_ty = x.ty;
    }

    Projections(projections)
}

type CaptureSpecMap = BTreeMap<RustPlace, (LiteralTypeWithRef, Option<LiteralTypeWithRef>)>;

/// Representation of the `IProps` that can appear in a requires or ensures clause.
#[derive(Clone, Debug)]
enum MetaIProp {
    /// `#[rr::requires("..")]` or `#[rr::requires("Ha" : "..")]`
    Pure(String, Option<String>),
    /// `#[rr::requires(#iris "..")]`
    Iris(coq::iris::IProp),
    /// `#[rr::requires(#type "l" : "rfn" @ "ty")]`
    Type(specs::TyOwnSpec),
    /// `#[rr::ensures(#observe "γ" : "2 * x")]`
    Observe(String, Option<String>, String),
    /// `#[rr::requires(#linktime "st_size {st_of T} < MaxInt isize")]`
    Linktime(String),
}

impl<'def, T: ParamLookup<'def>> Parse<T> for MetaIProp {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        if parse::Pound::peek(stream) {
            stream.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = stream.parse(meta)?;
            match macro_cmd.value().as_str() {
                "type" => {
                    let loc_span = stream.pos().unwrap_or(DUMMY_SP);
                    let loc_str: parse::LitStr = stream.parse(meta)?;
                    let (loc_str, mut annot_meta) = meta
                        .process_coq_literal(loc_span, &loc_str.value())
                        .map_err(|err| parse::Error::OtherErr(loc_span, err.to_string()))?;

                    stream.parse::<_, MToken![:]>(meta)?;

                    let rfn_span = stream.pos().unwrap_or(DUMMY_SP);
                    let rfn_str: parse::LitStr = stream.parse(meta)?;
                    let (rfn_str, annot_meta2) = meta
                        .process_coq_literal(rfn_span, &rfn_str.value())
                        .map_err(|err| parse::Error::OtherErr(rfn_span, err.to_string()))?;

                    annot_meta.join(&annot_meta2);

                    stream.parse::<_, MToken![@]>(meta)?;

                    let type_span = stream.pos().unwrap_or(DUMMY_SP);
                    let type_str: parse::LitStr = stream.parse(meta)?;
                    let (type_str, annot_meta3) = meta
                        .process_coq_literal(type_span, &type_str.value())
                        .map_err(|err| parse::Error::OtherErr(type_span, err.to_string()))?;
                    annot_meta.join(&annot_meta3);

                    let spec = specs::TyOwnSpec::new(loc_str, rfn_str, type_str, false, annot_meta);
                    Ok(Self::Type(spec))
                },
                "iris" => {
                    let prop: IProp = stream.parse(meta)?;
                    Ok(Self::Iris(prop.into()))
                },
                "observe" => {
                    let gname: parse::LitStr = stream.parse(meta)?;
                    stream.parse::<_, MToken![:]>(meta)?;

                    let term_span = stream.pos().unwrap_or(DUMMY_SP);
                    let term: parse::LitStr = stream.parse(meta)?;
                    let (term, _meta) = meta
                        .process_coq_literal(term_span, &term.value())
                        .map_err(|err| parse::Error::OtherErr(term_span, err.to_string()))?;

                    Ok(Self::Observe(gname.value(), None, term))
                },
                "linktime" => {
                    let term_span = stream.pos().unwrap_or(DUMMY_SP);
                    let term: parse::LitStr = stream.parse(meta)?;
                    let (term, _meta) = meta
                        .process_coq_literal(term_span, &term.value())
                        .map_err(|err| parse::Error::OtherErr(term_span, err.to_string()))?;
                    Ok(Self::Linktime(term))
                },
                _ => Err(parse::Error::OtherErr(
                    stream.pos().unwrap_or(DUMMY_SP),
                    format!("invalid macro command: {:?}", macro_cmd.value()),
                )),
            }
        } else {
            let name_or_prop_str: parse::LitStr = stream.parse(meta)?;
            if parse::Colon::peek(stream) {
                // this is a name
                let name_str = name_or_prop_str.value();

                stream.parse::<_, MToken![:]>(meta)?;

                let pure_span = stream.pos().unwrap_or(DUMMY_SP);
                let pure_prop: parse::LitStr = stream.parse(meta)?;
                let (pure_str, _annot_meta) = meta
                    .process_coq_literal(pure_span, &pure_prop.value())
                    .map_err(|err| parse::Error::OtherErr(pure_span, err.to_string()))?;
                // TODO: should we use annot_meta?

                Ok(Self::Pure(pure_str, Some(name_str)))
            } else {
                // this is a
                let lit_span = stream.pos().unwrap_or(DUMMY_SP);
                let (lit, _) = meta
                    .process_coq_literal(lit_span, &name_or_prop_str.value())
                    .map_err(|err| parse::Error::OtherErr(lit_span, err.to_string()))?;
                Ok(Self::Pure(lit, None))
            }
        }
    }
}

impl From<MetaIProp> for coq::iris::IProp {
    fn from(meta: MetaIProp) -> Self {
        match meta {
            MetaIProp::Pure(p, name) => match name {
                None => Self::Pure(Box::new(coq::term::Term::Literal(p))),
                Some(n) => Self::Pure(Box::new(coq::term::Term::UserDefined(model::Term::WithName(
                    Box::new(coq::term::Term::Literal(p)),
                    n,
                )))),
            },
            MetaIProp::Iris(p) => p,
            MetaIProp::Type(spec) => {
                let lit = spec.fmt_owned("π");
                Self::Atom(lit)
            },
            MetaIProp::Observe(name, ty_hint, term) => {
                if let Some(ty_hint) = ty_hint {
                    Self::Atom(format!("gvar_pobs {name} ($#@{{{ty_hint}}} {term})"))
                } else {
                    Self::Atom(format!("gvar_pobs {name} ({term})"))
                }
            },
            MetaIProp::Linktime(_) => Self::True,
        }
    }
}

/// Try to make it into a pure term
impl TryFrom<MetaIProp> for coq::term::Term {
    type Error = ();

    fn try_from(meta: MetaIProp) -> Result<Self, ()> {
        if let MetaIProp::Pure(p, name) = meta {
            let term = if let Some(name) = name { format!("name_hint \"{name}\" ({p})") } else { p };

            Ok(Self::Literal(term))
        } else {
            Err(())
        }
    }
}

/// The main parser.
pub(crate) struct VerboseFunctionSpecParser<'a, 'def, F, T> {
    /// argument types with substituted type parameters
    arg_types: &'a [specs::Type<'def>],
    /// return types with substituted type parameters
    ret_type: &'a specs::Type<'def>,

    /// whether the return type is an Option
    ret_is_option: bool,
    /// whether the return type is a Result
    ret_is_result: bool,

    /// optionally, the argument names of this function
    arg_names: Option<&'a [String]>,

    /// the scope of generics
    scope: &'a T,

    /// Function to intern a literal type
    make_literal: F,

    fn_requirements: FunctionRequirements,
}

/// State for assembling fallible specs
pub(crate) struct OkSpec {
    ok_mode: bool,
    ok_exists: Vec<coq::binder::Binder>,
    ok_requires: Vec<coq::term::Term>,
    ok_ensures: Vec<coq::term::Term>,
}

impl OkSpec {
    const fn new() -> Self {
        Self {
            ok_mode: false,
            ok_exists: Vec::new(),
            ok_requires: Vec::new(),
            ok_ensures: Vec::new(),
        }
    }
}

/// Extra requirements of a function.
#[derive(Default)]
pub(crate) struct FunctionRequirements {
    /// additional late coq parameters
    pub late_coq_params: Vec<coq::binder::Binder>,
    /// additional early coq parameters
    pub early_coq_params: Vec<coq::binder::Binder>,
    /// proof information
    pub proof_info: ProofInfo,
}

/// Proof information that we parse.
#[derive(Default)]
pub(crate) struct ProofInfo {
    /// sidecondition tactics that are annotated
    pub sidecond_tactics: Vec<String>,
    /// linktime assumptions
    pub linktime_assumptions: Vec<String>,
}

impl<'a, 'def, F, T> From<VerboseFunctionSpecParser<'a, 'def, F, T>> for FunctionRequirements {
    fn from(x: VerboseFunctionSpecParser<'a, 'def, F, T>) -> Self {
        x.fn_requirements
    }
}

impl<'a, 'def, F, T: ParamLookup<'def>> VerboseFunctionSpecParser<'a, 'def, F, T>
where
    F: Fn(specs::types::Literal) -> specs::types::LiteralRef<'def>,
{
    /// Type parameters must already have been substituted in the given types.
    pub(crate) fn new(
        arg_types: &'a [specs::Type<'def>],
        ret_type: &'a specs::Type<'def>,
        ret_is_option: bool,
        ret_is_result: bool,
        arg_names: Option<&'a [String]>,
        scope: &'a T,
        make_literal: F,
    ) -> Self {
        VerboseFunctionSpecParser {
            arg_types,
            ret_type,
            ret_is_option,
            ret_is_result,
            arg_names,
            make_literal,
            scope,
            fn_requirements: FunctionRequirements::default(),
        }
    }

    /// Given a type annotation (either `r` or `r @ ty0`) and a translated Rust type `ty`, get the
    /// full type with refinement and, optionally, a Coq refinement type hint that will be used
    /// for the refinement `r`.
    fn make_type_with_ref(
        &self,
        lit: &LiteralTypeWithRef,
        ty: &specs::Type<'def>,
    ) -> (specs::TypeWithRef<'def>, Option<coq::term::Type>) {
        if let Some(lit_ty) = &lit.ty {
            // literal type given, we use this literal type as the RR semantic type
            // TODO: get CoqType for refinement. maybe have it as an annotation? the Infer is currently a
            // placeholder.

            let lit_ty = specs::types::Literal {
                rust_name: None,
                type_term: lit_ty.to_owned(),
                refinement_type: coq::term::Type::Infer,
                syn_type: ty.into(),
                raw_type: None,
                info: specs::types::AdtShimInfo::empty(),
            };
            let lit_ref = (self.make_literal)(lit_ty);
            let lit_ty_use = specs::types::LiteralUse::new_with_annot(lit_ref);

            (specs::TypeWithRef::new(specs::Type::Literal(lit_ty_use), lit.rfn.to_string()), None)
        } else {
            // no literal type given, just a refinement
            // we use the translated Rust type with the given refinement
            let mut ty = ty.clone();
            if lit.raw == specs::structs::TypeIsRaw::Yes {
                ty.make_raw();
            }
            let rt = ty.get_xt_type();
            (specs::TypeWithRef::new(ty, lit.rfn.to_string()), Some(rt))
        }
    }
}

struct ParsedSpecInfo<'def> {
    // boolean flag indicates whether this is a param explicitly added via a rr::params clause or
    // not
    params: Vec<(RRParam, bool)>,
    args: Vec<specs::TypeWithRef<'def>>,
    preconditions: Vec<MetaIProp>,
    postconditions: Vec<MetaIProp>,
    unwind_conditions: Vec<coq::term::Term>,
    unwind_postconditions: Vec<MetaIProp>,
    existentials: Vec<RRParam>,
    ret: Option<specs::TypeWithRef<'def>>,
    unsafe_lifetime_constraints: Vec<String>,

    ok_spec: OkSpec,

    got_args: bool,
}

impl<'def> ParsedSpecInfo<'def> {
    const fn new() -> Self {
        Self {
            params: Vec::new(),
            args: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            unwind_conditions: Vec::new(),
            unwind_postconditions: Vec::new(),
            existentials: Vec::new(),
            ret: None,
            unsafe_lifetime_constraints: Vec::new(),
            ok_spec: OkSpec::new(),
            got_args: false,
        }
    }

    fn push_to_builder(
        &self,
        builder: &mut specs::functions::LiteralSpecBuilder<'def>,
    ) -> Result<(), String> {
        for (param, _) in &self.params {
            builder.add_param(param.clone().into())?;
        }

        for arg in &self.args {
            builder.add_arg(arg.to_owned());
        }

        for pre in &self.preconditions {
            let pre: MetaIProp = pre.to_owned();
            builder.add_precondition(pre.into());
        }

        for post in &self.postconditions {
            let post = post.to_owned();
            builder.add_postcondition(post.into());
        }

        for condition in &self.unwind_conditions {
            builder.add_unwind_condition(condition.to_owned());
        }

        for post in &self.unwind_postconditions {
            builder.add_unwind_postcondition(post.to_owned().into());
        }

        for ex in &self.existentials {
            let ex = ex.to_owned();
            builder.add_existential(ex.into())?;
        }

        if let Some(ret) = &self.ret {
            builder.set_ret_type(ret.to_owned())?;
        }

        for cstr in &self.unsafe_lifetime_constraints {
            builder.add_literal_lifetime_constraint(cstr.to_owned());
        }

        if self.ret.is_some() && self.got_args {
            builder.have_spec();
        }

        Ok(())
    }

    /// add a coq type annotation for a parameter when no type is currently known.
    /// this can e.g. be used to later on add knowledge about the type of a refinement.
    fn add_param_type_annot(
        &mut self,
        span: Span,
        name: &String,
        ty: coq::term::Type,
    ) -> Result<(), SpannedError<ParserError>> {
        for (param, _) in &mut self.params {
            let Some(param_name) = param.0.get_name_ref() else {
                continue;
            };

            if param_name == name {
                let Some(param_ty) = param.0.get_type() else {
                    unreachable!("Binder is typed");
                };

                if *param_ty == coq::term::Type::Infer {
                    param.0 = coq::binder::Binder::new(Some(name.clone()), ty);
                }
                return Ok(());
            }
        }
        Err(spanned_error(span, ParserError::CouldNotFindName))
    }

    /// Assemble a fallible specification.
    fn assemble_fallible_spec(
        &mut self,
        span: Span,
        ret_name: &str,
        ret_is_option: bool,
        ret_is_result: bool,
    ) -> Result<(), SpannedError<ParserError>> {
        let ok_spec = mem::replace(&mut self.ok_spec, OkSpec::new());

        // now assemble the ok-specification
        if ok_spec.ok_mode {
            if !(ret_is_option || ret_is_result) {
                return Err(spanned_error(span, ParserError::SpecifiedReturnsAndOkAtSameTime));
            }

            let conjoined_postconds = coq::term::Term::Exists(
                coq::binder::BinderList::new(ok_spec.ok_exists),
                Box::new(coq::term::Term::Infix("∧".to_owned(), ok_spec.ok_ensures)),
            );

            // The encoding assumes that the preconditions are precise to distinguish the success
            // and failure cases.
            let mut ok_case_conjuncts = ok_spec.ok_requires.clone();
            ok_case_conjuncts.push(conjoined_postconds);
            let ok_condition = coq::term::Term::Infix("∧".to_owned(), ok_case_conjuncts);

            let lambda_binders = coq::binder::BinderList::new(vec![coq::binder::Binder::new(
                Some(ret_name.to_owned()),
                coq::term::Type::Infer,
            )]);
            let ok_condition = coq::term::Term::Lambda(lambda_binders.clone(), Box::new(ok_condition));

            let err_condition = coq::term::Term::Prefix(
                "¬".to_owned(),
                Box::new(coq::term::Term::Infix("∧".to_owned(), ok_spec.ok_requires)),
            );

            if ret_is_result {
                let ok_condition = coq::term::Term::App(Box::new(coq::term::App::new(
                    coq::term::Term::Literal(format!("if_Ok {ret_name}")),
                    vec![ok_condition],
                )));

                self.postconditions.push(MetaIProp::Pure(ok_condition.to_string(), None));

                let err_condition = coq::term::Term::Lambda(lambda_binders, Box::new(err_condition));
                let err_condition = coq::term::Term::App(Box::new(coq::term::App::new(
                    coq::term::Term::Literal(format!("if_Err {ret_name}")),
                    vec![err_condition],
                )));

                self.postconditions.push(MetaIProp::Pure(err_condition.to_string(), None));
            } else if ret_is_option {
                let some_condition = coq::term::Term::App(Box::new(coq::term::App::new(
                    coq::term::Term::Literal(format!("if_Some {ret_name}")),
                    vec![ok_condition],
                )));

                self.postconditions.push(MetaIProp::Pure(some_condition.to_string(), None));

                let none_condition = err_condition;
                let none_condition = coq::term::Term::App(Box::new(coq::term::App::new(
                    coq::term::Term::Literal(format!("if_None {ret_name}")),
                    vec![none_condition],
                )));

                self.postconditions.push(MetaIProp::Pure(none_condition.to_string(), None));
            }
        }

        Ok(())
    }
}

/// Specification parts related to the captures of a closure.
struct ParsedClosureSpecInfo<'def> {
    params: Vec<coq::binder::Binder>,
    postconditions: Vec<MetaIProp>,
    fnmut_observes: Option<MetaIProp>,
    closure_arg: specs::TypeWithRef<'def>,
    closure_self_rfn: String,
    closure_self_post_rfn: String,
}

impl<'def> ParsedClosureSpecInfo<'def> {
    fn push_to_builder(
        &self,
        builder: &mut specs::functions::LiteralSpecBuilder<'def>,
    ) -> Result<(), String> {
        for param in &self.params {
            builder.add_param(param.to_owned())?;
        }

        // we have one big observation for self
        if let Some(fnmut_observes) = &self.fnmut_observes {
            builder.add_postcondition(fnmut_observes.to_owned().into());
        } else {
            // otherwise, add the smaller postconditions on individual mutable captures
            for post in &self.postconditions {
                builder.add_postcondition(post.to_owned().into());
            }
        }

        builder.add_arg(self.closure_arg.clone());

        Ok(())
    }
}

impl<'def, F, T: ParamLookup<'def>> VerboseFunctionSpecParser<'_, 'def, F, T>
where
    F: Fn(specs::types::Literal) -> specs::types::LiteralRef<'def>,
{
    /// Handles attributes common among functions/methods and closures.
    fn handle_common_attributes<X>(
        &mut self,
        span: Span,
        name: &str,
        buffer: &parse::Buffer,
        builder: &mut ParsedSpecInfo<'def>,
        scope: &X,
        in_closure: bool,
    ) -> Result<bool, SpannedError<ParserError>>
    where
        X: ParamLookup<'def>,
    {
        match name {
            "ok" => {
                builder.ok_spec.ok_mode = true;
            },
            "params" => {
                let params = RRParams::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                for param in params.params {
                    builder.params.push((param, true));
                }
            },
            "param" => {
                let param = RRParam::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                builder.params.push((param, true));
            },
            "args" => {
                let args = RRArgs::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                if self.arg_types.len() != args.args.len() {
                    return Err(spanned_error(
                        span,
                        ParserError::WrongFunctionArgumentCount(self.arg_types.len()),
                    ));
                }
                builder.got_args = true;
                for (arg, ty) in args.args.into_iter().zip(self.arg_types) {
                    let (ty, hint) = self.make_type_with_ref(&arg, ty);
                    builder.args.push(ty);
                    if let Some(cty) = hint {
                        // potentially add a typing hint to the refinement
                        if let IdentOrTerm::Ident(i) = arg.rfn {
                            info!("Trying to add a typing hint for {}", i);
                            builder.add_param_type_annot(span, &i, cty)?;
                        }
                    }
                }
            },
            "requires" => {
                let iprop = MetaIProp::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                info!("parsed iprop: {iprop:?}");
                if let MetaIProp::Linktime(assum) = iprop {
                    if in_closure {
                        return Err(spanned_error(
                            span,
                            ParserError::LinktimeAssumptionsNotAllowedOnClosures,
                        ));
                    }
                    self.fn_requirements.proof_info.linktime_assumptions.push(assum);
                } else if builder.ok_spec.ok_mode {
                    // only accept pure assertions
                    if !matches!(iprop, MetaIProp::Pure(_, _)) {
                        return Err(spanned_error(span, ParserError::NonPureRequiresClauseAfterOk));
                    }
                    let term = iprop.try_into().unwrap();
                    builder.ok_spec.ok_requires.push(term);
                } else {
                    builder.preconditions.push(iprop);
                }
            },
            "ensures" => {
                let iprop = MetaIProp::parse(buffer, scope).map_err(|err| parse_err(span, err))?;

                if builder.ok_spec.ok_mode {
                    // only accept pure assertions
                    if !matches!(iprop, MetaIProp::Pure(_, _)) {
                        return Err(spanned_error(span, ParserError::NonPureEnsuresClauseAfterOk));
                    }
                    builder.ok_spec.ok_ensures.push(iprop.try_into().unwrap());
                } else {
                    builder.postconditions.push(iprop);
                }
            },
            "observe" => {
                let m = || {
                    let gname: parse::LitStr = buffer.parse(scope)?;
                    buffer.parse::<_, MToken![:]>(scope)?;

                    let term: parse::LitStr = buffer.parse(scope)?;
                    let (term, _) = scope
                        .process_coq_literal(span, &term.value())
                        .map_err(|err| parse::Error::OtherErr(span, err.to_string()))?;
                    Ok(MetaIProp::Observe(gname.value(), None, term))
                };
                let m = m().map_err(|err| parse_err(span, err))?;
                builder.postconditions.push(m);
            },
            "returns" => {
                let tr = LiteralTypeWithRef::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                // convert to type
                let (ty, _) = self.make_type_with_ref(&tr, self.ret_type);
                builder.ret = Some(ty);
            },
            "exists" => {
                let params = RRParams::parse(buffer, scope).map_err(|err| parse_err(span, err))?;

                if builder.ok_spec.ok_mode {
                    for param in params.params {
                        builder.ok_spec.ok_exists.push(param.into());
                    }
                } else {
                    for param in params.params {
                        builder.existentials.push(param);
                    }
                }
            },
            "tactics" => {
                let tacs = parse::LitStr::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                let tacs = tacs.value();
                self.fn_requirements.proof_info.sidecond_tactics.push(tacs);
            },
            "unsafe_elctx" => {
                // TODO: do not allow this on closures.
                let term = parse::LitStr::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                let (term, _) = scope
                    .process_coq_literal(span, &term.value())
                    .map_err(|err| spanned_error(span, ParserError::AntiQuotation(err)))?;
                builder.unsafe_lifetime_constraints.push(term);
            },
            "context" => {
                // TODO: do not allow this on closures?
                let context_item =
                    RRCoqContextItem::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                let at_end = context_item.at_end;
                let param = context_item.into();
                if at_end {
                    self.fn_requirements.late_coq_params.push(param);
                } else {
                    self.fn_requirements.early_coq_params.push(param);
                }
            },
            "verify" => {
                // accept the attribute, but do not adjust the spec
            },
            "may_unwind_if" => {
                let invalid_argument = || {
                    spanned_error(
                        span,
                        ParserError::Parse("may_unwind_if expects exactly one string literal".to_owned()),
                    )
                };
                let condition = parse::LitStr::parse(buffer, scope).map_err(|_err| invalid_argument())?;
                if buffer.pos().is_some() {
                    return Err(invalid_argument());
                }
                let (condition, _) = scope
                    .process_coq_literal(span, &condition.value())
                    .map_err(|err| spanned_error(span, ParserError::AntiQuotation(err)))?;
                builder.unwind_conditions.push(coq::term::Term::Literal(condition));
            },
            "ensures_on_unwind" => {
                let iprop = MetaIProp::parse(buffer, scope).map_err(|err| parse_err(span, err))?;
                builder.unwind_postconditions.push(iprop);
            },
            _ => {
                return Ok(false);
            },
        }

        Ok(true)
    }

    /// Merges information on captured variables with specifications on captures.
    /// `capture_specs`: the parsed capture specification
    /// `make_tuple`: closure to make a new Radium tuple type
    /// `builder`: the function builder to push new specification components to
    fn merge_capture_information<H>(
        &self,
        span: Span,
        capture_specs: &CaptureSpecMap,
        meta: ClosureMetaInfo<'_, '_, 'def>,
        mut make_tuple: H,
    ) -> Result<ParsedClosureSpecInfo<'def>, SpannedError<ParserError>>
    where
        H: FnMut(Vec<specs::Type<'def>>) -> specs::Type<'def>,
    {
        enum CapturePostRfn {
            // mutable capture: (pattern, ghost_var, type_behind_reference)
            Mut(String, String, String),
            // immutable or once capture: pattern
            ImmutOrConsume(String),
        }

        // new ghost vars created for mut-captures
        let mut new_ghost_vars: Vec<String> = Vec::new();
        let mut pre_types: Vec<specs::TypeWithRef<'_>> = Vec::new();
        // post patterns and optional ghost variable, if this is a by-mut-ref capture
        let mut post_patterns: Vec<CapturePostRfn> = Vec::new();

        // Plan:
        // First phase:
        // - implicit binding of captures
        // - for that, generate the map from the captures. add bindes to params.
        // - for post binders: maybe introduce a new name/notation for referring to that and then
        // just allow to specify equality constraints. e.g., x.new?
        //
        // Second phase:
        // - allow captures of projections
        //
        //
        // First, let's add the infrastructure for projections, even if rr::captures can't specify
        // them now

        // assemble the pre types
        for (capture, ty) in meta.captures.iter().zip(meta.capture_tys.iter()) {
            let projections = compute_projection(&capture.place);
            let base = capture.var_ident.name.as_str();
            let projection_suffix = projections.to_string();
            let capture_ghost_name = if projection_suffix.is_empty() {
                format!("_γcapture_{base}_g")
            } else {
                format!("_γcapture_{base}_{projection_suffix}_g")
            };
            let place = RustPlace {
                base: base.to_owned(),
                proj: projections,
            };
            if let Some((pre, post)) = capture_specs.get(&place) {
                // we kinda want to specify the thing independently of how it is captured
                match capture.info.capture_kind {
                    ty::UpvarCapture::ByValue => {
                        // full ownership
                        let (processed_ty, _) = self.make_type_with_ref(pre, ty);
                        let rfn = processed_ty.1.clone();
                        pre_types.push(processed_ty);

                        if let Some(post) = post {
                            // this should not contain any post
                            return Err(spanned_error(
                                span,
                                ParserError::DidNotExpectPostconditionForByValueCapture(format!(
                                    "{:?}",
                                    post
                                )),
                            ));
                        }

                        // to make things well-typed in the PostMut definition
                        post_patterns.push(CapturePostRfn::ImmutOrConsume(rfn));
                    },
                    ty::UpvarCapture::ByRef(ty::BorrowKind::Immutable) => {
                        // shared borrow
                        // if there's a manually specified type, we need to wrap it in the reference
                        if let specs::Type::ShrRef(deref!(auto_type), lft) = ty {
                            let (processed_ty, _) = self.make_type_with_ref(pre, auto_type);
                            // now wrap it in a shared reference again
                            let altered_ty = specs::Type::ShrRef(Box::new(processed_ty.0), lft.clone());
                            let altered_rfn = format!("({})", processed_ty.1);
                            pre_types.push(specs::TypeWithRef::new(altered_ty, altered_rfn.clone()));

                            // push the same pattern for the post, no ghost variable
                            post_patterns.push(CapturePostRfn::ImmutOrConsume(altered_rfn));
                        }
                    },
                    ty::UpvarCapture::ByRef(_) => {
                        // mutable borrow
                        // we handle ty::BorrowKind::Mutable and ty::BorrowKind::UniqueImmutable
                        // the same way, as they are not really different for RefinedRust's type
                        // system
                        if let specs::Type::MutRef(deref!(auto_type), lft) = ty {
                            let (processed_ty, _) = self.make_type_with_ref(pre, auto_type);
                            // now wrap it in a mutable reference again
                            // we create a ghost variable
                            let ghost_var = capture_ghost_name;
                            new_ghost_vars.push(ghost_var.clone());
                            let altered_ty = specs::Type::MutRef(Box::new(processed_ty.0), lft.clone());
                            let altered_rfn = format!("(({}), {ghost_var})", processed_ty.1);
                            pre_types.push(specs::TypeWithRef::new(altered_ty, altered_rfn));

                            // NB: needs the rfn type, not the xt type.
                            let type_hint = auto_type.get_rfn_type().to_string();
                            if let Some(post) = post {
                                post_patterns.push(CapturePostRfn::Mut(
                                    post.rfn.to_string(),
                                    ghost_var,
                                    type_hint,
                                ));
                            } else {
                                // push the same pattern for the post
                                post_patterns.push(CapturePostRfn::Mut(processed_ty.1, ghost_var, type_hint));
                            }
                        }
                    },
                    ty::UpvarCapture::ByUse => {
                        // The semantics of this are not really clear yet
                        return Err(spanned_error(span, ParserError::ClosureCapturesByUseNotSupported));
                    },
                }
            } else {
                return Err(spanned_error(span, ParserError::AmbiguousCapture(format!("{:?}", capture))));
            }
        }

        let mut params = Vec::new();
        let closure_arg;
        let mut postconditions = Vec::new();

        // push everything to the builder
        for x in new_ghost_vars {
            params.push(coq::binder::Binder::new(Some(x), model::Type::Gname));
        }

        // assemble a string for the closure arg
        let mut pre_rfn_pat = String::new();
        let mut pre_tys = Vec::new();
        let mut pre_rfn_term = String::new();

        if pre_types.is_empty() {
            pre_rfn_pat.push_str("()");
            pre_rfn_term.push_str("tt");
        } else {
            pre_rfn_pat.push_str(" *[");
            push_str_list!(pre_rfn_pat, pre_types.clone(), "; ", |x| format!("({})", x.1));
            pre_rfn_pat.push(']');

            pre_rfn_term.push_str(" *[");
            push_str_list!(pre_rfn_term, pre_types.clone(), "; ", |x| format!("({})", x.1));
            pre_rfn_term.push(']');

            pre_tys = pre_types.iter().map(|x| x.0.clone()).collect();
        }
        let capture_tuple = make_tuple(pre_tys);

        // the term describing the refinement of the closure after the closure returns
        let mut post_rfn_pat = String::new();
        let mut post_rfn_term = String::new();
        if post_patterns.is_empty() {
            post_rfn_pat.push_str("()");
            post_rfn_term.push_str("tt");
        } else {
            post_rfn_pat.push_str(" *[");
            push_str_list!(post_rfn_pat, &post_patterns, "; ", |p| match p {
                CapturePostRfn::ImmutOrConsume(pat) => format!("({pat})"),
                CapturePostRfn::Mut(pat, gvar, _) => format!("(({pat}), {gvar})"),
            });
            post_rfn_pat.push(']');

            post_rfn_term.push_str(" *[");
            push_str_list!(post_rfn_term, &post_patterns, "; ", |p| match p {
                CapturePostRfn::ImmutOrConsume(pat) => format!("({pat})"),
                CapturePostRfn::Mut(pat, gvar, _) => format!("(({pat}), {gvar})"),
            });
            post_rfn_term.push(']');
        }
        let mut fnmut_observes = None;

        // generate observations on all the mut-ref captures
        for p in post_patterns {
            match p {
                CapturePostRfn::ImmutOrConsume(_) => {
                    // nothing mutated
                },
                CapturePostRfn::Mut(pat, gvar, type_hint) => {
                    // add an observation on `gvar`
                    postconditions.push(MetaIProp::Observe(gvar, Some(type_hint), pat));
                },
            }
        }

        match meta.kind {
            ty::ClosureKind::FnOnce => {
                closure_arg = specs::TypeWithRef::new(capture_tuple, pre_rfn_pat);
            },
            ty::ClosureKind::Fn => {
                // wrap the argument in a shared reference
                // all the captures are by shared ref

                let lft = meta.closure_lifetime.unwrap();
                let ref_ty = specs::Type::ShrRef(Box::new(capture_tuple), lft);
                let ref_rfn = pre_rfn_pat;

                closure_arg = specs::TypeWithRef::new(ref_ty, ref_rfn);
            },
            ty::ClosureKind::FnMut => {
                // wrap the argument in a mutable reference
                let post_name = "__γclos";
                params.push(coq::binder::Binder::new(Some(post_name.to_owned()), model::Type::Gname));

                let lft = meta.closure_lifetime.unwrap();
                let ref_ty = specs::Type::MutRef(Box::new(capture_tuple.clone()), lft);
                let ref_rfn = format!("(({}), {})", pre_rfn_pat, post_name);

                closure_arg = specs::TypeWithRef::new(ref_ty, ref_rfn);

                // assemble a postcondition on the closure
                // we observe on the outer mutable reference for the capture, not on the individual
                // references
                fnmut_observes = Some(MetaIProp::Observe(
                    post_name.to_owned(),
                    Some(capture_tuple.get_rfn_type().to_string()),
                    post_rfn_pat,
                ));
            },
        }

        let spec = ParsedClosureSpecInfo {
            params,
            postconditions,
            fnmut_observes,
            closure_arg,
            closure_self_rfn: pre_rfn_term,
            closure_self_post_rfn: post_rfn_term,
        };

        Ok(spec)
    }

    /// In case we didn't get a specification of argument and return types, add the default types,
    /// and add binders to refer to them by their Rust name
    fn add_default_spec(
        &self,
        span: Span,
        spec: &mut ParsedSpecInfo<'def>,
    ) -> Result<(), SpannedError<ParserError>> {
        if !spec.got_args
            && let Some(arg_names) = self.arg_names
        {
            for (arg, ty) in arg_names.iter().zip(self.arg_types) {
                spec.params.push((
                    RRParam(coq::binder::Binder::new(Some(arg.to_owned()), coq::term::Type::Infer)),
                    false,
                ));
                let ty_with_ref = specs::TypeWithRef::new(ty.to_owned(), arg.to_owned());
                spec.args.push(ty_with_ref);
            }
            spec.got_args = true;
        }
        // TODO: if we don't have arg names, use _0 ... etc

        let implicit_ret_name = "ret";
        let is_implicit_ret = if spec.ret.is_some() {
            false
        } else {
            // create a new ret val that is existentially quantified
            spec.existentials.push(RRParam(coq::binder::Binder::new(
                Some(implicit_ret_name.to_owned()),
                coq::term::Type::Infer,
            )));

            let tr = LiteralTypeWithRef {
                rfn: IdentOrTerm::Ident(implicit_ret_name.to_owned()),
                ty: None,
                raw: specs::structs::TypeIsRaw::No,
            };
            let (ty, _) = self.make_type_with_ref(&tr, self.ret_type);

            spec.ret = Some(ty);

            true
        };

        if spec.ok_spec.ok_mode {
            if !is_implicit_ret {
                return Err(spanned_error(span, ParserError::SpecifiedReturnsAndOkAtSameTime));
            }
            spec.assemble_fallible_spec(span, implicit_ret_name, self.ret_is_option, self.ret_is_result)?;
        }
        Ok(())
    }
}

struct ClosureCaptureScope<'a, T> {
    scope: &'a T,
    map: &'a CaptureSpecMap,
}
impl<'def, T> ParamLookup<'def> for ClosureCaptureScope<'_, T>
where
    T: ParamLookup<'def>,
{
    fn lookup_ty_param(&self, path: &RustPath) -> Option<specs::Type<'def>> {
        self.scope.lookup_ty_param(path)
    }

    fn lookup_lft(&self, lft: &str) -> Option<&specs::LftParam> {
        self.scope.lookup_lft(lft)
    }

    fn lookup_literal(&self, path: &RustPath) -> Option<String> {
        self.scope.lookup_literal(path)
    }

    fn lookup_place(&self, place: &RustPlace, modifier: Option<String>) -> Option<String> {
        let x = self.map.get(place)?;
        if let Some(modifier) = modifier {
            if modifier == "new"
                && let Some(y) = &x.1
            {
                Some(y.rfn.to_string())
            } else {
                None
            }
        } else {
            Some(x.0.rfn.to_string())
        }
    }
}

impl<'def, F, T: ParamLookup<'def>> FunctionSpecParser<'def> for VerboseFunctionSpecParser<'_, 'def, F, T>
where
    F: Fn(specs::types::Literal) -> specs::types::LiteralRef<'def>,
{
    fn parse_closure_spec<'a, H>(
        &'a mut self,
        attrs: &'a [&'a hir::AttrItem],
        builder: &'a mut specs::functions::LiteralSpecBuilder<'def>,
        closure_meta: ClosureMetaInfo<'_, '_, 'def>,
        make_tuple: H,
    ) -> Result<ClosureSpecInfo, SpannedError<ParserError>>
    where
        H: FnMut(Vec<specs::Type<'def>>) -> specs::Type<'def>,
    {
        let span = attrs.first().map_or(DUMMY_SP, |a| a.span);
        let mut spec = ParsedSpecInfo::new();

        let mut capture_spec_map: CaptureSpecMap = BTreeMap::new();
        let mut param_binders = Vec::new();
        let mut ex_binders = Vec::new();
        for (capture, ty) in closure_meta.captures.iter().zip(closure_meta.capture_tys) {
            let projection = compute_projection(&capture.place);
            let base = capture.var_ident.name.as_str();
            let kind = capture.info.capture_kind;
            let capture_is_mut = matches!(kind, ty::UpvarCapture::ByRef(ty::BorrowKind::Mutable));
            let capture_name = format!("capture_{base}_{projection}");
            let capture_post_name = format!("capture_{base}_{projection}_new");

            let capture_ty = if matches!(kind, ty::UpvarCapture::ByRef(_)) {
                if let specs::Type::MutRef(ty, _) = ty {
                    ty.get_xt_type()
                } else if let specs::Type::ShrRef(ty, _) = ty {
                    ty.get_xt_type()
                } else {
                    unreachable!();
                }
            } else {
                ty.get_xt_type()
            };

            let capture_binder = coq::binder::Binder::new(Some(capture_name), capture_ty.clone());
            let pre_ty = LiteralTypeWithRef {
                rfn: IdentOrTerm::Term(capture_binder.get_name_ref().as_ref().unwrap().to_owned()),
                ty: None,
                raw: specs::structs::TypeIsRaw::No,
            };
            let capture_post = capture_is_mut.then(|| {
                let binder = coq::binder::Binder::new(Some(capture_post_name.clone()), capture_ty);
                let post_ty = LiteralTypeWithRef {
                    rfn: IdentOrTerm::Term(capture_post_name),
                    ty: None,
                    raw: specs::structs::TypeIsRaw::No,
                };
                (binder, post_ty)
            });

            param_binders.push(capture_binder);
            if let Some((binder, _)) = &capture_post {
                ex_binders.push(binder.to_owned());
            }

            let place = RustPlace {
                base: base.to_owned(),
                proj: projection,
            };

            capture_spec_map.insert(place, (pre_ty, capture_post.map(|x| x.1)));
        }

        for param in &param_binders {
            builder
                .add_param(param.to_owned())
                .map_err(|err| spanned_error(span, ParserError::Builder(err)))?;
        }
        for param in &ex_binders {
            builder
                .add_existential(param.to_owned())
                .map_err(|err| spanned_error(span, ParserError::Builder(err)))?;
        }

        let scope = ClosureCaptureScope {
            scope: self.scope,
            map: &capture_spec_map,
        };

        let capture_spec =
            self.merge_capture_information(span, &capture_spec_map, closure_meta, make_tuple)?;
        capture_spec
            .push_to_builder(builder)
            .map_err(|err| spanned_error(span, ParserError::Builder(err)))?;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::Buffer::new(&attr_args_tokens(args));
                let name = seg.as_str();

                let handled =
                    self.handle_common_attributes(it.span, name, &buffer, &mut spec, &scope, true)?;
                if !handled
                    && name != "capture"
                    && name != "only_spec"
                    && name != "verify"
                    && name != "trust_me"
                    && name != "use_panic_abort"
                {
                    return Err(spanned_error(
                        it.span,
                        ParserError::UnknownClosureAttribute(name.to_owned()),
                    ));
                }
            }
        }

        // in case we didn't get an args annotation,
        // implicitly add argument parameters matching their Rust names
        // IMPORTANT: We do this after pushing the `capture_spec`
        self.add_default_spec(span, &mut spec)?;
        spec.push_to_builder(builder)
            .map_err(|err| spanned_error(span, ParserError::Builder(err)))?;

        let spec_info =
            ClosureSpecInfo::new_from_parsed_spec(&spec, &capture_spec, param_binders, ex_binders);

        Ok(spec_info)
    }

    fn parse_function_spec(
        &mut self,
        attrs: &[&hir::AttrItem],
        builder: &mut specs::functions::LiteralSpecBuilder<'def>,
    ) -> Result<(), SpannedError<ParserError>> {
        let span = attrs.first().map_or(DUMMY_SP, |a| a.span);
        let mut spec = ParsedSpecInfo::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(args));
            let name = seg.as_str();
            match self.handle_common_attributes(it.span, name, &buffer, &mut spec, self.scope, false) {
                Ok(b) => {
                    if !b
                        && name != "code_shim"
                        && name != "export_as"
                        && name != "inline"
                        && name != "only_spec"
                        && name != "raw_mut_self"
                        && name != "verify"
                        && name != "trust_me"
                        && name != "use_panic_abort"
                    {
                        return Err(spanned_error(
                            it.span,
                            ParserError::UnknownFunctionAttribute(name.to_owned()),
                        ));
                    }
                },
                Err(e) => {
                    return Err(e);
                },
            }
        }

        // in case we didn't get an args annotation,
        // implicitly add argument parameters matching their Rust names
        self.add_default_spec(span, &mut spec)?;

        spec.push_to_builder(builder)
            .map_err(|err| spanned_error(span, ParserError::Builder(err)))?;

        Ok(())
    }
}
