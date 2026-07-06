// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt::Write as _;

use derive_more::Constructor;

use crate::specs::{GenericScope, IncludeSelfReq, TyOwnSpec};
use crate::{coq, fmt_list, model};

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SpecFlags {
    /// fully persistent and timeless invariant
    Persistent,
    /// invariant with own sharing predicate,
    Plain,
    NonAtomic,
    Atomic,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Mode {
    All,
    OnlyShared,
    OnlyOwned,
}

#[derive(Clone, PartialEq, Eq, Debug, Constructor)]
pub struct Spec {
    /// the name of the definition
    name: String,

    flags: SpecFlags,

    /// the refinement type of this struct
    pub(crate) rfn_type: coq::term::Type,

    /// the binding pattern for the refinement of this type
    rfn_pat: coq::binder::Pattern,

    /// existentials that are introduced in the invariant
    existentials: Vec<coq::binder::Binder>,

    /// an optional invariant as a separating conjunction,
    invariants: Vec<(coq::iris::IProp, Mode)>,

    /// additional type ownership
    ty_own_invariants: Vec<TyOwnSpec>,

    // additional ty_lfts
    ty_lfts: Vec<String>,

    // additional ty_wf_elctx
    ty_wf_elctx: Vec<String>,

    // optional override for ty_ghost_drop
    ty_ghost_drop: Option<coq::iris::IProp>,

    // whether this type has trivial drop
    ty_trivial_drop: bool,

    /// the specification of the abstracted refinement under a context where `rfn_pat` is bound
    pub(crate) abstracted_refinement: Option<coq::binder::Pattern>,

    // TODO add stuff for non-atomic/atomic invariants
    /// name, type, implicit or not
    pub(crate) coq_params: Vec<coq::binder::Binder>,
}

impl Spec {
    fn push_obligation<I>(out: &mut coq::Document, ltac: I, terminator: coq::proof::Terminator)
    where
        I: Into<coq::ltac::LTac>,
    {
        out.push(coq::command::Command::NextObligation(coq::command::ObligationProof::new(ltac, terminator)));
    }

    pub(crate) fn format_extra_context_items_doc(
        items: &[coq::binder::Binder],
        out: &mut coq::Document,
    ) -> (Vec<String>, Vec<String>) {
        let mut context_names = Vec::new();
        let mut context_names_without_sigma = Vec::new();

        if items.is_empty() {
            return (context_names, context_names_without_sigma);
        }

        let mut binders = Vec::with_capacity(items.len());
        for (counter, it) in items.iter().enumerate() {
            let name = format!("_CTX{counter}");
            if !it.is_dependent_on_sigma() {
                context_names_without_sigma.push(name.clone());
            }
            context_names.push(name.clone());
            binders.push(it.clone().set_name(name));
        }

        out.push(coq::Sentence::Comment("Additional parameters".to_owned()));
        out.push(coq::command::Context::new(coq::binder::BinderList::new(binders)));

        (context_names, context_names_without_sigma)
    }

    #[must_use]
    pub(crate) fn type_name(&self) -> String {
        format!("{}_inv_t", self.name)
    }

    #[must_use]
    pub(crate) fn rt_def_name(&self) -> String {
        format!("{}_rt", self.type_name())
    }

    #[must_use]
    pub(crate) fn spec_name(&self) -> String {
        format!("{}_inv_spec", self.type_name())
    }

    /// Add the abstracted refinement, if it was not already provided.
    pub fn provide_abstracted_refinement(&mut self, abstracted_refinement: coq::binder::Pattern) {
        if self.abstracted_refinement.is_some() {
            panic!("abstracted refinement for {} already provided", self.type_name());
        }
        self.abstracted_refinement = Some(abstracted_refinement);
    }

    fn make_existential_binders(&self) -> String {
        if self.existentials.is_empty() {
            return String::new();
        }

        format!("∃ {}, ", fmt_list!(&self.existentials, " "))
    }

    /// Assemble the owned invariant predicate for the plain mode.
    fn assemble_plain_owned_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        write!(
            out,
            "λ π inner_rfn (_ty_rfn : RT_rt ({}%type : RT)),
            let '{} := _ty_rfn in {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_type,
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();

        for own in &self.ty_own_invariants {
            write!(out, "{} ∗ ", coq::iris::IProp::Atom(own.fmt_owned("π"))).unwrap();
        }

        for (inv, mode) in &self.invariants {
            match mode {
                Mode::All | Mode::OnlyOwned => {
                    write!(out, "{} ∗ ", inv).unwrap();
                },
                _ => (),
            }
        }
        write!(out, "True").unwrap();

        out
    }

    /// Assemble the sharing invariant predicate for the plain mode.
    fn assemble_plain_shared_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        write!(
            out,
            "λ π κ inner_rfn (_ty_rfn : RT_rt ({}%type : RT)),
            let '{} := _ty_rfn in {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_type,
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();
        for own in &self.ty_own_invariants {
            write!(out, "{} ∗ ", coq::iris::IProp::Atom(own.fmt_shared("π", "κ"))).unwrap();
        }
        for (inv, mode) in &self.invariants {
            match mode {
                Mode::All | Mode::OnlyShared => {
                    write!(out, "{} ∗ ", inv).unwrap();
                },
                _ => (),
            }
        }
        write!(out, "True").unwrap();

        out
    }

    /// Assemble the list of lifetimes the invariant requires to be alive.
    fn assemble_ty_lfts(&self) -> String {
        let mut out = String::with_capacity(200);

        write!(out, "[]").unwrap();

        // go over all the types and concat their lfts
        for spec in &self.ty_own_invariants {
            for ty in &spec.annot_meta.escaped_tyvars {
                write!(out, " ++ (ty_lfts ({}))", ty.type_term()).unwrap();
            }
            for lft in &spec.annot_meta.escaped_lfts {
                write!(out, " ++ [{}]", lft).unwrap();
            }
        }
        for x in &self.ty_lfts {
            write!(out, " ++ {x}").unwrap();
        }

        out
    }

    /// Assemble the lifetime constraints that this type requires.
    fn assemble_ty_wf_elctx(&self) -> String {
        let mut out = String::with_capacity(200);
        write!(out, "[]").unwrap();

        // go over all the types and concat their lfts
        for spec in &self.ty_own_invariants {
            for ty in &spec.annot_meta.escaped_tyvars {
                write!(out, " ++ (ty_wf_E ({}))", ty.type_term()).unwrap();
            }
        }
        for x in &self.ty_wf_elctx {
            write!(out, " ++ {x}").unwrap();
        }

        out
    }

    /// Assemble the invariant for the persistent mode.
    fn assemble_pers_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        // TODO: maybe use some other formulation, the destructing let will make the
        // persistence/timeless inference go nuts.
        write!(
            out,
            "λ inner_rfn (_rfn_binder : RT_rt ({}%type : RT)),
            let '{} := _rfn_binder in {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_type,
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();
        for (inv, _) in &self.invariants {
            write!(out, "{} ∗ ", inv).unwrap();
        }
        write!(out, "True").unwrap();

        out
    }

    fn assemble_ghost_drop(&self) -> Option<String> {
        let gd = self.ty_ghost_drop.as_ref()?;

        let mut out = String::with_capacity(200);

        write!(
            out,
            "λ π _ (_rfn_binder : RT_rt ({}%type : RT)),
            let '{} := _rfn_binder in {gd} ∗ True",
            self.rfn_type, self.rfn_pat,
        )
        .unwrap();

        Some(out)
    }

    pub(crate) fn generate_coq_invariant_def_doc(
        &self,
        scope: &GenericScope<'_>,
        base_rfn_type: &str,
    ) -> coq::Document {
        if self.flags == SpecFlags::Persistent {
            assert!(self.invariants.iter().all(|it| it.1 == Mode::All) && self.ty_own_invariants.is_empty());
        }

        let mut out = coq::Document::default();
        let indent = "  ";

        // generate the spec definition
        let spec_name = self.spec_name();

        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);

        let inv_def_kind = if self.flags == SpecFlags::NonAtomic { "na_ex_inv_def" } else { "ex_inv_def" };
        let ty = scope.get_spec_all_type_term(Box::new(coq::term::Type::Literal(format!(
            "{inv_def_kind} ({base_rfn_type})%type ({})%type",
            self.rfn_type,
        ))));

        let trivial_drop = self.ty_trivial_drop;
        let mut body = String::with_capacity(200);
        match self.flags {
            SpecFlags::Persistent => {
                let inv = self.assemble_pers_invariant();
                write!(
                    body,
                    "{scope} mk_pers_ex_inv_def\n\
                       {indent}{indent}({inv})%I _ _\n\
                       {indent}",
                )
                .unwrap();
            },
            SpecFlags::Plain => {
                let own_inv = self.assemble_plain_owned_invariant();
                let shr_inv = self.assemble_plain_shared_invariant();
                let lft_outlives = self.assemble_ty_lfts();
                let lft_wf_elctx = self.assemble_ty_wf_elctx();

                // If there are no specific invariants given just for owned/shared ownership, use
                // automatic inference of the sharing predicate
                if self.invariants.iter().all(|(_, mode)| *mode == Mode::All) {
                    if let Some(gd) = self.assemble_ghost_drop() {
                        write!(
                            body,
                            "{scope} mk_ex_inv_def_auto_shr\n\
                            {indent}{indent}({own_inv})%I\n\
                            {indent}{indent}({gd})%I\n\
                            {indent}{indent}({trivial_drop})\n\
                            {indent}{indent}({lft_outlives})\n\
                            {indent}{indent}({lft_wf_elctx})\n\
                            {indent}{indent}_ _ _ _\n\
                            {indent}",
                        )
                        .unwrap();
                    } else {
                        write!(
                            body,
                            "{scope} mk_auto_ex_inv_def\n\
                            {indent}{indent}({own_inv})%I\n\
                            {indent}{indent}({trivial_drop})\n\
                            {indent}{indent}({lft_outlives})\n\
                            {indent}{indent}({lft_wf_elctx})\n\
                            {indent}{indent}_ _ _ _\n\
                            {indent}",
                        )
                        .unwrap();
                    }
                } else if let Some(gd) = self.assemble_ghost_drop() {
                    write!(
                        body,
                        "{scope} mk_ex_inv_def\n\
                        {indent}{indent}({own_inv})%I\n\
                        {indent}{indent}({shr_inv})%I\n\
                        {indent}{indent}({gd})%I\n\
                        {indent}{indent}({trivial_drop})\n\
                        {indent}{indent}_\n\
                        {indent}{indent}({lft_outlives})\n\
                        {indent}{indent}({lft_wf_elctx})\n\
                        {indent}{indent}_ _ _\n\
                        {indent}",
                    )
                    .unwrap();
                } else {
                    write!(
                        body,
                        "{scope} mk_ex_inv_def_auto_ghost_drop\n\
                        {indent}{indent}({own_inv})%I\n\
                        {indent}{indent}({shr_inv})%I\n\
                        {indent}{indent}({trivial_drop})\n\
                        {indent}{indent}_\n\
                        {indent}{indent}({lft_outlives})\n\
                        {indent}{indent}({lft_wf_elctx})\n\
                        {indent}{indent}_ _ _\n\
                        {indent}",
                    )
                    .unwrap();
                }
            },
            SpecFlags::NonAtomic => {
                let own_inv = self.assemble_plain_owned_invariant();
                let lft_outlives = self.assemble_ty_lfts();
                let lft_wf_elctx = self.assemble_ty_wf_elctx();

                write!(
                    body,
                    "{scope} na_mk_ex_inv_def\n\
                    {indent}{indent}({own_inv})%I\n\
                    {indent}{indent}({trivial_drop})\n\
                    {indent}{indent}({lft_outlives})\n\
                    {indent}{indent}({lft_wf_elctx})\n\
                    {indent}",
                )
                .unwrap();
            },
            _ => {
                panic!("unimplemented invariant spec flag: {:?}", self.flags);
            },
        }

        out.push(coq::command::Definition::program(
            spec_name,
            attr_binders,
            Some(ty),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(body)),
        ));

        match self.flags {
            SpecFlags::Persistent => {
                Self::push_obligation(
                    &mut out,
                    coq::ltac::LTac::Literal("ex_t_solve_persistent".to_owned()),
                    coq::proof::Terminator::Qed,
                );
                Self::push_obligation(
                    &mut out,
                    coq::ltac::LTac::Literal("ex_t_solve_timeless".to_owned()),
                    coq::proof::Terminator::Qed,
                );
            },
            SpecFlags::Plain => {
                let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
                let attr_intro = if attr_binders.0.is_empty() {
                    String::new()
                } else {
                    format!("intros{}; ", " ?".repeat(attr_binders.0.len()))
                };

                if self.invariants.iter().all(|(_, mode)| *mode == Mode::All) {
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal("ex_plain_t_solve_shr_auto".to_owned()),
                        coq::proof::Terminator::Defined,
                    );
                    if self.ty_ghost_drop.is_some() {
                        Self::push_obligation(
                            &mut out,
                            coq::ltac::LTac::Literal("ex_t_solve_persistent".to_owned()),
                            coq::proof::Terminator::Qed,
                        );
                        Self::push_obligation(
                            &mut out,
                            coq::ltac::LTac::Literal(format!("{attr_intro}ex_plain_t_solve_shr_mono")),
                            coq::proof::Terminator::Qed,
                        );
                        Self::push_obligation(
                            &mut out,
                            coq::ltac::LTac::Literal(format!("{attr_intro}ex_plain_t_solve_ghost_drop")),
                            coq::proof::Terminator::Qed,
                        );
                    } else {
                        Self::push_obligation(
                            &mut out,
                            coq::ltac::LTac::Literal("ex_plain_t_solve_ghost_drop_auto".to_owned()),
                            coq::proof::Terminator::Defined,
                        );
                        Self::push_obligation(
                            &mut out,
                            coq::ltac::LTac::Literal("ex_t_solve_persistent".to_owned()),
                            coq::proof::Terminator::Qed,
                        );
                        Self::push_obligation(
                            &mut out,
                            coq::ltac::LTac::Literal(format!("{attr_intro}ex_plain_t_solve_shr_mono")),
                            coq::proof::Terminator::Qed,
                        );
                    }
                } else if self.ty_ghost_drop.is_some() {
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal("ex_t_solve_persistent".to_owned()),
                        coq::proof::Terminator::Qed,
                    );
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal(format!("{attr_intro}ex_plain_t_solve_shr_mono")),
                        coq::proof::Terminator::Qed,
                    );
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal(format!("{attr_intro}ex_plain_t_solve_shr")),
                        coq::proof::Terminator::Qed,
                    );
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal(format!("{attr_intro}ex_plain_t_solve_ghost_drop")),
                        coq::proof::Terminator::Qed,
                    );
                } else {
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal("ex_plain_t_solve_ghost_drop_auto".to_owned()),
                        coq::proof::Terminator::Defined,
                    );
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal("ex_t_solve_persistent".to_owned()),
                        coq::proof::Terminator::Qed,
                    );
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal(format!("{attr_intro}ex_plain_t_solve_shr_mono")),
                        coq::proof::Terminator::Qed,
                    );
                    Self::push_obligation(
                        &mut out,
                        coq::ltac::LTac::Literal(format!("{attr_intro}ex_plain_t_solve_shr")),
                        coq::proof::Terminator::Qed,
                    );
                }
            },
            SpecFlags::NonAtomic => {},
            _ => unreachable!(),
        }

        out
    }

    #[expect(dead_code)]
    pub(crate) fn generate_coq_invariant_def(&self, scope: &GenericScope<'_>, base_rfn_type: &str) -> String {
        self.generate_coq_invariant_def_doc(scope, base_rfn_type).to_string()
    }

    /// Generate the Coq definition of the type, without the surrounding context assumptions.
    pub(crate) fn generate_coq_type_def_core(
        &self,
        base_type: &str,
        base_rfn_type: &str,
        generics_rts: &[coq::term::Term],
        scope: &GenericScope<'_>,
        context_names: &[String],
    ) -> String {
        self.generate_coq_type_def_core_doc(base_type, base_rfn_type, generics_rts, scope, context_names)
            .to_string()
    }

    pub(crate) fn generate_coq_type_def_core_doc(
        &self,
        base_type: &str,
        base_rfn_type: &str,
        generics_rts: &[coq::term::Term],
        scope: &GenericScope<'_>,
        context_names: &[String],
    ) -> coq::Document {
        let mut out = coq::Document::default();

        out.append_document(self.generate_coq_invariant_def_doc(scope, base_rfn_type));
        out.append_document(self.generate_wrapped_type_def_doc(
            base_type,
            generics_rts,
            scope,
            context_names,
        ));

        out
    }

    pub(crate) fn generate_wrapped_type_body(&self, base_type: &str, scope: &GenericScope<'_>) -> String {
        self.generate_wrapped_type_body_inner(base_type, scope, true)
    }

    pub(crate) fn generate_wrapped_type_body_at_current_params(
        &self,
        base_type: &str,
        scope: &GenericScope<'_>,
    ) -> String {
        self.generate_wrapped_type_body_inner(base_type, scope, false)
    }

    fn generate_wrapped_type_body_inner(
        &self,
        base_type: &str,
        scope: &GenericScope<'_>,
        include_scope_abstraction: bool,
    ) -> String {
        let spec_name = self.spec_name();

        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
        let attr_binders_uses = attr_binders.make_using_terms();
        let scope_abstraction = if include_scope_abstraction { format!("{scope} ") } else { String::new() };

        if SpecFlags::NonAtomic == self.flags {
            format!(
                "{scope_abstraction}na_ex_plain_t _ _ ({spec_name} {} {}) {base_type}",
                fmt_list!(attr_binders_uses, " "),
                scope.identity_instantiation_term(),
            )
        } else {
            format!(
                "{scope_abstraction}ex_plain_t _ _ ({spec_name} {} {}) {base_type}",
                fmt_list!(attr_binders_uses, " "),
                scope.identity_instantiation_term(),
            )
        }
    }

    pub(crate) fn generate_wrapped_type_def_doc(
        &self,
        base_type: &str,
        generics_rts: &[coq::term::Term],
        scope: &GenericScope<'_>,
        context_names: &[String],
    ) -> coq::Document {
        let mut out = coq::Document::default();

        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
        let body = self.generate_wrapped_type_body(base_type, scope);

        out.push(coq::command::Definition::new(
            self.type_name(),
            attr_binders,
            Some(
                scope.get_spec_all_type_term(Box::new(
                    model::Type::Ttype(Box::new(coq::term::Type::Literal(format!(
                        "({})%type",
                        self.rfn_type
                    ))))
                    .into(),
                )),
            ),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(body)),
        ));

        out.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.spec_name(),
                arguments_string: ": simpl never".to_owned(),
            })
            .attributes("global"),
        );
        out.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.type_name(),
                arguments_string: ": simpl never".to_owned(),
            })
            .attributes("global"),
        );
        out.push(
            coq::command::CommandAttrs::new(coq::command::Command::TypeclassesTransparent(self.type_name()))
                .attributes("global"),
        );

        out.append_document(self.generate_normalized_rt_def_doc(generics_rts, context_names));

        out
    }

    pub(crate) fn generate_normalized_rt_def_doc(
        &self,
        generics_rts: &[coq::term::Term],
        context_names: &[String],
    ) -> coq::Document {
        let mut out = coq::Document::default();

        out.push(coq::command::Definition::new(
            format!("{}_rt", self.type_name()),
            coq::binder::BinderList::empty(),
            Some(coq::term::Type::RT),
            coq::command::DefinitionBody::Proof(coq::proof::Proof::new_using(
                format!("{} {}", fmt_list!(generics_rts, " "), context_names.join(" ")),
                coq::proof::Terminator::Defined,
                |proof| {
                    proof.push(coq::ltac::LetIn::new(
                        "__a",
                        coq::term::App::new(
                            coq::term::Term::Literal("normalized_rt_of_spec_ty".to_owned()),
                            vec![coq::term::Term::Literal(self.type_name())],
                        ),
                        coq::ltac::LTac::Exact(coq::term::Term::Literal("__a".to_owned())),
                    ));
                },
            )),
        ));
        out.push(
            coq::command::CommandAttrs::new(coq::command::Command::TypeclassesTransparent(format!(
                "{}_rt",
                self.type_name()
            )))
            .attributes("global"),
        );

        out
    }

    /// Generate the definition of the Coq type, including introduction of type parameters to the
    /// context.
    pub(crate) fn generate_coq_type_def(
        &self,
        base_type_name: &str,
        base_rfn_type: &str,
        scope: &GenericScope<'_>,
    ) -> String {
        self.generate_coq_type_def_doc(base_type_name, base_rfn_type, scope).to_string()
    }

    pub(crate) fn generate_coq_type_def_doc(
        &self,
        base_type_name: &str,
        base_rfn_type: &str,
        scope: &GenericScope<'_>,
    ) -> coq::Document {
        let mut out = coq::Document::default();

        assert!(self.abstracted_refinement.is_some());

        let all_ty_params = scope.get_all_ty_params_with_assocs();

        let mut section_context = coq::Document::default();
        section_context.push(coq::command::Context::refinedrust());
        if !all_ty_params.params.is_empty() {
            let rt_param_binders = all_ty_params
                .params
                .iter()
                .map(|names| coq::binder::Binder::new(Some(names.refinement_type()), coq::term::Type::RT))
                .collect();
            section_context.push(coq::command::Context::new(coq::binder::BinderList::new(rt_param_binders)));
        }

        let (_context_names, context_names_without_sigma) =
            Self::format_extra_context_items_doc(&self.coq_params, &mut section_context);

        // get the applied base_rfn_type
        let rt_instantiations = all_ty_params.get_coq_ty_rt_params().make_using_terms();
        let applied_base_rt = coq::term::App::new(base_rfn_type, rt_instantiations.clone());

        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
        let attr_binders_uses = attr_binders.make_using_terms();

        // get the applied base type
        let applied_base_type = coq::term::App::new(
            coq::term::Term::App(Box::new(coq::term::App::new(
                coq::term::Term::Literal(base_type_name.to_owned()),
                rt_instantiations.clone(),
            ))),
            attr_binders_uses,
        );
        let applied_base_type = format!("({applied_base_type} {})", scope.identity_instantiation_term());

        section_context.append_document(self.generate_coq_type_def_core_doc(
            &applied_base_type,
            applied_base_rt.to_string().as_str(),
            &rt_instantiations,
            scope,
            &context_names_without_sigma,
        ));

        out.push(coq::section::Section::new(self.type_name(), |doc| doc.append_document(section_context)));
        out.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.rt_def_name(),
                arguments_string: ": clear implicits".to_owned(),
            })
            .attributes("global"),
        );
        if !context_names_without_sigma.is_empty() {
            //let dep_sigma_str = if dep_sigma { "{_} " } else { "" };
            let dep_sigma_str = "";

            out.push(
                coq::command::CommandAttrs::new(coq::command::Arguments {
                    name: self.rt_def_name(),
                    arguments_string: format!(
                        "{}{} {{{}}}",
                        dep_sigma_str,
                        "_ ".repeat(all_ty_params.params.len()),
                        "_ ".repeat(context_names_without_sigma.len())
                    ),
                })
                .attributes("global"),
            );
        }

        out
    }
}
