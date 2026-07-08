// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::RefCell;
use std::fmt;
use std::fmt::Write as _;
use std::ops::Add;

use derive_more::{Constructor, Display};

use crate::specs::bundles::BundleableType;
use crate::specs::invariants::{generate_type_implicit_arg_flags, setup_type_section_context};
use crate::specs::{GenericScope, GenericScopeInst, Type, invariants, structs, types};
use crate::{coq, fmt_list, lang, model, push_str_list};

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
/// Enum representation options supported by Radium
pub enum Repr {
    Rust,
    C,
    Transparent,
}

impl fmt::Display for Repr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rust => write!(f, "EnumReprRust"),
            Self::C => write!(f, "EnumReprC"),
            Self::Transparent => write!(f, "EnumReprTransparent"),
        }
    }
}

/// Specification of an enum in terms of a Coq type refining it.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Spec {
    /// the refinement type of the enum
    pub rfn_type: coq::term::Type,
    /// the refinement patterns for each of the variants
    /// eg. for options:
    /// - `(None, [], -[])`
    /// - `(Some, [x], -[x])`
    pub variant_patterns: Vec<(String, Vec<String>, String)>,
    /// true if the map from refinement to variants is partial
    pub is_partial: bool,
}

/// Enum to represent large discriminants
#[derive(Clone, Copy, Display, PartialEq, Debug, Eq)]
pub enum Int128 {
    #[display("{}", _0)]
    Signed(i128),
    #[display("{}", _0)]
    Unsigned(u128),
}

impl Add<u32> for Int128 {
    type Output = Self;

    fn add(self, rhs: u32) -> Self {
        match self {
            Self::Signed(i) => Self::Signed(i + i128::from(rhs)),
            Self::Unsigned(i) => Self::Unsigned(i + u128::from(rhs)),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Abstract<'def> {
    /// variants of this enum: name, variant, a mask describing which of the type parameters it uses, and the
    /// discriminant
    variants: Vec<(String, structs::AbstractRef<'def>, Int128)>,

    /// specification
    spec: Spec,

    /// the enum's name
    name: String,

    /// the representation of the enum
    repr: Repr,

    /// an optional declaration of a Coq inductive for this enum
    optional_inductive_def: Option<coq::inductive::Inductive>,

    /// name of the plain enum type (without additional invariants)
    plain_ty_name: String,
    plain_rt_name: String,

    /// name of the `enum_layout_spec` definition
    els_def_name: String,
    st_def_name: String,

    /// name of the enum definition
    enum_def_name: String,

    /// type of the integer discriminant
    discriminant_type: lang::IntType,

    /// these should be the same also across all the variants
    scope: GenericScope<'def>,

    pub(crate) coq_params: Vec<coq::binder::Binder>,
}

pub type AbstractRef<'def> = &'def RefCell<Option<Abstract<'def>>>;

impl<'def> BundleableType<'def> for Abstract<'def> {
    fn ty_name(&self) -> String {
        self.plain_ty_name.clone()
    }

    fn rt_name(&self) -> String {
        self.plain_rt_name.clone()
    }

    fn bundle_rt_term(&self) -> String {
        self.spec.rfn_type.to_string()
    }

    fn scope(&self) -> GenericScope<'def> {
        self.scope.clone()
    }

    fn extra_coq_params(&self) -> Vec<coq::binder::Binder> {
        self.coq_params.clone()
    }

    fn generate_recursive_prelude_entry(&self, doc: &mut coq::Document) {
        let all_ty_params = self.scope.get_all_ty_params_with_assocs();
        let mut recursive_prelude = String::new();

        write!(recursive_prelude, "Let {}", self.plain_rt_name).unwrap();
        for names in &all_ty_params.params {
            write!(recursive_prelude, " (_{} : RT)", names.refinement_type()).unwrap();
        }
        writeln!(recursive_prelude, " := {}.", self.spec.rfn_type).unwrap();

        let dummy_ty_name = format!("_{}", self.plain_ty_name);
        writeln!(recursive_prelude, "Context ({dummy_ty_name} : type {}).", self.spec.rfn_type).unwrap();

        write!(recursive_prelude, "Let {}", self.plain_ty_name).unwrap();
        for names in &all_ty_params.params {
            write!(recursive_prelude, " ({} : RT)", names.refinement_type()).unwrap();
        }
        writeln!(recursive_prelude, " := {} {dummy_ty_name}.", self.scope).unwrap();

        doc.push(coq::command::Command::Literal(recursive_prelude));
    }

    fn generate_in_context(
        &self,
        doc: &mut coq::Document,
        ty_name: &str,
        rt_name: &str,
        ty_context_names: &[String],
        rt_context_names: &[String],
    ) {
        let pre_enum_def_name = if ty_name.ends_with("_pre_raw") {
            format!("{}_pre_raw", self.enum_def_name)
        } else {
            format!("{}_pre", self.enum_def_name)
        };

        self.generate_coq_type_def_in_context(
            doc,
            &pre_enum_def_name,
            ty_name,
            rt_name,
            ty_context_names,
            rt_context_names,
        );
    }

    fn set_flags(&self, doc: &mut coq::Document, rt_context_names: &[String]) {
        let all_ty_params = self.scope.get_all_ty_params_with_assocs();

        // make it Typeclasses Transparent
        doc.push(
            coq::command::CommandAttrs::new(coq::command::Command::TypeclassesTransparent(
                self.plain_ty_name.clone(),
            ))
            .attributes("global"),
        );
        doc.push(
            coq::command::CommandAttrs::new(coq::command::Command::TypeclassesTransparent(
                self.plain_rt_name.clone(),
            ))
            .attributes("global"),
        );

        doc.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.enum_def_name.clone(),
                arguments_string: ": simpl never".to_owned(),
            })
            .attributes("global"),
        );

        generate_type_implicit_arg_flags(doc, &self.plain_rt_name, &all_ty_params, rt_context_names);
        invariants::generate_semtype_implicit_arg_flags(
            doc,
            &self.plain_ty_name,
            &all_ty_params,
            &self.coq_params,
        );

        doc.push(coq::command::Command::Literal(format!(
            "Global Hint Unfold {} : solve_protected_eq_db.",
            self.plain_ty_name
        )));
    }

    fn generate_bundle_projection(
        &self,
        doc: &mut coq::Document,
        bundle_tys_name: &str,
        index: usize,
        projection_names: &[String],
    ) {
        let attr_binders = self.scope.get_all_attr_trait_parameters(crate::specs::IncludeSelfReq::Dont);
        let attr_uses = attr_binders.make_using_terms();
        let bundle_tys = coq::term::App::new(bundle_tys_name.to_owned(), attr_uses.clone());
        let scope_inst = self.scope.identity_instantiation_term();
        let type_type = self
            .scope
            .get_spec_all_type_term(Box::new(model::Type::Ttype(Box::new(coq::term::Type::Infer)).into()));
        doc.push(coq::command::Definition::new(
            self.plain_ty_name.clone(),
            attr_binders.clone(),
            Some(type_type),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(format!(
                "{} mut_type_project ({bundle_tys} {scope_inst}) {index} eq_refl",
                self.scope,
            ))),
        ));

        let enum_type = self.scope.get_spec_all_type_term(Box::new(coq::term::Type::Literal(format!(
            "enum ({})",
            self.spec.rfn_type
        ))));
        let pre_enum_def_name = format!("{}_pre", self.enum_def_name);
        let mut args = projection_names.to_owned();
        args.extend(attr_uses.into_iter().map(|term| term.to_string()));
        args.push(scope_inst);
        doc.push(coq::command::Definition::new(
            self.enum_def_name.clone(),
            attr_binders,
            Some(enum_type),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(format!(
                "{} {pre_enum_def_name} {}",
                self.scope,
                args.join(" "),
            ))),
        ));
    }

    fn generate_bundle_pre_wrapper(
        &self,
        doc: &mut coq::Document,
        pre_ty_name: &str,
        raw_pre_ty_name: &str,
        projection_names: &[String],
    ) {
        let mut type_body = String::new();
        let mut enum_body = String::new();
        for projection_name in projection_names {
            type_body.push_str(&format!("let _ := {projection_name} in\n"));
            enum_body.push_str(&format!("let _ := {projection_name} in\n"));
        }
        type_body.push_str(raw_pre_ty_name);
        enum_body.push_str(&format!("{}_pre_raw", self.enum_def_name));

        doc.push(coq::command::Definition::new(
            pre_ty_name.to_owned(),
            coq::binder::BinderList::empty(),
            None,
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(type_body)),
        ));
        doc.push(coq::command::Definition::new(
            format!("{}_pre", self.enum_def_name),
            coq::binder::BinderList::empty(),
            None,
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(enum_body)),
        ));
    }
}

impl<'def> Abstract<'def> {
    /// Get the name of this enum.
    #[must_use]
    fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub(crate) fn public_type_name(&self) -> &str {
        &self.plain_ty_name
    }

    #[must_use]
    fn public_rt_def_name(&self) -> &str {
        &self.plain_rt_name
    }

    #[must_use]
    fn els_def_name(&self) -> &str {
        &self.els_def_name
    }

    #[must_use]
    pub fn get_variant(&self, i: usize) -> Option<&(String, structs::AbstractRef<'def>, Int128)> {
        self.variants.get(i)
    }

    /// Generate a Coq definition for the enum layout spec, and all the `struct_layout_specs` for the
    /// variants.
    #[must_use]
    pub fn generate_coq_els_def(&self) -> String {
        let indent = "  ";

        let mut out = String::with_capacity(200);

        out.push_str(&format!("Section {}.\n", self.els_def_name));
        out.push_str(&format!("{indent}Context `{{RRGS : !refinedrustGS Σ}}.\n"));
        out.push('\n');

        // add syntype parameters
        let all_ty_st_params = self.scope.get_all_ty_params_with_assocs().get_coq_ty_st_params();
        let all_ty_st_params_uses = all_ty_st_params.make_using_terms();

        // generate all the component structs
        for (_, v, _) in &self.variants {
            let vbor = v.borrow();
            let vbor = vbor.as_ref().unwrap();

            out.push_str(
                &vbor.variant_def.generate_coq_sls_def_core(&all_ty_st_params, Some(&self.st_def_name)),
            );
            out.push('\n');
        }

        // intro to main def
        out.push_str(&format!(
            "{indent}Program Definition {} {all_ty_st_params} : enum_layout_spec := mk_els \"{}\" {} [",
            self.els_def_name, self.name, self.discriminant_type
        ));

        push_str_list!(out, &self.variants, ";", |(name, var, _)| {
            let vbor = var.borrow();
            let vbor = vbor.as_ref().unwrap();

            format!("\n{}{}(\"{}\", {} {all_ty_st_params})", indent, indent, name, vbor.st_def_name())
        });

        // write the repr
        out.push_str(&format!("] {} [", self.repr));

        // now write the tag-discriminant list
        push_str_list!(out, &self.variants, "; ", |(name, _, discr)| format!("(\"{name}\", {discr})"));

        out.push_str("] _ _ _ _.\n");
        out.push_str(&format!("{indent}Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.\n"));
        out.push_str(&format!("{indent}Next Obligation. solve_enum_layout_spec_variants_eq. Qed.\n"));
        out.push_str(&format!("{indent}Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.\n"));
        out.push_str(&format!(
            "{indent}Next Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.\n"
        ));
        out.push_str(&format!("{indent}Global Typeclasses Opaque {}.\n", self.els_def_name));

        // also write an st definition
        out.push_str(&format!(
            "{indent}Definition {} {all_ty_st_params} : syn_type := {} {}.\n",
            self.st_def_name,
            self.els_def_name,
            fmt_list!(all_ty_st_params_uses, " ")
        ));

        // finish
        out.push_str(&format!("End {}.\n", self.els_def_name));

        out
    }

    /// Generate a function that maps the refinement to the tag as a Coq string (`enum_tag`).
    fn generate_enum_tag(&self) -> String {
        let mut out = String::with_capacity(200);

        let spec = &self.spec;
        if spec.is_partial {
            write!(out, "λ rfn, match rfn with ").unwrap();
            for ((name, _, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
                write!(out, "| {} => Some \"{name}\" ", coq::term::App::new(pat, apps.clone())).unwrap();
            }
            write!(out, "| _ => None ").unwrap();
            write!(out, "end").unwrap();
        } else {
            write!(out, "λ rfn, Some (match rfn with ").unwrap();
            for ((name, _, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
                write!(out, "| {} => \"{name}\" ", coq::term::App::new(pat, apps.clone())).unwrap();
            }
            write!(out, "end)").unwrap();
        }

        out
    }

    fn enum_rt_def_name(&self) -> String {
        format!("{}_rt", self.enum_def_name)
    }

    fn enum_ty_def_name(&self) -> String {
        format!("{}_ty", self.enum_def_name)
    }

    /// Generate a function that maps the refinement to the refinement type.
    /// Assumes that the generated code is placed in an environment where all the type parameters
    /// are available and the variant types have been instantiated already.
    fn generate_enum_rt(&self) -> coq::command::Definition {
        let mut out = String::with_capacity(200);
        let spec = &self.spec;

        write!(out, "λ rfn : {}, match rfn with ", spec.rfn_type).unwrap();
        for ((_, var, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            let v = var.borrow();
            let v = v.as_ref().unwrap();

            write!(out, "| {} => {}", coq::term::App::new(pat, apps.clone()), v.public_rt_def_name())
                .unwrap();
        }
        if spec.is_partial {
            write!(out, "| _ => unitRT ").unwrap();
        }
        write!(out, " end").unwrap();

        coq::command::Definition {
            program_mode: false,
            name: self.enum_rt_def_name(),
            params: coq::binder::BinderList::empty(),
            ty: None,
            body: coq::command::DefinitionBody::Term(coq::term::RocqTerm::Literal(out)),
        }
    }

    /// Generate a function that maps the refinement to the semantic type.
    fn generate_enum_ty(&self) -> coq::command::Definition {
        let mut out = String::with_capacity(200);
        let spec = &self.spec;

        write!(out, "{} λ rfn, match rfn as x return type ({} x) with ", self.scope, self.enum_rt_def_name())
            .unwrap();
        for ((_, var, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            let v = var.borrow();
            let v = v.as_ref().unwrap();
            // we can just use the plain name here, because we assume this is used in an
            // environment where all the type parametes are already instantiated.
            let ty = v.public_type_name();

            write!(
                out,
                "| {} => {ty} {}",
                coq::term::App::new(pat, apps.clone()),
                v.scope.identity_instantiation_term()
            )
            .unwrap();
        }
        if spec.is_partial {
            write!(out, "| _ => unit_t ").unwrap();
        }
        write!(out, " end").unwrap();

        //∀ x, type ([enum_rt_def_name] x)
        let ty: coq::term::Type = coq::term::RocqType::Term(Box::new(coq::term::RocqTerm::All(
            coq::binder::BinderList::new(vec![coq::binder::Binder::Default(
                Some("x".to_owned()),
                coq::term::Type::Infer,
            )]),
            Box::new(coq::term::RocqTerm::Type(Box::new(coq::term::RocqType::UserDefined(
                model::Type::Ttype(Box::new(coq::term::RocqType::Term(Box::new(coq::term::RocqTerm::App(
                    Box::new(coq::term::App::new(
                        coq::term::RocqTerm::Ident(coq::Ident::new(&self.enum_rt_def_name())),
                        vec![coq::term::RocqTerm::Ident(coq::Ident::new("x"))],
                    )),
                ))))),
            )))),
        )));
        let ty = self.scope.get_spec_all_type_term(Box::new(ty));

        coq::command::Definition {
            program_mode: false,
            name: self.enum_ty_def_name(),
            params: coq::binder::BinderList::empty(),
            ty: Some(ty),
            body: coq::command::DefinitionBody::Term(coq::term::RocqTerm::Literal(out)),
        }
    }

    /// Generate a function that maps the refinement to the refinement.
    fn generate_enum_rfn(&self) -> String {
        let mut out = String::with_capacity(200);
        let spec = &self.spec;

        write!(out, "λ rfn, match rfn with ").unwrap();
        for ((_, _, _), (pat, apps, rfn)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            write!(out, "| {} => {rfn}", coq::term::App::new(pat, apps.clone())).unwrap();
        }
        if spec.is_partial {
            write!(out, "| _ => () ").unwrap();
        }
        write!(out, " end").unwrap();

        out
    }

    /// Generate a function that maps (valid) tags to the corresponding Coq type for the variant.
    fn generate_enum_match(&self) -> String {
        let conditions: Vec<_> = self
            .variants
            .iter()
            .zip(self.spec.variant_patterns.iter())
            .map(|((name, var, _), (pat, apps, rfn))| {
                let v = var.borrow();
                let v = v.as_ref().unwrap();
                let ty = v.public_type_name();

                // injection
                let inj = format!("(λ '( {rfn}), {})", coq::term::App::new(pat, apps.clone()));

                format!(
                    "(\"{name}\", mk_enum_tag_sem _ ({ty} {}) {inj})",
                    v.scope.identity_instantiation_term()
                )
            })
            .collect();
        format!("[{}]", conditions.join("; "))
    }

    fn generate_coq_type_def_in_context(
        &self,
        document: &mut coq::Document,
        enum_name: &str,
        ty_name: &str,
        rt_name: &str,
        ty_context_names: &[String],
        rt_context_names: &[String],
    ) {
        let all_ty_params = self.scope.get_all_ty_params_with_assocs();
        let rt_param_uses = all_ty_params.get_coq_ty_rt_params().make_using_terms();

        // define types and type abstractions for all the component types.
        for (_name, variant, _) in &self.variants {
            let v = variant.borrow();
            let v = v.as_ref().unwrap();
            // TODO: might also need to handle extra context items
            v.variant_def.generate_coq_type_def_in_context(
                document,
                &v.scope,
                ty_context_names,
                rt_context_names,
            );

            if let Some(inv) = &v.invariant {
                let base_type = format!(
                    "({} {})",
                    v.variant_def.plain_ty_name.as_str(),
                    v.scope.identity_instantiation_term(),
                );
                let inv_def = inv.generate_coq_type_def_core(
                    &base_type,
                    v.variant_def.plain_rt_def_name.as_str(),
                    &inv.type_name(),
                    &inv.rt_def_name(),
                    &rt_param_uses,
                    &v.scope,
                    rt_context_names,
                );
                document.append_document(inv_def);
            }
        }

        // write the Coq inductive, if applicable
        if let Some(ind) = &self.optional_inductive_def {
            let name = ind.get_name();

            let mut doc = coq::Document::default();

            let comment = format!("Auto-generated representation of {}", name);
            doc.push(coq::Sentence::Comment(comment));
            doc.push(coq::command::Command::Inductive(ind.clone()));
            // add the canonical structure declaration for the corresponding RT
            let rt_name = format!("{name}RT");
            let defn = coq::command::Definition {
                program_mode: false,
                name: rt_name.clone(),
                params: coq::binder::BinderList::empty(),
                ty: Some(coq::term::Type::RT),
                body: coq::command::DefinitionBody::Term(coq::term::RocqTerm::App(Box::new(
                    coq::term::App::new(coq::term::Term::Ident(coq::Ident::new("directRT")), vec![
                        coq::term::Term::Ident(coq::Ident::new(name)),
                    ]),
                ))),
            };
            doc.push(coq::command::CommandAttrs::new(defn));
            doc.push(coq::command::CommandAttrs::new(coq::command::CanonicalDecl(coq::Ident::new(&rt_name))));

            doc.push(
                coq::command::CommandAttrs::new(coq::command::Instance {
                    name: None,
                    params: coq::binder::BinderList::empty(),
                    ty: coq::term::Type::Literal(format!("Inhabited {}", name)),
                    body: coq::proof::Proof::new(coq::proof::Terminator::Qed, |proof| {
                        proof.push(model::LTac::SolveInhabited);
                    }),
                })
                .attributes("global"),
            );

            document.append_document(doc);
        }

        // build the els term applied to generics
        // generate terms to apply the sls app to
        let mut els_app = Vec::new();
        for names in &all_ty_params.params {
            let term = format!("(ty_syn_type {} MetaNone)", names.type_term());
            els_app.push(term);
        }
        let els_app_term = coq::term::App::new(&self.els_def_name, els_app);

        document.push(self.generate_enum_rt());
        document.push(self.generate_enum_ty());

        let scope_inst = self.scope.identity_instantiation().instantiation(true, true);
        let enum_type = self.scope.get_spec_all_type_term(Box::new(coq::term::Type::Literal(format!(
            "enum ({})",
            self.spec.rfn_type
        ))));

        // main def
        let enum_body = format!(
            "{} mk_enum\n\
               _\n\
               ({els_app_term})\n\
               ({})\n\
               ({})\n\
               ({} {})\n\
               ({})\n\
               ({})\n\
               _\n\
               _",
            self.scope,
            self.generate_enum_tag(),
            self.enum_rt_def_name(),
            self.enum_ty_def_name(),
            scope_inst,
            self.generate_enum_rfn(),
            self.generate_enum_match(),
        );
        document.push(coq::command::Definition::program(
            enum_name.to_owned(),
            coq::binder::BinderList::empty(),
            Some(enum_type),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(enum_body)),
        ));
        document.push(coq::command::Command::NextObligation(coq::command::ObligationProof::new(
            coq::ltac::LTac::Literal("solve_inhabited".to_owned()),
            coq::proof::Terminator::Defined,
        )));
        document.push(coq::command::Command::NextObligation(coq::command::ObligationProof::new(
            coq::ltac::LTac::Literal("done".to_owned()),
            coq::proof::Terminator::Qed,
        )));
        document.push(coq::command::Command::NextObligation(coq::command::ObligationProof::new(
            coq::ltac::LTac::Literal("solve_mk_enum_tag_consistent".to_owned()),
            coq::proof::Terminator::Defined,
        )));

        document.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: enum_name.to_owned(),
                arguments_string: ": simpl never".to_owned(),
            })
            .attributes("global"),
        );

        let type_type = self
            .scope
            .get_spec_all_type_term(Box::new(model::Type::Ttype(Box::new(coq::term::Type::Infer)).into()));
        document.push(coq::command::Definition::new(
            ty_name.to_owned(),
            coq::binder::BinderList::empty(),
            Some(type_type),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(format!(
                "{} enum_t ({enum_name} {scope_inst})",
                self.scope,
            ))),
        ));

        document.append_document(invariants::generate_normalized_rt_def(
            rt_name,
            ty_name,
            &rt_param_uses,
            rt_context_names,
        ));
    }

    #[must_use]
    pub fn generate_coq_type_def(&self) -> String {
        let all_ty_params = self.scope.get_all_ty_params_with_assocs();

        let mut section_context = setup_type_section_context(&all_ty_params);
        let (_context_names, context_names_without_sigma) =
            invariants::format_extra_context_items(&self.coq_params, &mut section_context);

        let rt_param_uses = all_ty_params.get_coq_ty_rt_params().make_using_terms();

        let mut components = coq::Document::default();

        let pre_enum_def_name = self.enum_def_name.clone();
        let pre_enum_ty_name = format!("{}_pre", self.plain_ty_name);
        let pre_enum_rt_name = format!("{}_pre", self.plain_rt_name);

        self.generate_coq_type_def_in_context(
            &mut components,
            &pre_enum_def_name,
            &pre_enum_ty_name,
            &pre_enum_rt_name,
            &[],
            &context_names_without_sigma,
        );

        section_context.push(coq::section::Section::new("components".to_owned(), |doc| {
            doc.append_document(components);
        }));

        // locally needed for the EnumContractive solver
        section_context.push(coq::command::CommandAttrs::new(coq::command::Arguments {
            name: "enum_ty".to_owned(),
            arguments_string: ": simpl never".to_owned(),
        }));

        let type_type = self
            .scope
            .get_spec_all_type_term(Box::new(model::Type::Ttype(Box::new(coq::term::Type::Infer)).into()));
        let scope_inst = self.scope.identity_instantiation().instantiation(true, true);

        // define the actual type
        section_context.push(coq::command::Definition::new(
            self.plain_ty_name.clone(),
            coq::binder::BinderList::empty(),
            Some(type_type),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(format!(
                "{} enum_t ({pre_enum_def_name} {scope_inst})",
                self.scope,
            ))),
        ));

        // generate the refinement type definition
        section_context.append_document(invariants::generate_normalized_rt_def(
            &self.plain_rt_name,
            &self.plain_ty_name,
            &rt_param_uses,
            &context_names_without_sigma,
        ));

        let mut out = coq::Document::default();
        out.push(coq::section::Section::new(self.plain_ty_name.clone(), |doc| {
            doc.append_document(section_context);
        }));

        self.set_flags(&mut out, &context_names_without_sigma);

        out.to_string()
    }

    /// Make a literal type.
    #[must_use]
    pub fn make_literal_type(&self) -> types::Literal {
        let info = types::AdtShimInfo::new(Some(self.enum_def_name.clone()), false);

        types::Literal {
            rust_name: Some(self.name().to_owned()),
            type_term: self.public_type_name().to_owned(),
            refinement_type: coq::term::Type::Literal(self.public_rt_def_name().to_owned()),
            syn_type: lang::SynType::Literal(self.els_def_name().to_owned()),
            raw_type: Some(types::RawLiteralType {
                type_term: self.public_type_name().to_owned(),
                refinement_type: coq::term::Type::Literal(self.public_rt_def_name().to_owned()),
            }),
            info,
        }
    }
}

/// A builder for plain enums without fancy invariants etc.
pub struct Builder<'def> {
    /// the variants
    variants: Vec<(String, structs::AbstractRef<'def>, Int128)>,
    /// the enum's name
    name: String,
    /// names for the type parameters (for the Coq definitions)
    scope: GenericScope<'def>,
    /// type of the integer discriminant
    discriminant_type: lang::IntType,
    /// representation options for the enum
    repr: Repr,
}

impl<'def> Builder<'def> {
    /// Initialize an enum builder.
    /// `ty_params` are the user-facing type parameter names in the Rust code.
    #[must_use]
    pub const fn new(
        name: String,
        scope: GenericScope<'def>,
        discriminant_type: lang::IntType,
        repr: Repr,
    ) -> Self {
        Self {
            variants: Vec::new(),
            name,
            scope,
            discriminant_type,
            repr,
        }
    }

    /// Finish building the enum type and generate an abstract enum definition.
    #[must_use]
    pub fn finish(
        self,
        optional_inductive_def: Option<coq::inductive::Inductive>,
        spec: Spec,
    ) -> Abstract<'def> {
        let els_def_name: String = format!("{}_els", self.name);
        let st_def_name: String = format!("{}_st", self.name);
        let plain_ty_name: String = format!("{}_ty", self.name);
        let plain_rt_name: String = format!("{}_rt", self.name);
        let enum_def_name: String = format!("{}_enum", self.name);

        Abstract {
            variants: self.variants,
            name: self.name,
            plain_ty_name,
            plain_rt_name,
            els_def_name,
            st_def_name,
            enum_def_name,
            spec,
            optional_inductive_def,
            scope: self.scope,
            discriminant_type: self.discriminant_type,
            repr: self.repr,
            coq_params: Vec::new(),
        }
    }

    /// Append a variant to the struct def.
    /// `name` is also the Coq constructor of the refinement type we use.
    /// `used_params` is a mask describing which type parameters are used by this variant.
    pub fn add_variant(&mut self, name: &str, variant: structs::AbstractRef<'def>, discriminant: Int128) {
        self.variants.push((name.to_owned(), variant, discriminant));
    }
}

/// A usage of an `Abstract` that instantiates its type parameters.
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct AbstractUse<'def> {
    /// reference to the enum's definition
    pub(crate) def: AbstractRef<'def>,

    /// Instantiations for type parameters
    pub(crate) scope_inst: GenericScopeInst<'def>,
}

impl AbstractUse<'_> {
    /// Get the refinement type of an enum usage.
    /// This requires that all type parameters of the enum have been instantiated.
    #[must_use]
    pub(crate) fn get_rfn_type(&self) -> String {
        let def = self.def.borrow();
        let def = def.as_ref().unwrap();

        let rfn_instantiations: Vec<_> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Type::get_rfn_type).collect();

        let applied = coq::term::App::new(def.plain_rt_name.clone(), rfn_instantiations);
        applied.to_string()
    }

    /// Get the `syn_type` term for this enum use.
    #[must_use]
    pub(crate) fn generate_syn_type_term(&self) -> lang::SynType {
        let param_sts: Vec<lang::SynType> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Into::into).collect();

        let def = self.def.borrow();
        let def = def.as_ref().unwrap();
        // [my_spec] [params]
        let specialized_spec = coq::term::App::new(def.st_def_name.clone(), param_sts);
        lang::SynType::Literal(specialized_spec.to_string())
    }

    /// Generate a string representation of this enum use.
    #[must_use]
    pub(crate) fn generate_type_term(&self) -> String {
        let def = self.def.borrow();
        let def = def.as_ref().unwrap();

        let rt_inst = self
            .scope_inst
            .get_all_ty_params_with_assocs()
            .iter()
            .map(|ty| format!("({})", ty.get_rfn_type()))
            .collect::<Vec<_>>()
            .join(" ");
        format!("({} {} {})", def.plain_ty_name, rt_inst, self.scope_inst.instantiation(true, true))
    }
}
