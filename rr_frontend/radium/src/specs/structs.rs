// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::RefCell;
use std::fmt::Write as _;
use std::{fmt, slice};

use crate::specs::bundles::BundleableType;
use crate::specs::invariants::{
    generate_normalized_rt_def, generate_type_implicit_arg_flags, setup_type_section_context,
};
use crate::specs::{
    GenericScope, GenericScopeInst, LiteralTyParam, TyParamList, Type, invariants, traits, types,
};
use crate::{coq, fmt_list, lang, model, push_str_list};

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TypeIsRaw {
    Yes,
    No,
}

/// Representation options for structs.
///
/// Struct representation options supported by Radium
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Repr {
    Rust,
    C,
    Transparent,
}

impl fmt::Display for Repr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rust => write!(f, "StructReprRust"),
            Self::C => write!(f, "StructReprC"),
            Self::Transparent => write!(f, "StructReprTransparent"),
        }
    }
}

/// Description of a variant of a struct or enum.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AbstractVariant<'def> {
    /// the fields, closed under a surrounding scope
    fields: Vec<(String, Type<'def>)>,
    /// the struct representation mode
    repr: Repr,
    /// the struct's name
    name: String,
    /// the Coq def name for the struct's plain tydef alias (without the optional invariant wrapper)
    pub(crate) plain_ty_name: String,
    /// the Coq def name for the struct's layout spec definition (of type `struct_layout_spec`)
    sls_def_name: String,
    st_def_name: String,
    /// the Coq def name for the struct's refinement type
    /// (used for using occurrences, but not for the definition itself)
    pub(crate) plain_rt_def_name: String,
}

impl<'def> AbstractVariant<'def> {
    /// Get the name of this variant
    #[must_use]
    fn name(&self) -> &str {
        &self.name
    }

    fn rfn_type(&self) -> coq::term::Type {
        model::Type::PList(
            "place_rfnRT".to_owned(),
            self.fields.iter().map(|(_, t)| t.get_rfn_type()).collect(),
            "RT".to_owned(),
        )
        .into()
    }

    /// The core of generating the sls definition, without the section + context intro.
    /// `opt_enum_name` is the optional name of a surrounding enum, to make recursive references working.
    #[must_use]
    pub(crate) fn generate_coq_sls_def_core(
        &self,
        typarams: &coq::binder::BinderList,
        shadow_st_names: &[String],
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // intro to main def
        write!(out, "{indent}Definition {} {typarams} : struct_layout_spec :=\n", self.sls_def_name).unwrap();

        // for recursive uses
        for st_name in shadow_st_names {
            write!(out, "{indent}{indent}let {st_name} {typarams} := UnitSynType in\n").unwrap();
        }

        write!(out, "{indent}{indent}mk_sls \"{}\" [", self.name).unwrap();

        push_str_list!(out, &self.fields, ";", |(name, ty)| {
            let synty: lang::SynType = ty.into();

            format!("\n{indent}{indent}(\"{name}\", {synty})")
        });

        write!(out, "] {}.\n", self.repr).unwrap();

        // also generate a definition for the syntype
        write!(
            out,
            "{indent}Definition {} {typarams} : syn_type := {} {}.\n",
            self.st_def_name,
            self.sls_def_name.clone(),
            fmt_list!(typarams.make_using_terms(), " "),
        )
        .unwrap();

        out
    }

    /// Generate a Coq definition for the struct layout spec.
    #[must_use]
    fn generate_coq_sls_def(&self, scope: &GenericScope<'def>) -> String {
        let mut out = String::with_capacity(200);

        let indent = "  ";
        write!(out, "Section {}.\n", self.sls_def_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        // add syntype parameters
        let typarams = scope.get_all_ty_params_with_assocs().get_coq_ty_st_params();
        out.push('\n');

        write!(out, "{}", self.generate_coq_sls_def_core(&typarams, slice::from_ref(&self.st_def_name)))
            .unwrap();

        // finish
        write!(out, "End {}.\n", self.sls_def_name).unwrap();
        out
    }

    #[must_use]
    fn get_coq_type_term(&self, ty_params: &TyParamList) -> coq::term::Type {
        let sls_app = ty_params
            .params
            .iter()
            .map(|names| coq::term::Term::Literal(format!("(ty_syn_type {} MetaNone)", names.type_term())))
            .collect();

        let sls = coq::term::App::new(coq::term::Term::Literal(self.sls_def_name.clone()), sls_app);

        let tys = self.fields.iter().map(|(_, ty)| coq::term::Type::Literal(ty.to_string())).collect();

        model::Type::StructT(Box::new(sls).into(), tys).into()
    }

    pub(crate) fn generate_coq_type_def_in_context(
        &self,
        document: &mut coq::Document,
        scope: &GenericScope<'def>,
        ty_context_names: &[String],
        rt_context_names: &[String],
    ) {
        let all_ty_params = scope.get_all_ty_params_with_assocs();

        let attr_binders = scope.get_all_attr_trait_parameters(super::IncludeSelfReq::Dont);

        // Intro to main def
        document.push(coq::command::Definition {
            program_mode: false,
            name: self.plain_ty_name.clone(),
            params: attr_binders,
            ty: Some(
                scope.get_spec_all_type_term(Box::new(model::Type::Ttype(Box::new(self.rfn_type()))).into()),
            ),
            body: coq::command::DefinitionBody::Proof(coq::proof::Proof::new_using(
                ty_context_names.join(" "),
                coq::proof::Terminator::Defined,
                |proof| {
                    proof.push(coq::ltac::LTac::Exact(coq::term::Term::Literal(format!(
                        "({scope} {})",
                        self.get_coq_type_term(&all_ty_params)
                    ))));
                },
            )),
        });

        // Generate the refinement type definition
        let rt_params = all_ty_params.get_coq_ty_rt_params();
        document.append_document(generate_normalized_rt_def(
            &self.plain_rt_def_name,
            &self.plain_ty_name,
            &rt_params.make_using_terms(),
            rt_context_names,
        ));

        // Make it Typeclasses Transparent
        document.push(
            coq::command::CommandAttrs::new(coq::command::Command::TypeclassesTransparent(
                self.plain_ty_name.clone(),
            ))
            .attributes("global"),
        );
    }

    /// Generate a Coq definition for the struct type alias.
    /// TODO: maybe we should also generate a separate alias def for the refinement type to make
    /// things more readable?
    #[must_use]
    fn generate_coq_type_def(
        &self,
        scope: &GenericScope<'def>,
        extra_context: &[coq::binder::Binder],
    ) -> coq::Document {
        let all_ty_params = scope.get_all_ty_params_with_assocs();
        let mut section_context = setup_type_section_context(&all_ty_params);

        // write coq parameters
        let (context_names, context_names_without_sigma) =
            invariants::format_extra_context_items(extra_context, &mut section_context);

        self.generate_coq_type_def_in_context(
            &mut section_context,
            scope,
            &context_names,
            &context_names_without_sigma,
        );

        let mut out = coq::Document::default();
        out.push(coq::section::Section::new(self.plain_ty_name.clone(), |doc| {
            doc.append_document(section_context);
        }));

        generate_type_implicit_arg_flags(
            &mut out,
            &self.plain_rt_def_name,
            &all_ty_params,
            &context_names_without_sigma,
        );
        invariants::generate_semtype_implicit_arg_flags(
            &mut out,
            &self.plain_ty_name,
            &all_ty_params,
            extra_context,
        );

        out
    }
}

/// Description of a struct type.
#[derive(Clone, Eq, PartialEq)]
pub struct Abstract<'def> {
    /// an optional invariant/ existential abstraction for this struct
    pub(crate) invariant: Option<invariants::Spec>,

    /// the actual definition of the variant
    pub(crate) variant_def: AbstractVariant<'def>,

    /// scope this is generic over
    pub(crate) scope: GenericScope<'def>,
}

impl fmt::Debug for Abstract<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "AbstractStruct<name={}>", self.variant_def.name)
    }
}

pub type AbstractRef<'def> = &'def RefCell<Option<Abstract<'def>>>;

impl<'def> BundleableType<'def> for Abstract<'def> {
    fn ty_name(&self) -> String {
        let Some(inv) = &self.invariant else {
            panic!("only types with invariants are bundleable");
        };

        inv.type_name()
    }

    fn rt_name(&self) -> String {
        let Some(inv) = &self.invariant else {
            panic!("only types with invariants are bundleable");
        };

        inv.rt_def_name()
    }

    fn bundle_rt_term(&self) -> String {
        let Some(inv) = &self.invariant else {
            panic!("only types with invariants are bundleable");
        };

        inv.rfn_type.to_string()
    }

    fn bundle_st_def_name(&self) -> String {
        self.st_def_name().to_owned()
    }

    fn generate_bundle_layout_def(
        &self,
        typarams: &coq::binder::BinderList,
        shadow_st_names: &[String],
    ) -> String {
        self.generate_coq_sls_def_core(typarams, shadow_st_names)
    }

    fn scope(&self) -> GenericScope<'def> {
        self.scope.clone()
    }

    fn extra_coq_params(&self) -> Vec<coq::binder::Binder> {
        let Some(inv) = &self.invariant else {
            panic!("only types with invariants are bundleable");
        };

        inv.coq_params.clone()
    }

    fn generate_recursive_prelude_entry(&self, doc: &mut coq::Document) {
        let Some(inv) = self.invariant.as_ref() else {
            panic!("Recursive types need an invariant");
        };

        let all_ty_params = self.scope.get_all_ty_params_with_assocs();
        let type_name = inv.type_name();
        let rfn_type = &inv.rfn_type;
        let attr_binders = self.scope.get_all_attr_trait_parameters(super::IncludeSelfReq::Dont);

        let mut recursive_prelude = String::new();
        write!(recursive_prelude, "Let {}", inv.rt_def_name()).unwrap();
        for names in &all_ty_params.params {
            write!(recursive_prelude, " (_{} : RT)", names.refinement_type()).unwrap();
        }
        writeln!(recursive_prelude, " := {}.", inv.rfn_type).unwrap();

        let dummy_ty_name = format!("_{type_name}");
        writeln!(recursive_prelude, "Context ({dummy_ty_name} : type {rfn_type}).").unwrap();

        write!(recursive_prelude, "Let {type_name}").unwrap();
        for names in &all_ty_params.params {
            write!(recursive_prelude, " ({} : RT)", names.refinement_type()).unwrap();
        }
        if !attr_binders.0.is_empty() {
            write!(recursive_prelude, " {attr_binders}").unwrap();
        }
        writeln!(recursive_prelude, " := {} {dummy_ty_name}.", self.scope).unwrap();

        doc.push(coq::command::Command::Literal(recursive_prelude));
    }

    fn generate_in_context(
        &self,
        doc: &mut coq::Document,
        ty_name: &str,
        rt_name: &str,
        _ty_context_names: &[String],
        rt_context_names: &[String],
    ) {
        let Some(inv) = self.invariant.as_ref() else {
            panic!("Recursive types need an invariant");
        };

        let all_ty_params = self.scope.get_all_ty_params_with_assocs();
        let rt_instantiations = all_ty_params.get_coq_ty_rt_params().make_using_terms();

        doc.push(coq::command::Definition::new(
            self.variant_def.plain_rt_def_name.clone(),
            coq::binder::BinderList::empty(),
            Some(coq::term::Type::RT),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(
                self.variant_def.rfn_type().to_string(),
            )),
        ));
        let base_type = format!("({})", self.variant_def.get_coq_type_term(&all_ty_params));

        doc.append_document(inv.generate_coq_type_def_core(
            &base_type,
            &self.variant_def.plain_rt_def_name,
            ty_name,
            rt_name,
            &rt_instantiations,
            &self.scope,
            rt_context_names,
        ));
    }

    fn set_flags(
        &self,
        doc: &mut coq::Document,
        rt_context_names: &[String],
        context_items: &[coq::binder::Binder],
    ) {
        let Some(inv) = self.invariant.as_ref() else {
            panic!("Recursive types need an invariant");
        };

        let all_ty_params = self.scope.get_all_ty_params_with_assocs();

        generate_type_implicit_arg_flags(doc, &inv.rt_def_name(), &all_ty_params, rt_context_names);
        invariants::generate_semtype_implicit_arg_flags(doc, &inv.type_name(), &all_ty_params, context_items);
        invariants::generate_semtype_implicit_arg_flags(doc, &inv.spec_name(), &all_ty_params, context_items);
    }
}

impl<'def> Abstract<'def> {
    #[must_use]
    pub const fn new(variant_def: AbstractVariant<'def>, scope: GenericScope<'def>) -> Self {
        Abstract {
            invariant: None,
            variant_def,
            scope,
        }
    }

    /// Create a struct representation of a tuple with `num_fields`, all of which are generic.
    #[must_use]
    pub fn new_from_tuple(num_fields: usize) -> Self {
        let name = format!("tuple{}", num_fields);

        let mut scope = GenericScope::empty();
        let mut builder = VariantBuilder::new(name, Repr::Rust);

        for i in 0..num_fields {
            let param_name = format!("T{}", i);
            let lit = LiteralTyParam::new(&param_name);
            scope.add_ty_param(lit.clone());

            builder.add_field(&i.to_string(), Type::LiteralParam(lit));
        }

        builder.finish_as_struct(scope)
    }

    /// Check if an invariant has been declared on this type.
    #[must_use]
    pub const fn has_invariant(&self) -> bool {
        self.invariant.is_some()
    }

    /// Get the name of this struct
    #[must_use]
    fn name(&self) -> &str {
        self.variant_def.name()
    }

    #[must_use]
    fn sls_def_name(&self) -> &str {
        &self.variant_def.sls_def_name
    }

    #[must_use]
    pub(crate) fn st_def_name(&self) -> &str {
        &self.variant_def.st_def_name
    }

    #[must_use]
    pub(crate) fn generate_coq_sls_def_core(
        &self,
        typarams: &coq::binder::BinderList,
        shadow_st_names: &[String],
    ) -> String {
        self.variant_def.generate_coq_sls_def_core(typarams, shadow_st_names)
    }

    #[must_use]
    pub(crate) fn plain_ty_name(&self) -> &str {
        &self.variant_def.plain_ty_name
    }

    /// Get the name of the struct, or an ADT defined on it, if available.
    #[must_use]
    pub(crate) fn public_type_name(&self) -> String {
        match &self.invariant {
            Some(inv) => inv.type_name(),
            None => self.plain_ty_name().to_owned(),
        }
    }

    #[must_use]
    pub fn plain_rt_def_name(&self) -> &str {
        &self.variant_def.plain_rt_def_name
    }

    #[must_use]
    pub fn public_rt_def_name(&self) -> String {
        match &self.invariant {
            Some(inv) => inv.rt_def_name(),
            None => self.plain_rt_def_name().to_owned(),
        }
    }

    /// Add an invariant specification to this type.
    pub fn add_invariant(&mut self, spec: invariants::Spec) {
        if self.invariant.is_some() {
            panic!("already specified an invariant for type {}", self.name());
        }
        self.invariant = Some(spec);
    }

    /// Generate a Coq definition for the struct layout spec.
    #[must_use]
    pub fn generate_coq_sls_def(&self) -> String {
        self.variant_def.generate_coq_sls_def(&self.scope)
    }

    /// Generate a Coq definition for the struct type alias.
    #[must_use]
    pub fn generate_coq_type_def(&self) -> coq::Document {
        // This path makes sure that the raw type gets a proper usable definition; we use this
        // for the #raw annotation currently.

        let extra_context = if let Some(inv) = &self.invariant { inv.coq_params.as_slice() } else { &[] };

        // the raw type
        let mut out = self.variant_def.generate_coq_type_def(&self.scope, extra_context);

        // the invariant
        if let Some(spec) = self.invariant.as_ref() {
            let s = spec.generate_coq_type_def(self.plain_ty_name(), self.plain_rt_def_name(), &self.scope);
            out.append_document(s);
        }

        out
    }

    /// Make a literal type.
    #[must_use]
    pub fn make_literal_type(&self) -> types::Literal {
        let info = types::AdtShimInfo::new(None, true);

        types::Literal {
            rust_name: Some(self.name().to_owned()),
            type_term: self.public_type_name(),
            refinement_type: coq::term::Type::Literal(self.public_rt_def_name()),
            syn_type: lang::SynType::Literal(self.sls_def_name().to_owned()),
            raw_type: Some(types::RawLiteralType {
                type_term: self.plain_ty_name().to_owned(),
                refinement_type: coq::term::Type::Literal(self.plain_rt_def_name().to_owned()),
            }),
            info,
        }
    }
}

/// A builder for ADT variants without fancy invariants etc.
pub struct VariantBuilder<'def> {
    /// the fields
    fields: Vec<(String, Type<'def>)>,
    /// the variant's representation mode
    repr: Repr,
    /// the variants's name
    name: String,
}

impl<'def> VariantBuilder<'def> {
    /// Initialize a struct builder.
    /// `ty_params` are the user-facing type parameter names in the Rust code.
    #[must_use]
    pub const fn new(name: String, repr: Repr) -> Self {
        VariantBuilder {
            fields: Vec::new(),
            name,
            repr,
        }
    }

    #[must_use]
    pub fn finish(self) -> AbstractVariant<'def> {
        let sls_def_name: String = format!("{}_sls", self.name);
        let st_def_name: String = format!("{}_st", self.name);
        let plain_ty_name: String = format!("{}_ty", self.name);
        let plain_rt_def_name: String = format!("{}_rt", self.name);

        AbstractVariant {
            fields: self.fields,
            repr: self.repr,
            name: self.name,
            plain_ty_name,
            sls_def_name,
            st_def_name,
            plain_rt_def_name,
        }
    }

    /// Finish building the struct type and generate an abstract struct definition.
    #[must_use]
    pub fn finish_as_struct(self, scope: GenericScope<'def>) -> Abstract<'def> {
        let variant = self.finish();
        Abstract {
            variant_def: variant,
            invariant: None,
            scope,
        }
    }

    /// Append a field to the struct def.
    pub fn add_field(&mut self, name: &str, ty: Type<'def>) {
        self.fields.push((name.to_owned(), ty));
    }
}

/// A usage of an `Abstract` that instantiates its type parameters.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AbstractUse<'def> {
    /// reference to the struct's definition, or None if unit
    pub(crate) def: Option<AbstractRef<'def>>,

    /// Instantiations for type parameters
    pub(crate) scope_inst: GenericScopeInst<'def>,

    /// does this refer to the raw type without invariants?
    raw: TypeIsRaw,
}

impl<'def> AbstractUse<'def> {
    #[must_use]
    pub const fn new(s: AbstractRef<'def>, scope_inst: GenericScopeInst<'def>, raw: TypeIsRaw) -> Self {
        AbstractUse {
            def: Some(s),
            scope_inst,
            raw,
        }
    }

    /// Creates a new use of unit.
    #[must_use]
    pub const fn new_unit() -> Self {
        AbstractUse {
            def: None,
            scope_inst: GenericScopeInst::empty(),
            raw: TypeIsRaw::Yes,
        }
    }

    #[must_use]
    pub(crate) fn is_raw(&self) -> bool {
        self.raw == TypeIsRaw::Yes
    }

    pub(crate) const fn make_raw(&mut self) {
        self.raw = TypeIsRaw::Yes;
    }

    /// Get the refinement type of a struct usage.
    /// This requires that all type parameters of the struct have been instantiated.
    #[must_use]
    pub(crate) fn get_rfn_type(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return coq::term::Type::Unit.to_string();
        };

        let rfn_instantiations: Vec<_> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Type::get_rfn_type).collect();

        let def = def.borrow();
        let def = def.as_ref().unwrap();
        let inv = &def.invariant.as_ref();

        if self.is_raw() || inv.is_none() {
            let rfn_type = def.plain_rt_def_name().to_owned();
            let applied = coq::term::App::new(rfn_type, rfn_instantiations);
            applied.to_string()
        } else {
            let rfn_type = inv.unwrap().rt_def_name();
            let applied = coq::term::App::new(rfn_type, rfn_instantiations);
            applied.to_string()
        }
    }

    /// Get the `syn_type` term for this struct use.
    #[must_use]
    pub(crate) fn generate_syn_type_term(&self) -> lang::SynType {
        let Some(def) = self.def.as_ref() else {
            return lang::SynType::Unit;
        };

        // first get the syntys for the type params
        let param_sts: Vec<lang::SynType> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Into::into).collect();

        let def = def.borrow();
        let def = def.as_ref().unwrap();
        let specialized_spec = coq::term::App::new(def.st_def_name().to_owned(), param_sts);
        lang::SynType::Literal(specialized_spec.to_string())
    }

    /// Generate a string representation of this struct use.
    #[must_use]
    pub(crate) fn generate_type_term(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return Type::Unit.to_string();
        };

        let rt_inst = self
            .scope_inst
            .get_all_ty_params_with_assocs()
            .iter()
            .map(|ty| format!("({})", ty.get_rfn_type()))
            .collect::<Vec<_>>()
            .join(" ");

        let def = def.borrow();
        let def = def.as_ref().unwrap();
        let attrs = if self.is_raw() {
            String::new()
        } else {
            fmt_list!(
                self.scope_inst
                    .get_surrounding_trait_requirements()
                    .iter()
                    .chain(self.scope_inst.get_direct_trait_requirements())
                    .filter_map(traits::ReqInst::get_attr_term),
                " "
            )
        };
        if !self.is_raw() && def.invariant.is_some() {
            let Some(inv) = &def.invariant else {
                unreachable!();
            };

            format!("({} {rt_inst} {attrs} {})", inv.type_name(), self.scope_inst.instantiation(true, true))
        } else {
            format!(
                "({} {rt_inst} {attrs} {})",
                def.plain_ty_name(),
                self.scope_inst.instantiation(true, true)
            )
        }
    }
}
