// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use crate::specs::{GenericScope, IncludeSelfReq, enums, invariants, structs};
use crate::{coq, model};

pub trait BundleableType<'def> {
    fn ty_name(&self) -> String;

    fn rt_name(&self) -> String;

    fn bundle_rt_term(&self) -> String;

    fn scope(&self) -> GenericScope<'def>;

    fn extra_coq_params(&self) -> Vec<coq::binder::Binder>;

    fn generate_recursive_prelude_entry(&self, doc: &mut coq::Document);

    fn generate_in_context(
        &self,
        doc: &mut coq::Document,
        ty_name: &str,
        rt_name: &str,
        ty_context_names: &[String],
        rt_context_names: &[String],
    );

    fn bundle_component_term(&self, pre_ty_name: &str, projection_names: &[String]) -> String {
        let scope = self.scope();
        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
        let mut args = projection_names.to_owned();
        args.extend(attr_binders.make_using_terms().into_iter().map(|term| term.to_string()));
        args.push(scope.identity_instantiation_term());

        format!("{pre_ty_name} {}", args.join(" "))
    }

    fn generate_bundle_pre_wrapper(
        &self,
        doc: &mut coq::Document,
        pre_ty_name: &str,
        raw_pre_ty_name: &str,
        projection_names: &[String],
    ) {
        let mut body = String::new();
        for projection_name in projection_names {
            body.push_str(&format!("let _ := {projection_name} in\n"));
        }
        body.push_str(raw_pre_ty_name);

        doc.push(coq::command::Definition::new(
            pre_ty_name.to_owned(),
            coq::binder::BinderList::empty(),
            None,
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(body)),
        ));
    }

    fn generate_bundle_projection(
        &self,
        doc: &mut coq::Document,
        bundle_tys_name: &str,
        index: usize,
        _projection_names: &[String],
    ) {
        let scope = self.scope();
        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
        let attr_uses = attr_binders.make_using_terms();
        let type_type = scope
            .get_spec_all_type_term(Box::new(model::Type::Ttype(Box::new(coq::term::Type::Infer)).into()));
        let bundle_tys = coq::term::App::new(bundle_tys_name.to_owned(), attr_uses);

        doc.push(coq::command::Definition::new(
            self.ty_name(),
            attr_binders,
            Some(type_type),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(format!(
                "{} mut_type_project ({bundle_tys} {}) {index} eq_refl",
                scope,
                scope.identity_instantiation_term(),
            ))),
        ));
    }

    fn set_flags(&self, doc: &mut coq::Document, rt_context_names: &[String]);
}

pub enum BundleType<'def> {
    Struct(structs::AbstractRef<'def>),
    Enum(enums::AbstractRef<'def>),
}

impl<'def> BundleableType<'def> for BundleType<'def> {
    fn ty_name(&self) -> String {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().ty_name()
            },
            Self::Enum(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().ty_name()
            },
        }
    }

    fn rt_name(&self) -> String {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().rt_name()
            },
            Self::Enum(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().rt_name()
            },
        }
    }

    fn bundle_rt_term(&self) -> String {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().bundle_rt_term()
            },
            Self::Enum(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().bundle_rt_term()
            },
        }
    }

    fn scope(&self) -> GenericScope<'def> {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                let s = s.as_ref().unwrap();
                s.scope()
            },
            Self::Enum(s) => {
                let s = s.borrow();
                let s = s.as_ref().unwrap();
                s.scope()
            },
        }
    }

    fn extra_coq_params(&self) -> Vec<coq::binder::Binder> {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                let s = s.as_ref().unwrap();
                s.extra_coq_params()
            },
            Self::Enum(s) => {
                let s = s.borrow();
                let s = s.as_ref().unwrap();
                s.extra_coq_params()
            },
        }
    }

    fn generate_recursive_prelude_entry(&self, doc: &mut coq::Document) {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                let s = s.as_ref().unwrap();
                s.generate_recursive_prelude_entry(doc);
            },
            Self::Enum(s) => {
                let s = s.borrow();
                let s = s.as_ref().unwrap();
                s.generate_recursive_prelude_entry(doc);
            },
        }
    }

    fn generate_in_context(
        &self,
        doc: &mut coq::Document,
        ty_name: &str,
        rt_name: &str,
        ty_context_names: &[String],
        rt_context_names: &[String],
    ) {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().generate_in_context(
                    doc,
                    ty_name,
                    rt_name,
                    ty_context_names,
                    rt_context_names,
                );
            },
            Self::Enum(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().generate_in_context(
                    doc,
                    ty_name,
                    rt_name,
                    ty_context_names,
                    rt_context_names,
                );
            },
        }
    }

    fn set_flags(&self, doc: &mut coq::Document, rt_context_names: &[String]) {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().set_flags(doc, rt_context_names);
            },
            Self::Enum(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().set_flags(doc, rt_context_names);
            },
        }
    }

    fn generate_bundle_projection(
        &self,
        doc: &mut coq::Document,
        bundle_tys_name: &str,
        index: usize,
        projection_names: &[String],
    ) {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                s.as_ref()
                    .unwrap()
                    .generate_bundle_projection(doc, bundle_tys_name, index, projection_names);
            },
            Self::Enum(s) => {
                let s = s.borrow();
                s.as_ref()
                    .unwrap()
                    .generate_bundle_projection(doc, bundle_tys_name, index, projection_names);
            },
        }
    }

    fn generate_bundle_pre_wrapper(
        &self,
        doc: &mut coq::Document,
        pre_ty_name: &str,
        raw_pre_ty_name: &str,
        projection_names: &[String],
    ) {
        match self {
            Self::Struct(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().generate_bundle_pre_wrapper(
                    doc,
                    pre_ty_name,
                    raw_pre_ty_name,
                    projection_names,
                );
            },
            Self::Enum(s) => {
                let s = s.borrow();
                s.as_ref().unwrap().generate_bundle_pre_wrapper(
                    doc,
                    pre_ty_name,
                    raw_pre_ty_name,
                    projection_names,
                );
            },
        }
    }
}

pub struct Bundle<'def> {
    components: Vec<BundleType<'def>>,
}

impl<'def> Bundle<'def> {
    #[must_use]
    pub const fn new(components: Vec<BundleType<'def>>) -> Self {
        Self { components }
    }

    fn common_scope(&self) -> GenericScope<'def> {
        let Some((first, rest)) = self.components.split_first() else {
            panic!("recursive type bundles must contain at least one component");
        };

        let scope = first.scope();
        for component in rest {
            let component_scope = component.scope();
            if component_scope != scope {
                panic!(
                    "RefinedRust does not currently support recursive type bundles with differing generic scopes: {}",
                    component.ty_name(),
                );
            }
        }

        scope
    }

    fn name_prefix(&self) -> String {
        format!("{}_bundle", self.components[0].ty_name())
    }

    #[must_use]
    pub fn generate(&self) -> coq::Document {
        let scope = self.common_scope();
        let all_ty_params = scope.get_all_ty_params_with_assocs();

        let mut section_context = invariants::setup_type_section_context(&all_ty_params);
        let extra_coq_params =
            self.components.iter().flat_map(BundleableType::extra_coq_params).collect::<Vec<_>>();
        let (context_names, context_names_without_sigma) =
            invariants::format_extra_context_items(&extra_coq_params, &mut section_context);

        // start section
        // TODO: use the checked common scope of the bundled types.

        // start section for components
        // generate Let prelude of all the types
        let mut components = coq::Document::default();
        for component in &self.components {
            component.generate_recursive_prelude_entry(&mut components);
        }

        let projection_names = self.components.iter().map(BundleableType::ty_name).collect::<Vec<_>>();

        // write all the components with generate_in_context, using _pre names derived from ty_name / rt_name
        for component in &self.components {
            let raw_pre_ty_name = format!("{}_pre_raw", component.ty_name());
            component.generate_in_context(
                &mut components,
                &raw_pre_ty_name,
                &format!("{}_pre_raw", component.rt_name()),
                &context_names,
                &context_names_without_sigma,
            );
            component.generate_bundle_pre_wrapper(
                &mut components,
                &format!("{}_pre", component.ty_name()),
                &raw_pre_ty_name,
                &projection_names,
            );
        }

        // close section for components
        section_context.push(coq::section::Section::new("components".to_owned(), |doc| {
            doc.append_document(components);
        }));

        // define bundle functor using _pre names
        let rt_params = all_ty_params.get_coq_ty_rt_params().make_using_terms();
        let rts = self.components.iter().map(BundleableType::bundle_rt_term).collect::<Vec<_>>();
        let bundle_prefix = self.name_prefix();
        let rts_name = format!("{bundle_prefix}_rts");
        let functor_name = format!("{bundle_prefix}_F");
        let tys_name = format!("{bundle_prefix}_tys");
        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
        let attr_uses = attr_binders.make_using_terms();
        let scope_inst = scope.identity_instantiation_term();
        let bundle_tys_type =
            scope.get_spec_all_type_term(Box::new(coq::term::Type::Literal(format!("mut_types {rts_name}"))));

        section_context.push(coq::command::Definition::new(
            rts_name.clone(),
            coq::binder::BinderList::empty(),
            Some(coq::term::Type::Literal("list RT".to_owned())),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(format!("[({} : RT)]", rts.join("; ")))),
        ));

        let mut functor_body = String::new();
        for (i, projection_name) in projection_names.iter().enumerate() {
            functor_body.push_str(&format!("let {projection_name} := mut_type_project tys {i} eq_refl in\n"));
        }
        for component in &self.components {
            let pre_ty_name = format!("{}_pre", component.ty_name());
            let component_term = component.bundle_component_term(&pre_ty_name, &projection_names);
            functor_body.push_str(&format!("{component_term} +::\n"));
        }
        functor_body.push_str("+[]");

        section_context.push(coq::command::Definition::new(
            functor_name.clone(),
            {
                let mut params = attr_binders.clone();
                params.append(vec![coq::binder::Binder::new(
                    Some("tys".to_owned()),
                    coq::term::Type::Literal(format!("mut_types {rts_name}")),
                )]);
                params
            },
            Some(bundle_tys_type.clone()),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(format!("{scope} {functor_body}"))),
        ));

        // take fixpoint of bundle
        section_context.push(coq::command::CommandAttrs::new(coq::command::Arguments {
            name: "enum_ty".to_owned(),
            arguments_string: ": simpl never".to_owned(),
        }));
        section_context.push(coq::command::Definition::new(
            tys_name.clone(),
            attr_binders,
            Some(bundle_tys_type),
            coq::command::DefinitionBody::Term(coq::term::Term::Literal(format!(
                "{scope} mut_fixpoint (λ tys, {functor_name} {} tys {scope_inst})",
                attr_uses.iter().map(ToString::to_string).collect::<Vec<_>>().join(" "),
            ))),
        ));

        // define projections for the proper non _pre names; this should probably be a hook taking the type
        // term or so, so that we can also define the enum definition with recursive knots tied
        for (index, component) in self.components.iter().enumerate() {
            component.generate_bundle_projection(&mut section_context, &tys_name, index, &projection_names);
        }

        // generate the normalized rt (mechanical, using generate_normalized_rt_def)
        for component in &self.components {
            section_context.append_document(invariants::generate_normalized_rt_def(
                &component.rt_name(),
                &component.ty_name(),
                &rt_params,
                &context_names_without_sigma,
            ));
        }

        // end section

        // use set_flags
        //

        let mut doc = coq::Document::default();
        doc.push(coq::section::Section::new(self.components[0].ty_name(), |doc| {
            doc.append_document(section_context);
        }));
        for component in &self.components {
            component.set_flags(&mut doc, &context_names_without_sigma);
        }

        doc
    }
}
