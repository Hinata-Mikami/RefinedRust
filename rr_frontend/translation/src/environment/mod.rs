// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.
pub mod borrowck;
mod collect_closure_defs_visitor;
mod collect_prusti_spec_visitor;
mod dump_borrowck_info;
mod loops;
pub mod mir_analyses;
pub mod mir_sets;
pub mod mir_storage;
pub mod mir_utils;
pub mod polonius_info;
pub mod procedure;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::rc::Rc;

use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{ast, hir, span};

use crate::attrs;
use crate::data::ProcedureDefId;
use crate::environment::borrowck::facts;
use crate::environment::collect_closure_defs_visitor::CollectClosureDefsVisitor;
use crate::environment::collect_prusti_spec_visitor::CollectPrustiSpecVisitor;
use crate::environment::procedure::Procedure;

/// Facade to the Rust compiler.
pub struct Environment<'tcx> {
    /// Cached MIR bodies.
    bodies: RefCell<HashMap<hir::def_id::LocalDefId, Rc<mir::Body<'tcx>>>>,
    /// Cached borrowck information.
    borrowck_facts: RefCell<HashMap<hir::def_id::LocalDefId, Rc<facts::Borrowck>>>,
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> Environment<'tcx> {
    /// Builds an environment given a compiler state.
    #[must_use]
    pub fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        Environment {
            tcx,
            bodies: RefCell::new(HashMap::new()),
            borrowck_facts: RefCell::new(HashMap::new()),
        }
    }

    /// Returns the path of the source that is being compiled
    pub fn source_path(&self) -> PathBuf {
        self.tcx.sess.local_crate_source_file().unwrap()
    }

    /// Returns the file name of the source that is being compiled
    pub fn source_file_name(&self) -> String {
        let source_path = self.source_path();
        source_path.file_name().unwrap().to_str().unwrap().to_owned()
    }

    /// Returns the name of the crate that is being compiled
    pub fn crate_name(&self) -> String {
        self.tcx.crate_name(span::def_id::LOCAL_CRATE).to_string()
    }

    /// Returns the typing context
    pub const fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    /// Returns the `CodeMap`
    pub fn codemap(&self) -> &'tcx span::source_map::SourceMap {
        self.tcx.sess.source_map()
    }

    /// Returns true if an error has been emitted
    pub fn has_errors(&self) -> bool {
        self.tcx.sess.has_errors().is_some()
    }

    /// Get ids of Rust procedures.
    pub fn get_procedures(&self) -> Vec<hir::def_id::LocalDefId> {
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        visitor.run();
        // TODO: cache results
        let (functions, _, _, _, _) = visitor.get_results();
        functions
    }

    /// Get ids of Rust statics.
    pub fn get_statics(&self) -> Vec<hir::def_id::LocalDefId> {
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        visitor.run();
        // TODO: cache results
        let (_, _, statics, _, _) = visitor.get_results();
        statics
    }

    /// Get ids of Rust consts.
    pub fn get_consts(&self) -> Vec<hir::def_id::LocalDefId> {
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        visitor.run();
        // TODO: cache results
        let (_, _, _, consts, _) = visitor.get_results();
        consts
    }

    /// Get ids of Rust modules.
    pub fn get_modules(&self) -> Vec<hir::def_id::LocalDefId> {
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        visitor.run();
        // TODO: cache results
        let (_, modules, _, _, _) = visitor.get_results();
        modules
    }

    /// Get ids of trait declarations.
    pub fn get_traits(&self) -> Vec<hir::def_id::LocalDefId> {
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        visitor.run();
        // TODO: cache results
        let (_, _, _, _, traits) = visitor.get_results();
        traits
    }

    /// Get ids of trait impls.
    pub fn get_trait_impls(&self) -> Vec<hir::def_id::LocalDefId> {
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        // TODO cache results
        visitor.run();
        visitor.get_trait_impls()
    }

    /// Get ids of Rust closures.
    pub fn get_closures(&self) -> Vec<hir::def_id::LocalDefId> {
        let tcx = self.tcx;
        let mut cl_visitor = CollectClosureDefsVisitor::new(self);
        tcx.hir().visit_all_item_likes_in_crate(&mut cl_visitor);
        cl_visitor.get_closure_defs()
    }

    /// Find whether the procedure has a particular `[tool]::<name>` attribute.
    pub fn has_tool_attribute(&self, def_id: ProcedureDefId, name: &str) -> bool {
        let tcx = self.tcx();
        // TODO: migrate to get_attrs
        attrs::has_tool_attr(tcx.get_attrs_unchecked(def_id), name)
    }

    /// Find whether the procedure has a particular `[tool]::<name>` attribute; if so, return its
    /// name.
    pub fn get_tool_attribute<'a>(&'a self, def_id: ProcedureDefId, name: &str) -> Option<&'a ast::AttrArgs> {
        let tcx = self.tcx();
        // TODO: migrate to get_attrs
        attrs::get_tool_attr(tcx.get_attrs_unchecked(def_id), name)
    }

    /// Check whether the procedure has any `[tool]` attribute.
    pub fn has_any_tool_attribute(&self, def_id: ProcedureDefId) -> bool {
        let tcx = self.tcx();
        // TODO: migrate to get_attrs
        attrs::has_any_tool_attr(tcx.get_attrs_unchecked(def_id))
    }

    /// Get the attributes of an item (e.g. procedures).
    pub fn get_attributes(&self, def_id: hir::def_id::DefId) -> &[ast::ast::Attribute] {
        // TODO: migrate to get_attrs
        self.tcx().get_attrs_unchecked(def_id)
    }

    /// Get tool attributes of this function, including selected attributes from the surrounding impl.
    pub fn get_attributes_of_function<F>(
        &self,
        did: hir::def_id::DefId,
        propagate_from_impl: &F,
    ) -> Vec<&ast::ast::AttrItem>
    where
        F: for<'a> Fn(&'a ast::ast::AttrItem) -> bool,
    {
        let attrs = self.get_attributes(did);
        let mut filtered_attrs = attrs::filter_for_tool(attrs);
        // also add selected attributes from the surrounding impl
        if let Some(impl_did) = self.tcx().impl_of_method(did) {
            let impl_attrs = self.get_attributes(impl_did);
            let filtered_impl_attrs = attrs::filter_for_tool(impl_attrs);
            filtered_attrs.extend(filtered_impl_attrs.into_iter().filter(|x| propagate_from_impl(x)));
        }

        // for closures, propagate from the surrounding function
        if self.tcx().is_closure(did) {
            let parent_did = self.tcx().parent(did);
            let parent_attrs = self.get_attributes_of_function(parent_did, propagate_from_impl);
            filtered_attrs.extend(parent_attrs.into_iter().filter(|x| propagate_from_impl(x)));
        }

        filtered_attrs
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    pub fn get_item_def_path(&self, def_id: hir::def_id::DefId) -> String {
        let def_path = self.tcx.def_path(def_id);
        let mut crate_name = self.tcx.crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate_verbose());
        crate_name
    }

    /// Get the span of a definition
    /// Note: panics on non-local `def_id`
    pub fn get_item_span(&self, def_id: hir::def_id::DefId) -> span::Span {
        self.tcx.hir().span_if_local(def_id).unwrap()
    }

    pub fn get_absolute_item_name(&self, def_id: hir::def_id::DefId) -> String {
        self.tcx.def_path_str(def_id)
    }

    pub fn get_item_name(&self, def_id: hir::def_id::DefId) -> String {
        self.tcx.def_path_str(def_id)
        // self.tcx().item_path_str(def_id)
    }

    /// Get the name of an item without the path prefix.
    pub fn get_assoc_item_name(&self, trait_method_did: hir::def_id::DefId) -> Option<String> {
        let def_path = self.tcx.def_path(trait_method_did);
        if let Some(last_elem) = def_path.data.last() {
            if let Some(name) = last_elem.data.get_opt_name() {
                return Some(name.as_str().to_owned());
            }
        }
        None
    }

    /// Get the associated types of a trait.
    pub fn get_trait_assoc_types(&self, trait_did: hir::def_id::DefId) -> Vec<hir::def_id::DefId> {
        let assoc_items: &ty::AssocItems = self.tcx.associated_items(trait_did);

        let mut assoc_tys = Vec::new();
        for c in assoc_items.in_definition_order() {
            if ty::AssocKind::Type == c.kind {
                assoc_tys.push(c.def_id);
            }
        }
        assoc_tys
    }

    /// Check if this is the `DefId` of a method.
    pub fn is_method_did(&self, did: hir::def_id::DefId) -> bool {
        if self.tcx.is_trait(did) {
            return false;
        }

        // TODO: find a more robust way to check this. We cannot call `type_of` on all dids.
        let ty: ty::EarlyBinder<ty::Ty<'tcx>> = self.tcx.type_of(did);
        let ty = ty.skip_binder();
        matches!(ty.kind(), ty::TyKind::FnDef(_, _))
    }

    /// Get the id of a trait impl surrounding a method.
    #[must_use]
    pub fn trait_impl_of_method(&self, method_did: hir::def_id::DefId) -> Option<hir::def_id::DefId> {
        if let Some(impl_did) = self.tcx().impl_of_method(method_did) {
            self.tcx().trait_id_of_impl(impl_did).is_some().then_some(impl_did)
        } else {
            None
        }
    }

    /// Get a Procedure.
    pub fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Procedure<'tcx> {
        Procedure::new(self, proc_def_id)
    }

    /// Get the MIR body of a local procedure.
    pub fn local_mir(&self, def_id: hir::def_id::LocalDefId) -> Rc<mir::Body<'tcx>> {
        let mut bodies = self.bodies.borrow_mut();

        if let Some(body) = bodies.get(&def_id) {
            return body.clone();
        }

        // SAFETY: This is safe because we are feeding in the same `tcx`
        // that was used to store the data.
        let body_with_facts = unsafe { self::mir_storage::retrieve_mir_body(self.tcx, def_id) };
        let body = body_with_facts.body;
        let facts = facts::Borrowck {
            input_facts: RefCell::new(body_with_facts.input_facts),
            output_facts: body_with_facts.output_facts.unwrap(),
            location_table: RefCell::new(body_with_facts.location_table),
        };

        let mut borrowck_facts = self.borrowck_facts.borrow_mut();
        borrowck_facts.insert(def_id, Rc::new(facts));

        bodies.entry(def_id).or_insert_with(|| Rc::new(body)).clone()
    }

    /// Get Polonius facts of a local procedure.
    pub fn local_mir_borrowck_facts(&self, def_id: hir::def_id::LocalDefId) -> Rc<facts::Borrowck> {
        // ensure that we have already fetched the body & facts
        self.local_mir(def_id);
        let borrowck_facts = self.borrowck_facts.borrow();
        borrowck_facts.get(&def_id).unwrap().clone()
    }

    /// Get the MIR body of an external procedure.
    pub fn external_mir<'a>(&self, def_id: hir::def_id::DefId) -> &'a mir::Body<'tcx> {
        self.tcx().optimized_mir(def_id)
    }

    /// Get all relevant trait declarations for some type.
    pub fn get_traits_decls_for_type(&self, ty: ty::Ty<'tcx>) -> HashSet<hir::def_id::DefId> {
        let mut res = HashSet::new();
        let traits = self.tcx().all_traits();
        for trait_id in traits {
            self.tcx().for_each_relevant_impl(trait_id, ty, |impl_id| {
                if let Some(relevant_trait_id) = self.tcx().trait_id_of_impl(impl_id) {
                    res.insert(relevant_trait_id);
                }
            });
        }
        res
    }

    /// Get an associated item by name.
    pub fn get_assoc_item(&self, id: hir::def_id::DefId, name: span::Symbol) -> Option<ty::AssocItem> {
        // FIXME: Probably we should use https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.AssociatedItems.html#method.find_by_name_and_namespace
        // instead.
        self.tcx().associated_items(id).filter_by_name_unhygienic(name).next().copied()
    }

    /// Get a trait method declaration by name for type.
    pub fn get_trait_method_decl_for_type(
        &self,
        typ: ty::Ty<'tcx>,
        trait_id: hir::def_id::DefId,
        name: span::Symbol,
    ) -> Vec<ty::AssocItem> {
        let mut result = Vec::new();
        self.tcx().for_each_relevant_impl(trait_id, typ, |impl_id| {
            let item = self.get_assoc_item(impl_id, name);
            if let Some(inner) = item {
                result.push(inner);
            }
        });
        result
    }
}

pub fn dump_borrowck_info<'a, 'tcx>(
    env: &'a Environment<'tcx>,
    procedure: ProcedureDefId,
    info: &'a polonius_info::PoloniusInfo<'a, 'tcx>,
) {
    dump_borrowck_info::dump_borrowck_info(env, procedure, info);
}
