// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, btree_map};

use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::base::*;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Mode {
    Prove,
    OnlySpec,
    TrustMe,
    Shim,
    CodeShim,
    Ignore,
}

impl Mode {
    pub fn is_prove(self) -> bool {
        self == Self::Prove
    }

    pub fn is_only_spec(self) -> bool {
        self == Self::OnlySpec
    }

    pub fn is_trust_me(self) -> bool {
        self == Self::TrustMe
    }

    pub fn is_shim(self) -> bool {
        self == Self::Shim
    }

    pub fn is_code_shim(self) -> bool {
        self == Self::CodeShim
    }

    pub fn is_ignore(self) -> bool {
        self == Self::Ignore
    }

    pub fn needs_proof(self) -> bool {
        self == Self::Prove || self == Self::CodeShim
    }

    pub fn needs_def(self) -> bool {
        self == Self::Prove || self == Self::TrustMe
    }

    pub fn needs_spec(self) -> bool {
        self == Self::Prove || self == Self::TrustMe || self == Self::OnlySpec || self == Self::CodeShim
    }
}

#[derive(Clone)]
pub struct Meta {
    /// name for the specification
    spec_name: String,
    /// name for the code
    code_name: String,
    /// name for the trait inclusion def
    trait_req_incl_name: String,
    /// mangled name of the function
    name: String,
    /// what should `RefinedRust` do with this function?
    mode: Mode,
    /// true if this is a default trait impl
    is_default_trait_impl: bool,
}

impl Meta {
    pub const fn new(
        spec_name: String,
        code_name: String,
        trait_req_incl_name: String,
        name: String,
        mode: Mode,
        is_default_trait_impl: bool,
    ) -> Self {
        Self {
            spec_name,
            code_name,
            trait_req_incl_name,
            name,
            mode,
            is_default_trait_impl,
        }
    }

    pub fn get_spec_name(&self) -> &str {
        &self.spec_name
    }

    pub fn get_trait_req_incl_name(&self) -> &str {
        &self.trait_req_incl_name
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_code_name(&self) -> &str {
        &self.code_name
    }

    pub const fn get_mode(&self) -> Mode {
        self.mode
    }

    pub const fn is_trait_default(&self) -> bool {
        self.is_default_trait_impl
    }
}

/**
 * Tracks the functions we translated and the Coq names they are available under.
 * To account for dependencies between functions, we may register translated names before we have
 * actually translated the function.
 */
pub struct Scope<'tcx, 'def> {
    tcx: ty::TyCtxt<'tcx>,
    /// maps the defid to `(code_name, spec_name, trait_req_incl_name, name)`
    name_map: BTreeMap<OrderedDefId, Meta>,
    /// track the actually translated functions
    translated_functions: BTreeMap<OrderedDefId, radium::Function<'def>>,
    /// track the functions with just a specification (`rr::only_spec`)
    specced_functions:
        BTreeMap<OrderedDefId, &'def radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>>,
}

impl<'tcx, 'def> Scope<'tcx, 'def> {
    pub const fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            name_map: BTreeMap::new(),
            translated_functions: BTreeMap::new(),
            specced_functions: BTreeMap::new(),
        }
    }

    fn get_ordered_did(&self, did: DefId) -> OrderedDefId {
        OrderedDefId::new(self.tcx, did)
    }

    /// Lookup the meta information of a function.
    pub fn lookup_function(&self, did: DefId) -> Option<Meta> {
        self.name_map.get(&self.get_ordered_did(did)).cloned()
    }

    /// Lookup a translated function spec
    pub fn lookup_function_spec(
        &self,
        did: DefId,
    ) -> Option<&'def radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>> {
        let ordered_did = self.get_ordered_did(did);
        if let Some(translated_fn) = self.translated_functions.get(&ordered_did) {
            Some(translated_fn.spec)
        } else if let Some(translated_spec) = self.specced_functions.get(&ordered_did) {
            Some(translated_spec)
        } else {
            None
        }
    }

    /// Lookup the mode for a function.
    pub fn lookup_function_mode(&self, did: DefId) -> Option<Mode> {
        self.name_map.get(&self.get_ordered_did(did)).map(Meta::get_mode)
    }

    /// Register a function.
    pub fn register_function(&mut self, did: DefId, meta: Meta) -> Result<(), TranslationError<'tcx>> {
        if self.name_map.insert(self.get_ordered_did(did), meta).is_some() {
            Err(TranslationError::ProcedureRegistry(format!(
                "function for defid {:?} has already been registered",
                did
            )))
        } else {
            Ok(())
        }
    }

    /// For a function which is a trait member's default impl, provide the overridden spec names
    /// from the trait registry.
    pub fn override_trait_default_impl_names(
        &mut self,
        did: DefId,
        spec_name: &str,
        trait_req_incl_name: &str,
    ) {
        if let Some(names) = self.name_map.get_mut(&self.get_ordered_did(did)) {
            assert!(names.is_default_trait_impl);
            spec_name.clone_into(&mut names.spec_name);
            trait_req_incl_name.clone_into(&mut names.trait_req_incl_name);
        }
    }

    /// Provide the code for a translated function.
    pub fn provide_translated_function(&mut self, did: DefId, trf: radium::Function<'def>) {
        let ordered_did = self.get_ordered_did(did);
        let meta = &self.name_map[&ordered_did];
        assert!(meta.get_mode().needs_def() || meta.get_mode().is_code_shim());
        assert!(self.translated_functions.insert(ordered_did, trf).is_none());
    }

    /// Provide the specification for an `only_spec` function.
    pub fn provide_specced_function(
        &mut self,
        did: DefId,
        spec: &'def radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>,
    ) {
        let ordered_did = self.get_ordered_did(did);
        let meta = &self.name_map[&ordered_did];
        assert!(meta.get_mode().is_only_spec());
        assert!(self.specced_functions.insert(ordered_did, spec).is_none());
    }

    /// Iterate over the functions we have generated code for.
    pub fn iter_code(&self) -> btree_map::Iter<'_, OrderedDefId, radium::Function<'def>> {
        self.translated_functions.iter()
    }

    /// Iterate over the functions we have generated only specs for.
    pub fn iter_only_spec(
        &self,
    ) -> btree_map::Iter<'_, OrderedDefId, &'def radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>>
    {
        self.specced_functions.iter()
    }
}
