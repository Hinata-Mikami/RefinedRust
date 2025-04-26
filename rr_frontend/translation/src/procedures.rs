// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{btree_map, BTreeMap};

use rr_rustc_interface::hir;

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
    spec_name: String,
    code_name: String,
    trait_req_incl_name: String,
    name: String,
    mode: Mode,
}

impl Meta {
    pub const fn new(
        spec_name: String,
        code_name: String,
        trait_req_incl_name: String,
        name: String,
        mode: Mode,
    ) -> Self {
        Self {
            spec_name,
            code_name,
            trait_req_incl_name,
            name,
            mode,
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
}

/**
 * Tracks the functions we translated and the Coq names they are available under.
 * To account for dependencies between functions, we may register translated names before we have
 * actually translated the function.
 */
pub struct Scope<'def> {
    /// maps the defid to (code_name, spec_name, trait_req_incl_name, name)
    name_map: BTreeMap<hir::def_id::DefId, Meta>,
    /// track the actually translated functions
    translated_functions: BTreeMap<hir::def_id::DefId, radium::Function<'def>>,
    /// track the functions with just a specification (rr::only_spec)
    specced_functions:
        BTreeMap<hir::def_id::DefId, &'def radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>>,
}

impl<'def> Scope<'def> {
    pub fn new() -> Self {
        Self {
            name_map: BTreeMap::new(),
            translated_functions: BTreeMap::new(),
            specced_functions: BTreeMap::new(),
        }
    }

    /// Lookup the meta information of a function.
    pub fn lookup_function(&self, did: hir::def_id::DefId) -> Option<Meta> {
        self.name_map.get(&did).cloned()
    }

    /// Lookup a translated function spec
    pub fn lookup_function_spec(
        &self,
        did: hir::def_id::DefId,
    ) -> Option<&'def radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>> {
        if let Some(translated_fn) = self.translated_functions.get(&did) {
            Some(translated_fn.spec)
        } else if let Some(translated_spec) = self.specced_functions.get(&did) {
            Some(translated_spec)
        } else {
            None
        }
    }

    /// Lookup the Coq spec name for a function.
    pub fn lookup_function_spec_name(&self, did: hir::def_id::DefId) -> Option<&str> {
        self.name_map.get(&did).map(Meta::get_spec_name)
    }

    /// Lookup the name for a function.
    pub fn lookup_function_mangled_name(&self, did: hir::def_id::DefId) -> Option<&str> {
        self.name_map.get(&did).map(Meta::get_name)
    }

    /// Lookup the mode for a function.
    pub fn lookup_function_mode(&self, did: hir::def_id::DefId) -> Option<Mode> {
        self.name_map.get(&did).map(Meta::get_mode)
    }

    /// Register a function.
    pub fn register_function<'tcx>(
        &mut self,
        did: hir::def_id::DefId,
        meta: Meta,
    ) -> Result<(), TranslationError<'tcx>> {
        if self.name_map.insert(did, meta).is_some() {
            Err(TranslationError::ProcedureRegistry(format!(
                "function for defid {:?} has already been registered",
                did
            )))
        } else {
            Ok(())
        }
    }

    /// Provide the code for a translated function.
    pub fn provide_translated_function(&mut self, did: hir::def_id::DefId, trf: radium::Function<'def>) {
        let meta = &self.name_map[&did];
        assert!(meta.get_mode().needs_def() || meta.get_mode().is_code_shim());
        assert!(self.translated_functions.insert(did, trf).is_none());
    }

    /// Provide the specification for an `only_spec` function.
    pub fn provide_specced_function(
        &mut self,
        did: hir::def_id::DefId,
        spec: &'def radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>,
    ) {
        let meta = &self.name_map[&did];
        assert!(meta.get_mode().is_only_spec());
        assert!(self.specced_functions.insert(did, spec).is_none());
    }

    /// Iterate over the functions we have generated code for.
    pub fn iter_code(&self) -> btree_map::Iter<'_, hir::def_id::DefId, radium::Function<'def>> {
        self.translated_functions.iter()
    }

    /// Iterate over the functions we have generated only specs for.
    pub fn iter_only_spec(
        &self,
    ) -> btree_map::Iter<
        '_,
        hir::def_id::DefId,
        &'def radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>,
    > {
        self.specced_functions.iter()
    }
}
