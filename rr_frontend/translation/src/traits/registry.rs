// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet};

use log::{info, trace};
use radium::specs;
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::middle::ty;
use traits::{Error, TraitResult, resolution};
use typed_arena::Arena;

use crate::base::*;
use crate::body::signature;
use crate::environment::Environment;
use crate::regions::region_bi_folder::RegionBiFolder;
use crate::spec_parsers::propagate_method_attr_from_impl;
use crate::spec_parsers::trait_attr_parser::{
    TraitAttrParser as _, VerboseTraitAttrParser, get_declared_trait_attrs,
};
use crate::spec_parsers::trait_impl_attr_parser::{TraitImplAttrParser as _, VerboseTraitImplAttrParser};
use crate::traits::requirements;
use crate::types::scope;
use crate::{attrs, procedures, traits, types};

pub(crate) struct TR<'tcx, 'def> {
    /// environment
    env: &'def Environment<'tcx>,
    type_translator: Cell<Option<&'def types::TX<'def, 'tcx>>>,

    /// trait declarations
    trait_decls: RefCell<HashMap<LocalDefId, radium::TraitSpecDecl<'def>>>,
    /// trait literals for using occurrences, including shims we import
    trait_literals: RefCell<HashMap<DefId, specs::LiteralTraitSpecRef<'def>>>,

    /// for the trait instances in scope, the names for their Coq definitions
    /// (to enable references to them when translating functions)
    impl_literals: RefCell<HashMap<DefId, specs::LiteralTraitImplRef<'def>>>,

    /// arena for allocating trait literals
    trait_arena: &'def Arena<specs::LiteralTraitSpec>,
    /// arena for allocating impl literals
    impl_arena: &'def Arena<specs::LiteralTraitImpl>,
    /// arena for allocating trait use references
    trait_use_arena: &'def Arena<radium::LiteralTraitSpecUseCell<'def>>,
    /// arena for function specifications
    fn_spec_arena: &'def Arena<specs::FunctionSpec<'def, specs::InnerFunctionSpec<'def>>>,
}

impl<'tcx, 'def> TR<'tcx, 'def> {
    pub(crate) const fn type_translator(&self) -> &'def types::TX<'def, 'tcx> {
        self.type_translator.get().unwrap()
    }

    /// Create an empty trait registry.
    pub(crate) fn new(
        env: &'def Environment<'tcx>,
        trait_arena: &'def Arena<specs::LiteralTraitSpec>,
        impl_arena: &'def Arena<specs::LiteralTraitImpl>,
        trait_use_arena: &'def Arena<radium::LiteralTraitSpecUseCell<'def>>,
        fn_spec_arena: &'def Arena<specs::FunctionSpec<'def, specs::InnerFunctionSpec<'def>>>,
    ) -> Self {
        Self {
            env,
            type_translator: Cell::new(None),
            trait_arena,
            impl_arena,
            trait_use_arena,
            fn_spec_arena,
            trait_decls: RefCell::new(HashMap::new()),
            trait_literals: RefCell::new(HashMap::new()),
            impl_literals: RefCell::new(HashMap::new()),
        }
    }

    pub(crate) fn provide_type_translator(&self, ty_translator: &'def types::TX<'def, 'tcx>) {
        self.type_translator.set(Some(ty_translator));
    }

    /// Get registered trait declarations in the local crate.
    pub(crate) fn get_trait_decls(&self) -> HashMap<LocalDefId, specs::TraitSpecDecl<'def>> {
        let decls = self.trait_decls.borrow();
        decls.clone()
    }

    /// Get a set of other (different) traits that this trait depends on.
    pub(crate) fn get_deps_of_trait(&self, did: DefId) -> HashSet<DefId> {
        let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(did);

        let mut deps = HashSet::new();
        for clause in param_env.caller_bounds() {
            let kind = clause.kind().skip_binder();
            if let ty::ClauseKind::Trait(pred) = kind {
                let other_did = pred.trait_ref.def_id;

                if other_did != did {
                    deps.insert(other_did);
                }
            }
        }

        deps
    }

    /// Order the given traits according to their dependencies.
    pub(crate) fn get_trait_deps(&self, traits: &[LocalDefId]) -> HashMap<DefId, HashSet<DefId>> {
        let mut dep_map = HashMap::new();

        for trait_decl in traits {
            let deps = self.get_deps_of_trait(trait_decl.to_def_id());
            dep_map.insert(trait_decl.to_def_id(), deps);
        }

        dep_map
    }

    /// Get a map of dependencies between traits.
    pub(crate) fn get_registered_trait_deps(&self) -> HashMap<DefId, HashSet<DefId>> {
        let mut dep_map = HashMap::new();

        let decls = self.trait_decls.borrow();
        for trait_decl in decls.keys() {
            let deps = self.get_deps_of_trait(trait_decl.to_def_id());
            dep_map.insert(trait_decl.to_def_id(), deps);
        }

        dep_map
    }

    /// Get the names of associated types of this trait.
    pub(crate) fn get_associated_type_names(&self, did: DefId) -> Vec<String> {
        let mut assoc_tys = Vec::new();

        // get associated types
        let assoc_types = self.env.get_trait_assoc_types(did);
        for ty_did in &assoc_types {
            let ty_name = self.env.get_assoc_item_name(*ty_did).unwrap();
            assoc_tys.push(ty_name);
        }

        assoc_tys
    }

    /// Generate names for a trait.
    fn make_literal_trait_spec(
        &self,
        did: DefId,
        name: String,
        declared_attrs: Vec<String>,
        has_semantic_interp: bool,
    ) -> Result<specs::LiteralTraitSpec, Error<'tcx>> {
        let spec_record = format!("{name}_spec");
        let spec_params_record = format!("{name}_spec_params");
        let spec_attrs_record = format!("{name}_spec_attrs");
        let base_spec = format!("{name}_base_spec");
        let base_spec_params = format!("{name}_base_spec_params");
        let spec_subsumption = format!("{name}_spec_incl");

        let spec_semantic = has_semantic_interp.then(|| format!("{name}_semantic_interp"));

        let mut method_trait_incl_decls = BTreeMap::new();

        let items: &ty::AssocItems = self.env.tcx().associated_items(did);
        for c in items.in_definition_order() {
            if let ty::AssocKind::Fn { .. } = c.kind {
                // get function name
                let method_name =
                    self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotATraitMethod(c.def_id))?;
                let method_name = strip_coq_ident(&method_name);

                let trait_incl_decl = format!("trait_incl_of_{name}_{method_name}");
                method_trait_incl_decls.insert(method_name, trait_incl_decl);
            }
        }

        Ok(specs::LiteralTraitSpec {
            name,
            assoc_tys: self.get_associated_type_names(did),
            spec_record,
            spec_params_record,
            spec_attrs_record,
            spec_semantic,
            base_spec,
            base_spec_params,
            spec_subsumption,
            declared_attrs,
            method_trait_incl_decls,
        })
    }

    /// Register a new annotated trait in the local crate with the registry.
    pub(crate) fn register_trait(
        &'def self,
        did: LocalDefId,
        proc_registry: &mut procedures::Scope<'tcx, 'def>,
    ) -> Result<(), TranslationError<'tcx>> {
        trace!("enter TR::register_trait for did={did:?}");

        {
            let scope = self.trait_decls.borrow();
            if scope.get(&did).is_some() {
                return Ok(());
            }
        }

        // first register the shim so we can handle recursive traits
        let trait_name = strip_coq_ident(&self.env.get_absolute_item_name(did.to_def_id()));
        let trait_attrs = attrs::filter_for_tool(self.env.get_attributes(did.into()));

        let has_semantic_interp = self.env.has_tool_attribute(did.into(), "semantic");

        // get the declared attributes that are allowed on impls
        let valid_attrs: Vec<String> =
            get_declared_trait_attrs(&trait_attrs).map_err(|e| Error::TraitSpec(did.into(), e))?;

        // make the literal we are going to use
        let lit_trait_spec = self.make_literal_trait_spec(
            did.to_def_id(),
            trait_name.clone(),
            valid_attrs,
            has_semantic_interp,
        )?;
        // already register it for use
        // In particular, this is also needed to be able to register the methods of this trait
        // below, as they need to be able to access the associated types of this trait already.
        // (in fact, their environment contains their self instance)
        let lit_trait_spec_ref = self.register_shim(did.to_def_id(), lit_trait_spec)?;

        let mut cont = || -> Result<(), TranslationError<'tcx>> {
            // get generics
            let trait_generics: &'tcx ty::Generics = self.env.tcx().generics_of(did.to_def_id());
            let mut param_scope = scope::Params::from(trait_generics.own_params.as_slice());
            param_scope.add_param_env(did.to_def_id(), self.env, self.type_translator(), self)?;

            let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(did.to_def_id());
            trace!("param env is {:?}", param_env);

            // parse trait spec
            // As different attributes of the spec may depend on each other, we need to pass a closure
            // determining under which Coq name we are going to introduce them
            // Note: This needs to match up with `radium::LiteralTraitSpec.make_spec_attr_name`!
            let mut attr_parser =
                VerboseTraitAttrParser::new(&param_scope, |id| format!("{trait_name}_{id}"));
            let trait_spec =
                attr_parser.parse_trait_attrs(&trait_attrs).map_err(|e| Error::TraitSpec(did.into(), e))?;

            // get items
            let mut methods = BTreeMap::new();
            let mut assoc_types = Vec::new();
            let items: &ty::AssocItems = self.env.tcx().associated_items(did);
            for c in items.in_definition_order() {
                if ty::AssocTag::Fn == c.as_tag() {
                    // get attributes
                    let attrs =
                        self.env.get_attributes_of_function(c.def_id, &propagate_method_attr_from_impl);

                    // get function name
                    let method_name =
                        self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotATraitMethod(c.def_id))?;
                    let method_name = strip_coq_ident(&method_name);

                    let name = format!("{trait_name}_{method_name}");
                    let spec_name = format!("{name}_base_spec");

                    let trait_incl_name = &lit_trait_spec_ref.method_trait_incl_decls[&method_name];

                    // get spec
                    let spec = signature::TX::spec_for_trait_method(
                        self.env,
                        c.def_id,
                        &name,
                        &spec_name,
                        trait_incl_name,
                        attrs.as_slice(),
                        self.type_translator(),
                        self,
                    )?;
                    let spec_ref = self.fn_spec_arena.alloc(spec);

                    // override the names in the procedure registry
                    proc_registry.override_trait_default_impl_names(c.def_id, &spec_name, trait_incl_name);

                    methods.insert(method_name, &*spec_ref);
                } else if let ty::AssocKind::Type { .. } = c.kind {
                    // get name
                    let type_name =
                        self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotAnAssocType(c.def_id))?;
                    let type_name = strip_coq_ident(&type_name);
                    let lit = radium::LiteralTyParam::new(&type_name, &type_name);
                    assoc_types.push(lit);
                } else {
                    return Err(Error::AssocConstNotSupported.into());
                }
            }

            let base_instance_spec = radium::TraitInstanceSpec::new(methods);
            let decl = radium::TraitSpecDecl::new(
                lit_trait_spec_ref,
                param_scope.into(),
                assoc_types,
                base_instance_spec,
                trait_spec.attrs,
            );

            let mut scope = self.trait_decls.borrow_mut();
            scope.insert(did, decl);
            Ok(())
        };

        if let Err(err) = cont() {
            // if there is an error, rollback the registration of the shim
            let mut trait_literals = self.trait_literals.borrow_mut();
            trait_literals.remove(&did.to_def_id());
            trace!("leave TR::register_trait (failed)");
            return Err(err);
        }

        trace!("leave TR::register_trait");
        Ok(())
    }

    /// Register a shim with the trait registry.
    ///
    /// Errors:
    /// - NotATrait(did) if did is not a trait
    /// - TraitAlreadyExists(did) if this trait has already been registered
    pub(crate) fn register_shim(
        &self,
        did: DefId,
        spec: radium::LiteralTraitSpec,
    ) -> TraitResult<'tcx, radium::LiteralTraitSpecRef<'def>> {
        if !self.env.tcx().is_trait(did) {
            return Err(Error::NotATrait(did));
        }

        let mut trait_literals = self.trait_literals.borrow_mut();
        if trait_literals.get(&did).is_some() {
            return Err(Error::TraitAlreadyExists(did));
        }

        let spec = self.trait_arena.alloc(spec);
        trait_literals.insert(did, &*spec);

        Ok(spec)
    }

    /// Register a shim for a trait impl.
    pub(crate) fn register_impl_shim(
        &self,
        did: DefId,
        spec: radium::LiteralTraitImpl,
    ) -> TraitResult<'tcx, radium::LiteralTraitImplRef<'def>> {
        if self.env.tcx().trait_id_of_impl(did).is_none() {
            return Err(Error::NotATraitImpl(did));
        }

        let mut impl_literals = self.impl_literals.borrow_mut();
        if impl_literals.get(&did).is_some() {
            return Err(Error::ImplAlreadyExists(did));
        }

        let spec = self.impl_arena.alloc(spec);
        impl_literals.insert(did, &*spec);

        Ok(spec)
    }

    /// Lookup a trait.
    pub(crate) fn lookup_trait(&self, trait_did: DefId) -> Option<radium::LiteralTraitSpecRef<'def>> {
        let trait_literals = self.trait_literals.borrow();
        trait_literals.get(&trait_did).copied()
    }

    /// Lookup the spec for an impl.
    /// If None, use the default spec.
    pub(crate) fn lookup_impl(&self, impl_did: DefId) -> Option<radium::LiteralTraitImplRef<'def>> {
        let impl_literals = self.impl_literals.borrow();
        impl_literals.get(&impl_did).copied()
    }

    /// Get the term for the specification of a trait impl (applied to the given arguments of the trait),
    /// as well as the list of associated types.
    pub(crate) fn get_impl_spec_term(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        impl_did: DefId,
        impl_args: &[ty::GenericArg<'tcx>],
        trait_args: &[ty::GenericArg<'tcx>],
    ) -> Result<(radium::SpecializedTraitImpl<'def>, Vec<ty::Ty<'tcx>>), TranslationError<'tcx>> {
        trace!(
            "enter TR::get_impl_spec_term for impl_did={impl_did:?} impl_args={impl_args:?} trait_args={trait_args:?}"
        );
        let trait_did = self.env.tcx().trait_id_of_impl(impl_did).ok_or(Error::NotATraitImpl(impl_did))?;

        self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;

        let mut assoc_args = Vec::new();
        // get associated types of this impl
        // Since we know the concrete impl, we can directly resolve all of the associated types
        // TODO is this definition order guaranteed to be the same as on the trait?
        let assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(impl_did);
        for it in assoc_items.in_definition_order() {
            if let ty::AssocKind::Type { .. } = it.kind {
                let item_did = it.def_id;
                let item_ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = self.env.tcx().type_of(item_did);
                let subst_ty = item_ty.instantiate(self.env.tcx(), impl_args);

                assoc_args.push(subst_ty);
            }
        }

        // check if there's a more specific impl spec
        let term = if let Some(impl_spec) = self.lookup_impl(impl_did) {
            let scope_inst =
                self.compute_scope_inst_in_state(state, impl_did, self.env.tcx().mk_args(impl_args))?;

            radium::SpecializedTraitImpl::new(impl_spec, scope_inst)
        } else {
            return Err(TranslationError::TraitTranslation(Error::UnregisteredImpl(impl_did)));
        };

        trace!("leave TR::get_impl_spec_term");
        Ok((term, assoc_args))
    }

    /// Resolve the trait requirements of a [did] substituted with [params].
    /// [did] should have been resolved as much as possible,
    /// as the requirements can be different depending on which impl we consider.
    /// The requirements are sorted stably across compilations, and consistently with the
    /// declaration order.
    pub(crate) fn resolve_trait_requirements_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        did: DefId,
        params: ty::GenericArgsRef<'tcx>,
    ) -> Result<Vec<radium::TraitReqInst<'def, ty::Ty<'tcx>>>, TranslationError<'tcx>> {
        trace!("Enter resolve_trait_requirements_in_state with did={did:?} and params={params:?}");

        let current_typing_env: ty::TypingEnv<'tcx> = state.get_typing_env(self.env.tcx());
        trace!("current typing env: {current_typing_env:?}");

        let callee_typing_env = ty::TypingEnv::post_analysis(self.env.tcx(), did);
        trace!("callee typing env {callee_typing_env:?}");

        // Get the trait requirements of the callee
        let callee_requirements = requirements::get_trait_requirements_with_origin(self.env, did);
        trace!("non-trivial callee requirements: {callee_requirements:?}");
        trace!("substituting with args {:?}", params);

        // For each trait requirement, resolve to a trait spec that we can provide

        // separate direct and indirect origins
        // (indirect = surrounding scope)
        // (direct = directly on this item)
        let mut direct_trait_spec_terms = Vec::new();
        let mut indirect_trait_spec_terms = Vec::new();

        for req in &callee_requirements {
            if req.is_self_in_trait_decl {
                continue;
            }

            // substitute the args with the arg instantiation of the callee at this call site
            // in order to get the args of this trait instance
            let args = req.trait_ref.args;
            let mut subst_args = Vec::new();
            for arg in args {
                let bound = ty::EarlyBinder::bind(arg);
                let bound = bound.instantiate(self.env.tcx(), params.as_slice());
                subst_args.push(bound);
            }

            let trait_spec =
                self.lookup_trait(req.trait_ref.def_id).ok_or(Error::NotATrait(req.trait_ref.def_id))?;

            // Check if the target is a method of the same trait with the same args
            // Since this happens in the same ParamEnv, this is the assumption of the trait method
            // for its own trait, so we skip it.
            if self.env.is_method_did(did) {
                if let Some(trait_did) = self.env.tcx().trait_of_item(did) {
                    // Get the params of the trait we're calling
                    let calling_trait_params =
                        types::LocalTX::split_trait_method_args(self.env, trait_did, params).0;
                    if req.trait_ref.def_id == trait_did && subst_args == calling_trait_params.as_slice() {
                        // if they match, this is the Self assumption, so skip
                        continue;
                    }
                } else if let Some(_impl_did) = self.env.trait_impl_of_method(did) {
                    // TODO
                }
            }

            // build the new args
            let subst_args = self.env.tcx().mk_args(subst_args.as_slice());

            // try to infer an instance for this
            trace!(
                "Trying to resolve requirement def_id={:?} with args = {subst_args:?}",
                req.trait_ref.def_id
            );
            if let Some((impl_did, impl_args, kind)) = resolution::resolve_trait(
                self.env.tcx(),
                current_typing_env,
                req.trait_ref.def_id,
                subst_args,
                req.binders,
            ) {
                info!("resolved trait impl as {impl_did:?} with {args:?} {kind:?}");

                // compute the new scope including the bound regions for HRTBs
                let mut scope = state.get_param_scope();
                let binders = scope.translate_bound_regions(req.bound_regions.as_slice());
                let mut state = state.setup_trait_state(self.env.tcx(), scope);

                let req_inst = match kind {
                    resolution::TraitResolutionKind::UserDefined => {
                        // we can resolve it to a concrete implementation of the trait that the
                        // call links up against
                        // therefore, we specialize it to the specification for this implementation
                        //
                        // This is sound, as the compiler will make the same choice when resolving
                        // the trait reference in codegen

                        let (spec_term, assoc_tys) = self.get_impl_spec_term(
                            &mut state,
                            impl_did,
                            impl_args.as_slice(),
                            subst_args.as_slice(),
                        )?;

                        radium::TraitReqInst::new(
                            radium::TraitReqInstSpec::Specialized(spec_term),
                            req.origin,
                            assoc_tys,
                            trait_spec,
                            binders,
                        )
                    },
                    resolution::TraitResolutionKind::Param => {
                        // Lookup in our current parameter environment to satisfy this trait
                        // assumption
                        let trait_did = req.trait_ref.def_id;

                        let assoc_types_did = self.env.get_trait_assoc_types(trait_did);
                        let mut assoc_types = Vec::new();
                        for did in assoc_types_did {
                            let alias = ty::AliasTy::new(self.env.tcx(), did, subst_args);
                            let tykind = ty::TyKind::Alias(ty::AliasTyKind::Projection, alias);
                            let ty = self.env.tcx().mk_ty_from_kind(tykind);
                            assoc_types.push(ty);
                        }
                        info!("Param associated types: {:?}", assoc_types);

                        let trait_use =
                            state.lookup_trait_use(self.env.tcx(), trait_did, subst_args.as_slice())?;
                        let trait_use_ref = trait_use.trait_use;

                        trace!(
                            "need to compute HRTB instantiation for {:?}, by unifying {:?} to {:?}",
                            trait_use.bound_regions, trait_use.trait_ref.args, subst_args
                        );

                        // compute the instantiation of the quantified trait assumption in terms
                        // of the variables introduced by the trait assumption we are proving.
                        let mut unifier = LateBoundUnifier::new(&trait_use.bound_regions);
                        unifier.map_generic_args(trait_use.trait_ref.args, subst_args);
                        let (inst, _) = unifier.get_result();
                        trace!("computed instantiation: {inst:?}");

                        // lookup the instances in the `binders` scope for the new trait assumption
                        let mut mapped_inst = Vec::new();
                        for region in inst {
                            let translated_region = types::TX::translate_region(&mut state, region)?;
                            mapped_inst.push(translated_region);
                        }
                        let mapped_inst = radium::TraitReqScopeInst::new(mapped_inst);
                        trace!("mapped instantiation: {mapped_inst:?}");

                        let trait_impl = radium::QuantifiedTraitImpl::new(trait_use_ref, mapped_inst);
                        radium::TraitReqInst::new(
                            radium::TraitReqInstSpec::Quantified(trait_impl),
                            req.origin,
                            assoc_types,
                            trait_spec,
                            binders,
                        )
                    },
                    resolution::TraitResolutionKind::Closure => {
                        // The callee requires a closure trait bound.
                        // This happens when we pass a closure as an argument?
                        return Err(TranslationError::UnsupportedFeature {
                            description: "TODO: do not support Closure parameters".to_owned(),
                        });
                    },
                };

                if req_inst.origin == radium::TyParamOrigin::Direct {
                    direct_trait_spec_terms.push(req_inst);
                } else {
                    indirect_trait_spec_terms.push(req_inst);
                }
            } else {
                return Err(TranslationError::TraitResolution(
                    "could not resolve trait required for method call".to_owned(),
                ));
            }
        }
        indirect_trait_spec_terms.extend(direct_trait_spec_terms);
        let trait_spec_terms = indirect_trait_spec_terms;

        info!("collected spec terms: {trait_spec_terms:?}");

        trace!("Leave resolve_trait_requirements_in_state with trait_spec_terms={trait_spec_terms:?}");
        Ok(trait_spec_terms)
    }

    /// TODO: handle surrounding params
    pub(crate) fn compute_scope_inst_in_state_without_traits(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        params_inst: ty::GenericArgsRef<'tcx>,
    ) -> Result<radium::GenericScopeInst<'def>, TranslationError<'tcx>> {
        let mut scope_inst = radium::GenericScopeInst::empty();

        // pass the args for this specific impl
        for arg in params_inst {
            if let ty::GenericArgKind::Type(ty) = arg.kind() {
                let ty = self.type_translator().translate_type_in_state(ty, state)?;
                scope_inst.add_direct_ty_param(ty);
            } else if let Some(lft) = arg.as_region() {
                let lft = types::TX::translate_region(state, lft)?;
                scope_inst.add_lft_param(lft);
            }
        }
        Ok(scope_inst)
    }

    fn resolve_radium_trait_requirements_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        did: DefId,
        params_inst: ty::GenericArgsRef<'tcx>,
    ) -> Result<Vec<radium::TraitReqInst<'def, radium::Type<'def>>>, TranslationError<'tcx>> {
        let mut trait_reqs = Vec::new();
        for trait_req in self.resolve_trait_requirements_in_state(state, did, params_inst)? {
            // compute the new scope including the bound regions.
            let mut scope = state.get_param_scope();
            scope.add_trait_req_scope(&trait_req.scope);
            let mut state = state.setup_trait_state(self.env.tcx(), scope);

            let mut assoc_inst = Vec::new();
            for ty in trait_req.assoc_ty_inst {
                let ty = self.type_translator().translate_type_in_state(ty, &mut state)?;
                assoc_inst.push(ty);
            }
            let trait_req = radium::TraitReqInst::new(
                trait_req.spec,
                trait_req.origin,
                assoc_inst,
                trait_req.of_trait,
                trait_req.scope,
            );

            trait_reqs.push(trait_req);
        }
        Ok(trait_reqs)
    }

    /// Compute the instantiation of the generic scope for a particular instantiation of an object.
    pub(crate) fn compute_scope_inst_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        did: DefId,
        params_inst: ty::GenericArgsRef<'tcx>,
    ) -> Result<radium::GenericScopeInst<'def>, TranslationError<'tcx>> {
        let mut scope_inst = self.compute_scope_inst_in_state_without_traits(state, params_inst)?;

        for trait_req in self.resolve_radium_trait_requirements_in_state(state, did, params_inst)? {
            scope_inst.add_trait_requirement(trait_req);
        }

        Ok(scope_inst)
    }

    /// Get information on a trait implementation and create its Radium encoding.
    pub(crate) fn get_trait_impl_info(
        &self,
        trait_impl_did: DefId,
    ) -> Result<radium::TraitRefInst<'def>, TranslationError<'tcx>> {
        let trait_did = self
            .env
            .tcx()
            .trait_id_of_impl(trait_impl_did)
            .ok_or(Error::NotATraitImpl(trait_impl_did))?;

        // check if we registered this impl previously
        let trait_spec_ref = self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;
        let impl_ref = self.lookup_impl(trait_impl_did).ok_or(Error::NotATraitImpl(trait_impl_did))?;

        // get all associated items
        let assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(trait_impl_did);
        let trait_assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(trait_did);

        // figure out the parameters this impl gets and make a scope
        let impl_generics: &'tcx ty::Generics = self.env.tcx().generics_of(trait_impl_did);
        let mut param_scope = scope::Params::from(impl_generics.own_params.as_slice());
        param_scope.add_param_env(trait_impl_did, self.env, self.type_translator(), self)?;

        // parse specification
        let trait_impl_attrs = attrs::filter_for_tool(self.env.get_attributes(trait_impl_did));
        let mut attr_parser = VerboseTraitImplAttrParser::new(&param_scope);
        let impl_spec = attr_parser
            .parse_trait_impl_attrs(&trait_impl_attrs)
            .map_err(|e| Error::TraitImplSpec(trait_impl_did, e))?;

        // figure out the trait ref for this
        let subject = self.env.tcx().impl_subject(trait_impl_did).skip_binder();
        if let ty::ImplSubject::Trait(trait_ref) = subject {
            // set up scope
            let typing_env = ty::TypingEnv::post_analysis(self.env.tcx(), trait_impl_did);
            let state = types::TraitState::new(param_scope.clone(), typing_env, None, None);
            let mut state = types::STInner::TraitReqs(Box::new(state));

            let scope_inst =
                self.compute_scope_inst_in_state(&mut state, trait_ref.def_id, trait_ref.args)?;
            //trace!("Determined trait requirements in impl: {trait_reqs:?}");

            // get instantiation for the associated types
            let mut assoc_types_inst = Vec::new();

            // TODO don't rely on definition order
            // maybe instead iterate over the assoc items of the trait

            for x in trait_assoc_items.in_definition_order() {
                if let ty::AssocKind::Type { .. } = x.kind {
                    let ty_item = assoc_items.find_by_ident_and_kind(
                        self.env.tcx(),
                        x.ident(self.env.tcx()),
                        ty::AssocTag::Type,
                        trait_impl_did,
                    );
                    if let Some(ty_item) = ty_item {
                        let ty_did = ty_item.def_id;
                        let ty = self.env.tcx().type_of(ty_did);
                        let translated_ty = self.type_translator().translate_type_in_scope(
                            &param_scope,
                            typing_env,
                            ty.skip_binder(),
                        )?;
                        assoc_types_inst.push(translated_ty);
                    } else {
                        unreachable!("trait impl does not have required item");
                    }
                }
            }

            Ok(radium::TraitRefInst::new(
                trait_spec_ref,
                impl_ref,
                param_scope.into(),
                scope_inst,
                assoc_types_inst,
                impl_spec.attrs,
            ))
        } else {
            unreachable!("Expected trait impl");
        }
    }
}

/// A using occurrence of a trait in the signature of the function.
#[derive(Debug, Clone)]
pub(crate) struct GenericTraitUse<'tcx, 'def> {
    /// the `DefId` of the trait
    pub did: DefId,
    pub trait_ref: ty::TraitRef<'tcx>,
    /// the Coq-level trait use
    pub trait_use: radium::LiteralTraitSpecUseRef<'def>,
    /// quantifiers for HRTBs
    pub bound_regions: Vec<ty::BoundRegionKind>,
    /// this is a trait use of the trait itself in a trait declaration
    pub is_self_use: bool,
}

impl<'tcx, 'def> GenericTraitUse<'tcx, 'def> {
    /// Get the associated type instantiation of an associated type given by [did] for this instantiation.
    /// This is used in the translation of symbolic `TyKind::Alias`.
    pub(crate) fn get_associated_type_use(
        &self,
        env: &Environment<'tcx>,
        did: DefId,
    ) -> Result<radium::Type<'def>, Error<'tcx>> {
        let type_name = env.get_assoc_item_name(did).ok_or(Error::NotAnAssocType(did))?;

        // this is an associated type of the trait that is currently being declared
        // so make a symbolic reference
        if self.is_self_use {
            // make a literal
            let lit = radium::LiteralTyParam::new_with_origin(
                &type_name,
                &type_name,
                radium::TyParamOrigin::AssocInDecl,
            );
            Ok(radium::Type::LiteralParam(lit))
        } else {
            let trait_use_ref = self.trait_use.borrow();
            let trait_use = trait_use_ref.as_ref().unwrap();

            Ok(trait_use.make_assoc_type_use(&strip_coq_ident(&type_name)))
        }
    }

    pub(crate) fn get_associated_types(&self, env: &Environment<'_>) -> Vec<(String, radium::Type<'def>)> {
        let mut assoc_tys = Vec::new();

        // get associated types
        let assoc_types = env.get_trait_assoc_types(self.did);
        for ty_did in &assoc_types {
            let ty_name = env.get_assoc_item_name(*ty_did).unwrap();
            let trait_use_ref = self.trait_use.borrow();
            let trait_use = trait_use_ref.as_ref().unwrap();
            let lit = trait_use.make_assoc_type_use(&strip_coq_ident(&ty_name));
            assoc_tys.push((ty_name.clone(), lit));
        }
        assoc_tys
    }
}

impl<'tcx, 'def> TR<'tcx, 'def> {
    /// Allocate an empty trait use reference.
    pub(crate) fn make_empty_trait_use(
        &self,
        trait_ref: ty::TraitRef<'tcx>,
        bound_regions: &[ty::BoundRegionKind],
    ) -> GenericTraitUse<'tcx, 'def> {
        let dummy_trait_use = RefCell::new(None);
        let trait_use = self.trait_use_arena.alloc(dummy_trait_use);

        let did = trait_ref.def_id;

        GenericTraitUse {
            did,
            trait_ref,
            trait_use,
            bound_regions: bound_regions.to_vec(),
            is_self_use: false,
        }
    }

    /// Make a trait use for the identity trait use in a trait declaration.
    pub(crate) fn make_trait_self_use(&self, trait_ref: ty::TraitRef<'tcx>) -> GenericTraitUse<'tcx, 'def> {
        let dummy_trait_use = RefCell::new(None);
        let trait_use = self.trait_use_arena.alloc(dummy_trait_use);

        let did = trait_ref.def_id;

        GenericTraitUse {
            did,
            trait_ref,
            trait_use,
            bound_regions: vec![],
            is_self_use: true,
        }
    }

    /// Fills an existing trait use.
    /// Does not compute the dependencies on other traits yet,
    /// these have to be filled later.
    pub(crate) fn fill_trait_use(
        &self,
        trait_use: &GenericTraitUse<'tcx, 'def>,
        scope: &scope::Params<'tcx, 'def>,
        typing_env: ty::TypingEnv<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        spec_ref: radium::LiteralTraitSpecRef<'def>,
        is_used_in_self_trait: bool,
        assoc_ty_constraints: HashMap<String, radium::Type<'def>>,
        origin: radium::TyParamOrigin,
    ) -> Result<(), TranslationError<'tcx>> {
        trace!("Enter fill_trait_use with trait_ref = {trait_ref:?}, spec_ref = {spec_ref:?}");

        let mut new_scope = scope.clone();
        let quantified_regions = new_scope.translate_bound_regions(&trait_use.bound_regions);
        let mut state =
            types::STInner::TraitReqs(Box::new(types::TraitState::new(new_scope, typing_env, None, None)));

        let scope_inst = self.compute_scope_inst_in_state_without_traits(&mut state, trait_ref.args)?;
        // do not compute the assoc dep inst for now, as this may use other trait requirements from the
        // current scope which have not been filled yet

        // TODO: allow to override the assumed specification using attributes
        let spec_override = None;

        // create a name for this instance by including the args
        let mangled_base = types::mangle_name_with_args(&spec_ref.name, trait_ref.args.as_slice());
        let spec_use = radium::LiteralTraitSpecUse::new(
            spec_ref,
            quantified_regions,
            scope_inst,
            spec_override,
            mangled_base,
            is_used_in_self_trait,
            assoc_ty_constraints,
            origin,
        );

        let mut trait_ref = trait_use.trait_use.borrow_mut();
        trait_ref.replace(spec_use);

        trace!(
            "Leave fill_trait_use with trait_ref = {trait_ref:?}, spec_ref = {spec_ref:?} with trait_use = {trait_use:?}"
        );

        Ok(())
    }

    /// Finalize a trait use by computing the dependencies on other traits.
    pub(crate) fn finalize_trait_use(
        &self,
        trait_use: &GenericTraitUse<'tcx, 'def>,
        scope: types::ST<'_, '_, 'def, 'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
    ) -> Result<(), TranslationError<'tcx>> {
        let trait_reqs =
            self.resolve_radium_trait_requirements_in_state(scope, trait_ref.def_id, trait_ref.args)?;
        trace!("finalize_trait_use for {:?}: determined trait requirements: {trait_reqs:?}", trait_use.did);

        let mut trait_use_ref = trait_use.trait_use.borrow_mut();
        let trait_use = trait_use_ref.as_mut().unwrap();

        for trait_req in trait_reqs {
            trait_use.trait_inst.add_trait_requirement(trait_req);
        }

        Ok(())
    }
}

pub(crate) struct LateBoundUnifier<'tcx, 'a> {
    binders_to_unify: &'a [ty::BoundRegionKind],
    instantiation: HashMap<usize, ty::Region<'tcx>>,
    early_instantiation: HashMap<ty::EarlyParamRegion, ty::Region<'tcx>>,
}
impl<'tcx, 'a> LateBoundUnifier<'tcx, 'a> {
    pub(crate) fn new(binders_to_unify: &'a [ty::BoundRegionKind]) -> Self {
        Self {
            binders_to_unify,
            instantiation: HashMap::new(),
            early_instantiation: HashMap::new(),
        }
    }

    pub(crate) fn get_result(
        mut self,
    ) -> (Vec<ty::Region<'tcx>>, HashMap<ty::EarlyParamRegion, ty::Region<'tcx>>) {
        trace!("computed latebound unification map {:?}", self.instantiation);
        let mut res = Vec::new();
        for i in 0..self.binders_to_unify.len() {
            let r = self.instantiation.remove(&i).unwrap();
            res.push(r);
        }
        (res, self.early_instantiation)
    }
}
impl<'tcx> RegionBiFolder<'tcx> for LateBoundUnifier<'tcx, '_> {
    fn map_regions(&mut self, r1: ty::Region<'tcx>, r2: ty::Region<'tcx>) {
        if let ty::RegionKind::ReBound(_, b1) = r1.kind() {
            trace!("trying to unify region {r1:?} with {r2:?}");
            // only unify if this is in the range of binders to unify
            let index1 = b1.var.index();
            if index1 < self.binders_to_unify.len() {
                if let Some(r1_l) = self.instantiation.get(&index1) {
                    assert!(*r1_l == r2);
                } else {
                    self.instantiation.insert(index1, r2);
                }
            }
        } else if let ty::RegionKind::ReEarlyParam(e1) = r1.kind() {
            trace!("trying to unify region {r1:?} with {r2:?}");
            if let Some(r1_l) = self.early_instantiation.get(&e1) {
                assert!(*r1_l == r2);
            } else {
                self.early_instantiation.insert(e1, r2);
            }
        }
    }
}
