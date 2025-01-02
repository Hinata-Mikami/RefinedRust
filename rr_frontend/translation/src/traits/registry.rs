// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use derive_more::Display;
use log::{info, trace};
use radium::{self, coq, specs};
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::middle::ty;
use traits::{resolution, Error, TraitResult};
use typed_arena::Arena;

use crate::base::TranslationError;
use crate::environment::Environment;
use crate::function_body::FunctionTranslator;
use crate::spec_parsers::propagate_method_attr_from_impl;
use crate::spec_parsers::trait_attr_parser::{TraitAttrParser, VerboseTraitAttrParser};
use crate::spec_parsers::trait_impl_attr_parser::{TraitImplAttrParser, VerboseTraitImplAttrParser};
use crate::types::scope;
use crate::{attrs, base, traits, types};

pub struct TR<'tcx, 'def> {
    /// environment
    env: &'def Environment<'tcx>,
    type_translator: &'def types::TX<'def, 'tcx>,

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
    /// Create an empty trait registry.
    pub fn new(
        env: &'def Environment<'tcx>,
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_arena: &'def Arena<specs::LiteralTraitSpec>,
        impl_arena: &'def Arena<specs::LiteralTraitImpl>,
        trait_use_arena: &'def Arena<radium::LiteralTraitSpecUseCell<'def>>,
        fn_spec_arena: &'def Arena<specs::FunctionSpec<'def, specs::InnerFunctionSpec<'def>>>,
    ) -> Self {
        Self {
            env,
            type_translator: ty_translator,
            trait_arena,
            impl_arena,
            trait_use_arena,
            fn_spec_arena,
            trait_decls: RefCell::new(HashMap::new()),
            trait_literals: RefCell::new(HashMap::new()),
            impl_literals: RefCell::new(HashMap::new()),
        }
    }

    /// Get registered trait declarations in the local crate.
    pub fn get_trait_decls(&self) -> HashMap<LocalDefId, specs::TraitSpecDecl<'def>> {
        let decls = self.trait_decls.borrow();
        decls.clone()
    }

    /// Get a set of other (different) traits that this trait depends on.
    pub fn get_deps_of_trait(&self, did: DefId) -> HashSet<DefId> {
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
    pub fn get_trait_deps(&self, traits: &[LocalDefId]) -> HashMap<DefId, HashSet<DefId>> {
        let mut dep_map = HashMap::new();

        for trait_decl in traits {
            let deps = self.get_deps_of_trait(trait_decl.to_def_id());
            dep_map.insert(trait_decl.to_def_id(), deps);
        }

        dep_map
    }

    /// Get a map of dependencies between traits.
    pub fn get_registered_trait_deps(&self) -> HashMap<DefId, HashSet<DefId>> {
        let mut dep_map = HashMap::new();

        let decls = self.trait_decls.borrow();
        for trait_decl in decls.keys() {
            let deps = self.get_deps_of_trait(trait_decl.to_def_id());
            dep_map.insert(trait_decl.to_def_id(), deps);
        }

        dep_map
    }

    /// Get the names of associated types of this trait.
    pub fn get_associated_type_names(&self, did: DefId) -> Vec<String> {
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
        declared_attrs: HashSet<String>,
    ) -> specs::LiteralTraitSpec {
        let phys_record = format!("{name}_phys");
        let spec_record = format!("{name}_spec");
        let spec_params_record = format!("{name}_spec_params");
        let spec_attrs_record = format!("{name}_spec_attrs");
        let base_spec = format!("{name}_base_spec");
        let base_spec_params = format!("{name}_base_spec_params");
        let spec_subsumption = format!("{name}_spec_incl");

        specs::LiteralTraitSpec {
            name,
            assoc_tys: self.get_associated_type_names(did),
            spec_record,
            spec_params_record,
            spec_attrs_record,
            base_spec,
            base_spec_params,
            spec_subsumption,
            declared_attrs,
        }
    }

    /// Register a new annotated trait in the local crate with the registry.
    pub fn register_trait(&'def self, did: LocalDefId) -> Result<(), TranslationError<'tcx>> {
        trace!("enter TR::register_trait for did={did:?}");

        {
            let scope = self.trait_decls.borrow();
            if scope.get(&did).is_some() {
                return Ok(());
            }
        }

        // TODO: can we handle the case that this depends on a generic having the same trait?
        // In principle, yes, but currently the implementation does not allow it.
        // => Think more about this.

        // get generics
        let trait_generics: &'tcx ty::Generics = self.env.tcx().generics_of(did.to_def_id());
        let mut param_scope = scope::Params::from(trait_generics.params.as_slice());
        param_scope.add_param_env(did.to_def_id(), self.env, self.type_translator, self)?;

        let trait_name = base::strip_coq_ident(&self.env.get_absolute_item_name(did.to_def_id()));

        // parse trait spec
        let trait_attrs = attrs::filter_for_tool(self.env.get_attributes(did.into()));
        // As different attributes of the spec may depend on each other, we need to pass a closure
        // determining under which Coq name we are going to introduce them
        // Note: This needs to match up with `radium::LiteralTraitSpec.make_spec_attr_name`!
        let mut attr_parser = VerboseTraitAttrParser::new(&param_scope, |id| format!("{trait_name}_{id}"));
        let trait_spec =
            attr_parser.parse_trait_attrs(&trait_attrs).map_err(|e| Error::TraitSpec(did.into(), e))?;

        // get the declared attributes that are allowed on impls
        let valid_attrs: HashSet<String> = trait_spec.attrs.attrs.keys().cloned().collect();

        // make the literal we are going to use
        let lit_trait_spec = self.make_literal_trait_spec(did.to_def_id(), trait_name.clone(), valid_attrs);
        // already register it for use
        // In particular, this is also needed to be able to register the methods of this trait
        // below, as they need to be able to access the associated types of this trait already.
        // (in fact, their environment contains their self instance)
        let lit_trait_spec_ref = self.register_shim(did.to_def_id(), lit_trait_spec)?;

        // get items
        let mut methods = HashMap::new();
        let mut assoc_types = Vec::new();
        let items: &ty::AssocItems = self.env.tcx().associated_items(did);
        for c in items.in_definition_order() {
            if ty::AssocKind::Fn == c.kind {
                // get attributes
                let attrs = self.env.get_attributes_of_function(c.def_id, &propagate_method_attr_from_impl);

                // get function name
                let method_name =
                    self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotATraitMethod(c.def_id))?;
                let method_name = base::strip_coq_ident(&method_name);

                let name = format!("{trait_name}_{method_name}");
                let spec_name = format!("{name}_base_spec");

                // get spec
                let spec = FunctionTranslator::spec_for_trait_method(
                    self.env,
                    c.def_id,
                    &name,
                    &spec_name,
                    attrs.as_slice(),
                    self.type_translator,
                    self,
                )?;
                let spec_ref = self.fn_spec_arena.alloc(spec);

                methods.insert(method_name, &*spec_ref);
            } else if ty::AssocKind::Type == c.kind {
                // get name
                let type_name =
                    self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotATraitMethod(c.def_id))?;
                let type_name = base::strip_coq_ident(&type_name);
                let lit = radium::LiteralTyParam::new(&type_name, &type_name);
                assoc_types.push(lit);
            }
        }

        let base_instance_spec = radium::TraitInstanceSpec::new(methods);
        let decl = radium::TraitSpecDecl::new(
            lit_trait_spec_ref,
            coq::binder::BinderList::new(trait_spec.context_items),
            param_scope.into(),
            assoc_types,
            base_instance_spec,
            trait_spec.attrs,
        );

        let mut scope = self.trait_decls.borrow_mut();
        scope.insert(did, decl);

        trace!("leave TR::register_trait");
        Ok(())
    }

    /// Register a shim with the trait registry.
    ///
    /// Errors:
    /// - NotATrait(did) if did is not a trait
    /// - TraitAlreadyExists(did) if this trait has already been registered
    pub fn register_shim<'a>(
        &'a self,
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
    pub fn register_impl_shim<'a>(
        &'a self,
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
    pub fn lookup_trait(&self, trait_did: DefId) -> Option<radium::LiteralTraitSpecRef<'def>> {
        let trait_literals = self.trait_literals.borrow();
        trait_literals.get(&trait_did).copied()
    }

    /// Lookup the spec for an impl.
    /// If None, use the default spec.
    pub fn lookup_impl(&self, impl_did: DefId) -> Option<radium::LiteralTraitImplRef<'def>> {
        let impl_literals = self.impl_literals.borrow();
        impl_literals.get(&impl_did).copied()
    }

    /// Get the term for referring to the attribute record of a particular impl within a function of
    /// that impl.
    pub fn get_impl_attrs_term(&self, impl_did: DefId) -> Result<String, TranslationError<'tcx>> {
        let impl_ref = self.lookup_impl(impl_did).ok_or(Error::UnregisteredImpl(impl_did))?;
        let attr_record = &impl_ref.spec_attrs_record;
        let info = self.get_trait_impl_info(impl_did)?;
        // TODO: maybe it would be better to do the formatting in radium

        let mut attr_term = String::with_capacity(100);
        write!(attr_term, "{attr_record}").unwrap();

        // add the type parameters of the impl
        for ty in info.generics.get_all_ty_params_with_assocs().params {
            write!(attr_term, " {}", ty.refinement_type).unwrap();
        }

        Ok(attr_term)
    }

    /// Get the term for the specification of a trait impl (applied to the given arguments of the trait),
    /// as well as the list of associated types.
    pub fn get_impl_spec_term(
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

        let trait_instance = self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;

        let mut assoc_args = Vec::new();
        // get associated types of this impl
        // Since we know the concrete impl, we can directly resolve all of the associated types
        // TODO is this definition order guaranteed to be the same as on the trait?
        let assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(impl_did);
        for it in assoc_items.in_definition_order() {
            if it.kind == ty::AssocKind::Type {
                let item_did = it.def_id;
                let item_ty: ty::EarlyBinder<ty::Ty<'tcx>> = self.env.tcx().type_of(item_did);
                let subst_ty = item_ty.instantiate(self.env.tcx(), impl_args);

                assoc_args.push(subst_ty);
            }
        }

        // check if there's a more specific impl spec
        let term = if let Some(impl_spec) = self.lookup_impl(impl_did) {
            // pass the args for this specific impl
            let mut all_impl_args = Vec::new();
            for arg in impl_args {
                if let ty::GenericArgKind::Type(ty) = arg.unpack() {
                    let ty = self.type_translator.translate_type_in_state(ty, state)?;
                    all_impl_args.push(ty);
                }
            }

            radium::SpecializedTraitImpl::new(impl_spec, all_impl_args)
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
    pub fn resolve_trait_requirements_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        did: DefId,
        params: ty::GenericArgsRef<'tcx>,
    ) -> Result<Vec<radium::TraitReqInst<'def, ty::Ty<'tcx>>>, TranslationError<'tcx>> {
        trace!("Enter resolve_trait_requirements_in_state with did={did:?} and params={params:?}");

        let current_param_env: ty::ParamEnv<'tcx> = state.get_param_env(self.env.tcx());

        let callee_param_env = self.env.tcx().param_env(did);
        trace!("callee param env {callee_param_env:?}");

        // Get the trait requirements of the callee
        let callee_requirements = scope::Params::get_trait_requirements_with_origin(self.env, did);
        trace!("non-trivial callee requirements: {callee_requirements:?}");
        trace!("subsituting with args {:?}", params);

        // For each trait requirement, resolve to a trait spec that we can provide

        // separate direct and indirect origins
        let mut direct_trait_spec_terms = Vec::new();
        let mut indirect_trait_spec_terms = Vec::new();

        for (trait_ref, origin, _) in &callee_requirements {
            // substitute the args with the arg instantiation of the callee at this call site
            // in order to get the args of this trait instance
            let args = trait_ref.args;
            let mut subst_args = Vec::new();
            for arg in args {
                let bound = ty::EarlyBinder::bind(arg);
                let bound = bound.instantiate(self.env.tcx(), params.as_slice());
                subst_args.push(bound);
            }

            // Check if the target is a method of the same trait with the same args
            // Since this happens in the same ParamEnv, this is the assumption of the trait method
            // for its own trait, so we skip it.
            if self.env.is_method_did(did) {
                if let Some(trait_did) = self.env.tcx().trait_of_item(did) {
                    // Get the params of the trait we're calling
                    let calling_trait_params =
                        types::LocalTX::split_trait_method_args(self.env, trait_did, params).0;
                    if trait_ref.def_id == trait_did && subst_args == calling_trait_params.as_slice() {
                        // if they match, this is the Self assumption, so skip
                        continue;
                    }
                } else if let Some(impl_did) = self.env.trait_impl_of_method(did) {
                    // TODO
                }
            }

            // try to infer an instance for this
            let subst_args = self.env.tcx().mk_args(subst_args.as_slice());
            trace!("Trying to resolve requirement def_id={:?} with args = {subst_args:?}", trait_ref.def_id);
            if let Some((impl_did, impl_args, kind)) =
                resolution::resolve_trait(self.env.tcx(), current_param_env, trait_ref.def_id, subst_args)
            {
                info!("resolved trait impl as {impl_did:?} with {args:?} {kind:?}");

                let req_inst = match kind {
                    resolution::TraitResolutionKind::UserDefined => {
                        // we can resolve it to a concrete implementation of the trait that the
                        // call links up against
                        // therefore, we specialize it to the specification for this implementation
                        //
                        // This is sound, as the compiler will make the same choice when resolving
                        // the trait reference in codegen

                        let (spec_term, assoc_tys) = self.get_impl_spec_term(
                            state,
                            impl_did,
                            impl_args.as_slice(),
                            subst_args.as_slice(),
                        )?;
                        radium::TraitReqInst::new(
                            radium::TraitReqInstSpec::Specialized(spec_term),
                            *origin,
                            assoc_tys,
                        )
                    },
                    resolution::TraitResolutionKind::Param => {
                        // Lookup in our current parameter environment to satisfy this trait
                        // assumption
                        let trait_did = trait_ref.def_id;

                        let assoc_types_did = self.env.get_trait_assoc_types(trait_did);
                        let mut assoc_types = Vec::new();
                        for did in assoc_types_did {
                            let alias = self.env.tcx().mk_alias_ty(did, subst_args);
                            let tykind = ty::TyKind::Alias(ty::AliasKind::Projection, alias);
                            let ty = self.env.tcx().mk_ty_from_kind(tykind);
                            assoc_types.push(ty);
                        }
                        info!("Param associated types: {:?}", assoc_types);

                        let trait_use_ref = state
                            .lookup_trait_use(self.env.tcx(), trait_did, subst_args.as_slice())?
                            .trait_use;

                        // TODO: do we have to requantify here?
                        // I guess for HRTBs we might need to requantify lifetimes

                        let trait_impl = radium::QuantifiedTraitImpl::new(trait_use_ref);
                        radium::TraitReqInst::new(
                            radium::TraitReqInstSpec::Quantified(trait_impl),
                            *origin,
                            assoc_types,
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

    /// Get information on a trait implementation and create its Radium encoding.
    pub fn get_trait_impl_info(
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

        let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(trait_impl_did);

        // get all associated items
        let assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(trait_impl_did);
        let trait_assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(trait_did);

        // figure out the parameters this impl gets and make a scope
        let impl_generics: &'tcx ty::Generics = self.env.tcx().generics_of(trait_impl_did);
        let mut param_scope = scope::Params::from(impl_generics.params.as_slice());
        param_scope.add_param_env(trait_impl_did, self.env, self.type_translator, self)?;

        // parse specification
        let trait_impl_attrs = attrs::filter_for_tool(self.env.get_attributes(trait_impl_did));
        let mut attr_parser = VerboseTraitImplAttrParser::new(&param_scope);
        let impl_spec = attr_parser
            .parse_trait_impl_attrs(&trait_impl_attrs)
            .map_err(|e| Error::TraitImplSpec(trait_impl_did, e))?;

        // figure out the trait ref for this
        let subject = self.env.tcx().impl_subject(trait_impl_did).skip_binder();
        if let ty::ImplSubject::Trait(trait_ref) = subject {
            // get instantiation for parameters
            let mut params_inst = Vec::new();
            let mut lft_inst = Vec::new();
            for arg in trait_ref.args {
                if let Some(ty) = arg.as_type() {
                    let ty = self.type_translator.translate_type_in_scope(&param_scope, ty)?;
                    params_inst.push(ty);
                } else if let Some(lft) = arg.as_region() {
                    let lft = types::TX::translate_region_in_scope(&param_scope, lft)?;
                    lft_inst.push(lft);
                }
            }

            // get instantiation for the associated types
            let mut assoc_types_inst = Vec::new();

            // TODO don't rely on definition order
            // maybe instead iterate over the assoc items of the trait

            for x in trait_assoc_items.in_definition_order() {
                if x.kind == ty::AssocKind::Type {
                    let ty_item = assoc_items.find_by_name_and_kind(
                        self.env.tcx(),
                        x.ident(self.env.tcx()),
                        ty::AssocKind::Type,
                        trait_impl_did,
                    );
                    if let Some(ty_item) = ty_item {
                        let ty_did = ty_item.def_id;
                        let ty = self.env.tcx().type_of(ty_did);
                        let translated_ty =
                            self.type_translator.translate_type_in_scope(&param_scope, ty.skip_binder())?;
                        assoc_types_inst.push(translated_ty);
                    } else {
                        unreachable!("trait impl does not have required item");
                    }
                }
            }

            Ok(radium::TraitRefInst::new(
                trait_spec_ref,
                param_scope.into(),
                lft_inst,
                params_inst,
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
pub struct GenericTraitUse<'def> {
    /// the DefId of the trait
    pub did: DefId,
    /// the self type this is implemented for
    pub self_ty: ty::ParamTy,
    /// the Coq-level trait use
    pub trait_use: radium::LiteralTraitSpecUseRef<'def>,
}

impl<'def> GenericTraitUse<'def> {
    /// Get the names of associated types of this trait.
    pub fn get_associated_type_names(&self, env: &Environment<'_>) -> Vec<String> {
        let mut assoc_tys = Vec::new();

        // get associated types
        let assoc_types = env.get_trait_assoc_types(self.did);
        for ty_did in &assoc_types {
            let ty_name = env.get_assoc_item_name(*ty_did).unwrap();
            assoc_tys.push(ty_name);
        }
        assoc_tys
    }

    /// Get the associated type instantiations for this trait use.
    pub fn get_associated_type_uses(&self, env: &Environment<'_>) -> Vec<radium::Type<'def>> {
        let mut assoc_tys: Vec<radium::Type> = Vec::new();

        // get associated types
        let assoc_types = env.get_trait_assoc_types(self.did);
        for ty_did in &assoc_types {
            let ty_name = env.get_assoc_item_name(*ty_did).unwrap();
            let trait_use_ref = self.trait_use.borrow();
            let trait_use = trait_use_ref.as_ref().unwrap();
            let lit = trait_use.make_assoc_type_use(&base::strip_coq_ident(&ty_name));
            assoc_tys.push(lit);
        }
        assoc_tys
    }
}

impl<'tcx, 'def> TR<'tcx, 'def> {
    /// Allocate an empty trait use reference.
    pub fn make_empty_trait_use(&self, trait_ref: ty::TraitRef<'tcx>) -> GenericTraitUse<'def> {
        let dummy_trait_use = RefCell::new(None);
        let trait_use = self.trait_use_arena.alloc(dummy_trait_use);

        let did = trait_ref.def_id;

        // the self param should be a Param that is bound in the current scope
        let param = if let ty::TyKind::Param(param) = trait_ref.args[0].expect_ty().kind() {
            *param
        } else {
            unreachable!("self should be a Param");
        };

        GenericTraitUse {
            did,
            self_ty: param,
            trait_use,
        }
    }

    /// Fills an existing trait use.
    /// Does not compute the dependencies on other traits yet,
    /// these have to be filled later.
    #[allow(clippy::unnecessary_wraps)]
    pub fn fill_trait_use(
        &self,
        trait_use: &GenericTraitUse<'def>,
        scope: types::ST<'_, '_, 'def, 'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        spec_ref: radium::LiteralTraitSpecRef<'def>,
        is_used_in_self_trait: bool,
        assoc_ty_constraints: HashMap<String, radium::Type<'def>>,
        origin: radium::TyParamOrigin,
    ) -> Result<(), TranslationError<'tcx>> {
        let did = trait_ref.def_id;
        trace!("Enter fill_trait_use with trait_ref = {trait_ref:?}, spec_ref = {spec_ref:?}");

        // translate the arguments in the current scope
        let mut translated_args = Vec::new();
        for arg in trait_ref.args {
            if let ty::GenericArgKind::Type(ty) = arg.unpack() {
                let translated_ty = self.type_translator.translate_type_in_state(ty, scope).unwrap();
                translated_args.push(translated_ty);
            }
        }

        // Compute the instantiation of associated types of trait requirements
        let mut assoc_dep_inst = Vec::new();
        let trait_reqs = self.resolve_trait_requirements_in_state(scope, did, trait_ref.args)?;
        trace!("Determined trait requirements: {trait_reqs:?}");

        for req in trait_reqs {
            let mut tys = Vec::new();
            for ty in req.assoc_ty_inst {
                let translated_ty = self.type_translator.translate_type_in_state(ty, scope)?;
                tys.push(translated_ty);
            }
            let translated_req = radium::TraitReqInst::new(req.spec, req.origin, tys);
            assoc_dep_inst.push(translated_req);
        }

        // TODO: allow to override the assumed specification using attributes
        let spec_override = None;

        // create a name for this instance by including the args
        let mangled_base = types::mangle_name_with_args(&spec_ref.name, trait_ref.args.as_slice());
        let spec_use = radium::LiteralTraitSpecUse::new(
            spec_ref,
            translated_args,
            assoc_dep_inst,
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
    pub fn finalize_trait_use(
        &self,
        trait_use: &GenericTraitUse<'def>,
        scope: types::ST<'_, '_, 'def, 'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
    ) -> Result<(), TranslationError<'tcx>> {
        let trait_reqs = self.resolve_trait_requirements_in_state(scope, trait_ref.def_id, trait_ref.args)?;
        trace!("Determined trait requirements: {trait_reqs:?}");

        let mut assoc_dep_inst = Vec::new();
        for req in trait_reqs {
            let mut tys = Vec::new();
            for ty in req.assoc_ty_inst {
                let translated_ty = self.type_translator.translate_type_in_state(ty, scope)?;
                tys.push(translated_ty);
            }
            let translated_req = radium::TraitReqInst::new(req.spec, req.origin, tys);
            assoc_dep_inst.push(translated_req);
        }

        let mut trait_use_ref = trait_use.trait_use.borrow_mut();
        let trait_use = trait_use_ref.as_mut().unwrap();
        trait_use.trait_dep_assoc_inst = assoc_dep_inst;

        Ok(())
    }
}
