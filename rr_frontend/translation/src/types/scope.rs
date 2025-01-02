// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Defines scopes for maintaining generics and trait requirements.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use derive_more::{Constructor, Debug};
use log::{info, trace, warn};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TypeFoldable;

use crate::base::*;
use crate::environment::Environment;
use crate::spec_parsers::parse_utils::ParamLookup;
use crate::traits::registry::GenericTraitUse;
use crate::traits::{self, registry};
use crate::types::translator::*;
use crate::types::tyvars::*;
use crate::utils::strip_coq_ident;

/// Key used for resolving early-bound parameters for function calls.
/// Invariant: All regions contained in these types should be erased, as type parameter instantiation is
/// independent of lifetimes.
/// TODO: handle early-bound lifetimes?
pub type GenericsKey<'tcx> = Vec<ty::Ty<'tcx>>;

/// Generate a key for indexing into structures indexed by `GenericArg`s.
pub fn generate_args_inst_key<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty_params: &[ty::GenericArg<'tcx>],
) -> Result<GenericsKey<'tcx>, TranslationError<'tcx>> {
    // erase parameters to their syntactic types
    let mut key = Vec::new();
    let mut region_eraser = TyRegionEraseFolder::new(tcx);
    for p in ty_params {
        match p.unpack() {
            ty::GenericArgKind::Lifetime(_) => {
                // lifetimes are not relevant here
            },
            ty::GenericArgKind::Type(t) => {
                // TODO: this should erase to the syntactic type.
                // Is erasing regions enough for that?
                let t_erased = t.fold_with(&mut region_eraser);
                key.push(t_erased);
            },
            ty::GenericArgKind::Const(_c) => {
                return Err(TranslationError::UnsupportedFeature {
                    description: "RefinedRust does not support const generics".to_owned(),
                });
            },
        }
    }
    Ok(key)
}

/// Keys used to deduplicate adt uses for `syn_type` assumptions.
/// TODO maybe we should use `SimplifiedType` + `simplify_type` instead of the syntys?
/// Or types with erased regions?
#[derive(Eq, PartialEq, Hash, Debug)]
pub struct AdtUseKey {
    pub base_did: DefId,
    pub generics: Vec<radium::SynType>,
}

impl AdtUseKey {
    pub fn new(defid: DefId, params: &[radium::Type<'_>]) -> Self {
        let generic_syntys: Vec<_> = params.iter().map(radium::SynType::from).collect();
        Self {
            base_did: defid,
            generics: generic_syntys,
        }
    }
}

#[derive(Clone, Debug)]
enum Param {
    Region(radium::Lft),
    Ty(radium::LiteralTyParam),
    // Note: we do not currently support Const params
    Const,
}
impl Param {
    const fn as_type(&self) -> Option<&radium::LiteralTyParam> {
        match self {
            Self::Ty(lit) => Some(lit),
            _ => None,
        }
    }

    const fn as_region(&self) -> Option<&radium::Lft> {
        match self {
            Self::Region(lit) => Some(lit),
            _ => None,
        }
    }
}

/// Data structure that maps generic parameters for ADT/trait translation
#[derive(Constructor, Clone, Debug, Default)]
pub struct Params<'tcx, 'def> {
    /// maps generic indices (De Bruijn) to the corresponding Coq names in the current environment
    scope: Vec<Param>,

    /// conversely, map the declaration name of a lifetime to an index
    lft_names: HashMap<String, usize>,
    /// map types to their index
    ty_names: HashMap<String, usize>,

    /// the trait instances which are in scope
    trait_scope: Traits<'tcx, 'def>,
}

#[allow(clippy::fallible_impl_from)]
impl<'tcx, 'def> From<Params<'tcx, 'def>> for radium::GenericScope<'def, radium::LiteralTraitSpecUse<'def>> {
    fn from(mut x: Params<'tcx, 'def>) -> Self {
        let mut scope = Self::empty();
        for x in x.scope {
            match x {
                Param::Region(lft) => {
                    scope.add_lft_param(lft);
                },
                Param::Ty(ty) => {
                    scope.add_ty_param(ty);
                },
                Param::Const => (),
            }
        }
        for key in x.trait_scope.ordered_assumptions {
            let trait_use = x.trait_scope.used_traits.remove(&key).unwrap().trait_use;
            let trait_use = trait_use.borrow_mut().take().unwrap();
            scope.add_trait_requirement(trait_use);
        }
        scope
    }
}
impl<'tcx, 'def> ParamLookup for Params<'tcx, 'def> {
    fn lookup_ty_param(&self, path: &[&str]) -> Option<&radium::LiteralTyParam> {
        if path.len() == 1 {
            let idx = self.ty_names.get(path[0])?;
            self.lookup_ty_param_idx(*idx)
        } else {
            None
        }
    }

    fn lookup_lft(&self, lft: &str) -> Option<&radium::Lft> {
        let idx = self.lft_names.get(lft)?;
        self.lookup_region_idx(*idx)
    }

    fn lookup_literal(&self, path: &[&str]) -> Option<&str> {
        None
    }
}
impl<'tcx, 'def> Params<'tcx, 'def> {
    pub const fn trait_scope(&self) -> &Traits<'tcx, 'def> {
        &self.trait_scope
    }

    /// Create from generics, optionally annotating the type parameters with their origin.
    pub fn new_from_generics(
        x: ty::GenericArgsRef<'tcx>,
        with_origin: Option<(ty::TyCtxt<'tcx>, DefId)>,
    ) -> Self {
        let mut scope = Vec::new();
        let mut region_count = 0;

        let mut ty_names = HashMap::new();
        let mut lft_names = HashMap::new();

        for p in x {
            if let Some(r) = p.as_region() {
                if let Some(name) = r.get_name() {
                    lft_names.insert(name.as_str().to_owned(), scope.len());
                    scope.push(Param::Region(strip_coq_ident(name.as_str())));
                } else {
                    let name = format!("ulft_{region_count}");
                    region_count += 1;
                    scope.push(Param::Region(name));
                }
            } else if let Some(ty) = p.as_type() {
                if let ty::TyKind::Param(x) = ty.kind() {
                    ty_names.insert(x.name.as_str().to_owned(), scope.len());
                    let name = strip_coq_ident(x.name.as_str());

                    let lit = if let Some((tcx, of_did)) = with_origin {
                        let origin = Self::determine_origin_of_param(of_did, tcx, *x);
                        radium::LiteralTyParam::new_with_origin(&name, &name, origin)
                    } else {
                        radium::LiteralTyParam::new(&name, &name)
                    };
                    scope.push(Param::Ty(lit));
                } else {
                    unreachable!("Should not convert a non-parametric GenericArgsRef to a Params");
                }
            } else if p.as_const().is_some() {
                scope.push(Param::Const);
            }
        }
        Self {
            scope,
            lft_names,
            ty_names,
            trait_scope: Traits::default(),
        }
    }

    /// Lookup a type parameter by its De Bruijn index.
    #[must_use]
    pub fn lookup_ty_param_idx(&self, idx: usize) -> Option<&radium::LiteralTyParam> {
        let ty = self.scope.get(idx)?;
        ty.as_type()
    }

    /// Lookup a region parameter by its De Bruijn index.
    #[must_use]
    pub fn lookup_region_idx(&self, idx: usize) -> Option<&radium::Lft> {
        let lft = self.scope.get(idx)?;
        lft.as_region()
    }

    /// Get all type parameters in scope.
    #[must_use]
    pub fn tyvars(&self) -> Vec<radium::LiteralTyParam> {
        let mut tyvars = Vec::new();
        for x in &self.scope {
            if let Param::Ty(ty) = x {
                tyvars.push(ty.to_owned());
            }
        }
        tyvars
    }

    /// Create a scope of typarams masked by a set of parameters.
    /// The input must be sorted.
    #[must_use]
    pub fn mask_typarams(&self, used_params: &[ty::ParamTy]) -> Vec<radium::LiteralTyParam> {
        let mut res = Vec::new();
        for x in used_params {
            let ty = self.lookup_ty_param_idx(x.index as usize).unwrap();
            res.push(ty.to_owned());
        }
        res
    }

    /// Add a `ParamEnv` of a given `DefId` to the scope to process trait obligations.
    pub fn add_param_env(
        &mut self,
        did: DefId,
        env: &Environment<'tcx>,
        type_translator: &TX<'def, 'tcx>,
        trait_registry: &registry::TR<'tcx, 'def>,
    ) -> Result<(), TranslationError<'tcx>> {
        trace!("Enter add_param_env for did = {did:?}");
        let param_env: ty::ParamEnv<'tcx> = env.tcx().param_env(did);

        // TODO
        // What happens when we encounter the Self requirement when registering a trait?
        // Is it okay to skip that?

        // TODO: add scope for referring to associated types in specs

        let requirements = Self::get_trait_requirements_with_origin(env, did);

        // pre-register all the requirements, in order to resolve dependencies
        for (trait_ref, _, _) in &requirements {
            let key = (trait_ref.def_id, generate_args_inst_key(env.tcx(), trait_ref.args).unwrap());
            let dummy_trait_use = trait_registry.make_empty_trait_use(*trait_ref);
            self.trait_scope.used_traits.insert(key.clone(), dummy_trait_use);
        }

        for (trait_ref, origin, is_used_in_self_trait) in &requirements {
            // lookup the trait in the trait registry
            if let Some(trait_spec) = trait_registry.lookup_trait(trait_ref.def_id) {
                let key = (trait_ref.def_id, generate_args_inst_key(env.tcx(), trait_ref.args).unwrap());
                let entry = &self.trait_scope.used_traits[&key];

                let mut deps = HashSet::new();
                // the scope to translate the arguments in
                let mut state = STInner::TranslateAdt(AdtState::new(&mut deps, &*self, &param_env));

                trait_registry.fill_trait_use(
                    entry,
                    &mut state,
                    trait_ref.to_owned(),
                    trait_spec,
                    *is_used_in_self_trait,
                    // trait associated types are fully generic for now, we make a second pass
                    // below
                    HashMap::new(),
                    *origin,
                )?;

                self.trait_scope.ordered_assumptions.push(key);
            } else {
                return Err(traits::Error::UnregisteredTrait(trait_ref.def_id).into());
            }
        }

        // make a second pass to specify constraints on associated types
        // We do this in a second pass so that we can refer to the other associated types
        for (trait_ref, origin, _) in requirements {
            let assoc_constraints = traits::get_trait_assoc_constraints(env, param_env, trait_ref);

            let translated_constraints: HashMap<_, _> = assoc_constraints
                .into_iter()
                .map(|(name, ty)| {
                    let translated_ty = type_translator.translate_type_in_scope(self, ty).unwrap();
                    (name, translated_ty)
                })
                .collect();

            // lookup the trait use
            let key = (trait_ref.def_id, generate_args_inst_key(env.tcx(), trait_ref.args).unwrap());
            let entry = &self.trait_scope.used_traits[&key];

            {
                let mut trait_use_ref = entry.trait_use.borrow_mut();
                let trait_use = trait_use_ref.as_mut().unwrap();
                // and add the constraints
                for (name, constr) in translated_constraints {
                    trait_use.specialize_assoc_type(name, constr);
                }
            }

            // finalize the entry by adding dependencies on other trait parameters
            let mut deps = HashSet::new();
            let mut state = STInner::TranslateAdt(AdtState::new(&mut deps, &*self, &param_env));
            trait_registry.finalize_trait_use(entry, &mut state, trait_ref)?;
        }

        trace!("Leave add_param_env for did = {did:?}");
        Ok(())
    }
}
impl<'tcx, 'def> Params<'tcx, 'def> {
    /// Determine the declaration origin of a type parameter of a function.
    fn determine_origin_of_param(
        did: DefId,
        tcx: ty::TyCtxt<'tcx>,
        param: ty::ParamTy,
    ) -> radium::TyParamOrigin {
        // Check if there is a surrounding trait decl that introduces this parameter
        if let Some(trait_did) = tcx.trait_of_item(did) {
            let generics: &'tcx ty::Generics = tcx.generics_of(trait_did);

            for this_param in &generics.params {
                if this_param.name == param.name {
                    return radium::TyParamOrigin::SurroundingTrait;
                }
            }
        }
        // Check if there is a surrounding trait impl that introduces this parameter
        if let Some(impl_did) = tcx.impl_of_method(did) {
            let generics: &'tcx ty::Generics = tcx.generics_of(impl_did);

            for this_param in &generics.params {
                if this_param.name == param.name {
                    return radium::TyParamOrigin::SurroundingImpl;
                }
            }
        }

        radium::TyParamOrigin::Direct
    }

    /// Determine the number of args of a surrounding trait or impl.
    pub fn determine_number_of_surrounding_params(did: DefId, tcx: ty::TyCtxt<'tcx>) -> usize {
        // Check if there is a surrounding trait decl that introduces this parameter
        if let Some(trait_did) = tcx.trait_of_item(did) {
            let generics: &'tcx ty::Generics = tcx.generics_of(trait_did);

            return generics.params.len();
        }
        // Check if there is a surrounding trait impl that introduces this parameter
        if let Some(impl_did) = tcx.impl_of_method(did) {
            let generics: &'tcx ty::Generics = tcx.generics_of(impl_did);

            return generics.params.len();
        }

        0
    }

    /// Determine the origin of a trait obligation.
    /// `surrounding_reqs` are the requirements of a surrounding impl or decl.
    fn determine_origin_of_trait_requirement(
        did: DefId,
        tcx: ty::TyCtxt<'tcx>,
        surrounding_reqs: &Option<Vec<ty::TraitRef<'tcx>>>,
        req: ty::TraitRef<'tcx>,
    ) -> radium::TyParamOrigin {
        if let Some(surrounding_reqs) = surrounding_reqs {
            let in_trait_decl = tcx.trait_of_item(did);

            if surrounding_reqs.contains(&req) {
                if in_trait_decl.is_some() {
                    return radium::TyParamOrigin::SurroundingTrait;
                }
                return radium::TyParamOrigin::SurroundingImpl;
            }
        }
        radium::TyParamOrigin::Direct
    }

    /// Get the trait requirements of a [did], also determining their origin relative to the [did].
    /// The requirements are sorted in a way that is stable across compilations.
    pub fn get_trait_requirements_with_origin(
        env: &Environment<'tcx>,
        did: DefId,
    ) -> Vec<(ty::TraitRef<'tcx>, radium::TyParamOrigin, bool)> {
        trace!("Enter get_trait_requirements_with_origin for did={did:?}");
        let param_env: ty::ParamEnv<'tcx> = env.tcx().param_env(did);

        // Are we declaring the scope of a trait?
        let is_trait = env.tcx().is_trait(did);

        // Determine whether we are declaring the scope of a trait method or trait impl method
        let in_trait_decl = env.tcx().trait_of_item(did);
        let in_trait_impl = env.trait_impl_of_method(did);

        // if this has a surrounding scope, get the requirements declared on that, so that we can
        // determine the origin of this requirement below
        let surrounding_reqs = if let Some(trait_did) = in_trait_decl {
            let trait_param_env = env.tcx().param_env(trait_did);
            Some(traits::requirements::get_nontrivial(env.tcx(), trait_param_env, None))
        } else if let Some(impl_did) = in_trait_impl {
            let impl_param_env = env.tcx().param_env(impl_did);
            Some(traits::requirements::get_nontrivial(env.tcx(), impl_param_env, None))
        } else {
            None
        };

        let clauses = param_env.caller_bounds();
        info!("Caller bounds: {:?}", clauses);

        let in_trait_decl = if is_trait { Some(did) } else { in_trait_decl };
        let requirements = traits::requirements::get_nontrivial(env.tcx(), param_env, in_trait_decl);
        let mut annotated_requirements = Vec::new();

        for trait_ref in requirements {
            // check if we are in the process of translating a trait decl
            let is_self = trait_ref.args[0].as_type().unwrap().is_param(0);
            let mut is_used_in_self_trait = false;
            if let Some(trait_decl_did) = in_trait_decl {
                // is this a reference to the trait we are currently declaring
                let is_use_of_self_trait = trait_decl_did == trait_ref.def_id;

                if is_use_of_self_trait && is_self {
                    // This is the self assumption of the trait we are currently implementing
                    // For a function spec in a trait decl, we remember this, as we do not require
                    // a quantified spec for the Self trait.
                    is_used_in_self_trait = true;
                }
            }

            // we are processing the Self requirement in the scope of a trait declaration, so skip
            // this.
            if is_trait && is_self {
                continue;
            }

            let origin =
                Self::determine_origin_of_trait_requirement(did, env.tcx(), &surrounding_reqs, trait_ref);
            info!("Determined origin of requirement {trait_ref:?} as {origin:?}");

            annotated_requirements.push((trait_ref, origin, is_used_in_self_trait));
        }

        trace!(
            "Leave get_trait_requirements_with_origin for did={did:?} with annotated_requirements={annotated_requirements:?}"
        );
        annotated_requirements
    }
}

impl<'tcx, 'def> From<ty::GenericArgsRef<'tcx>> for Params<'tcx, 'def> {
    fn from(x: ty::GenericArgsRef<'tcx>) -> Self {
        Self::new_from_generics(x, None)
    }
}

impl<'a, 'tcx, 'def> From<&'a [ty::GenericParamDef]> for Params<'tcx, 'def> {
    fn from(x: &[ty::GenericParamDef]) -> Self {
        let mut scope = Vec::new();

        let mut ty_names = HashMap::new();
        let mut lft_names = HashMap::new();

        for p in x {
            let name = strip_coq_ident(p.name.as_str());
            match p.kind {
                ty::GenericParamDefKind::Const { .. } => {
                    scope.push(Param::Const);
                },
                ty::GenericParamDefKind::Type { .. } => {
                    let lit = radium::LiteralTyParam::new(&name, &name);
                    ty_names.insert(p.name.as_str().to_owned(), scope.len());
                    scope.push(Param::Ty(lit));
                },
                ty::GenericParamDefKind::Lifetime => {
                    let name = format!("ulft_{name}");
                    lft_names.insert(p.name.as_str().to_owned(), scope.len());
                    scope.push(Param::Region(name));
                },
            }
        }
        Self {
            scope,
            lft_names,
            ty_names,
            trait_scope: Traits::default(),
        }
    }
}

/// A scope for translated trait requirements from `where` clauses.
#[derive(Clone, Debug, Default)]
pub struct Traits<'tcx, 'def> {
    used_traits: HashMap<(DefId, GenericsKey<'tcx>), GenericTraitUse<'def>>,
    ordered_assumptions: Vec<(DefId, GenericsKey<'tcx>)>,
}

impl<'tcx, 'def> Traits<'tcx, 'def> {
    /// Lookup the trait use for a specific trait with given parameters.
    /// (here, args includes the self parameter as the first element)
    pub fn lookup_trait_use(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        trait_did: DefId,
        args: &[ty::GenericArg<'tcx>],
    ) -> Result<&GenericTraitUse<'def>, traits::Error<'tcx>> {
        if !tcx.is_trait(trait_did) {
            return Err(traits::Error::NotATrait(trait_did));
        }

        let key = (trait_did, generate_args_inst_key(tcx, args).unwrap());
        trace!("looking up trait use {key:?} in {:?}", self.used_traits);
        if let Some(trait_ref) = self.used_traits.get(&key) {
            Ok(trait_ref)
        } else {
            Err(traits::Error::UnknownLocalInstance(trait_did, tcx.mk_args(args)))
        }
    }

    /// Get trait uses in the current scope.
    pub const fn get_trait_uses(&self) -> &HashMap<(DefId, GenericsKey<'tcx>), GenericTraitUse<'def>> {
        &self.used_traits
    }

    /// Within a trait declaration, get the Self trait use.
    pub fn get_self_trait_use(&self) -> Option<&GenericTraitUse<'def>> {
        for trait_use in self.used_traits.values() {
            // check if this is the Self trait use
            {
                let spec_use_ref = trait_use.trait_use.borrow();
                let spec_use = spec_use_ref.as_ref().unwrap();
                if !spec_use.is_used_in_self_trait {
                    continue;
                }
            }
            return Some(trait_use);
        }
        None
    }
}
