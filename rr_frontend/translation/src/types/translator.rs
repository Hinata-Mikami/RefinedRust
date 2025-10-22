// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The main translator for translating types within certain environments.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap};

use derive_more::{Constructor, Debug};
use log::{info, trace};
use radium::{coq, push_str_list};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{abi, ast, span};
use typed_arena::Arena;

use crate::base::*;
use crate::environment::Environment;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::regions::{EarlyLateRegionMap, format_atomic_region_direct};
use crate::spec_parsers::enum_spec_parser::{
    EnumSpecParser as _, VerboseEnumSpecParser, parse_enum_refine_as,
};
use crate::spec_parsers::parse_utils::{ParamLookup, RustPath};
use crate::spec_parsers::struct_spec_parser::{self, InvariantSpecParser as _, StructFieldSpecParser as _};
use crate::spec_parsers::verbose_function_spec_parser::TraitReqHandler;
use crate::traits::registry;
use crate::types::scope;
use crate::{attrs, search};

/// A scope tracking the type translation state when translating the body of a function.
/// This also includes the state needed for tracking trait constraints, as type translation for
/// associated types in the current scope depends on that.
#[derive(Debug)]
#[expect(clippy::partial_pub_fields)]
pub(crate) struct FunctionState<'tcx, 'def> {
    /// defid of the current function
    pub did: DefId,

    /// generic mapping: map De Bruijn indices to type parameters
    pub generic_scope: scope::Params<'tcx, 'def>,
    /// mapping for regions
    pub lifetime_scope: EarlyLateRegionMap,

    /// collection of tuple types that we use
    pub tuple_uses: HashMap<Vec<radium::lang::SynType>, radium::LiteralTypeUse<'def>>,

    /// Shim uses for the current function
    pub shim_uses: HashMap<scope::AdtUseKey, radium::LiteralTypeUse<'def>>,

    /// optional Polonius Info for the current function
    #[debug(ignore)]
    polonius_info: Option<&'def PoloniusInfo<'def, 'tcx>>,
}

impl<'def> ParamLookup<'def> for FunctionState<'_, 'def> {
    fn lookup_ty_param(&self, path: &RustPath) -> Option<radium::Type<'def>> {
        self.generic_scope.lookup_ty_param(path)
    }

    fn lookup_lft(&self, lft: &str) -> Option<&radium::Lft> {
        let vid = self.lifetime_scope.lft_names.get(lft)?;
        self.lifetime_scope.region_names.get(vid)
    }

    fn lookup_literal(&self, path: &RustPath) -> Option<String> {
        self.generic_scope.lookup_literal(path)
    }
}

impl<'def> TraitReqHandler<'def> for FunctionState<'_, 'def> {
    fn determine_trait_requirement_origin(
        &self,
        typaram: &str,
        attr: &str,
    ) -> Option<radium::LiteralTraitSpecUseRef<'def>> {
        trace!("attaching trait attr requirement: {typaram:?}::{attr:?}");
        self.generic_scope.determine_trait_requirement_origin(typaram, attr)
    }

    fn attach_trait_attr_requirement(
        &self,
        name_prefix: &str,
        trait_use: radium::LiteralTraitSpecUseRef<'def>,
        reqs: &BTreeMap<String, radium::TraitSpecAttrInst>,
    ) -> Option<radium::FunctionSpecTraitReqSpecialization<'def>> {
        self.generic_scope.attach_trait_attr_requirement(name_prefix, trait_use, reqs)
    }
}

impl<'tcx, 'def> FunctionState<'tcx, 'def> {
    /// Create a new scope for a function translation with the given generic parameters and
    /// incorporating the trait environment.
    pub(crate) fn new_with_traits(
        did: DefId,
        env: &Environment<'tcx>,
        ty_params: ty::GenericArgsRef<'tcx>,
        lifetimes: EarlyLateRegionMap,
        type_translator: &TX<'def, 'tcx>,
        trait_registry: &registry::TR<'tcx, 'def>,
        info: Option<&'def PoloniusInfo<'def, 'tcx>>,
    ) -> Result<Self, TranslationError<'tcx>> {
        info!("Entering procedure with ty_params {:?} and lifetimes {:?}", ty_params, lifetimes);
        let mut generics = scope::Params::new_from_generics(env.tcx(), ty_params, Some(did));

        generics.add_param_env(did, env, type_translator, trait_registry)?;

        Ok(Self {
            did,
            tuple_uses: HashMap::new(),
            generic_scope: generics,
            shim_uses: HashMap::new(),
            polonius_info: info,
            lifetime_scope: lifetimes,
        })
    }

    /// Make a params scope including all late-bound lifetimes.
    pub(crate) fn make_params_scope(&self) -> scope::Params<'tcx, 'def> {
        let mut scope = self.generic_scope.clone();
        scope.with_region_map(&self.lifetime_scope);
        scope
    }
}

/// Type translation state when translating an ADT.
#[derive(Debug)]
pub(crate) struct AdtState<'a, 'tcx, 'def> {
    /// track dependencies on other ADTs
    deps: &'a mut BTreeSet<OrderedDefId>,
    /// scope to track parameters
    scope: &'a scope::Params<'tcx, 'def>,
    /// the current typingenv
    typing_env: &'a ty::TypingEnv<'tcx>,
}

impl<'a, 'tcx, 'def> AdtState<'a, 'tcx, 'def> {
    pub(crate) const fn new(
        deps: &'a mut BTreeSet<OrderedDefId>,
        scope: &'a scope::Params<'tcx, 'def>,
        typing_env: &'a ty::TypingEnv<'tcx>,
    ) -> Self {
        Self {
            deps,
            scope,
            typing_env,
        }
    }
}

/// Type translation state when translating trait requirements.
#[derive(Constructor, Debug)]
pub(crate) struct TraitState<'a, 'tcx, 'def> {
    /// scope to track parameters
    scope: scope::Params<'tcx, 'def>,
    /// the current typing env
    typing_env: ty::TypingEnv<'tcx>,
    /// optional Polonius Info for the current function
    #[debug(ignore)]
    polonius_info: Option<&'def PoloniusInfo<'def, 'tcx>>,
    lifetime_scope: Option<&'a EarlyLateRegionMap>,
}

/// Translation state for translating the interface of a called function.
/// Lifetimes are completely erased since we only need these types for syntactic types.
#[derive(Constructor, Clone, Copy, Debug)]
pub(crate) struct CalleeState<'a, 'tcx, 'def> {
    /// the env of the caller
    typing_env: &'a ty::TypingEnv<'tcx>,
    /// the generic scope of the caller
    param_scope: &'a scope::Params<'tcx, 'def>,
}

/// The type translator `TX` has three modes:
/// - translation of a type within the generic scope of a function
/// - translation of a type as part of an ADT definition, where we always translate parameters as variables,
///   but need to track dependencies on other ADTs.
/// - translation of a type when translating the signature of a callee. Regions are always erased.
#[derive(Debug)]
pub(crate) enum STInner<'b, 'def, 'tcx> {
    /// This type is used in a function
    InFunction(&'b mut FunctionState<'tcx, 'def>),
    /// We are generating the definition of an ADT and this type is used in there
    TranslateAdt(AdtState<'b, 'tcx, 'def>),
    /// We are translating in an empty dummy scope.
    /// All regions are erased.
    CalleeTranslation(CalleeState<'b, 'tcx, 'def>),
    /// we are translating trait requirements
    TraitReqs(Box<TraitState<'b, 'tcx, 'def>>),
}

pub(crate) type ST<'a, 'b, 'def, 'tcx> = &'a mut STInner<'b, 'def, 'tcx>;
pub(crate) type InFunctionState<'a, 'def, 'tcx> = &'a mut FunctionState<'tcx, 'def>;
pub(crate) type TranslateAdtState<'a, 'tcx, 'def> = AdtState<'a, 'tcx, 'def>;

impl<'def, 'tcx> STInner<'_, 'def, 'tcx> {
    /// Create a copy of the param scope.
    pub(crate) fn get_param_scope(&self) -> scope::Params<'tcx, 'def> {
        match &self {
            Self::InFunction(state) => state.make_params_scope(),
            Self::TranslateAdt(state) => state.scope.to_owned(),
            Self::CalleeTranslation(state) => state.param_scope.to_owned(),
            Self::TraitReqs(state) => state.scope.clone(),
        }
    }

    const fn param_scope(&self) -> &scope::Params<'tcx, 'def> {
        match &self {
            Self::InFunction(state) => &state.generic_scope,
            Self::TranslateAdt(state) => state.scope,
            Self::CalleeTranslation(state) => state.param_scope,
            Self::TraitReqs(state) => &state.scope,
        }
    }

    pub(crate) const fn polonius_info(&self) -> Option<&'def PoloniusInfo<'def, 'tcx>> {
        match &self {
            Self::InFunction(state) => state.polonius_info,
            Self::TraitReqs(state) => state.polonius_info,
            Self::TranslateAdt(_) | Self::CalleeTranslation(_) => None,
        }
    }

    pub(crate) const fn polonius_region_map(&self) -> Option<&EarlyLateRegionMap> {
        match &self {
            Self::InFunction(state) => Some(&state.lifetime_scope),
            Self::TraitReqs(state) => state.lifetime_scope,
            Self::TranslateAdt(_) | Self::CalleeTranslation(_) => None,
        }
    }

    pub(crate) fn setup_trait_state<'b>(
        &'b self,
        tcx: ty::TyCtxt<'tcx>,
        params: scope::Params<'tcx, 'def>,
    ) -> STInner<'b, 'def, 'tcx> {
        if let STInner::CalleeTranslation(s) = self {
            // make sure to keep the callee state, which translates regions to dummys
            STInner::CalleeTranslation(*s)
        } else {
            let typing_env = self.get_typing_env(tcx);
            let state = TraitState::new(params, typing_env, self.polonius_info(), self.polonius_region_map());
            STInner::TraitReqs(Box::new(state))
        }
    }

    /// Get the `ParamEnv` for the current state.
    pub(crate) fn get_typing_env(&self, tcx: ty::TyCtxt<'tcx>) -> ty::TypingEnv<'tcx> {
        match &self {
            Self::InFunction(state) => ty::TypingEnv::post_analysis(tcx, state.did),
            Self::TranslateAdt(state) => *state.typing_env,
            Self::CalleeTranslation(state) => *state.typing_env,
            Self::TraitReqs(state) => state.typing_env,
        }
    }

    /// Normalize a type in the given translation state.
    fn normalize_type_erasing_regions(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> Result<ty::Ty<'tcx>, TranslationError<'tcx>> {
        let typing_env = self.get_typing_env(tcx);
        tcx.try_normalize_erasing_regions(typing_env, ty)
            .map_err(|e| TranslationError::TraitResolution(format!("normalization error: {:?}", e)))
    }

    /// Lookup a trait parameter in the current state.
    pub(crate) fn lookup_trait_use(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        trait_did: DefId,
        args: &[ty::GenericArg<'tcx>],
    ) -> Result<&registry::GenericTraitUse<'tcx, 'def>, TranslationError<'tcx>> {
        //trace!("Enter lookup_trait_use for trait_did = {trait_did:?}, args = {args:?}, self = {self:?}");
        let res = self.param_scope().trait_scope().lookup_trait_use(tcx, trait_did, args)?;
        //trace!("Leave lookup_trait_use for trait_did = {trait_did:?}, args = {args:?} with res = {res:?}");
        Ok(res)
    }

    /// Lookup a type parameter in the current state
    fn lookup_ty_param(&self, param_ty: ty::ParamTy) -> Result<radium::Type<'def>, TranslationError<'tcx>> {
        let ty = self.param_scope().lookup_ty_param_idx(param_ty.index as usize).ok_or_else(|| {
            TranslationError::UnknownVar(format!("unknown generic parameter {:?}", param_ty))
        })?;
        Ok(radium::Type::LiteralParam(ty.clone()))
    }

    /// Lookup an early-bound region.
    fn lookup_early_region(
        &self,
        region: ty::EarlyParamRegion,
    ) -> Result<radium::Lft, TranslationError<'tcx>> {
        trace!("lookup_early_region in state={self:?}");
        match self {
            STInner::InFunction(scope) => {
                info!("Looking up lifetime {region:?} in scope {:?}", scope.lifetime_scope);
                let lft = scope
                    .lifetime_scope
                    .lookup_early_region(region.index as usize)
                    .ok_or(TranslationError::UnknownEarlyRegion(region))?;
                Ok(lft.to_owned())
            },
            STInner::TranslateAdt(_scope) => {
                // TODO: ?
                if region.is_named() {
                    let name = region.name.as_str();
                    Ok(coq::Ident::new(format!("ulft_{}", name)))
                } else {
                    Err(TranslationError::UnknownEarlyRegion(region))
                }
            },
            STInner::TraitReqs(scope) => {
                let lft = scope
                    .scope
                    .lookup_region_idx(region.index as usize)
                    .ok_or(TranslationError::UnknownEarlyRegion(region))?;
                Ok(lft.to_owned())

                /*
                // TODO: ?
                if region.has_name() {
                    let name = region.name.as_str();
                    Ok(coq::Ident::new(format!("ulft_{}", name)))
                } else {
                    Err(TranslationError::UnknownEarlyRegion(region))
                }
                    */
            },
            STInner::CalleeTranslation(_) => Ok(coq::Ident::new("DUMMY")),
        }
    }

    /// Lookup a late-bound region.
    fn lookup_late_region(&self, binder: usize, var: usize) -> Result<radium::Lft, TranslationError<'tcx>> {
        match self {
            STInner::InFunction(scope) => {
                info!("Looking up late lifetime ({binder:?}, {var:?}) in scope {:?}", scope.lifetime_scope);
                let lft = scope
                    .lifetime_scope
                    .lookup_late_region(binder, var)
                    .ok_or(TranslationError::UnknownLateRegion(binder, var))?;
                Ok(lft.to_owned())
            },
            STInner::TranslateAdt(scope) => {
                let lft = scope
                    .scope
                    .lookup_late_region_idx(binder, var)
                    .ok_or(TranslationError::UnknownLateRegionOutsideFunction(binder, var))?;
                Ok(lft.to_owned())
            },
            STInner::TraitReqs(scope) => {
                let lft = scope
                    .scope
                    .lookup_late_region_idx(binder, var)
                    .ok_or(TranslationError::UnknownLateRegionOutsideFunction(binder, var))?;
                Ok(lft.to_owned())
            },
            STInner::CalleeTranslation(_) => Ok(coq::Ident::new("DUMMY")),
        }
    }

    /// Try to translate a Polonius region variable to a Caesium lifetime.
    pub(crate) fn lookup_polonius_var(
        &self,
        v: facts::Region,
    ) -> Result<radium::Lft, TranslationError<'tcx>> {
        match self {
            STInner::InFunction(scope) => {
                if let Some(info) = scope.polonius_info {
                    // If there is Polonius Info available, use that for translation
                    let x = info.mk_atomic_region(v);
                    let r = format_atomic_region_direct(x, Some(&scope.lifetime_scope));
                    info!("Translating region: ReVar {:?} as {:?}", v, r);
                    Ok(r)
                } else {
                    // otherwise, just use the universal scope
                    let r = scope
                        .lifetime_scope
                        .lookup_region(v)
                        .ok_or(TranslationError::UnknownPoloniusRegion(v))?;
                    info!("Translating region: ReVar {:?} as {:?}", v, r);
                    Ok(r.to_owned())
                }
            },
            STInner::TraitReqs(scope) => {
                if let Some(info) = scope.polonius_info {
                    // If there is Polonius Info available, use that for translation
                    let x = info.mk_atomic_region(v);
                    let r = format_atomic_region_direct(x, scope.lifetime_scope);
                    info!("Translating region: ReVar {:?} as {:?}", v, r);
                    Ok(r)
                } else {
                    // otherwise, just use the universal scope
                    let r = scope
                        .lifetime_scope
                        .as_ref()
                        .ok_or(TranslationError::UnknownPoloniusRegion(v))?
                        .lookup_region(v)
                        .ok_or(TranslationError::UnknownPoloniusRegion(v))?;
                    info!("Translating region: ReVar {:?} as {:?}", v, r);
                    Ok(r.to_owned())
                    //info!("Translating region: ReVar {:?} as None (trait)", v);
                    //return Err(TranslationError::UnknownPoloniusRegion(v));
                }
            },
            STInner::TranslateAdt(_scope) => {
                info!("Translating region: ReVar {:?} as None (outside of function)", v);
                Err(TranslationError::PoloniusRegionOutsideFunction(v))
            },
            STInner::CalleeTranslation(_) => Ok(coq::Ident::new("DUMMY")),
        }
    }
}

pub(crate) struct TX<'def, 'tcx> {
    env: &'def Environment<'tcx>,

    trait_registry: Cell<Option<&'def registry::TR<'tcx, 'def>>>,

    /// arena for keeping ownership of structs
    /// during building, it will be None, afterwards it will always be Some
    struct_arena: &'def Arena<RefCell<Option<radium::specs::structs::Abstract<'def>>>>,
    /// arena for keeping ownership of enums
    enum_arena: &'def Arena<RefCell<Option<radium::specs::enums::Abstract<'def>>>>,
    /// arena for keeping ownership of shims
    shim_arena: &'def Arena<radium::LiteralType>,

    /// maps ADT variants to struct specifications.
    /// the boolean is true iff this is a variant of an enum.
    /// the literal is present after the variant has been fully translated
    variant_registry: RefCell<
        HashMap<
            DefId,
            (
                String,
                radium::specs::structs::AbstractRef<'def>,
                &'tcx ty::VariantDef,
                bool,
                Option<radium::LiteralTypeRef<'def>>,
            ),
        >,
    >,
    /// maps ADTs that are enums to the enum specifications
    /// the literal is present after the enum has been fully translated
    enum_registry: RefCell<
        HashMap<
            DefId,
            (
                String,
                radium::specs::enums::AbstractRef<'def>,
                ty::AdtDef<'tcx>,
                Option<radium::LiteralTypeRef<'def>>,
            ),
        >,
    >,
    /// a registry for abstract struct defs for tuples, indexed by the number of tuple fields
    tuple_registry:
        RefCell<HashMap<usize, (radium::specs::structs::AbstractRef<'def>, radium::LiteralTypeRef<'def>)>>,

    /// dependencies of one ADT definition on another ADT definition
    adt_deps: RefCell<BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>>>,

    /// shims for ADTs
    adt_shims: RefCell<HashMap<DefId, radium::LiteralTypeRef<'def>>>,
}

impl<'def, 'tcx: 'def> TX<'def, 'tcx> {
    pub(crate) fn new(
        env: &'def Environment<'tcx>,
        struct_arena: &'def Arena<RefCell<Option<radium::specs::structs::Abstract<'def>>>>,
        enum_arena: &'def Arena<RefCell<Option<radium::specs::enums::Abstract<'def>>>>,
        shim_arena: &'def Arena<radium::LiteralType>,
    ) -> Self {
        TX {
            env,
            trait_registry: Cell::new(None),
            adt_deps: RefCell::new(BTreeMap::new()),
            adt_shims: RefCell::new(HashMap::new()),
            struct_arena,
            enum_arena,
            shim_arena,
            variant_registry: RefCell::new(HashMap::new()),
            enum_registry: RefCell::new(HashMap::new()),
            tuple_registry: RefCell::new(HashMap::new()),
        }
    }

    pub(crate) const fn trait_registry(&self) -> &'def registry::TR<'tcx, 'def> {
        self.trait_registry.get().unwrap()
    }

    pub(crate) fn provide_trait_registry(&self, tr: &'def registry::TR<'tcx, 'def>) {
        self.trait_registry.set(Some(tr));
    }

    /// Intern a literal.
    pub(crate) fn intern_literal(&self, lit: radium::LiteralType) -> radium::LiteralTypeRef<'def> {
        self.shim_arena.alloc(lit)
    }

    pub(crate) const fn env(&self) -> &'def Environment<'tcx> {
        self.env
    }

    /// Register a shim for an ADT.
    pub(crate) fn register_adt_shim(&self, did: DefId, lit: &radium::LiteralType) -> Result<(), String> {
        let lit_ref = self.intern_literal(lit.clone());
        let mut shims = self.adt_shims.borrow_mut();
        if let Some(old) = shims.insert(did, lit_ref) {
            Err(format!("Shim for defid {:?} was {:?} before and has been overridden by {:?}", did, old, lit))
        } else {
            Ok(())
        }
    }

    /// Lookup a shim for an ADT.
    fn lookup_adt_shim(&self, did: DefId) -> Option<radium::LiteralTypeRef<'def>> {
        self.adt_shims.borrow().get(&did).copied()
    }

    /// Get all the struct definitions that clients have used (excluding the variants of enums).
    pub(crate) fn get_struct_defs(&self) -> HashMap<DefId, radium::specs::structs::AbstractRef<'def>> {
        let mut defs = HashMap::new();
        for (did, (_, su, _, is_of_enum, _)) in self.variant_registry.borrow().iter() {
            // skip structs belonging to enums
            if !is_of_enum {
                defs.insert(*did, *su);
            }
        }
        defs
    }

    /// Get all the variant definitions that clients have used (including the variants of enums).
    pub(crate) fn get_variant_defs(&self) -> HashMap<DefId, radium::specs::structs::AbstractRef<'def>> {
        let mut defs = HashMap::new();
        for (did, (_, su, _, _, _)) in self.variant_registry.borrow().iter() {
            defs.insert(*did, *su);
        }
        defs
    }

    /// Get all the enum definitions that clients have used.
    pub(crate) fn get_enum_defs(&self) -> HashMap<DefId, radium::specs::enums::AbstractRef<'def>> {
        let mut defs = HashMap::new();
        for (did, (_, su, _, _)) in self.enum_registry.borrow().iter() {
            defs.insert(*did, *su);
        }
        defs
    }

    /// Get the dependency map between ADTs.
    pub(crate) fn get_adt_deps(&self) -> BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>> {
        let deps = self.adt_deps.borrow();
        deps.clone()
    }

    /// Returns the Radium enum representation according to the Rust representation options.
    fn get_enum_representation(
        repr: &abi::ReprOptions,
    ) -> Result<radium::specs::enums::Repr, TranslationError<'tcx>> {
        if repr.c() {
            return Ok(radium::specs::enums::Repr::C);
        }

        if repr.transparent() {
            return Ok(radium::specs::enums::Repr::Transparent);
        }

        if repr.simd() {
            return Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support the SIMD flag".to_owned(),
            });
        }

        if repr.packed() {
            return Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support the repr(packed) flag".to_owned(),
            });
        }

        if repr.linear() {
            return Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support the linear flag".to_owned(),
            });
        }

        Ok(radium::specs::enums::Repr::Rust)
    }

    /// Returns the Radium structure representation according to the Rust representation options.
    fn get_struct_representation(
        repr: &abi::ReprOptions,
    ) -> Result<radium::specs::structs::Repr, TranslationError<'tcx>> {
        if repr.c() {
            return Ok(radium::specs::structs::Repr::C);
        }

        if repr.transparent() {
            return Ok(radium::specs::structs::Repr::Transparent);
        }

        if repr.simd() {
            return Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support the SIMD flag".to_owned(),
            });
        }

        if repr.packed() {
            return Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support the repr(packed) flag".to_owned(),
            });
        }

        if repr.linear() {
            return Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support the linear flag".to_owned(),
            });
        }

        Ok(radium::specs::structs::Repr::Rust)
    }

    /// Try to translate a region to a Caesium lifetime.
    pub(crate) fn translate_region(
        translation_state: ST<'_, '_, 'def, 'tcx>,
        region: ty::Region<'tcx>,
    ) -> Result<radium::Lft, TranslationError<'tcx>> {
        match region.kind() {
            ty::RegionKind::ReEarlyParam(early) => {
                info!("Translating region: EarlyParam {:?}", early);
                translation_state.lookup_early_region(early)
            },

            ty::RegionKind::ReBound(idx, r) => {
                info!("Translating region: Bound {:?} {:?}", idx, r);
                translation_state.lookup_late_region(usize::from(idx), r.var.index())
            },

            ty::RegionKind::RePlaceholder(placeholder) => {
                // TODO: not sure if any placeholders should remain at this stage.
                info!("Translating region: Placeholder {:?}", placeholder);
                Err(TranslationError::PlaceholderRegion)
            },

            ty::RegionKind::ReStatic => Ok(coq::Ident::new("static")),
            ty::RegionKind::ReErased => Ok(coq::Ident::new("erased")),

            ty::RegionKind::ReVar(v) => translation_state.lookup_polonius_var(v.into()),

            _ => {
                info!("Translating region: {:?}", region);
                Err(TranslationError::UnknownRegion(region))
            },
        }
    }

    /// Lookup an ADT variant and return a reference to its struct def.
    fn lookup_adt_variant(
        &self,
        did: DefId,
    ) -> Result<
        (radium::specs::structs::AbstractRef<'def>, Option<radium::LiteralTypeRef<'def>>),
        TranslationError<'tcx>,
    > {
        if let Some((_n, st, _, _, lit)) = self.variant_registry.borrow().get(&did) {
            Ok((*st, *lit))
        } else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    fn is_adt_variant_already_registered(&self, did: DefId) -> bool {
        if self.lookup_adt_shim(did).is_some() {
            return true;
        }
        let reg = self.variant_registry.borrow();
        reg.get(&did).is_some()
    }

    /// Lookup the literal for an ADT variant.
    fn lookup_adt_variant_literal(
        &self,
        did: DefId,
    ) -> Result<radium::LiteralTypeRef<'def>, TranslationError<'tcx>> {
        if let Some(lit) = self.lookup_adt_shim(did) {
            return Ok(lit);
        }

        if let Some((_n, _, _, _, lit)) = self.variant_registry.borrow().get(&did) {
            return Ok(lit.unwrap());
        }

        Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
    }

    /// Lookup an enum ADT and return a reference to its enum def.
    fn lookup_enum(
        &self,
        did: DefId,
    ) -> Result<
        (radium::specs::enums::AbstractRef<'def>, Option<radium::LiteralTypeRef<'def>>),
        TranslationError<'tcx>,
    > {
        if let Some((_n, st, _, lit)) = self.enum_registry.borrow().get(&did) {
            Ok((*st, *lit))
        } else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    fn is_enum_already_registered(&self, did: DefId) -> bool {
        if self.lookup_adt_shim(did).is_some() {
            return true;
        }
        let reg = self.enum_registry.borrow();
        reg.get(&did).is_some()
    }

    /// Lookup the literal for an enum.
    fn lookup_enum_literal(
        &self,
        did: DefId,
    ) -> Result<radium::LiteralTypeRef<'def>, TranslationError<'tcx>> {
        if let Some(lit) = self.lookup_adt_shim(did) {
            Ok(lit)
        } else if let Some((_n, _, _, lit)) = self.enum_registry.borrow().get(&did) {
            Ok(lit.unwrap())
        } else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    /// Generate a use of a struct, instantiated with type parameters.
    /// This should only be called on tuples and struct ADTs.
    /// Only for internal references as part of type translation.
    fn generate_structlike_use_internal(
        &self,
        ty: ty::Ty<'tcx>,
        variant: Option<abi::VariantIdx>,
        adt_deps: ST<'_, '_, 'def, 'tcx>,
    ) -> Result<radium::Type<'def>, TranslationError<'tcx>> {
        match ty.kind() {
            ty::TyKind::Adt(adt, args) => {
                // Check if we have a shim
                if self.lookup_adt_shim(adt.did()).is_some() {
                    return self.generate_adt_shim_use(*adt, args, adt_deps);
                }

                if adt.is_box() {
                    // TODO: for now, Box gets a special treatment and is not accurately
                    // translated. Reconsider this later on
                    return Err(TranslationError::UnknownError("Box is not a proper structlike".to_owned()));
                }

                if adt.is_struct() {
                    info!("generating struct use for {:?}", adt.did());
                    // register the ADT, if necessary
                    self.register_adt(*adt)?;

                    return self
                        .generate_struct_use_noshim(adt.did(), args, adt_deps)
                        .map(radium::Type::Struct);
                }

                if adt.is_enum() {
                    let Some(variant) = variant else {
                        return Err(TranslationError::UnknownError(
                            "a non-downcast enum is not a structlike".to_owned(),
                        ));
                    };

                    self.register_adt(*adt)?;

                    return self
                        .generate_enum_variant_use_noshim(adt.did(), variant, args, adt_deps)
                        .map(radium::Type::Struct);
                }

                Err(TranslationError::UnsupportedType {
                    description: "non-{enum, struct, tuple} ADTs are not supported".to_owned(),
                })
            },

            ty::TyKind::Tuple(args) => self.generate_tuple_use(*args, adt_deps).map(radium::Type::Literal),

            _ => Err(TranslationError::UnknownError("not a structlike".to_owned())),
        }
    }

    /// Generate the use of an enum.
    /// Only for internal references as part of type translation.
    fn generate_enum_use_noshim(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        state: ST<'_, '_, 'def, 'tcx>,
    ) -> Result<radium::specs::enums::AbstractUse<'def>, TranslationError<'tcx>> {
        info!("generating enum use for {:?}", adt_def.did());
        self.register_adt(adt_def)?;

        let (enum_ref, lit_ref) = self.lookup_enum(adt_def.did())?;
        let params = self.trait_registry().compute_scope_inst_in_state(state, adt_def.did(), args, None)?;
        let key = scope::AdtUseKey::new_from_inst(adt_def.did(), &params);

        // track this enum use for the current function
        if let STInner::InFunction(state) = state {
            let lit_uses = &mut state.shim_uses;

            lit_uses
                .entry(key)
                .or_insert_with(|| radium::LiteralTypeUse::new(lit_ref.unwrap(), params.clone()));
        }

        Ok(radium::specs::enums::AbstractUse::new(enum_ref, params))
    }

    /// Check if a variant given by a [`DefId`] is [`std::marker::PhantomData`].
    fn is_phantom_data(&self, did: DefId) -> Option<bool> {
        let ty: ty::Ty<'tcx> = self.env.tcx().type_of(did).instantiate_identity();
        match ty.kind() {
            ty::TyKind::Adt(def, _) => Some(def.is_phantom_data()),
            _ => None,
        }
    }

    /// Check if a struct is definitely zero-sized.
    fn is_struct_definitely_zero_sized(&self, did: DefId) -> Option<bool> {
        self.is_phantom_data(did)
    }

    /// Generate the use of a struct.
    /// Only for internal references as part of type translation.
    fn generate_struct_use_noshim(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        state: ST<'_, '_, 'def, 'tcx>,
    ) -> Result<radium::specs::structs::AbstractUse<'def>, TranslationError<'tcx>> {
        info!("generating struct use for {:?}", variant_id);

        if self.is_struct_definitely_zero_sized(variant_id) == Some(true) {
            info!("replacing zero-sized struct with unit");
            return Ok(radium::specs::structs::AbstractUse::new_unit());
        }

        let (struct_ref, lit_ref) = self.lookup_adt_variant(variant_id)?;
        let params = self.trait_registry().compute_scope_inst_in_state(state, variant_id, args, None)?;
        info!("struct use has params: {params:?}");

        if let STInner::InFunction(scope) = state {
            let key = scope::AdtUseKey::new_from_inst(variant_id, &params);
            let lit_uses = &mut scope.shim_uses;

            lit_uses
                .entry(key)
                .or_insert_with(|| radium::LiteralTypeUse::new(lit_ref.unwrap(), params.clone()));
        }

        let struct_use = radium::specs::structs::AbstractUse::new(
            struct_ref,
            params,
            radium::specs::structs::TypeIsRaw::No,
        );
        Ok(struct_use)
    }

    /// Generate the use of an enum variant.
    /// Only for internal references as part of type translation.
    fn generate_enum_variant_use_noshim(
        &self,
        adt_id: DefId,
        variant_idx: abi::VariantIdx,
        args: ty::GenericArgsRef<'tcx>,
        state: ST<'_, '_, 'def, 'tcx>,
    ) -> Result<radium::specs::structs::AbstractUse<'def>, TranslationError<'tcx>> {
        info!("generating variant use for variant {:?} of {:?}", variant_idx, adt_id);

        let variant_idx = variant_idx.as_usize();
        let (enum_ref, _lit_ref) = self.lookup_enum(adt_id)?;
        let en = enum_ref.borrow();
        let en = en.as_ref().unwrap();

        let (_, struct_ref, _) = en.get_variant(variant_idx).unwrap();
        let struct_ref: radium::specs::structs::AbstractRef<'def> = *struct_ref;

        // apply the generic parameters according to the mask
        let params = self.trait_registry().compute_scope_inst_in_state(state, adt_id, args, None)?;

        let struct_use = radium::specs::structs::AbstractUse::new(
            struct_ref,
            params,
            radium::specs::structs::TypeIsRaw::No,
        );

        // TODO maybe track the whole enum?
        // track this enum use for the current function
        //let mut struct_uses = self.struct_uses.borrow_mut();
        //struct_uses.push(struct_use.clone());

        Ok(struct_use)
    }

    /// Generate a tuple use for a tuple with the given types.
    pub(crate) fn generate_tuple_use<F>(
        &self,
        tys: F,
        state: ST<'_, '_, 'def, 'tcx>,
    ) -> Result<radium::LiteralTypeUse<'def>, TranslationError<'tcx>>
    where
        F: IntoIterator<Item = ty::Ty<'tcx>>,
    {
        let args: Vec<ty::GenericArg<'tcx>> = tys.into_iter().map(ty::GenericArg::from).collect();
        let args = self.env().tcx().mk_args(&args);
        let params = self.trait_registry().compute_scope_inst_in_state_without_traits(state, args)?;

        let num_components = params.get_direct_ty_params().len();
        let (_, lit) = self.get_tuple_struct_ref(num_components);

        let key: Vec<_> = params.get_direct_ty_params().iter().map(radium::lang::SynType::from).collect();
        let struct_use = radium::LiteralTypeUse::new(lit, params);
        if let STInner::InFunction(ref mut scope) = *state {
            let tuple_uses = &mut scope.tuple_uses;

            tuple_uses.entry(key).or_insert_with(|| struct_use.clone());
        }

        Ok(struct_use)
    }

    /// Get the struct ref for a tuple with `num_components` components.
    fn get_tuple_struct_ref(
        &self,
        num_components: usize,
    ) -> (radium::specs::structs::AbstractRef<'def>, radium::LiteralTypeRef<'def>) {
        self.register_tuple(num_components);
        let registry = self.tuple_registry.borrow();
        let (struct_ref, lit) = registry.get(&num_components).unwrap();
        (struct_ref, lit)
    }

    /// Register a tuple type with `num_components` components.
    fn register_tuple(&self, num_components: usize) {
        if self.tuple_registry.borrow().get(&num_components).is_some() {
            return;
        }

        info!("Generating a tuple type with {} components", num_components);
        let struct_def = radium::specs::structs::Abstract::new_from_tuple(num_components);
        let literal = self.intern_literal(struct_def.make_literal_type());

        let struct_def = self.struct_arena.alloc(RefCell::new(Some(struct_def)));
        self.tuple_registry.borrow_mut().insert(num_components, (struct_def, literal));
    }

    /// Register an ADT that is being used by the program.
    fn register_adt(&self, def: ty::AdtDef<'tcx>) -> Result<(), TranslationError<'tcx>> {
        trace!("Registering ADT {:?}", def.did());

        if def.is_union() {
            Err(TranslationError::Unimplemented {
                description: "union ADTs are not yet supported".to_owned(),
            })
        } else if self.is_struct_definitely_zero_sized(def.did()) == Some(true) {
            Ok(())
        } else if def.is_enum() {
            self.register_enum(def)
        } else if def.is_struct() {
            // register all variants
            for variant in def.variants() {
                self.register_struct(variant, def)?;
            }
            Ok(())
        } else {
            Err(TranslationError::Unimplemented {
                description: format!("unhandled ADT kind: {:?}", def),
            })
        }
    }

    /// Register a struct ADT type that is used by the program.
    fn register_struct(
        &self,
        ty: &'tcx ty::VariantDef,
        adt: ty::AdtDef<'_>,
    ) -> Result<(), TranslationError<'tcx>> {
        if self.is_adt_variant_already_registered(ty.def_id) {
            // already there, that's fine.
            return Ok(());
        }
        info!("registering struct {:?}", ty);

        let generics: &'tcx ty::Generics = self.env.tcx().generics_of(adt.did());
        let mut deps = BTreeSet::new();
        let mut scope = scope::Params::from(generics.own_params.as_slice());
        scope.add_param_env(adt.did(), self.env(), self, self.trait_registry())?;

        let tcx = self.env.tcx();
        let typing_env = ty::TypingEnv::post_analysis(tcx, adt.did());

        // to account for recursive structs and enable establishing circular references,
        // we first generate a dummy struct (None)
        let struct_def_init = self.struct_arena.alloc(RefCell::new(None));

        let struct_name = strip_coq_ident(&ty.ident(tcx).to_string());

        self.variant_registry
            .borrow_mut()
            .insert(ty.def_id, (struct_name, &*struct_def_init, ty, false, None));
        // TODO: can we also add the literal already?

        let translate_adt = || {
            let struct_name = strip_coq_ident(&ty.ident(tcx).to_string());
            let (variant_def, invariant_def) = self.make_adt_variant(
                &struct_name,
                ty,
                adt,
                &mut AdtState::new(&mut deps, &scope, &typing_env),
            )?;

            let mut struct_def = radium::specs::structs::Abstract::new(variant_def, scope.into());
            if let Some(invariant_def) = invariant_def {
                struct_def.add_invariant(invariant_def);
            }
            Ok(struct_def)
        };

        match translate_adt() {
            Ok(mut struct_def) => {
                let lit = self.intern_literal(struct_def.make_literal_type());

                // check the deps
                let is_rec_type = deps.contains(&OrderedDefId::new(self.env.tcx(), adt.did()));
                if is_rec_type {
                    if !struct_def.has_invariant() {
                        // this is an error, we need an invariant on recursive types
                        self.variant_registry.borrow_mut().remove(&ty.def_id);
                        return Err(TranslationError::RecursiveTypeWithoutInvariant(ty.def_id));
                    }

                    // remove it
                    deps.remove(&OrderedDefId::new(self.env.tcx(), adt.did()));
                    struct_def.set_is_recursive();
                }

                // finalize the definition
                // TODO for generating the semtype definition, we will also need to track dependencies
                // between structs so that we know when we need recursive types etc.
                let mut struct_def_ref = struct_def_init.borrow_mut();
                *struct_def_ref = Some(struct_def);

                let mut deps_ref = self.adt_deps.borrow_mut();
                deps_ref.insert(OrderedDefId::new(self.env.tcx(), adt.did()), deps);

                // also add the entry for the literal
                let mut reg = self.variant_registry.borrow_mut();
                let aref = reg.get_mut(&ty.def_id).unwrap();
                aref.4 = Some(lit);

                Ok(())
            },
            Err(err) => {
                // remove the partial definition
                self.variant_registry.borrow_mut().remove(&ty.def_id);
                Err(err)
            },
        }
    }

    /// Make an ADT variant.
    /// This assumes that this variant has already been pre-registered to account for recursive
    /// occurrences.
    fn make_adt_variant(
        &self,
        struct_name: &str,
        ty: &'tcx ty::VariantDef,
        adt: ty::AdtDef<'_>,
        adt_deps: &mut TranslateAdtState<'_, 'tcx, 'def>,
    ) -> Result<
        (radium::specs::structs::AbstractVariant<'def>, Option<radium::invariants::Spec>),
        TranslationError<'tcx>,
    > {
        info!("adt variant: {:?}", ty);

        let tcx = self.env.tcx();

        // check for representation flags
        let repr = Self::get_struct_representation(&adt.repr())?;
        let mut builder = radium::specs::structs::VariantBuilder::new(struct_name.to_owned(), repr);

        // parse attributes
        let outer_attrs = self.env.get_attributes(ty.def_id);

        let expect_refinement;
        let mut invariant_spec;
        if attrs::has_tool_attr(outer_attrs, "refined_by") {
            let outer_attrs = attrs::filter_for_tool(outer_attrs);
            let mut spec_parser = struct_spec_parser::VerboseInvariantSpecParser::new(adt_deps.scope);
            let ty_name = strip_coq_ident(format!("{}_inv_t", struct_name).as_str());
            let res = spec_parser
                .parse_invariant_spec(&ty_name, &outer_attrs)
                .map_err(TranslationError::FatalError)?;

            invariant_spec = Some(res.0);
            expect_refinement = !res.1;
        } else {
            invariant_spec = None;
            expect_refinement = false;
        }
        info!("adt variant spec: {:?}", invariant_spec);

        // assemble the field definition
        let mut field_refinements = Vec::new();
        for f in &ty.fields {
            let f_name = f.ident(tcx).to_string();

            let attrs = self.env.get_attributes(f.did);
            let attrs = attrs::filter_for_tool(attrs);

            let f_ty = self.env.tcx().type_of(f.did).instantiate_identity();
            let ty = self.translate_type_in_state(
                f_ty,
                &mut STInner::TranslateAdt(AdtState::new(adt_deps.deps, adt_deps.scope, adt_deps.typing_env)),
            )?;

            let mut parser = struct_spec_parser::VerboseStructFieldSpecParser::new(
                &ty,
                adt_deps.scope,
                expect_refinement,
                |lit| self.intern_literal(lit),
            );
            let field_spec =
                parser.parse_field_spec(&f_name, &attrs).map_err(TranslationError::UnknownError)?;

            //info!("adt variant field: {:?} -> {} (with rfn {:?})", f_name, field_spec.ty, field_spec.rfn);
            builder.add_field(&f_name, field_spec.ty);

            if expect_refinement {
                if let Some(rfn) = field_spec.rfn {
                    field_refinements.push(rfn);
                } else {
                    return Err(TranslationError::UnknownError(format!(
                        "No refinement annotated for field {:?}",
                        f_name
                    )));
                }
            }
        }

        let struct_def = builder.finish();
        info!("finished variant def: {:?}", struct_def);

        // now add the invariant, if one was annotated
        if let Some(invariant_spec) = &mut invariant_spec
            && expect_refinement
        {
            // make a plist out of this
            let mut rfn = String::with_capacity(100);

            rfn.push_str("-[");
            push_str_list!(rfn, &field_refinements, "; ", "#({})");
            rfn.push(']');

            invariant_spec.provide_abstracted_refinement(rfn);
        }

        // TODO for generating the semtype definition, we will also need to track dependencies
        // between structs so that we know when we need recursive types etc.

        Ok((struct_def, invariant_spec))
    }

    /// Make a `GlobalId` for constants (use for discriminants).
    fn make_global_id_for_discr(
        &self,
        did: DefId,
        env: &'_ [ty::GenericArg<'tcx>],
    ) -> mir::interpret::GlobalId<'tcx> {
        mir::interpret::GlobalId {
            instance: ty::Instance {
                def: ty::InstanceKind::Item(did),
                args: self.env.tcx().mk_args(env),
            },
            promoted: None,
        }
    }

    fn scalar_int_to_int128(s: ty::ScalarInt, signed: bool) -> radium::specs::enums::Int128 {
        if signed {
            radium::specs::enums::Int128::Signed(s.to_int(s.size()))
        } else {
            radium::specs::enums::Int128::Unsigned(s.to_uint(s.size()))
        }
    }

    /// Build a map from discriminant names to their value, if it fits in a i128.
    fn build_discriminant_map(
        &self,
        def: ty::AdtDef<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        signed: bool,
    ) -> Result<HashMap<String, radium::specs::enums::Int128>, TranslationError<'tcx>> {
        let mut map: HashMap<String, radium::specs::enums::Int128> = HashMap::new();
        let variants = def.variants();

        let mut last_explicit_discr = radium::specs::enums::Int128::Unsigned(0);
        for v in variants {
            let v: &ty::VariantDef = v;
            let name = v.name.to_string();
            info!("Discriminant for {:?}: {:?}", v, v.discr);
            match v.discr {
                ty::VariantDiscr::Explicit(did) => {
                    // we try to const-evaluate the discriminant
                    let evaluated_discr = self
                        .env
                        .tcx()
                        .const_eval_global_id_for_typeck(
                            typing_env,
                            self.make_global_id_for_discr(did, &[]),
                            span::DUMMY_SP,
                        )
                        .map_err(|err| {
                            TranslationError::FatalError(format!(
                                "Failed to const-evaluate discriminant: {:?}",
                                err
                            ))
                        })?;

                    let evaluated_discr = evaluated_discr.map_err(|_err| {
                        TranslationError::FatalError("Failed to const-evaluate discriminant".to_owned())
                    })?;

                    let evaluated_int = evaluated_discr.try_to_scalar_int().unwrap();
                    let evaluated_int = Self::scalar_int_to_int128(evaluated_int, signed);

                    info!("const-evaluated enum discriminant: {:?}", evaluated_int);

                    last_explicit_discr = evaluated_int;
                    map.insert(name, evaluated_int);
                },
                ty::VariantDiscr::Relative(offset) => {
                    let idx: radium::specs::enums::Int128 = last_explicit_discr + offset;
                    map.insert(name, idx);
                },
            }
        }
        info!("Discriminant map for {:?}: {:?}", def, map);
        Ok(map)
    }

    fn does_did_match(&self, did: DefId, path: &[&str]) -> bool {
        let lookup_did = search::try_resolve_did(self.env.tcx(), path);
        if let Some(lookup_did) = lookup_did
            && lookup_did == did
        {
            return true;
        }
        false
    }

    /// Check whether this is an Option type.
    pub(crate) fn is_builtin_option_type(&self, ty: ty::Ty<'tcx>) -> bool {
        if let ty::TyKind::Adt(def, _) = ty.kind() {
            self.does_did_match(def.did(), &["core", "option", "Option"])
        } else {
            false
        }
    }

    /// Check whether this is an Option type.
    pub(crate) fn is_builtin_result_type(&self, ty: ty::Ty<'tcx>) -> bool {
        if let ty::TyKind::Adt(def, _) = ty.kind() {
            self.does_did_match(def.did(), &["core", "result", "Result"])
        } else {
            false
        }
    }

    /// Given a Rust enum which has already been registered and whose fields have been translated, generate a
    /// corresponding Coq Inductive as well as an `enums::Spec`.
    fn generate_enum_spec(
        &self,
        def: ty::AdtDef<'tcx>,
        inductive_name: String,
    ) -> (coq::inductive::Inductive, radium::specs::enums::Spec) {
        trace!("Generating Inductive for enum {:?}", def);

        let mut variants: Vec<coq::inductive::Variant> = Vec::new();
        let mut variant_patterns = Vec::new();

        for v in def.variants() {
            let registry = self.variant_registry.borrow();
            let (variant_name, coq_def, variant_def, _, _) = registry.get(&v.def_id).unwrap();
            let coq_def = coq_def.borrow();
            let coq_def = coq_def.as_ref().unwrap();
            let refinement_type = coq_def.plain_rt_def_name().to_owned();

            // simple optimization: if the variant has no fields, also this constructor gets no arguments
            let (variant_args, variant_arg_binders, variant_rfn) = if variant_def.fields.is_empty() {
                (vec![], vec![], "*[]".to_owned())
            } else {
                let args = vec![coq::binder::Binder::new(None, coq::term::Type::Literal(refinement_type))];
                (args, vec!["x".to_owned()], "x".to_owned())
            };

            variants.push(coq::inductive::Variant::new(variant_name.clone(), variant_args));

            variant_patterns.push((variant_name.to_owned(), variant_arg_binders, variant_rfn));
        }

        // We assume the generated Inductive def is placed in a context where the generic types are in scope.
        let inductive = coq::inductive::Inductive::new(
            inductive_name.clone(),
            coq::binder::BinderList::empty(),
            variants,
        );

        let enum_spec = radium::specs::enums::Spec {
            rfn_type: coq::term::Type::Literal(inductive_name),
            variant_patterns,
            is_partial: false,
        };

        info!("Generated inductive for {:?}: {:?}", def, inductive);

        (inductive, enum_spec)
    }

    /// Register an enum ADT
    fn register_enum(&self, def: ty::AdtDef<'tcx>) -> Result<(), TranslationError<'tcx>> {
        if self.is_enum_already_registered(def.did()) {
            // already there, that's fine.
            return Ok(());
        }
        info!("Registering enum {:?}", def.did());

        let tcx = self.env.tcx();

        let generics: &'tcx ty::Generics = self.env.tcx().generics_of(def.did());
        let mut scope = scope::Params::from(generics.own_params.as_slice());
        scope.add_param_env(def.did(), self.env(), self, self.trait_registry())?;

        let mut deps = BTreeSet::new();
        let typing_env = ty::TypingEnv::post_analysis(tcx, def.did());

        // pre-register the enum for recursion
        let enum_def_init = self.enum_arena.alloc(RefCell::new(None));

        // TODO: currently a hack, I don't know how to query the name properly
        let enum_name = strip_coq_ident(format!("{:?}", def).as_str());

        // insert partial definition for recursive occurrences
        self.enum_registry
            .borrow_mut()
            .insert(def.did(), (enum_name.clone(), &*enum_def_init, def, None));

        let translate_variants = || {
            let mut variant_attrs = Vec::new();
            for v in def.variants() {
                // now generate the variant
                let struct_def_init = self.struct_arena.alloc(RefCell::new(None));

                let struct_name = strip_coq_ident(format!("{}_{}", enum_name, v.ident(tcx)).as_str());
                self.variant_registry
                    .borrow_mut()
                    .insert(v.def_id, (struct_name.clone(), &*struct_def_init, v, true, None));

                let (variant_def, invariant_def) = self.make_adt_variant(
                    struct_name.as_str(),
                    v,
                    def,
                    &mut AdtState::new(&mut deps, &scope, &typing_env),
                )?;

                let mut struct_def = radium::specs::structs::Abstract::new(variant_def, scope.clone().into());
                if let Some(invariant_def) = invariant_def {
                    struct_def.add_invariant(invariant_def);
                }

                // also remember the attributes for additional processing
                let outer_attrs = self.env.get_attributes(v.def_id);
                let outer_attrs = attrs::filter_for_tool(outer_attrs);
                variant_attrs.push(outer_attrs);

                // finalize the definition
                {
                    let lit = self.intern_literal(struct_def.make_literal_type());
                    let mut struct_def_ref = struct_def_init.borrow_mut();
                    *struct_def_ref = Some(struct_def);

                    let mut reg = self.variant_registry.borrow_mut();
                    let aref = reg.get_mut(&v.def_id).unwrap();
                    aref.4 = Some(lit);
                }
            }

            // get the type of the discriminant
            let it = def.repr().discr_type();
            let it_is_signed = it.is_signed();
            let translated_it = TX::translate_integer_type(it);

            // build the discriminant map
            let discrs = self.build_discriminant_map(def, typing_env, it_is_signed)?;

            // get representation options
            let repr = Self::get_enum_representation(&def.repr())?;

            // parse annotations for enum type
            let enum_spec;
            let mut inductive_decl = None;

            if self.env.has_tool_attribute(def.did(), "refined_by") {
                let attributes = self.env.get_attributes(def.did());
                let attributes = attrs::filter_for_tool(attributes);

                let mut parser = VerboseEnumSpecParser::new(&scope);

                enum_spec = parser
                    .parse_enum_spec("", &attributes, &variant_attrs)
                    .map_err(TranslationError::FatalError)?;
            } else {
                // generate a specification

                // get name for the inductive
                let ind_name = self
                    .env
                    .get_tool_attribute(def.did(), "refine_as")
                    .map_or_else(
                        || Ok(Some(enum_name.clone())),
                        |args| parse_enum_refine_as(args).map_err(TranslationError::FatalError),
                    )?
                    .unwrap_or_else(|| enum_name.clone());

                let decl;
                (decl, enum_spec) = self.generate_enum_spec(def, ind_name);
                inductive_decl = Some(decl);
            }

            // check the deps
            let is_rec_type = deps.contains(&OrderedDefId::new(self.env.tcx(), def.did()));
            if is_rec_type {
                // remove it
                deps.remove(&OrderedDefId::new(self.env.tcx(), def.did()));
            }

            let mut enum_builder =
                radium::specs::enums::Builder::new(enum_name, scope.into(), translated_it, repr, is_rec_type);

            // now build the enum itself
            for v in def.variants() {
                let (variant_ref, _) = self.lookup_adt_variant(v.def_id)?;
                let variant_name = strip_coq_ident(&v.ident(tcx).to_string());
                let discriminant = discrs[&variant_name];
                enum_builder.add_variant(&variant_name, variant_ref, discriminant);
            }

            Ok(enum_builder.finish(inductive_decl, enum_spec))
        };

        match translate_variants() {
            Ok(enum_def) => {
                let lit = self.intern_literal(enum_def.make_literal_type());

                // finalize the definition
                let mut enum_def_ref = enum_def_init.borrow_mut();
                *enum_def_ref = Some(enum_def);

                let mut reg = self.enum_registry.borrow_mut();
                let aref = reg.get_mut(&def.did()).unwrap();
                aref.3 = Some(lit);

                let mut deps_ref = self.adt_deps.borrow_mut();
                deps_ref.insert(OrderedDefId::new(self.env.tcx(), def.did()), deps);
                Ok(())
            },
            Err(err) => {
                // deregister the ADT again
                self.enum_registry.borrow_mut().remove(&def.did());
                Err(err)
            },
        }
    }

    fn generate_adt_shim_use(
        &self,
        adt: ty::AdtDef<'tcx>,
        substs: ty::GenericArgsRef<'tcx>,
        state: ST<'_, '_, 'def, 'tcx>,
    ) -> Result<radium::Type<'def>, TranslationError<'tcx>> {
        let Some(shim) = self.lookup_adt_shim(adt.did()) else {
            return Err(TranslationError::UnknownError(format!(
                "generate_adt_shim_use called for unknown adt shim {:?}",
                adt.did()
            )));
        };

        let params = self.trait_registry().compute_scope_inst_in_state(state, adt.did(), substs, None)?;

        if let STInner::InFunction(scope) = state {
            let key = scope::AdtUseKey::new_from_inst(adt.did(), &params);
            let shim_use = radium::LiteralTypeUse::new(shim, params);
            // track this shim use for the current function
            scope.shim_uses.entry(key).or_insert_with(|| shim_use.clone());
            Ok(radium::Type::Literal(shim_use))
        } else {
            let shim_use = radium::LiteralTypeUse::new(shim, params);
            Ok(radium::Type::Literal(shim_use))
        }
    }

    /// Translate types, while placing the `DefIds` of ADTs that this type uses in the `adt_deps`
    /// argument, if provided.
    pub(crate) fn translate_type_in_state(
        &self,
        ty: ty::Ty<'tcx>,
        state: ST<'_, '_, 'def, 'tcx>,
    ) -> Result<radium::Type<'def>, TranslationError<'tcx>> {
        match ty.kind() {
            ty::TyKind::Bool => Ok(radium::Type::Bool),
            ty::TyKind::Char => Ok(radium::Type::Char),

            ty::TyKind::Int(it) => Ok(radium::Type::Int(match it {
                ty::IntTy::I8 => radium::lang::IntType::I8,
                ty::IntTy::I16 => radium::lang::IntType::I16,
                ty::IntTy::I32 => radium::lang::IntType::I32,
                ty::IntTy::I64 => radium::lang::IntType::I64,
                ty::IntTy::I128 => radium::lang::IntType::I128,
                ty::IntTy::Isize => radium::lang::IntType::ISize, // should have same size as pointer types
            })),

            ty::TyKind::Uint(it) => Ok(radium::Type::Int(match it {
                ty::UintTy::U8 => radium::lang::IntType::U8,
                ty::UintTy::U16 => radium::lang::IntType::U16,
                ty::UintTy::U32 => radium::lang::IntType::U32,
                ty::UintTy::U64 => radium::lang::IntType::U64,
                ty::UintTy::U128 => radium::lang::IntType::U128,
                ty::UintTy::Usize => radium::lang::IntType::USize, // should have same size as pointer types
            })),

            ty::TyKind::RawPtr(_, _) => Ok(radium::Type::RawPtr),

            ty::TyKind::Ref(region, ty, mutability) => {
                // TODO: this will have to change for handling fat ptrs. see the corresponding rustc
                // def for inspiration.

                if ty.is_str() || ty.is_array_slice() {
                    // special handling for slice types commonly used in error handling branches we
                    // don't care about
                    // TODO: emit a warning
                    return Ok(radium::Type::Unit);
                }

                let translated_ty = self.translate_type_in_state(*ty, &mut *state)?;

                let lft = TX::translate_region(&mut *state, *region)?;

                match mutability {
                    ast::ast::Mutability::Mut => Ok(radium::Type::MutRef(Box::new(translated_ty), lft)),
                    _ => Ok(radium::Type::ShrRef(Box::new(translated_ty), lft)),
                }
            },

            ty::TyKind::Never => Ok(radium::Type::Never),

            ty::TyKind::Adt(adt, substs) => {
                if adt.is_box() {
                    // extract the type parameter
                    // the second parameter is the allocator, which we ignore for now
                    let [ty, _] = substs.as_slice() else {
                        return Err(TranslationError::UnsupportedFeature {
                            description: format!("unsupported ADT {:?}", ty),
                        });
                    };

                    let translated_ty = self.translate_type_in_state(ty.expect_ty(), &mut *state)?;
                    return Ok(radium::Type::BoxT(Box::new(translated_ty)));
                }

                if self.is_struct_definitely_zero_sized(adt.did()) == Some(true) {
                    // make this unit
                    return Ok(radium::Type::Unit);
                }

                if let STInner::TranslateAdt(state) = state {
                    state.deps.insert(OrderedDefId::new(self.env.tcx(), adt.did()));
                }

                if self.lookup_adt_shim(adt.did()).is_some() {
                    return self.generate_adt_shim_use(*adt, substs, &mut *state);
                }

                if adt.is_struct() {
                    return self.generate_structlike_use_internal(ty, None, &mut *state);
                }

                if adt.is_enum() {
                    return self.generate_enum_use_noshim(*adt, substs, &mut *state).map(radium::Type::Enum);
                }

                Err(TranslationError::UnsupportedFeature {
                    description: format!("unsupported ADT {:?}", ty),
                })
            },

            ty::TyKind::Closure(_def, closure_args) => {
                // We replace this with the tuple of the closure's state
                let clos = closure_args.as_closure();
                let upvar_tys = clos.tupled_upvars_ty();

                self.translate_type_in_state(upvar_tys, &mut *state)
            },

            ty::TyKind::Tuple(params) => {
                if params.is_empty() {
                    return Ok(radium::Type::Unit);
                }

                self.generate_tuple_use(params.iter(), &mut *state).map(radium::Type::Literal)
            },

            ty::TyKind::Param(param_ty) => state.lookup_ty_param(*param_ty),

            ty::TyKind::Float(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support floats".to_owned(),
            }),

            ty::TyKind::Array(_, _) => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does not support arrays".to_owned(),
            }),

            ty::TyKind::Slice(_) => {
                // TODO this should really be a fat ptr?
                Err(TranslationError::UnsupportedFeature {
                    description: "RefinedRust does not support slices".to_owned(),
                })
            },

            ty::TyKind::Alias(kind, alias_ty) => {
                // TODO do we get a problem because we are erasing regions?
                if let Ok(normalized_ty) = state.normalize_type_erasing_regions(self.env.tcx(), ty)
                    && !matches!(normalized_ty.kind(), ty::TyKind::Alias(_, _))
                {
                    // if we managed to normalize it, translate the normalized type
                    return self.translate_type_in_state(normalized_ty, state);
                }
                // otherwise, we can't normalize the projection
                match kind {
                    ty::AliasTyKind::Projection => {
                        info!(
                            "Trying to resolve projection of {:?} for {:?}",
                            alias_ty.def_id, alias_ty.args
                        );

                        let trait_did = self.env.tcx().parent(alias_ty.def_id);
                        let entry = &state.lookup_trait_use(self.env.tcx(), trait_did, alias_ty.args)?;
                        let assoc_type = entry.get_associated_type_use(self.env, alias_ty.def_id)?;

                        info!("Resolved projection to {assoc_type:?}");

                        Ok(assoc_type)
                    },
                    _ => Err(TranslationError::UnsupportedType {
                        description: format!("RefinedRust does not support Alias types of kind {kind:?}"),
                    }),
                }
            },

            ty::TyKind::Foreign(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support extern types".to_owned(),
            }),

            ty::TyKind::Str => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support str".to_owned(),
            }),

            ty::TyKind::Pat(_, _) => Err(TranslationError::Unimplemented {
                description: "RefinedRust does not support Pat".to_owned(),
            }),

            ty::TyKind::FnDef(_, _) => Err(TranslationError::Unimplemented {
                description: "RefinedRust does not support FnDef".to_owned(),
            }),

            ty::TyKind::FnPtr(..) => Err(TranslationError::Unimplemented {
                description: "RefinedRust does not support FnPtr".to_owned(),
            }),

            ty::TyKind::Dynamic(_, _, _) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support trait objects".to_owned(),
            }),

            ty::TyKind::UnsafeBinder(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support UnsafeBinder".to_owned(),
            }),

            ty::TyKind::Coroutine(_, _)
            | ty::TyKind::CoroutineWitness(_, _)
            | ty::TyKind::CoroutineClosure(_, _) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does currently not support coroutines".to_owned(),
            }),

            ty::TyKind::Infer(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support infer types".to_owned(),
            }),

            ty::TyKind::Bound(_, _) | ty::TyKind::Placeholder(_) | ty::TyKind::Error(_) => {
                Err(TranslationError::UnsupportedType {
                    description: "RefinedRust does not support higher-ranked types".to_owned(),
                })
            },
        }
    }

    /// Translate a `attr::IntType` (this is different from the `ty`
    /// `IntType`).
    const fn translate_integer_type(it: abi::IntegerType) -> radium::lang::IntType {
        match it {
            abi::IntegerType::Fixed(size, sign) => {
                if sign {
                    match size {
                        abi::Integer::I8 => radium::lang::IntType::I8,
                        abi::Integer::I16 => radium::lang::IntType::I16,
                        abi::Integer::I32 => radium::lang::IntType::I32,
                        abi::Integer::I64 => radium::lang::IntType::I64,
                        abi::Integer::I128 => radium::lang::IntType::I128,
                    }
                } else {
                    match size {
                        abi::Integer::I8 => radium::lang::IntType::U8,
                        abi::Integer::I16 => radium::lang::IntType::U16,
                        abi::Integer::I32 => radium::lang::IntType::U32,
                        abi::Integer::I64 => radium::lang::IntType::U64,
                        abi::Integer::I128 => radium::lang::IntType::U128,
                    }
                }
            },
            abi::IntegerType::Pointer(sign) => {
                if sign {
                    radium::lang::IntType::ISize
                } else {
                    radium::lang::IntType::USize
                }
            },
        }
    }

    /// Get the name for a field of an ADT or tuple type
    pub(crate) fn get_field_name_of(
        &self,
        f: abi::FieldIdx,
        ty: ty::Ty<'tcx>,
        variant: Option<usize>,
    ) -> Result<String, TranslationError<'tcx>> {
        let tcx = self.env.tcx();
        match ty.kind() {
            ty::TyKind::Adt(def, _) => {
                info!("getting field name of {:?} at {} (variant {:?})", f, ty, variant);
                if def.is_struct() {
                    let i = def.variants().get(abi::VariantIdx::from_usize(0)).unwrap();
                    i.fields.get(f).map(|f| f.ident(tcx).to_string()).ok_or_else(|| {
                        TranslationError::UnknownError(format!("could not get field {:?} of {}", f, ty))
                    })
                } else if def.is_enum() {
                    let variant = variant.unwrap();
                    let i = def.variants().get(abi::VariantIdx::from_usize(variant)).unwrap();
                    i.fields.get(f).map(|f| f.ident(tcx).to_string()).ok_or_else(|| {
                        TranslationError::UnknownError(format!("could not get field {:?} of {}", f, ty))
                    })
                } else {
                    Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported field access {:?}to ADT {:?}", f, ty),
                    })
                }
            },

            ty::TyKind::Tuple(_) => Ok(f.index().to_string()),

            ty::TyKind::Closure(_, _) => {
                // treat as tuple of upvars
                Ok(f.index().to_string())
            },

            _ => Err(TranslationError::InvalidLayout),
        }
    }

    /// Get the name of a variant of an enum.
    pub(crate) fn get_variant_name_of(
        ty: ty::Ty<'tcx>,
        variant: abi::VariantIdx,
    ) -> Result<String, TranslationError<'tcx>> {
        match ty.kind() {
            ty::TyKind::Adt(def, _) => {
                info!("getting variant name of {:?} at {}", variant, ty);
                let i = def.variants().get(variant).unwrap();
                Ok(i.name.to_string())
            },
            _ => Err(TranslationError::InvalidLayout),
        }
    }
}

/// Public functions used by the `BodyTranslator`.
impl<'def, 'tcx> TX<'def, 'tcx> {
    /// Translate a MIR type to the Caesium syntactic type we need when storing an element of the type,
    /// substituting all generics.
    pub(crate) fn translate_type_to_syn_type(
        &self,
        ty: ty::Ty<'tcx>,
        scope: ST<'_, '_, 'def, 'tcx>,
    ) -> Result<radium::lang::SynType, TranslationError<'tcx>> {
        self.translate_type_in_state(ty, scope).map(radium::lang::SynType::from)
    }

    /// Translate type in the scope of a function.
    pub(crate) fn translate_type(
        &self,
        ty: ty::Ty<'tcx>,
        scope: InFunctionState<'_, 'def, 'tcx>,
    ) -> Result<radium::Type<'def>, TranslationError<'tcx>> {
        self.translate_type_in_state(ty, &mut STInner::InFunction(&mut *scope))
    }

    /// Translate type in the given scope.
    pub(crate) fn translate_type_in_scope(
        &self,
        scope: &scope::Params<'tcx, 'def>,
        typing_env: ty::TypingEnv<'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> Result<radium::Type<'def>, TranslationError<'tcx>> {
        let mut deps = BTreeSet::new();
        let state = AdtState::new(&mut deps, scope, &typing_env);
        self.translate_type_in_state(ty, &mut STInner::TranslateAdt(state))
    }

    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub(crate) fn generate_structlike_use(
        &self,
        ty: ty::Ty<'tcx>,
        variant: Option<abi::VariantIdx>,
        scope: InFunctionState<'_, 'def, 'tcx>,
    ) -> Result<Option<radium::LiteralTypeUse<'def>>, TranslationError<'tcx>> {
        match ty.kind() {
            ty::TyKind::Adt(adt, args) => {
                if adt.is_struct() {
                    info!("generating struct use for {:?}", adt.did());
                    // register the ADT, if necessary
                    self.register_adt(*adt)?;
                    self.generate_struct_use(adt.did(), args, &mut *scope)
                } else if adt.is_enum() {
                    if let Some(variant) = variant {
                        self.register_adt(*adt)?;
                        let v = &adt.variants()[variant];
                        self.generate_enum_variant_use(v.def_id, args, scope).map(Some)
                    } else {
                        Err(TranslationError::UnknownError(
                            "a non-downcast enum is not a structlike".to_owned(),
                        ))
                    }
                } else {
                    Err(TranslationError::UnsupportedType {
                        description: "non-{enum, struct, tuple} ADTs are not supported".to_owned(),
                    })
                }
            },
            ty::TyKind::Tuple(args) => {
                self.generate_tuple_use(*args, &mut STInner::InFunction(scope)).map(Some)
            },
            ty::TyKind::Closure(_, args) => {
                // use the upvar tuple
                let closure_args = args.as_closure();
                let upvars = closure_args.upvar_tys();
                self.generate_tuple_use(upvars, &mut STInner::InFunction(scope)).map(Some)
            },
            _ => Err(TranslationError::UnknownError("not a structlike".to_owned())),
        }
    }

    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub(crate) fn generate_enum_use(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        state: InFunctionState<'_, 'def, 'tcx>,
    ) -> Result<radium::LiteralTypeUse<'def>, TranslationError<'tcx>> {
        info!("generating enum use for {:?}", adt_def.did());
        self.register_adt(adt_def)?;

        let enum_ref: radium::LiteralTypeRef<'def> = self.lookup_enum_literal(adt_def.did())?;
        let params = self.trait_registry().compute_scope_inst_in_state(
            &mut STInner::InFunction(&mut *state),
            adt_def.did(),
            args,
            None,
        )?;
        let key = scope::AdtUseKey::new_from_inst(adt_def.did(), &params);
        let enum_use = radium::LiteralTypeUse::new(enum_ref, params);

        // track this enum use for the current function
        let enum_uses = &mut state.shim_uses;
        enum_uses.entry(key).or_insert_with(|| enum_use.clone());

        Ok(enum_use)
    }

    /// Generate a struct use.
    /// Returns None if this should be unit.
    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub(crate) fn generate_struct_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        scope: InFunctionState<'_, 'def, 'tcx>,
    ) -> Result<Option<radium::LiteralTypeUse<'def>>, TranslationError<'tcx>> {
        info!("generating struct use for {:?}", variant_id);

        if self.is_struct_definitely_zero_sized(variant_id) == Some(true) {
            info!("replacing zero-sized struct with unit");
            return Ok(None);
        }

        let params = self.trait_registry().compute_scope_inst_in_state(
            &mut STInner::InFunction(&mut *scope),
            variant_id,
            args,
            None,
        )?;
        let key = scope::AdtUseKey::new_from_inst(variant_id, &params);

        let struct_ref: radium::LiteralTypeRef<'def> = self.lookup_adt_variant_literal(variant_id)?;
        let struct_use = radium::LiteralTypeUse::new(struct_ref, params);

        scope.shim_uses.entry(key).or_insert_with(|| struct_use.clone());

        Ok(Some(struct_use))
    }

    /// Generate a struct use.
    /// Returns None if this should be unit.
    pub(crate) fn generate_enum_variant_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        scope: InFunctionState<'_, 'def, 'tcx>,
    ) -> Result<radium::LiteralTypeUse<'def>, TranslationError<'tcx>> {
        info!("generating enum variant use for {:?}", variant_id);

        let params = self.trait_registry().compute_scope_inst_in_state(
            &mut STInner::InFunction(&mut *scope),
            variant_id,
            args,
            None,
        )?;
        let _key = scope::AdtUseKey::new_from_inst(variant_id, &params);

        let struct_ref: radium::LiteralTypeRef<'def> = self.lookup_adt_variant_literal(variant_id)?;
        let struct_use = radium::LiteralTypeUse::new(struct_ref, params);

        // TODO: track?
        // generate the struct use key
        //let mut shim_uses = self.shim_uses.borrow_mut();
        //if !shim_uses.contains_key(&key) {
        //shim_uses.insert(key, struct_use.clone());
        //}

        Ok(struct_use)
    }

    /// Make a tuple use.
    /// Hack: This does not take the translation state but rather a direct reference to the tuple
    /// use map so that we can this function when parsing closure specifications.
    pub(crate) fn make_tuple_use(
        &self,
        translated_tys: Vec<radium::Type<'def>>,
        uses: Option<&mut HashMap<Vec<radium::lang::SynType>, radium::LiteralTypeUse<'def>>>,
    ) -> radium::Type<'def> {
        let num_components = translated_tys.len();
        if num_components == 0 {
            return radium::Type::Unit;
        }

        let (_, lit) = self.get_tuple_struct_ref(num_components);
        let key: Vec<_> = translated_tys.iter().map(radium::lang::SynType::from).collect();
        let mut scope_inst = radium::GenericScopeInst::empty();
        for ty in translated_tys {
            scope_inst.add_direct_ty_param(ty);
        }
        let struct_use = radium::LiteralTypeUse::new(lit, scope_inst);
        if let Some(tuple_uses) = uses {
            tuple_uses.entry(key).or_insert_with(|| struct_use.clone());
        }

        radium::Type::Literal(struct_use)
    }
}
