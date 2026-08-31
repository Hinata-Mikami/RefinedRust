// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Defines scopes for maintaining generics and trait requirements.

use std::collections::{HashMap, hash_map};

use derive_more::{Constructor, Debug};
use log::{info, trace, warn};
use radium::{coq, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty::{RegionExt as _, TypeFoldable as _, TypeSuperFoldable as _};
use rr_rustc_interface::middle::{span_bug, ty};
use rr_rustc_interface::span::{DUMMY_SP, Symbol};

use crate::base::*;
use crate::error::Message;
use crate::spec_parsers::parse_utils::{ParamLookup, RustPath, RustPathElem};
use crate::traits::registry::{GenericTraitUse, TraitKey, VirtualTrait};
use crate::traits::{registry, requirements};
use crate::types::translator::TX;
use crate::types::tyvars::TyRegionEraseFolder;
use crate::{environment, regions};

/// Key used for resolving early-bound parameters for function calls.
/// Invariant: All regions contained in these types should be erased, as type parameter instantiation is
/// independent of lifetimes.
/// TODO: handle early-bound lifetimes?
pub(crate) type GenericsKey<'tcx> = Vec<ty::Ty<'tcx>>;

struct GenericKeyFolder<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for GenericKeyFolder<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, _: ty::Region<'tcx>) -> ty::Region<'tcx> {
        ty::Region::new_from_kind(self.tcx, ty::RegionKind::ReErased)
    }

    fn fold_ty(&mut self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        let ty = t.super_fold_with(self);
        match ty.kind() {
            // `skip_norm_wip` changes this marker while preserving the same projection.
            ty::TyKind::Alias(_, alias) => ty::Ty::new_alias(self.tcx, ty::IsRigid::No, *alias),
            _ => ty,
        }
    }
}

pub(crate) fn erase_regions<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
    ty.fold_with(&mut TyRegionEraseFolder::new(tcx))
}

/// Generate a key for indexing into structures indexed by `GenericArg`s.
pub(crate) fn generate_args_inst_key<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty_params: &[ty::GenericArg<'tcx>],
) -> Result<GenericsKey<'tcx>, TranslationError> {
    // erase parameters to their syntactic types
    let mut key = Vec::new();
    let mut key_folder = GenericKeyFolder { tcx };
    for p in ty_params {
        match p.kind() {
            ty::GenericArgKind::Lifetime(_) => {
                // lifetimes are not relevant here
            },
            ty::GenericArgKind::Type(t) => {
                // TODO: this should erase to the syntactic type.
                // Is erasing regions enough for that?
                let t_erased = t.fold_with(&mut key_folder);
                key.push(t_erased);
            },
            ty::GenericArgKind::Const(_c) => {
                return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                    "RefinedRust does not support const generics".to_owned(),
                ))));
            },
        }
    }
    Ok(key)
}

/// Keys used to deduplicate adt uses for `syn_type` assumptions.
/// TODO maybe we should use `SimplifiedType` + `simplify_type` instead of the syntys?
/// Or types with erased regions?
#[derive(Eq, PartialEq, Ord, PartialOrd, Debug)]
pub(crate) struct AdtUseKey {
    base_did: OrderedDefId,
    generics: Vec<lang::SynType>,
}

impl AdtUseKey {
    pub(crate) fn new_from_inst(defid: OrderedDefId, params: &specs::GenericScopeInst<'_>) -> Self {
        let generic_syntys: Vec<_> =
            params.get_all_ty_params_with_assocs().iter().map(lang::SynType::from).collect();
        Self {
            base_did: defid,
            generics: generic_syntys,
        }
    }
}

#[derive(Clone, Debug)]
enum Param {
    Region(specs::LftParam),
    Ty(specs::LiteralTyParam),
    // Note: we do not currently support Const params
    Const,
}
impl Param {
    const fn as_type(&self) -> Option<&specs::LiteralTyParam> {
        match self {
            Self::Ty(lit) => Some(lit),
            _ => None,
        }
    }

    const fn as_region(&self) -> Option<&specs::LftParam> {
        match self {
            Self::Region(lit) => Some(lit),
            _ => None,
        }
    }
}

/// Data structure that maps generic parameters for ADT/trait translation
#[derive(Constructor, Clone, Debug, Default)]
pub(crate) struct Params<'tcx, 'def> {
    /// maps generic indices (De Bruijn) to the corresponding Coq names in the current environment
    scope: Vec<Param>,
    /// maps De Bruijn indices for late lifetimes to the lifetime
    /// since rustc groups De Bruijn indices by (binder, var in the binder), this is a nested vec.
    late_scope: Vec<Vec<specs::LftParam>>,
    /// external lifetimes from surrounding bodies,
    /// mainly used for regions in closure captures which have no formal Rust parameters
    external_scope: Vec<specs::LftParam>,

    // lifetime constraints
    lifetime_inclusions: Vec<specs::LftConstrWithOrigin<'def>>,

    /// conversely, map the declaration name of a lifetime to an early index
    lft_names: HashMap<String, usize>,
    /// map types to their index
    ty_names: HashMap<String, u32>,

    /// the trait instances which are in scope
    trait_scope: Traits<'tcx, 'def>,
}

#[expect(clippy::fallible_impl_from)]
impl<'tcx, 'def> From<Params<'tcx, 'def>>
    for specs::GenericScope<'def, specs::traits::LiteralSpecUseRef<'def>>
{
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
        for x in x.late_scope {
            for lft in x {
                scope.add_lft_param(lft);
            }
        }
        for lft in x.external_scope {
            scope.add_lft_param(lft);
        }
        for key in x.trait_scope.ordered_assumptions {
            let trait_use = x.trait_scope.used_traits.remove(&key).unwrap();
            if !trait_use.is_self_use {
                scope.add_trait_requirement(trait_use.trait_use);
            }
        }
        for constr in x.lifetime_inclusions {
            scope.add_lft_constr(constr);
        }

        trace!("Computed GenericScope: {scope:?}");
        scope
    }
}

impl<'def> ParamLookup<'def> for Params<'_, 'def> {
    fn lookup_ty_param(&self, path: &RustPath) -> Option<specs::Type<'def>> {
        // first lookup if this is a type parameter
        if path.len() == 1 {
            let RustPathElem::AssocItem(it) = &path[0];
            if let Some(idx) = self.ty_names.get(it)
                && let Some(n) = self.lookup_ty_param_idx(*idx)
            {
                return Some(specs::Type::LiteralParam(n.to_owned()));
            }
        }
        // otherwise interpret this as an associated type path
        self.trait_scope.assoc_ty_names.get(path).cloned()
    }

    fn lookup_lft(&self, lft: &str) -> Option<&specs::LftParam> {
        let idx = self.lft_names.get(lft)?;
        self.lookup_region_idx(*idx)
    }

    fn lookup_literal(&self, path: &RustPath) -> Option<String> {
        self.trait_scope.attribute_names.get(path).cloned()
    }
}

impl<'tcx, 'def> Params<'tcx, 'def> {
    pub(crate) const fn trait_scope(&self) -> &Traits<'tcx, 'def> {
        &self.trait_scope
    }

    /// Create from generics, optionally annotating the type parameters with their origin.
    pub(crate) fn new_from_generics(
        tcx: ty::TyCtxt<'tcx>,
        x: ty::GenericArgsRef<'tcx>,
        with_origin: Option<DefId>,
    ) -> Self {
        let mut scope = Vec::new();

        let mut region_count = 0;

        let mut ty_names = HashMap::new();
        let mut lft_names = HashMap::new();

        for (num, p) in (0_u32..).zip(x) {
            let param = if let Some(r) = p.as_region() {
                if let Some(name) = r.get_name(tcx)
                    && name.as_str() != "'_"
                {
                    lft_names.insert(name.as_str().to_owned(), scope.len());
                    let name = format!("ulft_{}", name);

                    let ty::RegionKind::ReEarlyParam(early) = r.kind() else {
                        unreachable!("should have early param");
                    };

                    let origin = if let Some(of_did) = with_origin {
                        determine_origin_of_lft_param(of_did, tcx, early)
                    } else {
                        specs::LftParamOrigin::LocalEarlyBound
                    };

                    Param::Region(specs::LftParam::new(coq::Ident::new(&name), origin))
                } else {
                    let name = coq::Ident::new(&format!("ulft_{}", region_count));
                    region_count += 1;

                    Param::Region(specs::LftParam::new(name, specs::LftParamOrigin::LocalEarlyBound))
                }
            } else if let Some(ty) = p.as_type() {
                let ty::TyKind::Param(x) = ty.kind() else {
                    unreachable!("Should not convert a non-parametric GenericArgsRef to a Params");
                };

                ty_names.insert(x.name.as_str().to_owned(), num);
                let name = strip_coq_ident(x.name.as_str());

                let lit = if let Some(of_did) = with_origin {
                    let origin = Self::determine_origin_of_param(of_did, tcx, *x);
                    specs::LiteralTyParam::new_with_origin(&name, origin)
                } else {
                    specs::LiteralTyParam::new(&name)
                };

                Param::Ty(lit)
            } else if p.as_const().is_some() {
                Param::Const
            } else {
                unreachable!("Should not be a Term");
            };

            scope.push(param);
        }
        Self {
            scope,
            late_scope: Vec::new(),
            external_scope: Vec::new(),
            lft_names,
            ty_names,
            lifetime_inclusions: Vec::new(),
            trait_scope: Traits::default(),
        }
    }

    /// Lookup a type parameter by its De Bruijn index.
    #[must_use]
    pub(crate) fn lookup_ty_param_idx(&self, idx: u32) -> Option<&specs::LiteralTyParam> {
        let ty = self.scope.get(idx as usize)?;
        ty.as_type()
    }

    /// Lookup a region parameter by its De Bruijn index.
    #[must_use]
    pub(crate) fn lookup_region_idx(&self, idx: usize) -> Option<&specs::LftParam> {
        let lft = self.scope.get(idx)?;
        lft.as_region()
    }

    /// Lookup a late region parameter by its De Bruijn index.
    #[must_use]
    pub(crate) fn lookup_late_region_idx(&self, binder: usize, var: usize) -> Option<&specs::LftParam> {
        let binder = self.late_scope.get(binder)?;
        let lft = binder.get(var)?;
        Some(lft)
    }

    /// Get all type parameters in scope.
    #[must_use]
    pub(crate) fn tyvars(&self) -> Vec<specs::LiteralTyParam> {
        let mut tyvars = Vec::new();
        for x in &self.scope {
            if let Param::Ty(ty) = x {
                tyvars.push(ty.to_owned());
            }
        }
        tyvars
    }

    /// Add bound regions when descending under a for<...> binder.
    #[must_use]
    pub(crate) fn translate_bound_regions(
        &mut self,
        tcx: ty::TyCtxt<'tcx>,
        bound_regions: &[ty::BoundRegionKind<'tcx>],
    ) -> specs::traits::ReqScope {
        // We add these lifetimes to a special late scope, as the de bruijn indices are different
        // from the early-bound binders
        let mut regions_to_quantify = Vec::new();
        let mut new_binder = Vec::new();

        // the last element should be the one with the lowest index
        for (idx, region) in bound_regions.iter().rev().enumerate().rev() {
            // TODO smarter way to autogenerate anonymous names?
            let name = region.get_name(tcx).map_or_else(
                || coq::Ident::new(&format!("_lft_for_{}", idx)),
                |x| coq::Ident::new(&format!("lft_{}", x.as_str())),
            );

            new_binder.push(specs::LftParam::new(name.clone(), specs::LftParamOrigin::ForBinder));
            if region.get_name(tcx).is_some() {
                self.lft_names.insert(format!("{}", name), idx);
            }

            regions_to_quantify.push(specs::LftParam::new(name, specs::LftParamOrigin::ForBinder));
        }
        // NB only push a binder if there were any regions bound here.
        if !new_binder.is_empty() {
            self.late_scope.insert(0, new_binder);
        }

        specs::traits::ReqScope::new(regions_to_quantify)
    }

    /// Add bound regions when descending under a for<...> binder.
    pub(crate) fn add_trait_req_scope(&mut self, scope: &specs::traits::ReqScope) {
        let binder = scope.quantified_lfts.clone();
        self.late_scope.insert(0, binder);
    }

    /// Update the lifetimes in this scope with the information from a region map for a function.
    /// We use this in order to get a scope that is sufficient for type translation out of a
    /// `FunctionState`.
    pub(crate) fn with_region_map(&mut self, map: &regions::EarlyLateRegionMap<'def>) {
        // replace the early region names
        for (idx, param) in self.scope.iter_mut().enumerate() {
            let Some(_) = param.as_region() else { continue };

            let early_vid = map.early_regions[idx].as_ref().unwrap();
            let name = &map.region_names[early_vid];
            *param = Param::Region(name.to_owned());
        }

        // fill the late scope
        assert!(self.late_scope.is_empty());
        let mut idx = 0_usize;
        for binder in &map.late_regions {
            let mut new_binder = Vec::new();
            for late_vid in binder {
                let name = map.region_names.get(late_vid);
                let name = name.map_or_else(
                    || {
                        specs::LftParam::new(
                            coq::Ident::new(&format!("_lft_for_fn_{}", idx)),
                            specs::LftParamOrigin::LocalLateBound,
                        )
                    },
                    ToOwned::to_owned,
                );
                new_binder.push(name);
                idx += 1;
            }
            self.late_scope.push(new_binder);
        }

        // add extra closure regions
        for vid in &map.external_regions {
            let name = &map.region_names[vid];
            self.external_scope.push(name.to_owned());
        }

        // replace all existing constraints
        self.lifetime_inclusions = Vec::new();
        // add lifetime constraints
        for (constr, origin) in &map.constraints {
            match constr {
                regions::LftConstr::RegionOutlives(r1, r2) => {
                    let lft1 = map.lookup_region(*r1).unwrap();
                    let lft2 = map.lookup_region(*r2).unwrap();

                    let constr = specs::LftConstr::LftOutlives(
                        specs::UniversalLft::Local(lft2.lft().to_owned()),
                        specs::UniversalLft::Local(lft1.lft().to_owned()),
                    );
                    self.lifetime_inclusions.push(specs::LftConstrWithOrigin::new(constr, *origin));
                },
                regions::LftConstr::TypeOutlives(ty, r) => {
                    let lft = map.lookup_region(*r).unwrap();

                    let constr = specs::LftConstr::TypeOutlives(
                        ty.to_owned(),
                        specs::UniversalLft::Local(lft.lft().to_owned()),
                    );
                    self.lifetime_inclusions.push(specs::LftConstrWithOrigin::new(constr, *origin));
                },
            }
        }
    }

    fn translate_region(&self, region: ty::Region<'tcx>) -> Option<specs::Lft> {
        match region.kind() {
            ty::RegionKind::ReEarlyParam(early) => {
                self.lookup_region_idx(early.index as usize).map(|x| x.lft().to_owned())
            },
            ty::RegionKind::ReBound(idx, r) => {
                if let ty::BoundVarIndexKind::Bound(idx) = idx {
                    self.lookup_late_region_idx(usize::from(idx), r.var.index()).map(|x| x.lft().to_owned())
                } else {
                    unimplemented!("cannot handle Canonicalized binders");
                }
            },
            ty::RegionKind::ReStatic => Some(coq::Ident::new("static")),
            _ => None,
        }
    }

    /// Add the lifetime constraints of a `ParamEnv`.
    fn add_lifetime_constraints(
        &mut self,
        did: DefId,
        tcx: ty::TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        type_translator: &TX<'def, 'tcx>,
    ) -> Result<(), TranslationError> {
        let clauses_with_origin = requirements::get_clauses_with_origin(tcx, did, typing_env.param_env);
        for (cl, origin) in clauses_with_origin {
            let cl_kind = cl.kind();
            let cl_kind = cl_kind.skip_binder();

            if let ty::ClauseKind::RegionOutlives(region_pred) = cl_kind {
                info!("region outlives: {:?} {:?}", region_pred.0, region_pred.1);
                let lft1 = self.translate_region(region_pred.0).ok_or_else(|| {
                    TranslationError::ErrorReported(
                        type_translator.tcx().dcx().err(Message::UnknownRegion(region_pred.0)),
                    )
                })?;
                let lft2 = self.translate_region(region_pred.1).ok_or_else(|| {
                    TranslationError::ErrorReported(
                        type_translator.tcx().dcx().err(Message::UnknownRegion(region_pred.1)),
                    )
                })?;

                let constr = specs::LftConstr::LftOutlives(
                    specs::UniversalLft::Local(lft2),
                    specs::UniversalLft::Local(lft1),
                );
                self.lifetime_inclusions.push(specs::LftConstrWithOrigin::new(constr, origin));
            }
            if let ty::ClauseKind::TypeOutlives(outlives_pred) = cl_kind {
                info!("type outlives: {:?} {:?}", outlives_pred.0, outlives_pred.1);
                let translated_ty =
                    type_translator.translate_type_in_scope(&*self, typing_env, outlives_pred.0)?;
                let lft = self.translate_region(outlives_pred.1).ok_or_else(|| {
                    TranslationError::ErrorReported(
                        type_translator.tcx().dcx().err(Message::UnknownRegion(outlives_pred.1)),
                    )
                })?;

                let constr = specs::LftConstr::TypeOutlives(translated_ty, specs::UniversalLft::Local(lft));
                self.lifetime_inclusions.push(specs::LftConstrWithOrigin::new(constr, origin));
            }
        }

        Ok(())
    }

    fn add_trait_requirements(
        &mut self,
        did: DefId,
        tcx: ty::TyCtxt<'tcx>,
        type_translator: &TX<'def, 'tcx>,
        trait_registry: &registry::TR<'tcx, 'def>,
        requirements: &[requirements::TraitReqMeta<'tcx>],
    ) -> Result<(), TranslationError> {
        let typing_env = ty::TypingEnv::post_analysis(tcx, did);
        let is_trait = tcx.is_trait(did);

        // pre-register all the requirements, in order to resolve dependencies
        for req in requirements {
            let key = (
                TraitKey::rust(tcx, req.trait_ref.def_id),
                generate_args_inst_key(tcx, req.trait_ref.args).unwrap(),
            );
            if req.is_self_in_trait_decl {
                assert!(req.bound_regions.is_empty());
                let dummy_trait_use = trait_registry.make_trait_self_use(req.trait_ref);
                self.trait_scope.used_traits.insert(key.clone(), dummy_trait_use);
            } else {
                let dummy_trait_use =
                    trait_registry.make_empty_trait_use(req.trait_ref, req.bound_regions.as_slice());
                self.trait_scope.used_traits.insert(key.clone(), dummy_trait_use);
            }
            self.trait_scope.ordered_assumptions.push(key);
        }

        for req in requirements.iter().rev() {
            if req.is_self_in_trait_decl {
                continue;
            }

            // TODO: do we get into trouble with recursive trait requirements somewhere?
            // lookup the trait in the trait registry
            let Some(trait_spec) = trait_registry.lookup_trait(req.trait_ref.def_id) else {
                return Err(TranslationError::ErrorReported(tcx.dcx().span_err(
                    tcx.def_span(req.trait_ref.def_id),
                    Message::TraitNotRegisteredWithRefinedRust,
                )));
            };

            let key = (
                TraitKey::rust(tcx, req.trait_ref.def_id),
                generate_args_inst_key(tcx, req.trait_ref.args).unwrap(),
            );
            let entry = &self.trait_scope.used_traits[&key];

            registry::TR::fill_trait_use(
                entry,
                req.trait_ref,
                trait_spec,
                req.is_used_in_self_trait,
                // trait associated types are fully generic for now, we make a second pass
                // below
                Vec::new(),
                req.origin,
            );
        }

        // make a second pass to specify constraints on associated types
        // We do this in a second pass so that we can refer to the other associated types
        for req in requirements.iter().rev() {
            if req.is_self_in_trait_decl {
                continue;
            }

            // TODO: does that always work? Or do we get potentially cyclic problems because we
            // don't process requirements according to some dependency ordering?
            let translated_constraints: Vec<_> = req
                .assoc_constraints
                .iter()
                .map(|ty| ty.map(|ty| type_translator.translate_type_in_scope(self, typing_env, ty).unwrap()))
                .collect();

            // lookup the trait use
            let key = (
                TraitKey::rust(tcx, req.trait_ref.def_id),
                generate_args_inst_key(tcx, req.trait_ref.args).unwrap(),
            );
            let entry = &self.trait_scope.used_traits[&key];

            {
                let mut trait_use_ref = entry.trait_use.borrow_mut();
                let trait_use = trait_use_ref.as_mut().unwrap();
                // and add the constraints
                trait_use.assoc_ty_constraints = translated_constraints;
            }
        }

        // we make a third pass to finally resolve the scope of the trait, i.e. translate its args
        // and trait requirements
        for req in requirements.iter().rev() {
            if req.is_self_in_trait_decl {
                continue;
            }

            let key = (
                TraitKey::rust(tcx, req.trait_ref.def_id),
                generate_args_inst_key(tcx, req.trait_ref.args).unwrap(),
            );
            let entry = &self.trait_scope.used_traits[&key];

            // finalize the entry by adding dependencies on other trait parameters
            trait_registry.finalize_trait_use(entry, &*self, typing_env, req.trait_ref)?;
        }

        // make a final pass to precompute the paths to associated types and attributes
        for req in requirements {
            if req.is_self_in_trait_decl {
                continue;
            }

            let key = (
                TraitKey::rust(tcx, req.trait_ref.def_id),
                generate_args_inst_key(tcx, req.trait_ref.args).unwrap(),
            );
            let entry = &self.trait_scope.used_traits[&key];

            let assoc_tys = entry.get_associated_types(tcx);

            {
                let trait_use_ref = entry.trait_use.borrow();
                let trait_use = trait_use_ref.as_ref().unwrap();

                let self_ty = &trait_use.trait_inst.get_direct_ty_params()[0];
                let specs::Type::LiteralParam(self_param) = self_ty else {
                    // trait requirement for complex type, don't add shorthand notation
                    continue;
                };

                // iterate over all associated types
                for (name, ty) in assoc_tys {
                    let path = vec![
                        RustPathElem::AssocItem(self_param.rust_name.clone()),
                        RustPathElem::AssocItem(name.clone()),
                    ];
                    if let hash_map::Entry::Vacant(e) = self.trait_scope.assoc_ty_names.entry(path) {
                        e.insert(ty);
                    } else {
                        warn!("Associated type path collision on did={did:?} for name={name:?}");
                    }
                }

                // iterate over all attributes
                for attr in &trait_use.trait_ref.declared_attrs {
                    let term = trait_use.make_attr_item_term_in_spec(attr);
                    let path = vec![
                        RustPathElem::AssocItem(self_param.rust_name.clone()),
                        RustPathElem::AssocItem(attr.to_owned()),
                    ];
                    self.trait_scope.attribute_names.insert(path, term.to_string());
                }
            }
        }

        // finally, if we are in a trait declaration or impl declaration, add notation shorthands
        // to the scope
        if let Some(trait_did) = tcx.trait_of_assoc(did) {
            // we are in a trait declaration
            if let Some(trait_ref) = trait_registry.lookup_trait(trait_did) {
                // make the parameter for the attrs that the function is parametric over
                if let Some(trait_use_ref) = self.trait_scope.get_self_trait_use().cloned() {
                    // add the associated types
                    for (name, ty) in trait_use_ref.get_associated_types(tcx) {
                        let path = vec![RustPathElem::AssocItem(name.clone())];
                        if let hash_map::Entry::Vacant(e) = self.trait_scope.assoc_ty_names.entry(path) {
                            e.insert(ty);
                        } else {
                            warn!("Associated type path collision on did={did:?} for name={name:?}");
                        }
                    }

                    let trait_use_ref = trait_use_ref.trait_use.borrow();
                    let trait_use = trait_use_ref.as_ref().unwrap();
                    // add the corresponding record entries to the map
                    for attr in &trait_ref.declared_attrs {
                        let term = trait_use.make_attr_item_term_in_spec(attr);
                        let path = vec![RustPathElem::AssocItem(attr.to_owned())];
                        self.trait_scope.attribute_names.insert(path, term.to_string());
                    }
                }
            }
        }

        if let Some(impl_did) = tcx.impl_of_assoc(did)
            && tcx.impl_is_of_trait(impl_did)
        {
            // we are in a trait impl
            let (impl_ref, _, _) = trait_registry.get_trait_impl_info(impl_did)?;
            for attr in &impl_ref.of_trait.declared_attrs {
                let term = impl_ref.get_attr_record_item_term(attr);
                let path = vec![RustPathElem::AssocItem(attr.to_owned())];
                self.trait_scope.attribute_names.insert(path, term.to_string());
            }
        }

        // if we are declaring the trait itself, add the associated types of the trait to the scope
        // (we skip the self trait requirement above)
        if is_trait {
            let assoc_types = environment::get_trait_assoc_types(tcx, did);
            for ty_did in &assoc_types {
                let name = environment::get_assoc_item_name(tcx, *ty_did).unwrap();
                let path = vec![RustPathElem::AssocItem(name.clone())];
                let ty = specs::Type::LiteralParam(specs::LiteralTyParam::new(&name));
                if let hash_map::Entry::Vacant(e) = self.trait_scope.assoc_ty_names.entry(path) {
                    e.insert(ty);
                } else {
                    warn!("Associated type path collision on did={did:?} for name={name:?}");
                }
            }
        }
        Ok(())
    }

    /// Add a `ParamEnv` of a given `DefId` to the scope to process trait obligations.
    pub(crate) fn add_param_env(
        &mut self,
        did: DefId,
        tcx: ty::TyCtxt<'tcx>,
        type_translator: &TX<'def, 'tcx>,
        trait_registry: &registry::TR<'tcx, 'def>,
    ) -> Result<(), TranslationError> {
        trace!("Enter add_param_env for did = {did:?}");
        let typing_env = ty::TypingEnv::post_analysis(tcx, did);
        let requirements = requirements::get_trait_requirements_with_origin(tcx, did);

        self.add_lifetime_constraints(did, tcx, typing_env, type_translator)?;
        self.add_trait_requirements(did, tcx, type_translator, trait_registry, &requirements)?;
        self.add_implicit_drop_glue_assumptions(did, tcx, typing_env, trait_registry, &requirements)?;

        trace!("Leave add_param_env for did = {did:?} with trait scope {:?}", self.trait_scope);
        Ok(())
    }

    fn add_implicit_drop_glue_assumptions(
        &mut self,
        did: DefId,
        tcx: ty::TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        trait_registry: &registry::TR<'tcx, 'def>,
        requirements: &[requirements::TraitReqMeta<'tcx>],
    ) -> Result<(), TranslationError> {
        let mut ty_params = Vec::new();
        for (idx, param) in self.scope.iter().enumerate() {
            let Some(lit) = param.as_type() else { continue };
            let idx = u32::try_from(idx).map_err(|_err| {
                TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
                    "generic parameter index does not fit into u32: {idx}"
                ))))
            })?;
            ty_params.push((idx, Symbol::intern(&lit.rust_name)));
        }

        for (idx, name) in ty_params {
            let param_ty = ty::ParamTy::new(idx, name);
            let self_ty = tcx.mk_ty_from_kind(ty::TyKind::Param(param_ty));
            let origin = Self::determine_origin_of_param(did, tcx, param_ty);
            self.add_virtual_trait_assumption(
                tcx,
                typing_env,
                trait_registry,
                VirtualTrait::DropGlue,
                self_ty,
                origin,
            )?;
        }

        let mut assoc_tys = Vec::new();
        for req in requirements {
            if req.is_used_in_self_trait {
                continue;
            }

            let assoc_ty_dids = environment::get_trait_assoc_types(tcx, req.trait_ref.def_id);
            for (assoc_did, constraint) in assoc_ty_dids.into_iter().zip(&req.assoc_constraints) {
                if constraint.is_some() {
                    continue;
                }

                let alias = ty::AliasTy::new(
                    tcx,
                    ty::AliasTyKind::Projection { def_id: assoc_did },
                    req.trait_ref.args,
                );
                let self_ty = ty::Ty::new_alias(tcx, ty::IsRigid::No, alias);
                assoc_tys.push((self_ty, req.origin));
            }
        }

        for (self_ty, origin) in assoc_tys {
            self.add_virtual_trait_assumption(
                tcx,
                typing_env,
                trait_registry,
                VirtualTrait::DropGlue,
                self_ty,
                origin,
            )?;
        }

        let mut self_trait_assoc_tys = Vec::new();
        for req in requirements {
            if !req.is_used_in_self_trait {
                continue;
            }

            let assoc_ty_dids = environment::get_trait_assoc_types(tcx, req.trait_ref.def_id);
            for assoc_did in assoc_ty_dids {
                let alias = ty::AliasTy::new(
                    tcx,
                    ty::AliasTyKind::Projection { def_id: assoc_did },
                    req.trait_ref.args,
                );
                let self_ty = ty::Ty::new_alias(tcx, ty::IsRigid::No, alias);
                self_trait_assoc_tys.push(self_ty);
            }
        }

        for self_ty in self_trait_assoc_tys {
            self.add_virtual_trait_assumption(
                tcx,
                typing_env,
                trait_registry,
                VirtualTrait::DropGlue,
                self_ty,
                specs::TyParamOrigin::AssocInDecl,
            )?;
        }

        Ok(())
    }

    pub(crate) fn add_virtual_trait_assumption(
        &mut self,
        tcx: ty::TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        trait_registry: &registry::TR<'tcx, 'def>,
        virtual_trait: VirtualTrait,
        self_ty: ty::Ty<'tcx>,
        origin: specs::TyParamOrigin,
    ) -> Result<(), TranslationError> {
        let spec_ref = trait_registry.lookup_virtual_trait(virtual_trait).ok_or_else(|| {
            TranslationError::ErrorReported(tcx.dcx().err(Message::TraitResolution(format!(
                "virtual trait not registered with RefinedRust: {virtual_trait:?}"
            ))))
        })?;

        let trait_ref = match virtual_trait {
            VirtualTrait::DropGlue => registry::TraitUseRef::VirtualDropGlue { self_ty },
        };
        let key = (trait_ref.trait_key(tcx), trait_ref.args_for_key(tcx)?);
        if self.trait_scope.used_traits.contains_key(&key) {
            return Ok(());
        }

        let trait_use = trait_registry.make_empty_virtual_trait_use(virtual_trait, self_ty);
        self.trait_scope.used_traits.insert(key.clone(), trait_use);
        self.trait_scope.ordered_assumptions.push(key.clone());

        let entry = &self.trait_scope.used_traits[&key];
        registry::TR::fill_virtual_trait_use(entry, self_ty, spec_ref, origin);
        trait_registry.finalize_virtual_trait_use(entry, self, typing_env, self_ty)
    }
}

pub(crate) fn determine_origin_of_lft_param<'tcx>(
    did: DefId,
    tcx: ty::TyCtxt<'tcx>,
    param: ty::EarlyParamRegion,
) -> specs::LftParamOrigin {
    // Check if there is a surrounding trait decl that introduces this parameter
    if let Some(trait_did) = tcx.trait_of_assoc(did) {
        let generics: &'tcx ty::Generics = tcx.generics_of(trait_did);

        for this_param in &generics.own_params {
            if matches!(this_param.kind, ty::GenericParamDefKind::Lifetime)
                && this_param.name == param.name
                && this_param.index == param.index
            {
                return specs::LftParamOrigin::SurroundingTrait;
            }
        }
    }
    // Check if there is a surrounding trait impl that introduces this parameter
    if let Some(impl_did) = tcx.impl_of_assoc(did) {
        let generics: &'tcx ty::Generics = tcx.generics_of(impl_did);

        for this_param in &generics.own_params {
            if matches!(this_param.kind, ty::GenericParamDefKind::Lifetime)
                && this_param.name == param.name
                && this_param.index == param.index
            {
                return specs::LftParamOrigin::SurroundingImpl;
            }
        }
    }

    specs::LftParamOrigin::LocalEarlyBound
}

impl<'tcx> Params<'tcx, '_> {
    /// Determine the declaration origin of a type parameter of a function.
    fn determine_origin_of_param(
        did: DefId,
        tcx: ty::TyCtxt<'tcx>,
        param: ty::ParamTy,
    ) -> specs::TyParamOrigin {
        // Check if there is a surrounding trait decl that introduces this parameter
        if let Some(trait_did) = tcx.trait_of_assoc(did) {
            let generics: &'tcx ty::Generics = tcx.generics_of(trait_did);

            for this_param in &generics.own_params {
                if matches!(this_param.kind, ty::GenericParamDefKind::Type { .. })
                    && this_param.index == param.index
                {
                    return specs::TyParamOrigin::SurroundingTrait;
                }
            }
        }
        // Check if there is a surrounding trait impl that introduces this parameter
        if let Some(impl_did) = tcx.impl_of_assoc(did) {
            let generics: &'tcx ty::Generics = tcx.generics_of(impl_did);

            for this_param in &generics.own_params {
                if matches!(this_param.kind, ty::GenericParamDefKind::Type { .. })
                    && this_param.index == param.index
                {
                    return specs::TyParamOrigin::SurroundingImpl;
                }
            }
        }

        specs::TyParamOrigin::Direct
    }

    /// Determine the number of args of a surrounding trait or impl.
    pub(crate) fn determine_number_of_surrounding_params(did: DefId, tcx: ty::TyCtxt<'tcx>) -> usize {
        // Check if there is a surrounding trait decl that introduces this parameter
        if let Some(trait_did) = tcx.trait_of_assoc(did) {
            let generics: &'tcx ty::Generics = tcx.generics_of(trait_did);

            return generics.own_params.len();
        }
        // Check if there is a surrounding trait impl that introduces this parameter
        if let Some(impl_did) = tcx.impl_of_assoc(did) {
            let generics: &'tcx ty::Generics = tcx.generics_of(impl_did);

            return generics.own_params.len();
        }

        0
    }
}

impl From<&[ty::GenericParamDef]> for Params<'_, '_> {
    fn from(x: &[ty::GenericParamDef]) -> Self {
        let mut scope = Vec::new();

        let mut ty_names = HashMap::new();
        let mut lft_names = HashMap::new();

        for (num, p) in (0_u32..).zip(x) {
            let mut name = strip_coq_ident(p.name.as_str());
            if name == "_" {
                name = format!("p{num}");
            }

            let param = match p.kind {
                ty::GenericParamDefKind::Const { .. } => Param::Const,
                ty::GenericParamDefKind::Type { .. } => {
                    let lit = specs::LiteralTyParam::new(&name);
                    ty_names.insert(p.name.as_str().to_owned(), num);
                    Param::Ty(lit)
                },
                ty::GenericParamDefKind::Lifetime => {
                    let name = p.name.as_str().to_owned();
                    if name.as_str() == "'_" {
                        Param::Region(specs::LftParam::new(
                            coq::Ident::new(&format!("ulft_{}", num)),
                            specs::LftParamOrigin::LocalEarlyBound,
                        ))
                    } else {
                        let sanitized_name = name.replace('\'', "");
                        lft_names.insert(sanitized_name.clone(), scope.len());
                        Param::Region(specs::LftParam::new(
                            coq::Ident::new(&format!("ulft_{}", sanitized_name)),
                            specs::LftParamOrigin::LocalEarlyBound,
                        ))
                    }
                },
            };

            scope.push(param);
        }

        Self {
            scope,
            late_scope: Vec::new(),
            external_scope: Vec::new(),
            lft_names,
            ty_names,
            lifetime_inclusions: Vec::new(),
            trait_scope: Traits::default(),
        }
    }
}

/// A scope for translated trait requirements from `where` clauses.
#[derive(Clone, Debug, Default)]
pub(crate) struct Traits<'tcx, 'def> {
    used_traits: HashMap<(TraitKey, GenericsKey<'tcx>), GenericTraitUse<'tcx, 'def>>,
    ordered_assumptions: Vec<(TraitKey, GenericsKey<'tcx>)>,

    /// mapping of associated type paths in scope
    assoc_ty_names: HashMap<RustPath, specs::Type<'def>>,
    /// mapping of attribute paths which are in scope.
    /// Maps to a Coq expression describing this attribute in the current context.
    attribute_names: HashMap<RustPath, String>,
}

impl<'tcx, 'def> Traits<'tcx, 'def> {
    /// Lookup the trait use for a specific trait with given parameters.
    /// (here, args includes the self parameter as the first element)
    pub(crate) fn lookup_trait_use(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        trait_did: DefId,
        args: &[ty::GenericArg<'tcx>],
    ) -> &GenericTraitUse<'tcx, 'def> {
        if !tcx.is_trait(trait_did) {
            span_bug!(tcx.def_span(trait_did), "expected trait, found non-trait item");
        }

        let key = (TraitKey::rust(tcx, trait_did), generate_args_inst_key(tcx, args).unwrap());
        trace!("looking up trait use {key:?} in {:?}", self.used_traits);
        if let Some(trait_ref) = self.used_traits.get(&key) {
            trait_ref
        } else {
            span_bug!(
                tcx.def_span(trait_did),
                "could not find local instance for trait with generic args {:?}",
                tcx.mk_args(args)
            )
        }
    }

    pub(crate) fn lookup_virtual_trait_use(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        trait_key: VirtualTrait,
        args: &[ty::GenericArg<'tcx>],
    ) -> &GenericTraitUse<'tcx, 'def> {
        let key = (TraitKey::Virtual(trait_key), generate_args_inst_key(tcx, args).unwrap());
        trace!("looking up virtual trait use {key:?} in {:?}", self.used_traits);
        self.used_traits.get(&key).unwrap_or_else(|| {
            span_bug!(
                DUMMY_SP,
                "could not find local instance for virtual trait with generic args {:?}",
                tcx.mk_args(args)
            )
        })
    }

    /// Within a trait declaration, get the Self trait use.
    pub(crate) fn get_self_trait_use(&self) -> Option<&GenericTraitUse<'tcx, 'def>> {
        #[expect(clippy::iter_over_hash_type)]
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
