// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utility folders for handling type variables.

use std::collections::{BTreeSet, HashSet};

use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::{RegionExt as _, TypeSuperFoldable as _};
use rr_rustc_interface::type_ir::TypeFoldable as _;

use crate::{rustcmp, traits};

/// A `TypeFolder` that gathers all the type variables.
pub(crate) struct TyVarFolder<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    /// The caller's environment, used to resolve concrete associated types before collecting dependencies.
    typing_env: ty::TypingEnv<'tcx>,
    tyvars: BTreeSet<ty::ParamTy>,
    projections: HashSet<ty::AliasTy<'tcx>>,
}

impl<'tcx> TyVarFolder<'tcx> {
    pub(crate) fn new(tcx: ty::TyCtxt<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Self {
        TyVarFolder {
            tcx,
            typing_env,
            tyvars: BTreeSet::new(),
            projections: HashSet::new(),
        }
    }

    pub(crate) fn get_result(self) -> (BTreeSet<ty::ParamTy>, Vec<ty::AliasTy<'tcx>>) {
        // We first need to order the aliases
        let mut ordered_projections: Vec<_> = self.projections.into_iter().collect();

        ordered_projections.sort_by(|a, b| rustcmp::cmp_alias_ty(self.tcx, a, b));

        (self.tyvars, ordered_projections)
    }
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for TyVarFolder<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    // TODO: handle the case that we pass below binders
    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_ty(&mut self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        match t.kind() {
            ty::TyKind::Param(param) => {
                self.tyvars.insert(*param);
                t
            },
            ty::TyKind::Alias(_, alias_ty) if matches!(alias_ty.kind, ty::AliasTyKind::Projection { .. }) => {
                // Try to normalize aliases first; if we can normalize, fold the normalized type.
                // As a guard to avoid infinite recursion, only recurse if the normalize type is
                // different.
                if let Ok(normalized_ty) = traits::resolution::normalize_type(self.tcx, self.typing_env, t)
                    && normalized_ty != t
                {
                    normalized_ty.fold_with(self);
                } else {
                    self.projections.insert(*alias_ty);
                }

                t
            },
            _ => t.super_fold_with(self),
        }
    }
}

/// A `TypeFolder` that erases all regions.
pub(crate) struct TyRegionEraseFolder<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> TyRegionEraseFolder<'tcx> {
    pub(crate) const fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        TyRegionEraseFolder { tcx }
    }
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for TyRegionEraseFolder<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    // TODO: handle the case that we pass below binders
    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_region(&mut self, _: ty::Region<'tcx>) -> ty::Region<'tcx> {
        ty::Region::new_from_kind(self.cx(), ty::RegionKind::ReErased)
    }
}
