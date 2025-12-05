// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utility folders for handling type variables.

use std::collections::{BTreeSet, HashSet};

use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TypeSuperFoldable as _;

use crate::environment::Environment;
use crate::rustcmp;

/// A `TypeFolder` that gathers all the type variables.
pub(crate) struct TyVarFolder<'def, 'tcx> {
    env: &'def Environment<'tcx>,
    tyvars: BTreeSet<ty::ParamTy>,
    projections: HashSet<ty::AliasTy<'tcx>>,
}

impl<'def, 'tcx> TyVarFolder<'def, 'tcx> {
    pub(crate) fn new(env: &'def Environment<'tcx>) -> Self {
        TyVarFolder {
            env,
            tyvars: BTreeSet::new(),
            projections: HashSet::new(),
        }
    }

    pub(crate) fn get_result(self) -> (BTreeSet<ty::ParamTy>, Vec<ty::AliasTy<'tcx>>) {
        // We first need to order the aliases
        let mut ordered_projections: Vec<_> = self.projections.into_iter().collect();

        ordered_projections.sort_by(|a, b| rustcmp::cmp_alias_ty(self.env, a, b));

        (self.tyvars, ordered_projections)
    }
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for TyVarFolder<'_, 'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.env.tcx()
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
            ty::TyKind::Alias(kind, ty) => {
                if *kind == ty::AliasTyKind::Projection {
                    self.projections.insert(*ty);
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
