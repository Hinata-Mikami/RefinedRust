// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utility folders for handling type variables.

use std::collections::HashSet;

use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TypeSuperFoldable as _;

/// A `TypeFolder` that gathers all the type variables.
pub(crate) struct TyVarFolder<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    tyvars: HashSet<ty::ParamTy>,
    projections: HashSet<ty::AliasTy<'tcx>>,
}

impl<'tcx> TyVarFolder<'tcx> {
    pub(crate) fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        TyVarFolder {
            tcx,
            tyvars: HashSet::new(),
            projections: HashSet::new(),
        }
    }

    pub(crate) fn get_result(self) -> (HashSet<ty::ParamTy>, HashSet<ty::AliasTy<'tcx>>) {
        (self.tyvars, self.projections)
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
