use rr_rustc_interface::middle::ty::{self, TyCtxt};
/// From rustc, under the MIT license.
pub(crate) use rr_rustc_interface::type_ir::{TypeFoldable, TypeFolder, TypeSuperFoldable};

/// Folds over the substructure of a type, visiting its component
/// types and all regions that occur *free* within it.
///
/// That is, function pointer types and trait object can introduce
/// new bound regions which are not visited by this visitors as
/// they are not free; only regions that occur free will be
/// visited by `fld_r`.
pub(crate) struct RegionFolder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,

    /// Stores the index of a binder *just outside* the stuff we have
    /// visited. So this begins as INNERMOST; when we pass through a
    /// binder, it is incremented (via `shift_in`).
    current_index: ty::DebruijnIndex,

    /// Callback invokes for each free region. The `DebruijnIndex`
    /// points to the binder *just outside* the ones we have passed
    /// through.
    fold_region_fn: &'a mut (dyn FnMut(ty::Region<'tcx>, ty::DebruijnIndex) -> ty::Region<'tcx> + 'a),
}

impl<'a, 'tcx> RegionFolder<'a, 'tcx> {
    #[inline]
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        fold_region_fn: &'a mut dyn FnMut(ty::Region<'tcx>, ty::DebruijnIndex) -> ty::Region<'tcx>,
    ) -> Self {
        RegionFolder {
            tcx,
            current_index: ty::INNERMOST,
            fold_region_fn,
        }
    }
}

impl<'tcx> TypeFolder<TyCtxt<'tcx>> for RegionFolder<'_, 'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_binder<T: TypeFoldable<TyCtxt<'tcx>>>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T> {
        self.current_index.shift_in(1);
        let t = t.super_fold_with(self);
        self.current_index.shift_out(1);
        t
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match r.kind() {
            ty::ReBound(debruijn, _) if debruijn < self.current_index => {
                //debug!(?self.current_index, "skipped bound region");
                r
            },
            _ => {
                //debug!(?self.current_index, "folding free region");
                (self.fold_region_fn)(r, self.current_index)
            },
        }
    }
}
