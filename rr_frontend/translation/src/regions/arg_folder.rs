// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use rr_rustc_interface::middle::ty;
use rr_rustc_interface::type_ir::{TypeFoldable, TypeSuperFoldable as _, TypeVisitableExt as _};

use crate::environment::polonius_info::PoloniusInfo;
use crate::regions;
use crate::regions::EarlyLateRegionMap;

pub(crate) fn relabel_erased_regions<'tcx, T>(x: T, tcx: ty::TyCtxt<'tcx>) -> (T, usize)
where
    T: TypeFoldable<ty::TyCtxt<'tcx>>,
{
    let mut folder = RegionRelabelVisitor {
        tcx,
        new_regions: 0_usize,
    };
    (x.fold_with(&mut folder), folder.new_regions)
}

/// Relabel erased regions into `RegionVid`s.
struct RegionRelabelVisitor<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    new_regions: usize,
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for RegionRelabelVisitor<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match r.kind() {
            ty::ReErased => {
                let new_idx = self.new_regions;
                self.new_regions += 1;

                ty::Region::new_var(self.cx(), ty::RegionVid::from(new_idx))
            },
            _ => r,
        }
    }
}

pub(crate) fn rename_closure_capture_regions<'tcx, 'a, T>(
    x: T,
    tcx: ty::TyCtxt<'tcx>,
    substitution: &'a mut EarlyLateRegionMap<'_>,
    info: &'a PoloniusInfo<'a, 'tcx>,
) -> T
where
    T: TypeFoldable<ty::TyCtxt<'tcx>>,
{
    let mut folder = ClosureCaptureRegionVisitor {
        tcx,
        substitution,
        info,
    };
    x.fold_with(&mut folder)
}

/// Rename the regions appearing in closure captures to use the universal regions.
struct ClosureCaptureRegionVisitor<'a, 'def, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    substitution: &'a mut EarlyLateRegionMap<'def>,
    info: &'a PoloniusInfo<'a, 'tcx>,
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for ClosureCaptureRegionVisitor<'_, '_, 'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match r.kind() {
            ty::ReVar(v) => {
                // We need to do some hacks here to find the right Polonius region:
                // `r` is the non-placeholder region that the variable gets, but we are
                // looking for the corresponding placeholder region
                let r2 = regions::init::find_placeholder_region_for(v.into(), self.info).unwrap();

                let lft = self.info.mk_atomic_region(r2);
                self.substitution.ensure_closure_region(lft);

                ty::Region::new_var(self.cx(), r2.into())
            },
            _ => r,
        }
    }
}

/// Find the regions mentioned in the captures of a closure
pub(crate) struct ClosureCaptureRegionCollector<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    regions: Vec<ty::Region<'tcx>>,
}
impl<'tcx> ClosureCaptureRegionCollector<'tcx> {
    pub(crate) const fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            regions: vec![],
        }
    }

    pub(crate) fn result(self) -> Vec<ty::Region<'tcx>> {
        self.regions
    }
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for ClosureCaptureRegionCollector<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        self.regions.push(r);
        r
    }
}

pub(crate) fn rename_region_vids<'tcx, T>(x: T, tcx: ty::TyCtxt<'tcx>, map: Vec<ty::Region<'tcx>>) -> T
where
    T: TypeFoldable<ty::TyCtxt<'tcx>>,
{
    let mut folder = RegionRenameVisitor {
        tcx,
        rename_map: map,
    };
    x.fold_with(&mut folder)
}
/// Rename `RegionVid`s.
struct RegionRenameVisitor<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    rename_map: Vec<ty::Region<'tcx>>,
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for RegionRenameVisitor<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match r.kind() {
            ty::ReVar(v) => {
                let idx = v.index();
                self.rename_map[idx]
            },
            _ => r,
        }
    }
}

/// Relable late bound regions.
pub(crate) fn relabel_late_bounds<'tcx, T>(x: T, tcx: ty::TyCtxt<'tcx>) -> T
where
    T: TypeFoldable<ty::TyCtxt<'tcx>>,
{
    let mut folder = RelabelLateParamVisitor { tcx };
    x.fold_with(&mut folder)
}

/// Rename `RegionVid`s.
struct RelabelLateParamVisitor<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for RelabelLateParamVisitor<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match r.kind() {
            ty::ReBound(_idx, _) => {
                //let idx = v.index();
                //let new_idx = self.rename_map.get(idx).unwrap();

                //new_idx.to_owned()
                ty::Region::new_from_kind(self.cx(), ty::ReErased)
            },
            _ => r,
        }
    }
}

/// Instantiate a type with arguments.
/// The type may contain open region variables `ReVar`.
pub(crate) fn instantiate_open<'tcx, T>(x: T, tcx: ty::TyCtxt<'tcx>, args: &[ty::GenericArg<'tcx>]) -> T
where
    T: TypeFoldable<ty::TyCtxt<'tcx>>,
{
    let mut folder = ArgFolder {
        tcx,
        args,
        binders_passed: 0,
    };
    x.fold_with(&mut folder)
}

/// A version of the `ArgFolder` in `rr_rustc_interface::middle::src::ty::generic_args` that skips over
/// `ReVar` (instead of triggering a bug).
struct ArgFolder<'a, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    args: &'a [ty::GenericArg<'tcx>],

    /// Number of region binders we have passed through while doing the substitution
    binders_passed: u32,
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for ArgFolder<'_, 'tcx> {
    #[inline]
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_binder<T: TypeFoldable<ty::TyCtxt<'tcx>>>(
        &mut self,
        t: ty::Binder<'tcx, T>,
    ) -> ty::Binder<'tcx, T> {
        self.binders_passed += 1;
        let t = t.super_fold_with(self);
        self.binders_passed -= 1;
        t
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        #[cold]
        #[inline(never)]
        fn region_param_out_of_range(data: ty::EarlyParamRegion, args: &[ty::GenericArg<'_>]) -> ! {
            panic!(
                "Region parameter out of range when substituting in region {} (index={}, args = {:?})",
                data.name, data.index, args,
            )
        }

        #[cold]
        #[inline(never)]
        fn region_param_invalid(data: ty::EarlyParamRegion, other: &ty::GenericArgKind<'_>) -> ! {
            panic!(
                "Unexpected parameter {:?} when substituting in region {} (index={})",
                other, data.name, data.index
            )
        }

        // Note: This routine only handles regions that are bound on
        // type declarations and other outer declarations, not those
        // bound in *fn types*. Region substitution of the bound
        // regions that appear in a function signature is done using
        // the specialized routine `ty::replace_late_regions()`.
        match r.kind() {
            ty::ReEarlyParam(data) => {
                let rk = self.args.get(data.index as usize).map(|k| k.kind());
                match rk {
                    Some(ty::GenericArgKind::Lifetime(lt)) => self.shift_region_through_binders(lt),
                    Some(other) => region_param_invalid(data, &other),
                    None => region_param_out_of_range(data, self.args),
                }
            },

            ty::ReBound(..)
            | ty::ReLateParam(_)
            | ty::ReStatic
            | ty::RePlaceholder(_)
            | ty::ReErased
            | ty::ReError(_)
            | ty::ReVar(_) => r,
        }
    }

    fn fold_ty(&mut self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        if !t.has_param() {
            return t;
        }

        match *t.kind() {
            ty::Param(p) => self.ty_for_param(p, t),
            _ => t.super_fold_with(self),
        }
    }
}

impl<'tcx> ArgFolder<'_, 'tcx> {
    fn ty_for_param(&self, p: ty::ParamTy, source_ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        // Look up the type in the args. It really should be in there.
        let opt_ty = self.args.get(p.index as usize).map(|k| k.kind());
        let ty = match opt_ty {
            Some(ty::GenericArgKind::Type(ty)) => ty,
            Some(kind) => self.type_param_expected(p, source_ty, &kind),
            None => self.type_param_out_of_range(p, source_ty),
        };

        self.shift_vars_through_binders(ty)
    }

    #[cold]
    #[inline(never)]
    fn type_param_expected(&self, p: ty::ParamTy, ty: ty::Ty<'tcx>, kind: &ty::GenericArgKind<'tcx>) -> ! {
        panic!(
            "expected type for `{:?}` ({:?}/{}) but found {:?} when substituting, args={:?}",
            p, ty, p.index, kind, self.args,
        )
    }

    #[cold]
    #[inline(never)]
    fn type_param_out_of_range(&self, p: ty::ParamTy, ty: ty::Ty<'tcx>) -> ! {
        panic!(
            "type parameter `{:?}` ({:?}/{}) out of range when substituting, args={:?}",
            p, ty, p.index, self.args,
        )
    }

    /// It is sometimes necessary to adjust the De Bruijn indices during substitution. This occurs
    /// when we are substituting a type with escaping bound vars into a context where we have
    /// passed through binders. That's quite a mouthful. Let's see an example:
    ///
    /// ```
    /// type Func<A> = fn(A);
    /// type MetaFunc = for<'a> fn(Func<&'a i32>);
    /// ```
    ///
    /// The type `MetaFunc`, when fully expanded, will be
    /// ```ignore (illustrative)
    /// for<'a> fn(fn(&'a i32))
    /// //      ^~ ^~ ^~~
    /// //      |  |  |
    /// //      |  |  DebruijnIndex of 2
    /// //      Binders
    /// ```
    /// Here the `'a` lifetime is bound in the outer function, but appears as an argument of the
    /// inner one. Therefore, that appearance will have a `DebruijnIndex` of 2, because we must skip
    /// over the inner binder (remember that we count De Bruijn indices from 1). However, in the
    /// definition of `MetaFunc`, the binder is not visible, so the type `&'a i32` will have a
    /// De Bruijn index of 1. It's only during the substitution that we can see we must increase the
    /// depth by 1 to account for the binder that we passed through.
    ///
    /// As a second example, consider this twist:
    ///
    /// ```
    /// type FuncTuple<A> = (A, fn(A));
    /// type MetaFuncTuple = for<'a> fn(FuncTuple<&'a i32>);
    /// ```
    ///
    /// Here the final type will be:
    /// ```ignore (illustrative)
    /// for<'a> fn((&'a i32, fn(&'a i32)))
    /// //          ^~~         ^~~
    /// //          |           |
    /// //   DebruijnIndex of 1 |
    /// //               DebruijnIndex of 2
    /// ```
    /// As indicated in the diagram, here the same type `&'a i32` is substituted once, but in the
    /// first case we do not increase the De Bruijn index and in the second case we do. The reason
    /// is that only in the second case have we passed through a fn binder.
    fn shift_vars_through_binders<T: TypeFoldable<ty::TyCtxt<'tcx>>>(&self, val: T) -> T {
        if self.binders_passed == 0 || !val.has_escaping_bound_vars() {
            return val;
        }

        ty::shift_vars(ty::TypeFolder::cx(self), val, self.binders_passed)
    }

    fn shift_region_through_binders(&self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if self.binders_passed == 0 || !region.has_escaping_bound_vars() {
            return region;
        }
        ty::shift_region(self.tcx, region, self.binders_passed)
    }
}
