use std::cmp::Ordering;

use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use rr_rustc_utils::{RustcComparator, cmp_def_id_by_path};

use crate::base::LogicalDefKey;

fn comparator<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
) -> RustcComparator<'tcx, impl Fn(ty::TyCtxt<'tcx>, DefId, DefId) -> Ordering> {
    RustcComparator::new(tcx, cmp_defid)
}

pub(crate) fn cmp_defid(tcx: ty::TyCtxt<'_>, a: DefId, b: DefId) -> Ordering {
    LogicalDefKey::new(tcx, a)
        .cmp(&LogicalDefKey::new(tcx, b))
        .then_with(|| cmp_def_id_by_path(tcx, a, b))
}

pub(crate) fn cmp_tys<'tcx>(tcx: ty::TyCtxt<'tcx>, a: &[ty::Ty<'tcx>], b: &[ty::Ty<'tcx>]) -> Ordering {
    comparator(tcx).cmp_tys(a, b)
}

/// Compare two `TraitRef`s deterministically, giving a consistent order stable across compilations.
pub(crate) fn cmp_trait_ref<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    in_trait_decl: Option<DefId>,
    a: &ty::TraitRef<'tcx>,
    b: &ty::TraitRef<'tcx>,
) -> Ordering {
    // Put the current trait after its dependencies.
    if let Some(trait_did) = in_trait_decl {
        if a.def_id == trait_did && a.args[0].expect_ty().is_param(0) {
            return Ordering::Greater;
        }
        if b.def_id == trait_did && b.args[0].expect_ty().is_param(0) {
            return Ordering::Less;
        }
    }

    let comparator = comparator(tcx);
    comparator
        .cmp_def_id(a.def_id, b.def_id)
        .then_with(|| comparator.cmp_generic_args(a.args.as_slice(), b.args.as_slice()))
}

pub(crate) fn cmp_alias_ty<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    a: &ty::AliasTy<'tcx>,
    b: &ty::AliasTy<'tcx>,
) -> Ordering {
    comparator(tcx).cmp_alias_ty(a, b)
}
