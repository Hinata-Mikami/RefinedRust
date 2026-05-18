// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Body-level facade for Polonius-backed region information.

use log::info;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TypeFoldable;

use super::{
    AnnotationGenerator, EarlyLateRegionMap, RegionBiFolder as _, RegionVarResolver, arg_folder, init,
};
use crate::environment;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::traits::registry::RegionUnifier;

pub(crate) struct BodyRegionContext<'a, 'tcx> {
    info: &'a PoloniusInfo<'a, 'tcx>,
}

impl<'a, 'tcx: 'a> BodyRegionContext<'a, 'tcx> {
    pub(crate) fn new(procedure: &'a Procedure<'tcx>) -> Self {
        let info = PoloniusInfo::new(procedure);

        // TODO: avoid leak by making AnnotationGenerator own the Polonius-backed state.
        let info: &'a PoloniusInfo<'_, '_> = &*Box::leak(Box::new(info));

        Self { info }
    }

    pub(crate) fn dump_borrowck_info_if_enabled(&self, tcx: ty::TyCtxt<'tcx>, did: DefId) {
        if rrconfig::dump_borrowck_info() {
            environment::dump_borrowck_info(tcx, did, self.info);
        }
    }

    pub(crate) fn normalize_fn_sig<'def>(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        params: &[ty::GenericArg<'tcx>],
        of_did: DefId,
        sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
    ) -> (Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>, EarlyLateRegionMap<'def>) {
        self.normalize_fn_sig_with_additional_late_bounds(tcx, params, of_did, sig, 0)
    }

    pub(crate) fn normalize_fn_sig_with_additional_late_bounds<'def>(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        params: &[ty::GenericArg<'tcx>],
        of_did: DefId,
        sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
        additional_late_bounds: usize,
    ) -> (Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>, EarlyLateRegionMap<'def>) {
        let num_late_bounds = sig.bound_vars().len() + additional_late_bounds;
        init::replace_body_fnsig_args_with_polonius_vars(tcx, params, of_did, sig, self.info, num_late_bounds)
    }

    pub(crate) fn normalize_trait_impl_expected_sig<'def>(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        params: &[ty::GenericArg<'tcx>],
        of_did: DefId,
        actual_sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
        expected_sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
    ) -> (Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>, EarlyLateRegionMap<'def>) {
        let (direct_inputs, direct_output, _) = self.normalize_fn_sig(tcx, params, of_did, actual_sig);

        info!("direct signature: {direct_inputs:?} -> {direct_output:?}");

        let (inputs, output, mut mapping) = init::replace_body_fnsig_args_with_polonius_vars(
            tcx,
            params,
            of_did,
            expected_sig,
            self.info,
            actual_sig.bound_vars().len(),
        );

        // Now unify the two signatures.
        let typing_env = ty::TypingEnv::post_analysis(tcx, of_did);
        let mut unifier = RegionUnifier::new(tcx, typing_env);
        // Since we cannot reliably normalize here without erasing regions, ignore aliases for now.
        unifier.ignore_aliases();

        unifier.map_ty_slices(&direct_inputs, &inputs);
        unifier.map_tys(direct_output, output);
        let (_, vid_mapping) = unifier.get_result();

        info!("region mapping: {vid_mapping:?}");
        for (from, to) in vid_mapping {
            let to = to.as_var();
            if from != to {
                mapping.insert_vid_fixup(from.into(), to.into());
            }
        }
        // TODO: also add the equality constraints to the inclusion tracker?

        (inputs, output, mapping)
    }

    pub(crate) fn rename_closure_capture_regions<T>(
        &self,
        x: T,
        tcx: ty::TyCtxt<'tcx>,
        substitution: &mut EarlyLateRegionMap<'_>,
    ) -> T
    where
        T: TypeFoldable<ty::TyCtxt<'tcx>>,
    {
        arg_folder::rename_closure_capture_regions(x, tcx, substitution, self.info)
    }

    pub(crate) fn region_var_resolver(&self) -> RegionVarResolver {
        self.info.region_var_resolver()
    }

    pub(crate) fn annotation_generator(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        lifetime_scope: &EarlyLateRegionMap<'_>,
    ) -> AnnotationGenerator<'a, 'tcx> {
        AnnotationGenerator::new(tcx, lifetime_scope, self.info)
    }
}
