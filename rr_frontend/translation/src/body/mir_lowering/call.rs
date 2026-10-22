// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use radium::{code, specs};
use rr_rustc_interface::middle::ty;

/// Project a method specification from a concretely selected implementation realization.
pub(crate) fn make_realized_method_spec<'def>(
    impl_: &specs::traits::SpecializedImpl<'def>,
    trait_spec: specs::traits::LiteralSpecRef<'def>,
    method_name: &str,
    method_scope_inst: specs::traits::ReqScopeInst,
) -> code::UsedProcedureSpec<'def> {
    code::UsedProcedureSpec::RealizedMethod(specs::traits::RealizedMethodSpecUse::from_specialized_impl(
        impl_,
        trait_spec,
        method_name.to_owned(),
        method_scope_inst,
    ))
}

/// Use a realized method specification when available, retaining the literal specification as a
/// fallback while realization metadata is rolled out.
pub(crate) fn realized_method_or_literal<'def>(
    realized: Option<code::UsedProcedureSpec<'def>>,
    literal_spec: &str,
) -> code::UsedProcedureSpec<'def> {
    realized.unwrap_or_else(|| code::UsedProcedureSpec::Literal(literal_spec.to_owned()))
}

pub(crate) struct TraitMethodUseData<'def> {
    pub loc_name: String,
    pub spec_term: code::UsedProcedureSpec<'def>,
    pub spec_scope: specs::traits::ReqScope,
    pub spec_inst: specs::traits::ReqScopeInst,
}

pub(crate) fn make_trait_method_use_data<'def>(
    trait_use_ref: specs::traits::LiteralSpecUseRef<'def>,
    method_name: &str,
    loc_method_name: &str,
    bound_region_inst: impl IntoIterator<Item = specs::Lft>,
) -> TraitMethodUseData<'def> {
    let spec_inst = specs::traits::ReqScopeInst::new(bound_region_inst.into_iter().collect());

    let (loc_name, spec_scope) = {
        let trait_spec_use = trait_use_ref.borrow();
        let trait_spec_use = trait_spec_use.as_ref().unwrap();
        (trait_spec_use.make_loc_name(loc_method_name), trait_spec_use.scope.clone())
    };

    let quantified_impl =
        specs::traits::QuantifiedImpl::new(trait_use_ref, spec_scope.identity_instantiation());
    let spec_term = code::UsedProcedureSpec::TraitMethod(quantified_impl, method_name.to_owned());

    TraitMethodUseData {
        loc_name,
        spec_term,
        spec_scope,
        spec_inst,
    }
}

pub(crate) struct ProcedureInst<'tcx, 'def> {
    pub method_params: ty::GenericArgsRef<'tcx>,
    pub type_hint: Vec<specs::Type<'def>>,
    pub lft_hint: Vec<specs::Lft>,
    pub num_of_latebounds: usize,
    pub expected_num_lft_hints: Option<usize>,
    pub mapped_early_regions: BTreeMap<specs::Lft, usize>,
}
