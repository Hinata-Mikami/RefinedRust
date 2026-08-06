// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides functionality for generating lifetime annotations for assignments.

use std::collections::{BTreeMap, BTreeSet};
use std::mem;

use log::{info, trace, warn};
use radium::{code, coq, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::type_ir::TypeFoldable as _;

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::error::Message;
use crate::regions::RegionBiFolder as _;
use crate::regions::inclusion_tracker::{self, InclusionTracker};
use crate::{regions, types};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AssignmentRegionSource<'tcx> {
    Var(Region),
    Named(ty::Region<'tcx>),
}

struct AssignmentRegionMapper<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mappings: BTreeMap<Region, Vec<AssignmentRegionSource<'tcx>>>,
    error: Option<String>,
}

impl<'tcx> AssignmentRegionMapper<'tcx> {
    const fn new(tcx: ty::TyCtxt<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Self {
        Self {
            tcx,
            typing_env,
            mappings: BTreeMap::new(),
            error: None,
        }
    }

    fn record(&mut self, destination: Region, source: AssignmentRegionSource<'tcx>) {
        if self.error.is_some() {
            return;
        }

        let sources = self.mappings.entry(destination).or_default();
        if !sources.contains(&source) {
            sources.push(source);
        }
    }
}

pub(crate) fn map_regions_between_types<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    did: DefId,
    source_ty: ty::Ty<'tcx>,
    destination_ty: ty::Ty<'tcx>,
) -> Result<BTreeMap<Region, Vec<AssignmentRegionSource<'tcx>>>, TranslationError> {
    let typing_env = ty::TypingEnv::post_analysis(tcx, did);
    let source_ty = types::normalize_in_function(did, tcx, source_ty)?;
    let destination_ty = types::normalize_in_function(did, tcx, destination_ty)?;
    let mut mapper = AssignmentRegionMapper::new(tcx, typing_env);
    mapper.map_tys(source_ty, destination_ty);
    if let Some(error) = mapper.error {
        return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(error))));
    }
    Ok(mapper.mappings)
}

fn get_strong_assignment_mappings<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    did: DefId,
    rhs_ty: ty::Ty<'tcx>,
    lhs_ty: ty::Ty<'tcx>,
) -> Result<BTreeMap<Region, AssignmentRegionSource<'tcx>>, TranslationError> {
    let raw_mappings = map_regions_between_types(tcx, did, rhs_ty, lhs_ty)?;
    let mut mappings = BTreeMap::new();
    for (destination, sources) in raw_mappings {
        let mut sources = sources.into_iter();
        let Some(source) = sources.next() else {
            continue;
        };
        if let Some(other) = sources.next() {
            return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                format!(
                    "strong assignment maps destination region {destination:?} from both {source:?} and {other:?}"
                ),
            ))));
        }
        if !matches!(source, AssignmentRegionSource::Var(source) if source == destination) {
            mappings.insert(destination, source);
        }
    }
    Ok(mappings)
}

fn register_strong_assignment_effects(
    inclusion_tracker: &mut InclusionTracker<'_, '_>,
    midpoint: facts::PointIndex,
    mappings: &BTreeMap<Region, AssignmentRegionSource<'_>>,
) -> Result<(), Vec<Region>> {
    order_strong_updates(mappings)?;
    for destination in mappings.keys() {
        inclusion_tracker.add_barrier(*destination, midpoint);
        inclusion_tracker.add_known_region(*destination, midpoint);
    }
    for (destination, source) in mappings {
        if let AssignmentRegionSource::Var(source) = source
            && !mappings.contains_key(source)
        {
            inclusion_tracker.add_static_inclusion(*source, *destination, midpoint);
            inclusion_tracker.add_static_inclusion(*destination, *source, midpoint);
        }
    }
    Ok(())
}

fn register_strong_assignment_edge_effects(
    inclusion_tracker: &mut InclusionTracker<'_, '_>,
    from: facts::PointIndex,
    to: facts::PointIndex,
    mappings: &BTreeMap<Region, AssignmentRegionSource<'_>>,
) -> Result<(), Vec<Region>> {
    order_strong_updates(mappings)?;
    for destination in mappings.keys() {
        inclusion_tracker.add_edge_pre_barrier(*destination, from, to);
        inclusion_tracker.add_edge_known_region(*destination, from, to);
    }
    for (destination, source) in mappings {
        if let AssignmentRegionSource::Var(source) = source
            && !mappings.contains_key(source)
        {
            inclusion_tracker.add_edge_static_inclusion(*source, *destination, from, to);
            inclusion_tracker.add_edge_static_inclusion(*destination, *source, from, to);
        }
    }
    Ok(())
}

/// Register strong-update effects before block-local annotation decisions are made.
pub(crate) fn preregister_strong_assignment<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    did: DefId,
    midpoint: facts::PointIndex,
    lhs_ty: ty::Ty<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
) -> Result<(), TranslationError> {
    let mappings = get_strong_assignment_mappings(tcx, did, rhs_ty, lhs_ty)?;
    register_strong_assignment_effects(inclusion_tracker, midpoint, &mappings).map_err(|cycle| {
        TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "cyclic strong lifetime update involving regions {cycle:?}"
        ))))
    })
}

pub(crate) fn preregister_strong_assignment_on_edge<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    did: DefId,
    from: facts::PointIndex,
    to: facts::PointIndex,
    lhs_ty: ty::Ty<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
) -> Result<(), TranslationError> {
    let mappings = get_strong_assignment_mappings(tcx, did, rhs_ty, lhs_ty)?;
    register_strong_assignment_edge_effects(inclusion_tracker, from, to, &mappings).map_err(|cycle| {
        TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "cyclic strong lifetime update involving regions {cycle:?}"
        ))))
    })
}

impl<'tcx> regions::RegionBiFolder<'tcx> for AssignmentRegionMapper<'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn typing_env(&self) -> &ty::TypingEnv<'tcx> {
        &self.typing_env
    }

    fn examine_ty(&mut self, source: ty::Ty<'tcx>, destination: ty::Ty<'tcx>) -> bool {
        if let (
            ty::TyKind::Closure(source_def, source_args),
            ty::TyKind::Closure(destination_def, destination_args),
        ) = (source.kind(), destination.kind())
        {
            if source_def == destination_def {
                self.map_ty_slices(
                    source_args.as_closure().upvar_tys(),
                    destination_args.as_closure().upvar_tys(),
                );
            } else {
                self.error = Some(format!(
                    "strong assignment maps different closure types: {source:?} and {destination:?}"
                ));
            }
            return false;
        }

        let mut collector = regions::TyRegionCollectFolder::new(self.tcx);
        destination.fold_with(&mut collector);
        if collector.get_regions().is_empty() {
            return false;
        }

        if mem::discriminant(source.kind()) == mem::discriminant(destination.kind()) {
            return true;
        }

        self.error = Some(format!(
            "strong-assignment types have different shapes at a lifetime-bearing position: {source:?} and {destination:?}"
        ));
        false
    }

    fn map_regions(&mut self, r1: ty::Region<'tcx>, r2: ty::Region<'tcx>) {
        let (source, destination) = (r1, r2);
        let ty::RegionKind::ReVar(destination) = destination.kind() else {
            if source != destination {
                self.error = Some(format!(
                    "strong assignment maps non-variable destination region {destination:?} from {source:?}"
                ));
            }
            return;
        };

        let destination = destination.into();
        let source = match source.kind() {
            ty::RegionKind::ReVar(source) => AssignmentRegionSource::Var(source.into()),
            _ => AssignmentRegionSource::Named(source),
        };
        self.record(destination, source);
    }
}

fn order_strong_updates(
    mappings: &BTreeMap<Region, AssignmentRegionSource<'_>>,
) -> Result<Vec<Region>, Vec<Region>> {
    let mut remaining: BTreeSet<_> = mappings.keys().copied().collect();
    let mut ordered = Vec::with_capacity(remaining.len());

    while !remaining.is_empty() {
        let next = remaining.iter().copied().find(|candidate| {
            !remaining.iter().any(|other| {
                other != candidate
                    && matches!(mappings.get(other), Some(AssignmentRegionSource::Var(source)) if source == candidate)
            })
        });

        let Some(next) = next else {
            return Err(remaining.into_iter().collect());
        };
        remaining.remove(&next);
        ordered.push(next);
    }

    Ok(ordered)
}

/// Generate inclusions for a weak update assignment.
fn get_assignment_weak_update_constraints(
    inclusion_tracker: &InclusionTracker<'_, '_>,
    constraint_point: facts::PointIndex,
    effect_point: facts::PointIndex,
    lhs_regions: &BTreeSet<Region>,
) -> BTreeSet<(Region, Region, PointIndex)> {
    let info = inclusion_tracker.info();
    let mut constraints = BTreeSet::new();

    // A point may also contain constraints used to type dereferences on the path to the assigned
    // place. Only inclusions into lifetime positions actually stored in the LHS are relevant to
    // the weak update.
    for (s1, s2) in info.subset_base_at(constraint_point) {
        if lhs_regions.contains(&s2) {
            constraints.insert((s1, s2, effect_point));
        }
    }
    constraints
}

pub(crate) fn get_assignment_dynamic_requirements<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &InclusionTracker<'_, 'tcx>,
    constraint_point: facts::PointIndex,
    effect_point: facts::PointIndex,
    lhs_strongly_writeable: bool,
    lhs_ty: mir::PlaceTy<'tcx>,
) -> BTreeSet<(Region, Region, PointIndex)> {
    if lhs_strongly_writeable {
        return BTreeSet::new();
    }
    let lhs_regions = find_region_variables_of_place_type(tcx, lhs_ty);
    get_assignment_weak_update_constraints(inclusion_tracker, constraint_point, effect_point, &lhs_regions)
}

/// Get all region variables mentioned in a place type.
fn find_region_variables_of_place_type<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: mir::PlaceTy<'tcx>,
) -> BTreeSet<Region> {
    let mut collector = regions::TyRegionCollectFolder::new(tcx);
    ty.ty.fold_with(&mut collector);
    collector.get_regions()
}

/// Get newly introduced regions at this point which are unconstrained.
pub(crate) fn get_new_unconstrained_regions(
    inclusion_tracker: &InclusionTracker<'_, '_>,
    midpoint: facts::PointIndex,
) -> BTreeSet<Region> {
    let info = inclusion_tracker.info();

    let mut unconstrained_regions = BTreeSet::new();

    // for weak updates: should mirror the constraints generated by Polonius
    for (s1, _) in info.subset_base_at(midpoint) {
        // take this constraint
        // TODO should there be exceptions to this?
        let lft1 = info.mk_atomic_region(s1);

        if lft1.is_unconstrained() {
            unconstrained_regions.insert(s1);
        }
    }
    unconstrained_regions
}

#[derive(Debug, Default)]
pub(crate) struct RegionInfo {
    pub expr_annot: Option<code::Annotation>,
    pub required_dyn_inclusions: BTreeSet<(Region, Region, PointIndex)>,
    pub stmt_annot: Vec<code::Annotation>,
    pub unconstrained_regions: BTreeSet<Region>,
}

/// Compute the annotations for an assignment: an annotation for the rhs value, and a list of
/// annotations to prepend to the statement, and a list of annotations to put after the
/// statement.
pub(crate) fn get_assignment_annots<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    startpoint: facts::PointIndex,
    midpoint: facts::PointIndex,
    pre_assignment_effect_point: facts::PointIndex,
    lhs_strongly_writeable: bool,
    lhs_ty: mir::PlaceTy<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
    effects_preregistered: bool,
) -> Result<RegionInfo, TranslationError> {
    let new_dyn_inclusions;
    let expr_annot;
    let mut stmt_annot = Vec::new();

    let unconstrained_regions = get_new_unconstrained_regions(inclusion_tracker, midpoint);

    if lhs_strongly_writeable {
        let did = ty_translator.scope.borrow().did;
        let mappings = get_strong_assignment_mappings(tcx, did, rhs_ty, lhs_ty.ty)?;
        trace!(
            "strong update in {} at {startpoint:?}: {rhs_ty:?} -> {lhs_ty:?}; mappings: {:?}",
            tcx.def_path_str(did),
            mappings
        );

        for source in mappings.values() {
            let AssignmentRegionSource::Var(source) = source else {
                continue;
            };
            let atomic = inclusion_tracker.info().mk_atomic_region(*source);
            if !inclusion_tracker.is_region_known_before_dynamic(*source, startpoint)
                && !atomic.is_loan()
                && !atomic.is_unconstrained()
            {
                return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                    format!("strong assignment copies unknown source region {source:?}"),
                ))));
            }
        }

        let ordered = order_strong_updates(&mappings).map_err(|cycle| {
            TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
                "cyclic strong lifetime update involving regions {cycle:?}"
            ))))
        })?;
        if !effects_preregistered {
            register_strong_assignment_effects(inclusion_tracker, midpoint, &mappings).map_err(|cycle| {
                TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
                    "cyclic strong lifetime update involving regions {cycle:?}"
                ))))
            })?;
        }
        for destination in ordered {
            let source = mappings[&destination];
            let source_lft = match source {
                AssignmentRegionSource::Var(source) => {
                    let atomic = inclusion_tracker.info().mk_atomic_region(source);
                    // If the source is itself overwritten, its old semantic lifetime survives
                    // under the destination name but is no longer equal to the source name.
                    ty_translator.format_atomic_region(atomic)
                },
                AssignmentRegionSource::Named(source) => ty_translator.translate_region(source),
            };
            stmt_annot.push(code::Annotation::CopyLftName(
                source_lft,
                ty_translator.translate_region_var(destination),
            ));
        }

        expr_annot = None;

        new_dyn_inclusions = BTreeSet::new();
    } else {
        new_dyn_inclusions = get_assignment_dynamic_requirements(
            tcx,
            inclusion_tracker,
            midpoint,
            pre_assignment_effect_point,
            false,
            lhs_ty,
        );
        expr_annot = None;
    }

    Ok(RegionInfo {
        expr_annot,
        required_dyn_inclusions: new_dyn_inclusions,
        stmt_annot,
        unconstrained_regions,
    })
}

/// Generates dynamic inclusions for the set of inclusions in `incls`.
/// These inclusions should not hold yet.
pub(crate) fn generate_dyn_inclusion_annots<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    incls: &BTreeSet<(Region, Region, PointIndex)>,
) -> Result<Vec<code::Annotation>, TranslationError> {
    // before executing the assignment, first enforce dynamic inclusions
    info!("Generating dynamic inclusions {:?}", incls);

    let inclusions = inclusion_tracker.generate_dyn_inclusions(incls).map_err(|err| {
        TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "cannot establish mutual dynamic lifetime inclusions between {:?} and {:?} at {:?}",
            err.r1, err.r2, err.point
        ))))
    })?;

    Ok(inclusions
        .into_iter()
        .map(|incl| match incl {
            inclusion_tracker::DynamicInclusion::ExtendLft(l) => {
                code::Annotation::ExtendLft(ty_translator.format_atomic_region(l))
            },
            inclusion_tracker::DynamicInclusion::IncludeLft(l1, l2) => code::Annotation::DynIncludeLft(
                ty_translator.format_atomic_region(l1),
                ty_translator.format_atomic_region(l2),
            ),
        })
        .collect())
}

/// Find all regions that need to outlive a loan region at its point of creation.
fn get_outliving_regions_on_loan(
    inclusion_tracker: &InclusionTracker<'_, '_>,
    r: Region,
    constraint_point: PointIndex,
) -> Vec<Region> {
    // get all base subset constraints r' ⊆ r
    let info = inclusion_tracker.info();
    let mut outliving = Vec::new();

    for (r1, r2) in info.subset_base_at(constraint_point) {
        if r2 == r {
            outliving.push(r1);
        }
        // other subset constraints at this point are due to (for instance) the assignment of
        // the loan to a place and are handled there.
    }
    outliving
}

/// Get the annotations due to borrows appearing on the RHS of an assignment.
pub(crate) fn get_assignment_loan_annots<'tcx>(
    inclusion_tracker: &InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    loc: mir::Location,
    constraint_point: facts::PointIndex,
    _effect_point: facts::PointIndex,
    _rhs: &mir::Rvalue<'tcx>,
) -> Vec<code::Annotation> {
    let info = inclusion_tracker.info();
    let mut stmt_annots = Vec::new();

    // if we create a new loan here, start a new lifetime for it
    if let Some(loan) = info.get_optional_loan_at_point(constraint_point) {
        // TODO: is this fine for aggregates? I suppose, if I create a loan for an
        // aggregate, I want to use the same atomic region for all of its components
        // anyways.

        let lft = info.atomic_region_of_loan(loan);
        let r = lft.get_region();
        // The corresponding tracker effects were registered function-wide.
        let outliving = get_outliving_regions_on_loan(inclusion_tracker, r, constraint_point);

        let mut outliving_lfts: Vec<_> = outliving
            .iter()
            .map(|r| ty_translator.format_atomic_region(info.mk_atomic_region(*r)))
            .collect();
        // If there are no constraints, at least constrain the lifetime by the lifetime of the
        // current function
        if outliving_lfts.is_empty() {
            outliving_lfts.push(coq::Ident::new("_flft"));
        }

        // add statement for issuing the loan
        stmt_annots
            .insert(0, code::Annotation::StartLft(ty_translator.format_atomic_region(lft), outliving_lfts));

        let a = info.get_region_kind(r);
        info!("Issuing loan at {:?} with kind {:?}: {:?}; outliving: {:?}", loc, a, loan, outliving);
    }

    stmt_annots
}

/// Initialize the result region of a shared reborrow from the lifetime governing access to the
/// borrowed place. Shared reborrows do not issue a loan.
pub(crate) fn get_shared_reborrow_annots<'tcx>(
    inclusion_tracker: &InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    resolved: Option<(Region, Region)>,
) -> Vec<code::Annotation> {
    let Some((source, target)) = resolved else {
        return Vec::new();
    };
    vec![code::Annotation::CopyLftName(
        ty_translator.format_atomic_region(inclusion_tracker.info().mk_atomic_region(source)),
        ty_translator.translate_region_var(target),
    )]
}

pub(crate) fn resolve_shared_reborrow<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    rhs: &mir::Rvalue<'tcx>,
    constraint_point: facts::PointIndex,
    effect_point: facts::PointIndex,
    access_region: Option<ty::Region<'tcx>>,
) -> Result<Option<(Region, Region)>, TranslationError> {
    let mir::Rvalue::Ref(region, mir::BorrowKind::Shared, _) = rhs else {
        return Ok(None);
    };
    let ty::RegionKind::ReVar(target) = region.kind() else {
        return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "shared reborrow has non-variable result region {region:?}"
        )))));
    };
    let target = target.into();
    // Borrowck deliberately leaves raw-pointer-derived borrow lifetimes unconstrained. Their
    // semantic lifetime must remain user-instantiable rather than being inferred from place access.
    if inclusion_tracker.info().mk_atomic_region(target).is_unconstrained() {
        return Ok(None);
    }
    let Some(access_region) = access_region else {
        return Ok(None);
    };
    let ty::RegionKind::ReVar(source) = access_region.kind() else {
        return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "shared reborrow dereferences non-variable access region {access_region:?}"
        )))));
    };
    let access_region = source.into();

    if inclusion_tracker.is_region_known_before_shared_reborrow(target, effect_point) {
        return Ok(None);
    }

    // Borrowck may introduce intermediate origins for the place access. Follow only the
    // structurally selected access origin back to its unique known semantic lifetime.
    let mut pending = vec![access_region];
    let mut visited = BTreeSet::new();
    let mut known_sources = BTreeSet::new();
    while let Some(region) = pending.pop() {
        if !visited.insert(region) {
            continue;
        }
        if inclusion_tracker.is_region_known_before_shared_reborrow(region, effect_point) {
            known_sources.insert(region);
            continue;
        }
        pending.extend(
            inclusion_tracker
                .info()
                .subset_base_at(constraint_point)
                .filter_map(|(source, destination)| (destination == region).then_some(source)),
        );
        pending.extend(inclusion_tracker.regions_included_in_before_dynamic(region, effect_point));
    }

    let Some(source) = known_sources.first().copied() else {
        return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "shared reborrow access region {access_region:?} resolves to no known source"
        )))));
    };
    let all_equivalent = known_sources.iter().copied().all(|other| {
        inclusion_tracker.check_inclusion_before_shared_reborrow(source, other, effect_point)
            && inclusion_tracker.check_inclusion_before_shared_reborrow(other, source, effect_point)
    });
    if !all_equivalent {
        return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "shared reborrow access region {access_region:?} resolves to distinct known sources {known_sources:?}"
        )))));
    }

    Ok(Some((source, target)))
}

/// Register that a constrained shared reborrow initializes its result region. Source selection is
/// deferred until every function-wide known-region effect has been registered.
pub(crate) fn preregister_shared_reborrow<'tcx>(
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    rhs: &mir::Rvalue<'tcx>,
    effect_point: facts::PointIndex,
    access_region: Option<ty::Region<'tcx>>,
) {
    let mir::Rvalue::Ref(region, mir::BorrowKind::Shared, _) = rhs else {
        return;
    };
    let target = region.as_var();
    let target: Region = target.into();
    let Some(ty::RegionKind::ReVar(source)) = access_region.map(ty::Region::kind) else {
        return;
    };
    if inclusion_tracker.info().mk_atomic_region(target).is_unconstrained() {
        return;
    }

    let source = source.into();
    inclusion_tracker.add_shared_reborrow_static_inclusion(source, target, effect_point);
    inclusion_tracker.add_shared_reborrow_static_inclusion(target, source, effect_point);
    inclusion_tracker.add_shared_reborrow_known_region(target, effect_point);
}

pub(crate) fn preregister_unconstrained_regions(
    inclusion_tracker: &mut InclusionTracker<'_, '_>,
    regions: &BTreeSet<Region>,
    effect_point: facts::PointIndex,
) {
    for region in regions {
        inclusion_tracker.add_known_region(*region, effect_point);
    }
}

/// Make annotations for unconstrained regions introduced by the current assignment.
pub(crate) fn make_unconstrained_region_annotations<'tcx>(
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    unconstrained_regions: BTreeSet<Region>,
    effect_point: facts::PointIndex,
    rhs: Option<&mir::Rvalue<'tcx>>,
) -> (Vec<code::Annotation>, Vec<specs::Lft>) {
    let mut annotations = Vec::new();

    let mut unconstrained_hints = Vec::new();
    for r in unconstrained_regions {
        if inclusion_tracker.is_region_known_before_effects(r, effect_point) {
            continue;
        }
        if let Some(rhs) = rhs {
            // Detect uses of static variables
            if let mir::Rvalue::Use(mir::Operand::Constant(_), _) = rhs {
                // we are probably using a static variable here
                let lft = ty_translator.translate_region_var(r);
                annotations.push(code::Annotation::CopyLftName(coq::Ident::new("static"), lft));
                continue;
            }

            // If we do a borrow, probably this is a borrow from below a raw pointer.
            // In this case, ask the user to provide the constraints for this borrow.
            if let mir::Rvalue::Ref(region, _, _) = rhs
                && region.as_var() == r.into()
            {
                let lft = ty_translator.translate_region_var(r);
                annotations.push(code::Annotation::UnconstrainedLft(lft.clone()));
                unconstrained_hints.push(lft);
                continue;
            }

            // other cases?
            warn!("Encountered unconstrained region {r:?}, proof will likely fail");

            // in case we initialize enums where the lifetime is unconstrained (e.g. `None` in `Option<&T>`)
            let lft = ty_translator.translate_region_var(r);
            annotations.push(code::Annotation::CopyLftName(coq::Ident::new("static"), lft));
        }
    }

    (annotations, unconstrained_hints)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{AssignmentRegionSource, order_strong_updates};
    use crate::base::Region;

    fn region(index: usize) -> Region {
        Region::from(index)
    }

    #[test]
    fn strong_updates_preserve_sources_before_overwriting_them() {
        let mappings = BTreeMap::from([
            (region(0), AssignmentRegionSource::Var(region(1))),
            (region(1), AssignmentRegionSource::Var(region(2))),
        ]);

        assert_eq!(order_strong_updates(&mappings), Ok(vec![region(0), region(1)]));
    }

    #[test]
    fn cyclic_strong_updates_are_rejected() {
        let mappings = BTreeMap::from([
            (region(0), AssignmentRegionSource::Var(region(1))),
            (region(1), AssignmentRegionSource::Var(region(0))),
        ]);

        assert_eq!(order_strong_updates(&mappings), Err(vec![region(0), region(1)]));
    }
}
