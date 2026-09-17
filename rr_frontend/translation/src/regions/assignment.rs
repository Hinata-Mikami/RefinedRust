// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Lifetime effects associated with writing a MIR value into a place.
//!
//! This module provides five related pieces of assignment planning:
//!
//! - structural mapping between lifetime positions in source and destination types;
//! - strong destination updates, which replace semantic lifetime names;
//! - weak destination updates, which preserve names and establish required inclusions;
//! - initialization of loans and shared-reborrow lifetime names; and
//! - initialization of unconstrained region names.
//!
//! `rvalue` handles the structural creation of the RHS value. This module handles the borrow effects
//! surrounding that creation and the subsequent write into the LHS. Call results reuse the same
//! destination-write machinery, with effects restricted to the normal-return edge where necessary.
//! The function-wide preregistration and plan-construction pipeline is documented in `annotations`.
//!
//! # Planning Points
//!
//! For an ordinary assignment, the **startpoint** is where annotations that must run before evaluating
//! and writing the RHS are placed. The **midpoint** is where Polonius exposes assignment constraints and
//! where the tracker records effects that hold after the write. A call destination instead records
//! strong-update effects on the normal-return edge, because the destination is not initialized on unwind.
//!
//! Tracker effects are preregistered for every reachable assignment before concrete plans are prepared.
//! Preregistration does not emit code: it lets the must-analysis account for effects at their original
//! points without making results depend on block traversal or assignment planning order.
//!
//! # Strong And Weak Updates
//!
//! A strong update is permitted when the destination is not reached through a reference or raw pointer.
//! It kills the old destination lifetime names at the midpoint, marks the replacements known, and emits
//! ordered `CopyLftName` annotations after the memory write. Copies are ordered so every old source name
//! is read before that name is overwritten; cycles are rejected because no temporary name is available.
//!
//! A weak update writes through a potentially aliased place and therefore cannot replace its semantic
//! lifetime names. It extracts Polonius inclusions targeting lifetime positions stored in the LHS and
//! establishes the missing inclusions before the memory write. Dynamic requirements are preregistered as
//! ensure-actions and finalized only after all assignments and calls are known, preserving minimality.
//!
//! # Borrow Initialization
//!
//! An assignment midpoint carrying a Polonius loan emits `StartLft`. A shared reborrow does not
//! necessarily issue a loan; when its result region is not already initialized, it aliases that result
//! from the known lifetime governing access to the borrowed place. Shared-reborrow source resolution is
//! a separate function-wide batch so one assignment cannot observe another merely due to planning order.
//!
//! # Runtime Order
//!
//! The complete ordinary-assignment plan is assembled by `annotations` and rendered in this order:
//!
//! 1. statement-entry loan deaths;
//! 2. unconstrained lifetime initialization;
//! 3. structural rvalue lifetime transfers;
//! 4. loan creation or shared-reborrow aliases;
//! 5. dynamic inclusions required by a weak update;
//! 6. evaluation of the RHS and the memory write; and
//! 7. semantic lifetime-name copies required by a strong update.

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

// Structural region mapping between source and destination types.

/// A structural source for one variable lifetime position in a destination type.
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

// Strong writes replace destination semantic lifetime names.

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

// Weak writes preserve destination names and establish required inclusions.

/// Collect Polonius inclusions required before a weak destination write.
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
    is_strong_update: bool,
    lhs_ty: mir::PlaceTy<'tcx>,
) -> BTreeSet<(Region, Region, PointIndex)> {
    if is_strong_update {
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

// Destination-write plan components.

/// Parts of a destination-write plan assembled with rvalue and borrow annotations by `annotations`.
#[derive(Debug, Default)]
pub(crate) struct WriteInfo {
    /// Reserved for an update-specific annotation around the translated RHS expression.
    ///
    /// Current strong and weak writes do not require one.
    pub expr_annot: Option<code::Annotation>,
    /// Dynamic inclusions that must hold before a weak write.
    pub required_dyn_inclusions: BTreeSet<(Region, Region, PointIndex)>,
    /// Semantic lifetime-name updates emitted after the memory write.
    pub post_write_annots: Vec<code::Annotation>,
    /// Unconstrained region candidates whose names may need initialization before the write.
    pub unconstrained_regions: BTreeSet<Region>,
}

/// Prepare the destination-write portion of an assignment or normal call result.
///
/// Rvalue creation, loan issuance, shared reborrows, and unconstrained initializers are assembled by
/// `annotations`. Strong-update tracker effects must already be preregistered function-wide. This
/// function validates their sources and renders the ordered post-write name copies; weak updates
/// instead return dynamic inclusion requirements that are finalized function-wide.
pub(crate) fn get_assignment_annots<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    startpoint: facts::PointIndex,
    midpoint: facts::PointIndex,
    pre_assignment_effect_point: facts::PointIndex,
    is_strong_update: bool,
    lhs_ty: mir::PlaceTy<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
) -> Result<WriteInfo, TranslationError> {
    let required_dyn_inclusions;
    let expr_annot;
    let mut post_write_annots = Vec::new();

    let unconstrained_regions = get_new_unconstrained_regions(inclusion_tracker, midpoint);

    if is_strong_update {
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
            post_write_annots.push(code::Annotation::CopyLftName(
                source_lft,
                ty_translator.translate_region_var(destination),
            ));
        }

        expr_annot = None;

        required_dyn_inclusions = BTreeSet::new();
    } else {
        required_dyn_inclusions = get_assignment_dynamic_requirements(
            tcx,
            inclusion_tracker,
            midpoint,
            pre_assignment_effect_point,
            false,
            lhs_ty,
        );
        expr_annot = None;
    }

    Ok(WriteInfo {
        expr_annot,
        required_dyn_inclusions,
        post_write_annots,
        unconstrained_regions,
    })
}

// Dynamic inclusion finalization.

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
            inclusion_tracker::DynamicInclusion::ExtendLftTo { target, source } => {
                code::Annotation::ExtendLftTo(
                    ty_translator.format_atomic_region(target),
                    ty_translator.format_atomic_region(source),
                )
            },
            inclusion_tracker::DynamicInclusion::IncludeLft(l1, l2) => code::Annotation::DynIncludeLft(
                ty_translator.format_atomic_region(l1),
                ty_translator.format_atomic_region(l2),
            ),
        })
        .collect())
}

// Loan and shared-reborrow lifetime initialization.

/// Emit `StartLft` for the Polonius loan issued at an assignment midpoint, if any.
///
/// Not every borrow-looking rvalue issues a loan. In particular, shared reborrows may instead be
/// initialized by [`get_shared_reborrow_annots`]. The corresponding tracker effects were registered
/// function-wide before this rendering step.
pub(crate) fn get_assignment_loan_annots<'tcx>(
    inclusion_tracker: &InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    loc: mir::Location,
    constraint_point: facts::PointIndex,
    outliving: &[Region],
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
    resolved: Option<(BTreeSet<Region>, Region)>,
) -> Vec<code::Annotation> {
    let Some((sources, target)) = resolved else {
        return Vec::new();
    };
    let target = ty_translator.translate_region_var(target);
    let mut sources = sources
        .into_iter()
        .map(|source| ty_translator.format_atomic_region(inclusion_tracker.info().mk_atomic_region(source)));
    let Some(first) = sources.next() else {
        return Vec::new();
    };
    let Some(second) = sources.next() else {
        return vec![code::Annotation::CopyLftName(first, target)];
    };
    vec![code::Annotation::AliasLftIntersection(target, [first, second].into_iter().chain(sources).collect())]
}

pub(crate) fn resolve_shared_reborrow<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    rhs: &mir::Rvalue<'tcx>,
    constraint_point: facts::PointIndex,
    effect_point: facts::PointIndex,
    access_regions: &[ty::Region<'tcx>],
) -> Result<Option<(BTreeSet<Region>, Region)>, TranslationError> {
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
    if access_regions.is_empty() {
        return Ok(None);
    }

    if inclusion_tracker.is_region_known_after_ordinary_effects(target, effect_point) {
        return Ok(None);
    }

    // Borrowck may introduce intermediate origins for the place access. Follow the structurally
    // selected access origins back to their known semantic lifetime supports.
    let mut pending = Vec::with_capacity(access_regions.len());
    for access_region in access_regions {
        let ty::RegionKind::ReVar(source) = access_region.kind() else {
            return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                format!("shared reborrow dereferences non-variable access region {access_region:?}"),
            ))));
        };
        pending.push(source.into());
    }
    let mut visited = BTreeSet::new();
    let mut known_sources = BTreeSet::new();
    while let Some(region) = pending.pop() {
        if !visited.insert(region) {
            continue;
        }
        if inclusion_tracker.is_region_known_after_ordinary_effects(region, effect_point) {
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

    if known_sources.is_empty() {
        return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "shared reborrow access regions {access_regions:?} resolve to no known source"
        )))));
    }

    Ok(Some((known_sources, target)))
}

/// Register that a constrained shared reborrow initializes its result region. Source selection is
/// deferred until every function-wide known-region effect has been registered.
pub(crate) fn preregister_shared_reborrow<'tcx>(
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    rhs: &mir::Rvalue<'tcx>,
    effect_point: facts::PointIndex,
    access_regions: &[ty::Region<'tcx>],
) {
    let mir::Rvalue::Ref(region, mir::BorrowKind::Shared, _) = rhs else {
        return;
    };
    let target = region.as_var();
    let target: Region = target.into();
    if inclusion_tracker.info().mk_atomic_region(target).is_unconstrained() {
        return;
    }

    let Some(sources): Option<BTreeSet<Region>> = access_regions
        .iter()
        .map(|region| match region.kind() {
            ty::RegionKind::ReVar(source) => Some(source.into()),
            _ => None,
        })
        .collect()
    else {
        return;
    };
    if sources.is_empty() {
        return;
    }
    for source in &sources {
        inclusion_tracker.add_shared_reborrow_static_inclusion(*source, target, effect_point);
    }
    if let Some(source) = sources.iter().next().filter(|_| sources.len() == 1) {
        inclusion_tracker.add_shared_reborrow_static_inclusion(target, *source, effect_point);
    }
    inclusion_tracker.add_shared_reborrow_known_region(target, effect_point);
}

// Unconstrained region-name initialization.

/// Collect unconstrained source-region candidates introduced by subset constraints at this midpoint.
///
/// A candidate is not necessarily new: annotation rendering filters regions whose semantic names are
/// already guaranteed before the effect point.
pub(crate) fn get_new_unconstrained_regions(
    inclusion_tracker: &InclusionTracker<'_, '_>,
    midpoint: facts::PointIndex,
) -> BTreeSet<Region> {
    let info = inclusion_tracker.info();
    let mut unconstrained_regions = BTreeSet::new();

    // For weak updates, mirror the constraints generated by Polonius.
    for (source, _) in info.subset_base_at(midpoint) {
        if info.mk_atomic_region(source).is_unconstrained() {
            unconstrained_regions.insert(source);
        }
    }
    unconstrained_regions
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

/// Make annotations for unconstrained regions introduced by the current assignment or call.
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
        if rhs.is_none() {
            let lft = ty_translator.translate_region_var(r);
            annotations.push(code::Annotation::UnconstrainedLft(lft.clone()));
            unconstrained_hints.push(lft);
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
