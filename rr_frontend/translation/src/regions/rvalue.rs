// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Initializes semantic lifetime names introduced by MIR rvalues.

use std::collections::{BTreeMap, BTreeSet};
use std::iter;

use radium::{code, coq};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use crate::base::*;
use crate::error::Message;
use crate::regions::assignment::{AssignmentRegionSource, map_regions_between_types};
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::types;

fn aggregate_field_types<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    kind: &mir::AggregateKind<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
) -> Result<Vec<ty::Ty<'tcx>>, TranslationError> {
    match (kind, rhs_ty.kind()) {
        (mir::AggregateKind::Tuple, ty::TyKind::Tuple(fields)) => Ok(fields.to_vec()),
        (mir::AggregateKind::Array(_), ty::TyKind::Array(element, _)) => Ok(vec![*element]),
        (mir::AggregateKind::Adt(kind_def, variant, _, _, active_field), ty::TyKind::Adt(def, _))
            if kind_def == &def.did() =>
        {
            let variant_def = def.variant(*variant);
            Ok(variant_def
                .fields
                .iter_enumerated()
                .filter(|(field, _)| active_field.is_none_or(|active| active == *field))
                .map(|(field, _)| {
                    let variant = def.is_enum().then_some(*variant);
                    mir::PlaceTy::field_ty(tcx, rhs_ty, variant, field).skip_norm_wip()
                })
                .collect())
        },
        (mir::AggregateKind::Closure(kind_def, _), ty::TyKind::Closure(def, args)) if kind_def == def => {
            Ok(args.as_closure().upvar_tys().to_vec())
        },
        _ => Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "cannot structurally initialize lifetime-bearing aggregate {kind:?} with type {rhs_ty:?}"
        ))))),
    }
}

fn add_type_transfer<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    did: DefId,
    mappings: &mut BTreeMap<Region, Vec<AssignmentRegionSource<'tcx>>>,
    source: ty::Ty<'tcx>,
    destination: ty::Ty<'tcx>,
) -> Result<(), TranslationError> {
    for (destination, sources) in map_regions_between_types(tcx, did, source, destination)? {
        let destination_sources = mappings.entry(destination).or_default();
        for source in sources {
            if !destination_sources.contains(&source) {
                destination_sources.push(source);
            }
        }
    }
    Ok(())
}

fn order_transfers(
    mappings: &BTreeMap<Region, Vec<AssignmentRegionSource<'_>>>,
) -> Result<Vec<Region>, Vec<Region>> {
    let mut remaining: BTreeSet<_> = mappings.keys().copied().collect();
    let mut ordered = Vec::with_capacity(remaining.len());
    while !remaining.is_empty() {
        let next = remaining.iter().copied().find(|candidate| {
            !remaining.iter().any(|other| {
                other != candidate
                    && mappings[other].iter().any(
                        |source| matches!(source, AssignmentRegionSource::Var(source) if source == candidate),
                    )
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

fn format_source<'tcx>(
    ty_translator: &types::LocalTX<'_, 'tcx>,
    inclusion_tracker: &InclusionTracker<'_, 'tcx>,
    source: AssignmentRegionSource<'tcx>,
) -> coq::Ident {
    match source {
        AssignmentRegionSource::Var(source) => {
            ty_translator.format_atomic_region(inclusion_tracker.info().mk_atomic_region(source))
        },
        AssignmentRegionSource::Named(source) => ty_translator.translate_region(source),
    }
}

fn get_rvalue_transfers<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    did: DefId,
    rhs: &mir::Rvalue<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
    operand_tys: &[ty::Ty<'tcx>],
) -> Result<(BTreeMap<Region, Vec<AssignmentRegionSource<'tcx>>>, Vec<Region>), TranslationError> {
    let mut mappings = BTreeMap::new();
    match rhs {
        mir::Rvalue::Use(_, _) => {
            let [source] = operand_tys else {
                return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                    format!("Use rvalue has {} structural operand types", operand_tys.len()),
                ))));
            };
            add_type_transfer(tcx, did, &mut mappings, *source, rhs_ty)?;
        },
        mir::Rvalue::Ref(_, _, _) => {
            let [source] = operand_tys else {
                return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                    format!("reference rvalue has {} structural place types", operand_tys.len()),
                ))));
            };
            let ty::TyKind::Ref(_, referent, _) = rhs_ty.kind() else {
                return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                    format!("reference rvalue has non-reference region type {rhs_ty:?}"),
                ))));
            };
            add_type_transfer(tcx, did, &mut mappings, *source, *referent)?;
        },
        mir::Rvalue::Aggregate(kind, _) => {
            let field_tys = aggregate_field_types(tcx, kind, rhs_ty)?;
            let field_tys: Vec<_> = if matches!(kind.as_ref(), mir::AggregateKind::Array(_)) {
                iter::repeat_n(field_tys[0], operand_tys.len()).collect()
            } else {
                field_tys
            };
            if operand_tys.len() != field_tys.len() {
                return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                    format!(
                        "aggregate has {} operands but {} structural field types",
                        operand_tys.len(),
                        field_tys.len()
                    ),
                ))));
            }
            for (&source, destination) in operand_tys.iter().zip(field_tys) {
                add_type_transfer(tcx, did, &mut mappings, source, destination)?;
            }
        },
        _ => return Ok((BTreeMap::new(), Vec::new())),
    }

    for (destination, sources) in &mut mappings {
        sources.retain(|source| *source != AssignmentRegionSource::Var(*destination));
    }
    mappings.retain(|_, sources| !sources.is_empty());
    let ordered = order_transfers(&mappings).map_err(|cycle| {
        TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(format!(
            "cyclic rvalue lifetime initialization involving regions {cycle:?}"
        ))))
    })?;

    Ok((mappings, ordered))
}

/// Register structural rvalue effects before any annotation decisions query the tracker.
pub(crate) fn preregister_rvalue_creation<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    did: DefId,
    effect_point: PointIndex,
    rhs: &mir::Rvalue<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
    operand_tys: &[ty::Ty<'tcx>],
) -> Result<(), TranslationError> {
    let (mappings, ordered) = get_rvalue_transfers(tcx, did, rhs, rhs_ty, operand_tys)?;
    for destination in ordered {
        let sources = &mappings[&destination];
        inclusion_tracker.add_barrier(destination, effect_point);
        inclusion_tracker.add_known_region(destination, effect_point);
        if sources.len() == 1 {
            if let AssignmentRegionSource::Var(source) = sources[0] {
                inclusion_tracker.add_static_inclusion(source, destination, effect_point);
                inclusion_tracker.add_static_inclusion(destination, source, effect_point);
            }
        } else {
            for source in sources {
                if let AssignmentRegionSource::Var(source) = source {
                    inclusion_tracker.add_static_inclusion(*source, destination, effect_point);
                }
            }
        }
    }
    Ok(())
}

/// Initialize region names belonging to an rvalue from its structural MIR operands.
pub(crate) fn get_rvalue_creation_annots<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    effect_point: PointIndex,
    rhs: &mir::Rvalue<'tcx>,
    rhs_ty: ty::Ty<'tcx>,
    operand_tys: &[ty::Ty<'tcx>],
) -> Result<Vec<code::Annotation>, TranslationError> {
    let did = ty_translator.scope.borrow().did;
    let (mappings, ordered) = get_rvalue_transfers(tcx, did, rhs, rhs_ty, operand_tys)?;

    for sources in mappings.values() {
        for source in sources {
            if let AssignmentRegionSource::Var(source) = source {
                let atomic = inclusion_tracker.info().mk_atomic_region(*source);
                if !inclusion_tracker.is_region_known_before_effects(*source, effect_point)
                    && !atomic.is_loan()
                    && !atomic.is_unconstrained()
                {
                    return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                        format!("rvalue initialization copies unknown source region {source:?}"),
                    ))));
                }
            }
        }
    }

    let mut annotations = Vec::new();
    for destination in ordered {
        let sources = &mappings[&destination];
        let destination_lft = ty_translator.translate_region_var(destination);
        if sources.len() == 1 {
            let source = *sources.iter().next().unwrap();
            annotations.push(code::Annotation::CopyLftName(
                format_source(ty_translator, inclusion_tracker, source),
                destination_lft,
            ));
        } else {
            annotations.push(code::Annotation::AliasLftIntersection(
                destination_lft,
                sources
                    .iter()
                    .map(|source| format_source(ty_translator, inclusion_tracker, *source))
                    .collect(),
            ));
        }
    }
    Ok(annotations)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rvalue_transfers_preserve_sources_before_overwriting_them() {
        let r0 = Region::from(0_usize);
        let r1 = Region::from(1_usize);
        let r2 = Region::from(2_usize);
        let mappings = BTreeMap::from([
            (r0, vec![AssignmentRegionSource::Var(r1)]),
            (r1, vec![AssignmentRegionSource::Var(r2)]),
        ]);

        assert_eq!(order_transfers(&mappings), Ok(vec![r0, r1]));
    }

    #[test]
    fn cyclic_rvalue_transfers_are_rejected() {
        let r0 = Region::from(0_usize);
        let r1 = Region::from(1_usize);
        let mappings = BTreeMap::from([
            (r0, vec![AssignmentRegionSource::Var(r1)]),
            (r1, vec![AssignmentRegionSource::Var(r0)]),
        ]);

        assert_eq!(order_transfers(&mappings), Err(vec![r0, r1]));
    }
}
