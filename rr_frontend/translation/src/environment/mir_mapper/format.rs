// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use rr_rustc_interface::middle::mir::{BasicBlock, Body};

use super::util::count_locations;
use super::{MappingResult, Origin};
use crate::environment::borrowck::facts;

#[must_use]
pub fn format_mapping<'tcx>(bc: &Body<'tcx>, de: &Body<'tcx>, mapping: &MappingResult) -> String {
    let mut lines = Vec::new();
    let total = count_locations(de);
    lines.push(format!(
        "summary: total={} mapped={} unmapped={}",
        total,
        mapping.target_to_source.len(),
        mapping.unmapped_targets.len()
    ));
    lines.push(String::new());

    let mut locs: Vec<_> = mapping.target_to_source.iter().collect();
    locs.sort_by_key(|((bb, idx), _)| (bb.as_u32(), *idx));
    for ((bb_t, idx_t), origin) in locs {
        lines.push(format!(
            "{:?}[{}] {} -> {}",
            bb_t,
            idx_t,
            describe_location(de, *bb_t, *idx_t),
            format_origin(bc, *origin)
        ));
    }

    if !mapping.unmapped_targets.is_empty() {
        lines.push(String::new());
        lines.push("Unmapped:".to_owned());
        let mut unmapped = mapping.unmapped_targets.clone();
        unmapped.sort_by_key(|(bb, idx)| (bb.as_u32(), *idx));
        for (bb, idx) in unmapped {
            lines.push(format!("{:?}[{}] {}", bb, idx, describe_location(de, bb, idx)));
        }
    }

    let mut aliases = mapping.box_deref_aliases().collect::<Vec<_>>();
    aliases.sort_by_key(|alias| alias.alias_local().as_usize());
    if !aliases.is_empty() {
        lines.push(String::new());
        lines.push("Box deref aliases:".to_owned());
        for alias in aliases {
            let source =
                alias.source_loc().map_or_else(|| "none".to_owned(), |(bb, idx)| format!("{bb:?}[{idx}]"));
            lines.push(format!(
                "{:?} aliases *{:?} (source: {source})",
                alias.alias_local(),
                alias.box_local()
            ));
        }
    }

    lines.join("\n")
}

#[must_use]
pub fn format_inserted_terminator_point_mappings<'tcx>(
    bc: &Body<'tcx>,
    de: &Body<'tcx>,
    mapping: &MappingResult,
) -> String {
    let mut lines = Vec::new();
    let mut locs: Vec<_> = mapping
        .target_to_source
        .iter()
        .filter_map(|(&(bb, idx), &origin)| {
            (origin == Origin::Inserted && idx == de.basic_blocks[bb].statements.len()).then_some((bb, idx))
        })
        .collect();
    locs.sort_by_key(|(bb, idx)| (bb.as_u32(), *idx));

    for loc in locs {
        for point_type in [facts::PointType::Start, facts::PointType::Mid] {
            if let Some((source_bb, source_idx, source_type)) =
                mapping.source_point_for_target_loc(loc, point_type)
            {
                let (bb, idx) = loc;
                lines.push(format!(
                    "{bb:?}[{idx}] {} {point_type:?} -> {source_bb:?}[{source_idx}] {} {source_type:?}",
                    describe_location(de, bb, idx),
                    describe_location(bc, source_bb, source_idx)
                ));
            }
        }
    }

    lines.join("\n")
}

pub(super) fn format_origin(bc: &Body<'_>, origin: Origin) -> String {
    match origin {
        Origin::Source((bb, idx)) => {
            format!("Source({:?}[{}] {})", bb, idx, describe_location(bc, bb, idx))
        },
        Origin::Inserted => "Inserted".to_owned(),
        Origin::SplitFrom((bb, idx)) => {
            format!("SplitFrom({:?}[{}] {})", bb, idx, describe_location(bc, bb, idx))
        },
        Origin::FoldedFrom((bb, idx)) => {
            format!("FoldedFrom({:?}[{}] {})", bb, idx, describe_location(bc, bb, idx))
        },
    }
}

pub(super) fn describe_location(body: &Body<'_>, bb: BasicBlock, idx: usize) -> String {
    let data = &body.basic_blocks[bb];
    if idx < data.statements.len() {
        format!("{:?}", data.statements[idx].kind)
    } else {
        format!("{:?}", data.terminator().kind)
    }
}
