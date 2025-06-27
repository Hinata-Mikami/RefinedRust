// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{fmt, mem};

use rr_rustc_interface::data_structures::fx::FxHashSet;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::span::def_id::DefId;
use serde::ser::SerializeSeq as _;
use serde::{Serialize, Serializer};

use super::utils::*;
use crate::AnalysisError;
use crate::abstract_interpretation::AbstractState;

/// A set of MIR places that are definitely initialized at a program point
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.
#[derive(Clone)]
pub struct DefinitelyInitializedState<'mir, 'tcx> {
    pub(crate) def_init_places: FxHashSet<mir::Place<'tcx>>,
    pub(crate) def_id: DefId,
    pub(crate) mir: &'mir mir::Body<'tcx>,
    pub(crate) tcx: ty::TyCtxt<'tcx>,
}

impl fmt::Debug for DefinitelyInitializedState<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // ignore tcx & mir
        f.debug_struct("DefinitelyInitializedState")
            .field("def_init_places", &self.def_init_places)
            .finish()
    }
}

impl PartialEq for DefinitelyInitializedState<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        // TODO: This assert is commented out because the stable hasher crashes
        // on MIR that has region ids.
        //
        // debug_assert_eq!(
        //     {
        //         let mut stable_hasher = StableHasher::new();
        //         self.mir.hash_stable(
        //             &mut self.tcx.get_stable_hashing_context(),
        //             &mut stable_hasher,
        //         );
        //         stable_hasher.finish::<Fingerprint>()
        //     },
        //     {
        //         let mut stable_hasher = StableHasher::new();
        //         other.mir.hash_stable(
        //             &mut other.tcx.get_stable_hashing_context(),
        //             &mut stable_hasher,
        //         );
        //         stable_hasher.finish::<Fingerprint>()
        //     },
        // );
        self.def_init_places == other.def_init_places
    }
}

impl Eq for DefinitelyInitializedState<'_, '_> {}

impl Serialize for DefinitelyInitializedState<'_, '_> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_seq(Some(self.def_init_places.len()))?;

        let mut ordered_places: Vec<_> = self.def_init_places.iter().collect();
        ordered_places.sort_by(|a, b| cmp_place(self.tcx, a, b));

        for place in ordered_places {
            seq.serialize_element(&format!("{place:?}"))?;
        }
        seq.end()
    }
}

impl<'mir, 'tcx: 'mir> DefinitelyInitializedState<'mir, 'tcx> {
    #[must_use]
    pub fn get_def_init_mir_places(&self) -> FxHashSet<mir::Place<'tcx>> {
        self.def_init_places.iter().copied().collect()
    }

    /// The top element of the lattice contains no places
    fn new_top(def_id: DefId, mir: &'mir mir::Body<'tcx>, tcx: ty::TyCtxt<'tcx>) -> Self {
        Self {
            def_init_places: FxHashSet::default(),
            def_id,
            mir,
            tcx,
        }
    }

    fn check_invariant(&self) {
        for &place1 in &self.def_init_places {
            for &place2 in &self.def_init_places {
                if place1 != place2 {
                    debug_assert!(
                        !is_prefix(place1, place2),
                        "The place {place2:?} is a prefix of the place {place1:?}"
                    );
                    debug_assert!(
                        !is_prefix(place2, place1),
                        "The place {place1:?} is a prefix of the place {place2:?}"
                    );
                }
            }
        }
    }

    /// Sets `place` as definitely initialized (see `place_set/insert`())
    fn set_place_initialised(&mut self, place: mir::Place<'tcx>) {
        if cfg!(debug_assertions) {
            self.check_invariant();
        }

        // First, check that the place is not already marked as
        // definitely initialized.
        if !self.def_init_places.iter().any(|&current| is_prefix(place, current)) {
            // To maintain the invariant that we do not have a place and its
            // prefix in the set, we remove all places for which the given
            // one is a prefix.
            self.def_init_places.retain(|&current| !is_prefix(current, place));
            self.def_init_places.insert(place);
            // If all fields of a struct are definitely initialized,
            // just keep info that the struct is definitely initialized.
            collapse(self.mir, self.tcx, &mut self.def_init_places, place);
        }

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
    }

    /// Sets `place` as (possibly) uninitialised (see `place_set/remove`())
    fn set_place_uninitialised(&mut self, place: mir::Place<'tcx>) {
        if cfg!(debug_assertions) {
            self.check_invariant();
        }

        let old_places = mem::take(&mut self.def_init_places);
        for old_place in old_places {
            if is_prefix(place, old_place) {
                // We are uninitializing a field of the place `old_place`.
                self.def_init_places.extend(expand(self.mir, self.tcx, old_place, place));
            } else if is_prefix(old_place, place) {
                // We are uninitializing a place of which only some
                // fields are initialized. Just remove all initialized
                // fields.
                // This happens when the target place is already
                // initialized.
            } else {
                self.def_init_places.insert(old_place);
            }
        }

        // Check that place is properly removed
        for &place1 in &self.def_init_places {
            debug_assert!(
                !is_prefix(place1, place) && !is_prefix(place, place1),
                "Bug: failed to ensure that there are no prefixes: place={place:?} place1={place1:?}"
            );
        }

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
    }

    /// If the operand is move, make the place uninitialised
    /// If the place is a Copy type, uninitialise the place.
    fn apply_operand_effect(&mut self, operand: &mir::Operand<'tcx>) {
        if let mir::Operand::Move(place) = operand {
            self.set_place_uninitialised(*place);
        }
    }

    /// If the place is a Copy type, uninitialise the place.
    pub(crate) fn apply_statement_effect(&mut self, location: mir::Location) {
        let statement = &self.mir[location.block].statements[location.statement_index];

        match &statement.kind {
            mir::StatementKind::Assign(box (target, source)) => {
                match source {
                    mir::Rvalue::Repeat(operand, _)
                    | mir::Rvalue::Cast(_, operand, _)
                    | mir::Rvalue::UnaryOp(_, operand)
                    | mir::Rvalue::Use(operand) => {
                        self.apply_operand_effect(operand);
                    },
                    mir::Rvalue::BinaryOp(_, box (operand1, operand2)) => {
                        self.apply_operand_effect(operand1);
                        self.apply_operand_effect(operand2);
                    },
                    mir::Rvalue::Aggregate(_, operands) => {
                        for operand in operands {
                            self.apply_operand_effect(operand);
                        }
                    },
                    _ => {},
                }

                self.set_place_initialised(*target);
            },
            mir::StatementKind::StorageDead(local) => {
                self.set_place_uninitialised((*local).into());
            },
            _ => {},
        }
    }

    /// If the place is a Copy type, uninitialise the place.
    pub(crate) fn apply_terminator_effect(
        &self,
        location: mir::Location,
    ) -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        let mut new_state = self.clone();
        let mut res_vec = Vec::new();
        let terminator = self.mir[location.block].terminator();
        match &terminator.kind {
            mir::TerminatorKind::SwitchInt { discr, .. } => {
                // only operand has an effect on definitely initialized places, all successors
                // get the same state
                new_state.apply_operand_effect(discr);

                for bb in terminator.successors() {
                    res_vec.push((bb, new_state.clone()));
                }
            },
            mir::TerminatorKind::Drop {
                place,
                target,
                unwind,
                ..
            } => {
                new_state.set_place_uninitialised(*place);
                res_vec.push((*target, new_state));

                if let mir::UnwindAction::Cleanup(bb) = *unwind {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            },
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                for arg in args {
                    new_state.apply_operand_effect(&arg.node);
                }
                new_state.apply_operand_effect(func);
                if let Some(bb) = *target {
                    new_state.set_place_initialised(*destination);
                    res_vec.push((bb, new_state));
                }

                if let mir::UnwindAction::Cleanup(bb) = *unwind {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            },
            mir::TerminatorKind::Assert {
                cond,
                target,
                unwind,
                ..
            } => {
                new_state.apply_operand_effect(cond);
                res_vec.push((*target, new_state));

                if let mir::UnwindAction::Cleanup(bb) = *unwind {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            },
            mir::TerminatorKind::Yield {
                value,
                resume,
                drop,
                ..
            } => {
                // TODO: resume_arg?
                new_state.apply_operand_effect(value);
                res_vec.push((*resume, new_state));

                if let Some(bb) = *drop {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            },
            mir::TerminatorKind::InlineAsm { .. } => {
                return Err(AnalysisError::UnsupportedStatement(location));
            },

            _ => {
                for bb in terminator.successors() {
                    // no operation -> no change of state
                    res_vec.push((bb, self.clone()));
                }
            },
        }

        Ok(res_vec)
    }
}

impl<'mir, 'tcx: 'mir> AbstractState for DefinitelyInitializedState<'mir, 'tcx> {
    /// The lattice join intersects the two place sets
    fn join(&mut self, other: &Self) {
        if cfg!(debug_assertions) {
            self.check_invariant();
            other.check_invariant();
        }

        let mut intersection = FxHashSet::default();
        // TODO: make more efficient/modify self directly?
        let mut propagate_places_fn =
            |place_set1: &FxHashSet<mir::Place<'tcx>>, place_set2: &FxHashSet<mir::Place<'tcx>>| {
                for &place in place_set1 {
                    // find matching place in place_set2:
                    // if there is a matching place that contains exactly the same or more memory
                    // locations, place can be added to the resulting intersection
                    for &potential_prefix in place_set2 {
                        if is_prefix(place, potential_prefix) {
                            intersection.insert(place);
                            break;
                        }
                    }
                }
            };

        let self_places = &self.def_init_places;
        let other_places = &other.def_init_places;
        propagate_places_fn(self_places, other_places);
        propagate_places_fn(other_places, self_places);
        self.def_init_places = intersection;

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
    }
}
