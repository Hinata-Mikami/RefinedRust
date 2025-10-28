// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::BTreeSet;
use std::fmt;

use rr_rustc_interface::data_structures::fx::FxHashSet;
use rr_rustc_interface::middle::mir;
use serde::ser::SerializeSeq as _;
use serde::{Serialize, Serializer};

use crate::AnalysisError;
use crate::abstract_interpretation::AbstractState;

/// A set of MIR locals that are definitely allocated at a program point
#[derive(Clone)]
pub struct DefinitelyAllocatedState<'mir, 'tcx> {
    pub(crate) def_allocated_locals: FxHashSet<mir::Local>,
    pub(crate) mir: &'mir mir::Body<'tcx>,
}

impl fmt::Debug for DefinitelyAllocatedState<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // ignore mir
        f.debug_struct("DefinitelyAllocatedState")
            .field("def_allocated_locals", &self.def_allocated_locals)
            .finish()
    }
}

impl PartialEq for DefinitelyAllocatedState<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.def_allocated_locals == other.def_allocated_locals
    }
}

impl Eq for DefinitelyAllocatedState<'_, '_> {}

impl Serialize for DefinitelyAllocatedState<'_, '_> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_seq(Some(self.def_allocated_locals.len()))?;
        let oredered_set: BTreeSet<_> = self.def_allocated_locals.iter().collect();
        for local in oredered_set {
            seq.serialize_element(&format!("{:?}", local))?;
        }
        seq.end()
    }
}

impl DefinitelyAllocatedState<'_, '_> {
    /// Sets `local` as allocated.
    fn set_local_allocated(&mut self, local: mir::Local) {
        self.def_allocated_locals.insert(local);
    }

    /// Sets `local` as (possibly) not allocated.
    fn set_place_unallocated(&mut self, local: mir::Local) {
        self.def_allocated_locals.remove(&local);
    }

    pub(crate) fn apply_statement_effect(&mut self, location: mir::Location) {
        let statement = &self.mir[location.block].statements[location.statement_index];

        match statement.kind {
            mir::StatementKind::StorageLive(local) => {
                self.set_local_allocated(local);
            },
            mir::StatementKind::StorageDead(local) => {
                self.set_place_unallocated(local);
            },
            _ => {},
        }
    }

    #[expect(clippy::unnecessary_wraps)]
    pub(crate) fn apply_terminator_effect(
        &self,
        location: mir::Location,
    ) -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        let mut res_vec = Vec::new();
        let terminator = self.mir[location.block].terminator();
        for bb in terminator.successors() {
            res_vec.push((bb, self.clone()));
        }
        Ok(res_vec)
    }
}

impl AbstractState for DefinitelyAllocatedState<'_, '_> {
    /// The lattice join intersects the two sets of locals
    fn join(&mut self, other: &Self) {
        self.def_allocated_locals.retain(|local| other.def_allocated_locals.contains(local));
    }
}
