// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rr_rustc_interface::middle::mir;

#[derive(Copy, Clone, Debug)]
pub enum AnalysisError {
    UnsupportedStatement(mir::Location),
    /// The state is not defined on the edge between two MIR blocks (source, destination).
    NoStateAfterSuccessor(mir::BasicBlock, mir::BasicBlock),
}

impl AnalysisError {
    pub fn to_pretty_str(self, mir: &mir::Body<'_>) -> String {
        match self {
            Self::UnsupportedStatement(location) => {
                let stmt = location_to_stmt_str(location, mir);
                format!("Unsupported statement at {:?}: {}", location, stmt)
            },
            Self::NoStateAfterSuccessor(bb_src, bb_dst) => {
                let terminator = &mir[bb_src].terminator();
                format!(
                    "There is no state for the block {:?} after the terminator of block {:?} ({:?})",
                    bb_dst, bb_src, terminator.kind
                )
            },
        }
    }
}

/// Convert a `location` to a string representing the statement or terminator at that `location`
fn location_to_stmt_str(location: mir::Location, mir: &mir::Body<'_>) -> String {
    let bb_mir = &mir[location.block];
    if location.statement_index < bb_mir.statements.len() {
        let stmt = &bb_mir.statements[location.statement_index];
        format!("{stmt:?}")
    } else {
        // location = terminator
        let terminator = bb_mir.terminator();
        format!("{:?}", terminator.kind)
    }
}
