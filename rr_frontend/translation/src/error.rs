// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use derive_more::Display;
use rr_rustc_interface::errors::DiagMessage;
use rr_rustc_interface::hir::def_id::DefId;

use crate::procedures;

#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
pub(crate) enum Message {
    #[display("No assumption is allowed, but this function is annotated with `#[rr::{}]`", _0)]
    NoAssumptionAllowed(procedures::Mode),

    #[display("Unknown ADT: {:?}", _0)]
    UnknownAdt(DefId),

    #[display("ADT shim was overridden for {:?}", _0)]
    OverriddenAdtShim(DefId),
}

impl From<Message> for DiagMessage {
    fn from(msg: Message) -> Self {
        Self::Str(format!("[RefinedRust] {}", msg).into())
    }
}
