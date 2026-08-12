// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the License was not distributed with this file, You can obtain
// one at https://opensource.org/license/bsd-3-clause/.

use radium::{code, specs};
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::target::spec::PanicStrategy;

const PANIC_SHIM_LOC: &str = "panic_shim_loc";
const PANIC_SHIM_SPEC: &str = "type_of_panic_shim";
const PANIC_ABORT_LINK_ASSUMPTION: &str = "radium_panic_strategy_of = PanicAbort";

/// Require the linked Radium machine to match MIR compiled with aborting panics when permitted by
/// the frontend policy or an explicit local opt-in.
pub(crate) fn add_strategy_link_assumption(
    tcx: ty::TyCtxt<'_>,
    builder: &mut code::FunctionBuilder<'_>,
    opted_in: bool,
) {
    if tcx.sess.panic_strategy() == PanicStrategy::Abort
        && (rrconfig::panic_abort_mode() == rrconfig::PanicAbortMode::Permissive || opted_in)
    {
        builder.add_linktime_assumption(PANIC_ABORT_LINK_ASSUMPTION.to_owned());
    }
}

/// Local panic sites remain proof obligations in conservative mode.
pub(crate) fn local_panic_uses_shim(tcx: ty::TyCtxt<'_>) -> bool {
    tcx.sess.panic_strategy() != PanicStrategy::Abort
        || rrconfig::panic_abort_mode() == rrconfig::PanicAbortMode::Permissive
}

/// Translate the synthetic unwind edge used by closure call shims.
pub(crate) fn closure_unwind(tcx: ty::TyCtxt<'_>) -> code::Stmt {
    closure_unwind_for_strategy(tcx.sess.panic_strategy())
}

fn closure_unwind_for_strategy(strategy: PanicStrategy) -> code::Stmt {
    if strategy == PanicStrategy::Abort { code::Stmt::Stuck } else { code::Stmt::Unwind }
}

pub(crate) fn used_procedure<'def>() -> code::UsedProcedure<'def> {
    code::UsedProcedure::new(
        PANIC_SHIM_LOC.to_owned(),
        code::UsedProcedureSpec::Literal(PANIC_SHIM_SPEC.to_owned()),
        specs::GenericScope::empty(),
        specs::GenericScopeInst::empty(),
        Vec::new(),
    )
}

pub(crate) fn call(unwind: code::Stmt) -> code::Stmt {
    code::Stmt::Call {
        f: code::Expr::MetaParam(PANIC_SHIM_LOC.to_owned()),
        lfts: Vec::new(),
        tys: Vec::new(),
        args: Vec::new(),
        destination: Box::new(None),
        normal: Box::new(code::Stmt::Stuck),
        unwind: Box::new(unwind),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closure_unwind_follows_panic_strategy() {
        assert_eq!(closure_unwind_for_strategy(PanicStrategy::Abort), code::Stmt::Stuck);
        assert_eq!(closure_unwind_for_strategy(PanicStrategy::Unwind), code::Stmt::Unwind);
    }
}
