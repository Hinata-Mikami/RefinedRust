// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use radium::code;
use rr_rustc_interface::middle::mir;

/// Translate a MIR unwind action, delegating cleanup-block translation to the body translator.
pub(crate) fn translate_unwind_action<E>(
    action: mir::UnwindAction,
    translate_cleanup: impl FnOnce(mir::BasicBlock) -> Result<code::Stmt, E>,
) -> Result<code::Stmt, E> {
    match action {
        mir::UnwindAction::Cleanup(target) => translate_cleanup(target),
        mir::UnwindAction::Continue => Ok(code::Stmt::Unwind),
        mir::UnwindAction::Unreachable => Ok(code::Stmt::Stuck),
        mir::UnwindAction::Terminate(_) => Ok(code::Stmt::UnwindTerminate),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn translate(action: mir::UnwindAction) -> code::Stmt {
        translate_unwind_action(action, |target| Ok::<_, ()>(code::Stmt::GotoBlock(target.as_usize())))
            .unwrap()
    }

    #[test]
    fn translates_cleanup() {
        let target = mir::BasicBlock::from_u32(3);
        assert_eq!(translate(mir::UnwindAction::Cleanup(target)), code::Stmt::GotoBlock(3));
    }

    #[test]
    fn translates_continue() {
        assert_eq!(translate(mir::UnwindAction::Continue), code::Stmt::Unwind);
    }

    #[test]
    fn translates_unreachable() {
        assert_eq!(translate(mir::UnwindAction::Unreachable), code::Stmt::Stuck);
    }

    #[test]
    fn translates_terminate() {
        let action = mir::UnwindAction::Terminate(mir::UnwindTerminateReason::Abi);
        assert_eq!(translate(action), code::Stmt::UnwindTerminate);
    }
}
