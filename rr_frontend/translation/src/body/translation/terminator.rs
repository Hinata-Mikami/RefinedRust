// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use log::{info, trace, warn};
use rr_rustc_interface::middle::{mir, ty};

use super::TX;
use crate::base::*;
use crate::environment::borrowck::facts;
use crate::search;

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Check if a call goes to `std::rt::begin_panic`
    fn is_call_destination_panic(&mut self, func: &mir::Operand) -> bool {
        let mir::Operand::Constant(box c) = func else {
            return false;
        };

        let mir::ConstantKind::Val(_, ty) = c.literal else {
            return false;
        };

        let ty::TyKind::FnDef(did, _) = ty.kind() else {
            return false;
        };

        if let Some(panic_id_std) =
            search::try_resolve_did(self.env.tcx(), &["std", "panicking", "begin_panic"])
        {
            if panic_id_std == *did {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of std::panicking::begin_panic");
        }

        if let Some(panic_id_core) = search::try_resolve_did(self.env.tcx(), &["core", "panicking", "panic"])
        {
            if panic_id_core == *did {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of core::panicking::panic");
        }

        false
    }

    /// Translate a terminator.
    /// We pass the dying loans during this terminator. They need to be added at the right
    /// intermediate point.
    pub(super) fn translate_terminator(
        &mut self,
        term: &mir::Terminator<'tcx>,
        loc: mir::Location,
        dying_loans: Vec<facts::Loan>,
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        let mut endlfts = self.generate_endlfts(dying_loans.into_iter());

        match &term.kind {
            mir::TerminatorKind::Goto { target } => self.translate_goto_like(&loc, *target),

            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                trace!("translating Call {:?}", term);
                if self.is_call_destination_panic(func) {
                    info!("Replacing call to std::panicking::begin_panic with Stuck");
                    return Ok(radium::Stmt::Stuck);
                }

                self.translate_function_call(func, args, destination, *target, loc, endlfts)
            },

            mir::TerminatorKind::Return => {
                // TODO: this requires additional handling for reborrows

                // read from the return place
                // Is this semantics accurate wrt what the intended MIR semantics is?
                // Possibly handle this differently by making the first argument of a function a dedicated
                // return place? See also discussion at https://github.com/rust-lang/rust/issues/71117
                let stmt = radium::Stmt::Return(radium::Expr::Use {
                    ot: (&self.return_synty).into(),
                    e: Box::new(radium::Expr::Var(self.return_name.clone())),
                });

                // TODO is this right?
                Ok(radium::Stmt::Prim(endlfts, Box::new(stmt)))
            },

            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let operand = self.translate_operand(discr, true)?;
                let all_targets: &[mir::BasicBlock] = targets.all_targets();

                if self.get_type_of_operand(discr).is_bool() {
                    // we currently special-case this as Caesium has a built-in if and this is more
                    // convenient to handle for the type-checker

                    // implementation detail: the first index is the `false` branch, the second the
                    // `true` branch
                    let true_target = all_targets[1];
                    let false_target = all_targets[0];

                    let true_branch = self.translate_goto_like(&loc, true_target)?;
                    let false_branch = self.translate_goto_like(&loc, false_target)?;

                    let stmt = radium::Stmt::If {
                        e: operand,
                        ot: radium::OpType::Bool,
                        s1: Box::new(true_branch),
                        s2: Box::new(false_branch),
                    };

                    // TODO: is this right?
                    return Ok(radium::Stmt::Prim(endlfts, Box::new(stmt)));
                }

                //info!("switchint: {:?}", term.kind);
                let operand = self.translate_operand(discr, true)?;
                let ty = self.get_type_of_operand(discr);

                let mut target_map: HashMap<u128, usize> = HashMap::new();
                let mut translated_targets: Vec<radium::Stmt> = Vec::new();

                for (idx, (tgt, bb)) in targets.iter().enumerate() {
                    let bb: mir::BasicBlock = bb;
                    let translated_target = self.translate_goto_like(&loc, bb)?;

                    target_map.insert(tgt, idx);
                    translated_targets.push(translated_target);
                }

                let translated_default = self.translate_goto_like(&loc, targets.otherwise())?;
                // TODO: need to put endlfts infront of gotos?

                let translated_ty = self.ty_translator.translate_type(ty)?;
                let radium::Type::Int(it) = translated_ty else {
                    return Err(TranslationError::UnknownError(
                        "SwitchInt switching on non-integer type".to_owned(),
                    ));
                };

                Ok(radium::Stmt::Switch {
                    e: operand,
                    it,
                    index_map: target_map,
                    bs: translated_targets,
                    def: Box::new(translated_default),
                })
            },

            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                // this translation gets stuck on failure
                let cond_translated = self.translate_operand(cond, true)?;
                let comp = radium::Expr::BinOp {
                    o: radium::Binop::Eq,
                    ot1: radium::OpType::Bool,
                    ot2: radium::OpType::Bool,
                    e1: Box::new(cond_translated),
                    e2: Box::new(radium::Expr::Literal(radium::Literal::Bool(*expected))),
                };

                let stmt = self.translate_goto_like(&loc, *target)?;

                // TODO: should we really have this?
                endlfts.insert(0, radium::PrimStmt::AssertS(comp));
                Ok(radium::Stmt::Prim(endlfts, Box::new(stmt)))
            },

            mir::TerminatorKind::Drop { place, target, .. } => {
                let ty = self.get_type_of_place(place);
                self.register_drop_shim_for(ty.ty);

                let place_translated = self.translate_place(place)?;
                let _drope = radium::Expr::DropE(Box::new(place_translated));

                let stmt = self.translate_goto_like(&loc, *target)?;

                Ok(radium::Stmt::Prim(endlfts, Box::new(stmt)))
            },

            // just a goto for our purposes
            mir::TerminatorKind::FalseEdge { real_target, .. }
            // this is just a virtual edge for the borrowchecker, we can translate this to a normal goto
            | mir::TerminatorKind::FalseUnwind { real_target, .. } => {
                self.translate_goto_like(&loc, *real_target)
            },

            mir::TerminatorKind::Unreachable => Ok(radium::Stmt::Stuck),

            mir::TerminatorKind::UnwindResume => Err(TranslationError::Unimplemented {
                description: "implement UnwindResume".to_owned(),
            }),

            mir::TerminatorKind::UnwindTerminate(_) => Err(TranslationError::Unimplemented {
                description: "implement UnwindTerminate".to_owned(),
            }),

            mir::TerminatorKind::GeneratorDrop
            | mir::TerminatorKind::InlineAsm { .. }
            | mir::TerminatorKind::Yield { .. } => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of terminator (got: {:?})",
                    term
                ),
            }),
        }
    }
}
