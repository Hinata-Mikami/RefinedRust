// © 2025, The RefinedRust Develcpers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Procedures for checking whether two types are the same modulo renaming of variables.

use std::collections::HashMap;
use std::mem;

use log::{info, trace};
use rr_rustc_interface::hir::def_id::{DefId, CRATE_DEF_INDEX};
use rr_rustc_interface::middle::ty::{self, TyCtxt};
use rr_rustc_interface::{middle, span};

use crate::{types, unification};

type UnificationMap<'a, 'tcx> = &'a mut HashMap<u32, ty::GenericArg<'tcx>>;

pub fn unify_args<'tcx>(
    arg1: ty::GenericArg<'tcx>,
    arg2: ty::GenericArg<'tcx>,
    mapping: UnificationMap<'_, 'tcx>,
) -> bool {
    match arg1.unpack() {
        ty::GenericArgKind::Type(ty1) => {
            let Some(ty2) = arg2.as_type() else {
                return false;
            };
            unify_types(ty1, ty2, mapping)
        },
        ty::GenericArgKind::Const(c) => {
            // TODO
            false
        },
        ty::GenericArgKind::Lifetime(l) => {
            // TODO
            false
        },
    }
}
pub fn unify_generic_args<'tcx>(
    arg1: ty::GenericArgsRef<'tcx>,
    arg2: ty::GenericArgsRef<'tcx>,
    mapping: UnificationMap<'_, 'tcx>,
) -> bool {
    if arg1.len() != arg2.len() {
        return false;
    }
    for (a1, a2) in arg1.iter().zip(arg2.iter()) {
        if !unify_args(a1, a2, mapping) {
            return false;
        }
    }
    true
}
pub fn unify_types<'tcx>(ty1: ty::Ty<'tcx>, ty2: ty::Ty<'tcx>, mapping: UnificationMap<'_, 'tcx>) -> bool {
    match ty1.kind() {
        ty::TyKind::Adt(adt, args1) => {
            let ty::TyKind::Adt(adt2, args2) = ty2.kind() else {
                return false;
            };
            if adt != adt2 {
                return false;
            }

            unify_generic_args(args1, args2, mapping)
        },
        ty::TyKind::Param(p1) => {
            let ty::TyKind::Param(p2) = ty2.kind() else {
                return false;
            };
            let idx1 = p1.index;
            if let Some(a1) = mapping.get(&idx1) {
                let a1 = a1.to_owned();
                let Some(ty1x) = a1.as_type() else {
                    return false;
                };
                // check that it is the same param
                ty1x.is_param(p2.index)
            } else {
                // map idx1 to the type
                let a2 = ty::GenericArg::from(ty2);
                mapping.insert(idx1, a2);
                true
            }
        },
        _ => ty1 == ty2,
    }
}

/// Determine whether the two argument lists match for the type positions (ignoring consts and regions).
/// The first argument is the authority determining which argument positions are types.
/// The second argument may contain `None` for non-type positions.
pub fn args_unify_types<'tcx>(
    reference: &[ty::GenericArg<'tcx>],
    compare: &[Option<ty::GenericArg<'tcx>>],
    mapping: UnificationMap<'_, 'tcx>,
) -> bool {
    if reference.len() != compare.len() {
        return false;
    }

    for (arg1, arg2) in reference.iter().zip(compare.iter()) {
        // TODO check if other kinds of args are unifiable
        if let Some(ty1) = arg1.as_type() {
            if let Some(arg2) = arg2 {
                if let Some(ty2) = arg2.as_type() {
                    if !unify_types(ty1, ty2, mapping) {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }
    }
    true
}
