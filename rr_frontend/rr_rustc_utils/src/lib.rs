// © 2026, The RefinedRust Develcpers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utilities shared by crates that directly consume rustc interfaces.
#![feature(iter_order_by)]
#![feature(rustc_private)]

use std::cmp::Ordering;

use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

/// Normalize paths to equivalent definitions re-exported by `core`, `alloc`, and `std`.
#[must_use]
pub fn normalize_def_path_str(def_path: &str) -> String {
    let mut segments = def_path.split("::");
    if let Some(segment) = segments.next()
        && matches!(segment, "core" | "alloc" | "std")
    {
        return format!("std::{}", segments.collect::<Vec<_>>().join("::"));
    }
    def_path.to_owned()
}

/// Compare definitions by their normalized rustc paths, with IDs as deterministic tie-breakers.
#[must_use]
pub fn cmp_def_id_by_path(tcx: ty::TyCtxt<'_>, a: DefId, b: DefId) -> Ordering {
    normalize_def_path_str(&tcx.def_path_str(a))
        .cmp(&normalize_def_path_str(&tcx.def_path_str(b)))
        .then_with(|| a.krate.cmp(&b.krate).then_with(|| a.index.cmp(&b.index)))
}

/// Structural ordering of rustc types using a caller-selected definition ordering.
pub struct RustcComparator<'tcx, F> {
    tcx: ty::TyCtxt<'tcx>,
    cmp_def_ids: F,
}

impl<'tcx, F> RustcComparator<'tcx, F>
where
    F: Fn(ty::TyCtxt<'tcx>, DefId, DefId) -> Ordering,
{
    pub const fn new(tcx: ty::TyCtxt<'tcx>, cmp_def_ids: F) -> Self {
        Self { tcx, cmp_def_ids }
    }

    pub fn cmp_def_id(&self, a: DefId, b: DefId) -> Ordering {
        (self.cmp_def_ids)(self.tcx, a, b)
    }

    pub fn cmp_ty(&self, a: ty::Ty<'tcx>, b: ty::Ty<'tcx>) -> Ordering {
        ty_discriminant(a).cmp(&ty_discriminant(b)).then_with(|| {
            use ty::TyKind;
            match (a.kind(), b.kind()) {
                (TyKind::Int(a), TyKind::Int(b)) => a.cmp(b),
                (TyKind::Uint(a), TyKind::Uint(b)) => a.cmp(b),
                (TyKind::Float(a), TyKind::Float(b)) => a.cmp(b),
                (TyKind::Adt(a_def, a_args), TyKind::Adt(b_def, b_args)) => self
                    .cmp_def_id(a_def.did(), b_def.did())
                    .then_with(|| self.cmp_generic_args(a_args, b_args)),
                (TyKind::Foreign(a), TyKind::Foreign(b)) => self.cmp_def_id(*a, *b),
                (TyKind::Array(a_ty, a_const), TyKind::Array(b_ty, b_const)) => {
                    self.cmp_ty(*a_ty, *b_ty).then_with(|| cmp_const(*a_const, *b_const))
                },
                (TyKind::Pat(..), TyKind::Pat(..)) => unimplemented!("compare Pat"),
                (TyKind::Slice(a), TyKind::Slice(b)) => self.cmp_ty(*a, *b),
                (TyKind::RawPtr(a_ty, a_mut), TyKind::RawPtr(b_ty, b_mut)) => {
                    self.cmp_ty(*a_ty, *b_ty).then_with(|| a_mut.cmp(b_mut))
                },
                (TyKind::Ref(a_region, a_ty, a_mut), TyKind::Ref(b_region, b_ty, b_mut)) => {
                    cmp_region(*a_region, *b_region)
                        .then_with(|| self.cmp_ty(*a_ty, *b_ty).then_with(|| a_mut.cmp(b_mut)))
                },
                (TyKind::FnDef(a_def, a_args), TyKind::FnDef(b_def, b_args)) => self
                    .cmp_def_id(*a_def, *b_def)
                    .then_with(|| self.cmp_bound_generic_args(*a_args, *b_args)),
                (TyKind::FnPtr(..), TyKind::FnPtr(..)) => unimplemented!("compare FnPtr"),
                (TyKind::Dynamic(..), TyKind::Dynamic(..)) => unimplemented!("compare Dynamic"),
                (TyKind::Closure(a_def, a_args), TyKind::Closure(b_def, b_args))
                | (TyKind::CoroutineClosure(a_def, a_args), TyKind::CoroutineClosure(b_def, b_args))
                | (TyKind::Coroutine(a_def, a_args), TyKind::Coroutine(b_def, b_args))
                | (TyKind::CoroutineWitness(a_def, a_args), TyKind::CoroutineWitness(b_def, b_args)) => {
                    self.cmp_def_id(*a_def, *b_def).then_with(|| self.cmp_generic_args(a_args, b_args))
                },
                (TyKind::Tuple(a), TyKind::Tuple(b)) => a.iter().cmp_by(b.iter(), |a, b| self.cmp_ty(a, b)),
                (TyKind::Alias(a_rigid, a), TyKind::Alias(b_rigid, b)) => is_rigid_variant(*a_rigid)
                    .cmp(&is_rigid_variant(*b_rigid))
                    .then_with(|| alias_kind_variant(a.kind).cmp(&alias_kind_variant(b.kind)))
                    .then_with(|| self.cmp_def_id(alias_kind_def_id(a.kind), alias_kind_def_id(b.kind)))
                    .then_with(|| self.cmp_generic_args(a.args, b.args)),
                (TyKind::Param(a), TyKind::Param(b)) => a.cmp(b),
                (TyKind::Bound(a_kind, a_ty), TyKind::Bound(b_kind, b_ty)) => {
                    cmp_bound_var_index_kind(*a_kind, *b_kind).then_with(|| a_ty.var.cmp(&b_ty.var))
                },
                (TyKind::Placeholder(_), TyKind::Placeholder(_)) => unimplemented!("compare Placeholder"),
                (TyKind::Infer(_), TyKind::Infer(_)) => unimplemented!("compare Infer"),
                (TyKind::Error(_), TyKind::Error(_)) => unimplemented!("compare Error"),
                (TyKind::UnsafeBinder(_), TyKind::UnsafeBinder(_)) => unimplemented!("compare UnsafeBinder"),
                (TyKind::Bool, TyKind::Bool)
                | (TyKind::Char, TyKind::Char)
                | (TyKind::Str, TyKind::Str)
                | (TyKind::Never, TyKind::Never) => Ordering::Equal,
                _ => unreachable!(),
            }
        })
    }

    pub fn cmp_tys(&self, a: &[ty::Ty<'tcx>], b: &[ty::Ty<'tcx>]) -> Ordering {
        a.len().cmp(&b.len()).then_with(|| a.iter().cmp_by(b, |a, b| self.cmp_ty(*a, *b)))
    }

    pub fn cmp_generic_args(&self, a: &[ty::GenericArg<'tcx>], b: &[ty::GenericArg<'tcx>]) -> Ordering {
        a.len()
            .cmp(&b.len())
            .then_with(|| a.iter().cmp_by(b, |a, b| self.cmp_generic_arg(*a, *b)))
    }

    pub fn cmp_alias_ty(&self, a: &ty::AliasTy<'tcx>, b: &ty::AliasTy<'tcx>) -> Ordering {
        alias_kind_variant(a.kind)
            .cmp(&alias_kind_variant(b.kind))
            .then_with(|| self.cmp_def_id(alias_kind_def_id(a.kind), alias_kind_def_id(b.kind)))
            .then_with(|| self.cmp_generic_args(a.args.as_slice(), b.args.as_slice()))
    }

    fn cmp_generic_arg(&self, a: ty::GenericArg<'tcx>, b: ty::GenericArg<'tcx>) -> Ordering {
        generic_arg_kind_variant(a.kind()).cmp(&generic_arg_kind_variant(b.kind())).then_with(|| {
            match (a.kind(), b.kind()) {
                (ty::GenericArgKind::Const(a), ty::GenericArgKind::Const(b)) => cmp_const(a, b),
                (ty::GenericArgKind::Type(a), ty::GenericArgKind::Type(b)) => match (a.kind(), b.kind()) {
                    (ty::TyKind::Param(a), ty::TyKind::Param(b)) => a.cmp(b),
                    (ty::TyKind::Param(_), _) => Ordering::Less,
                    (_, ty::TyKind::Param(_)) => Ordering::Greater,
                    _ => self.cmp_ty(a, b),
                },
                (ty::GenericArgKind::Lifetime(a), ty::GenericArgKind::Lifetime(b)) => cmp_region(a, b),
                _ => unreachable!(),
            }
        })
    }

    fn cmp_bound_generic_args(
        &self,
        a: ty::Binder<'tcx, ty::GenericArgsRef<'tcx>>,
        b: ty::Binder<'tcx, ty::GenericArgsRef<'tcx>>,
    ) -> Ordering {
        cmp_bound_variable_kinds(a.bound_vars(), b.bound_vars())
            .then_with(|| self.cmp_generic_args(a.skip_binder(), b.skip_binder()))
    }
}

pub fn stable_comparator(
    tcx: ty::TyCtxt<'_>,
) -> RustcComparator<'_, impl Fn(ty::TyCtxt<'_>, DefId, DefId) -> Ordering> {
    RustcComparator::new(tcx, cmp_def_id_by_path)
}

fn region_discriminant(region: ty::Region<'_>) -> u8 {
    use ty::RegionKind;
    match region.kind() {
        RegionKind::ReEarlyParam(_) => 0,
        RegionKind::ReBound(_, _) => 1,
        RegionKind::ReLateParam(_) => 2,
        RegionKind::ReStatic => 3,
        RegionKind::ReVar(_) => 4,
        RegionKind::RePlaceholder(_) => 5,
        RegionKind::ReErased => 6,
        RegionKind::ReError(_) => 7,
    }
}

fn cmp_region(a: ty::Region<'_>, b: ty::Region<'_>) -> Ordering {
    region_discriminant(a).cmp(&region_discriminant(b)).then_with(|| {
        use ty::RegionKind;
        match (a.kind(), b.kind()) {
            (RegionKind::ReEarlyParam(a), RegionKind::ReEarlyParam(b)) => a.index.cmp(&b.index),
            (RegionKind::ReBound(a_kind, a), RegionKind::ReBound(b_kind, b)) => {
                cmp_bound_var_index_kind(a_kind, b_kind).then_with(|| a.var.cmp(&b.var))
            },
            (RegionKind::ReLateParam(_), RegionKind::ReLateParam(_)) => unimplemented!("compare ReLateParam"),
            (RegionKind::ReVar(a), RegionKind::ReVar(b)) => a.index().cmp(&b.index()),
            (RegionKind::RePlaceholder(_), RegionKind::RePlaceholder(_)) => {
                unimplemented!("compare RePlaceholder")
            },
            (RegionKind::ReStatic, RegionKind::ReStatic)
            | (RegionKind::ReErased, RegionKind::ReErased)
            | (RegionKind::ReError(_), RegionKind::ReError(_)) => Ordering::Equal,
            _ => unreachable!(),
        }
    })
}

fn cmp_bound_var_index_kind(a: ty::BoundVarIndexKind, b: ty::BoundVarIndexKind) -> Ordering {
    match (a, b) {
        (ty::BoundVarIndexKind::Canonical, ty::BoundVarIndexKind::Canonical) => Ordering::Equal,
        (ty::BoundVarIndexKind::Canonical, _) => Ordering::Greater,
        (ty::BoundVarIndexKind::Bound(a), ty::BoundVarIndexKind::Bound(b)) => a.cmp(&b),
        (ty::BoundVarIndexKind::Bound(_), ty::BoundVarIndexKind::Canonical) => Ordering::Less,
    }
}

fn cmp_const(a: ty::Const<'_>, b: ty::Const<'_>) -> Ordering {
    match (a.kind(), b.kind()) {
        (ty::ConstKind::Bound(a_kind, a), ty::ConstKind::Bound(b_kind, b)) => {
            cmp_bound_var_index_kind(a_kind, b_kind).then_with(|| a.var.cmp(&b.var))
        },
        _ => unimplemented!("compare Const"),
    }
}

fn cmp_bound_variable_kinds(a: &[ty::BoundVariableKind<'_>], b: &[ty::BoundVariableKind<'_>]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        a.iter()
            .map(|kind| bound_variable_kind_discriminant(*kind))
            .cmp(b.iter().map(|kind| bound_variable_kind_discriminant(*kind)))
    })
}

const fn bound_variable_kind_discriminant(kind: ty::BoundVariableKind<'_>) -> u8 {
    match kind {
        ty::BoundVariableKind::Ty(_) => 0,
        ty::BoundVariableKind::Region(_) => 1,
        ty::BoundVariableKind::Const => 2,
    }
}

const fn generic_arg_kind_variant(kind: ty::GenericArgKind<'_>) -> u8 {
    match kind {
        ty::GenericArgKind::Const(_) => 0,
        ty::GenericArgKind::Type(_) => 1,
        ty::GenericArgKind::Lifetime(_) => 2,
    }
}

fn ty_discriminant(ty: ty::Ty<'_>) -> u8 {
    use ty::TyKind;
    match ty.kind() {
        TyKind::Bool => 0,
        TyKind::Char => 1,
        TyKind::Int(_) => 2,
        TyKind::Uint(_) => 3,
        TyKind::Float(_) => 4,
        TyKind::Adt(_, _) => 5,
        TyKind::Foreign(_) => 6,
        TyKind::Str => 7,
        TyKind::Array(_, _) => 8,
        TyKind::Slice(_) => 9,
        TyKind::RawPtr(_, _) => 10,
        TyKind::Ref(_, _, _) => 11,
        TyKind::FnDef(_, _) => 12,
        TyKind::FnPtr(..) => 13,
        TyKind::Dynamic(..) => 14,
        TyKind::Closure(_, _) => 15,
        TyKind::CoroutineClosure(_, _) => 16,
        TyKind::Coroutine(_, _) => 17,
        TyKind::CoroutineWitness(_, _) => 18,
        TyKind::Never => 19,
        TyKind::Tuple(_) => 20,
        TyKind::Pat(_, _) => 21,
        TyKind::Alias(..) => 22,
        TyKind::Param(_) => 23,
        TyKind::Bound(_, _) => 24,
        TyKind::Placeholder(_) => 25,
        TyKind::Infer(_) => 26,
        TyKind::Error(_) => 27,
        TyKind::UnsafeBinder(_) => 28,
    }
}

const fn alias_kind_variant(kind: ty::AliasTyKind<'_>) -> u8 {
    match kind {
        ty::AliasTyKind::Projection { .. } => 0,
        ty::AliasTyKind::Inherent { .. } => 1,
        ty::AliasTyKind::Opaque { .. } => 2,
        ty::AliasTyKind::Free { .. } => 3,
    }
}

const fn alias_kind_def_id(kind: ty::AliasTyKind<'_>) -> DefId {
    match kind {
        ty::AliasTyKind::Projection { def_id }
        | ty::AliasTyKind::Inherent { def_id }
        | ty::AliasTyKind::Opaque { def_id }
        | ty::AliasTyKind::Free { def_id } => def_id,
    }
}

const fn is_rigid_variant(is_rigid: ty::IsRigid) -> u8 {
    match is_rigid {
        ty::IsRigid::No => 0,
        ty::IsRigid::Yes => 1,
    }
}
