// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Rust-side layout dependency analysis for ADTs.
//!
//! This is deliberately independent from the main type translation walk. It computes which Rust ADTs
//! are reachable through unguarded layout positions of another ADT. Consumers can later restrict the
//! result to the subset they care about, e.g. the members of a recursive type bundle.

use std::collections::BTreeSet;

use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::base::OrderedDefId;

/// Collect all ADTs reachable from `adt_did` through unguarded layout positions.
///
/// References and raw pointers are layout guards and stop the walk. ADTs are recorded and then
/// expanded structurally, so pointer-backed containers such as `Box<T>` and `Vec<T>` naturally stop
/// before reaching `T` once the walk gets to their pointer fields.
pub(crate) fn collect_adt_layout_deps(tcx: ty::TyCtxt<'_>, adt_did: DefId) -> BTreeSet<OrderedDefId> {
    let typing_env = ty::TypingEnv::post_analysis(tcx, adt_did);
    let mut collector = Collector {
        tcx,
        typing_env,
        deps: BTreeSet::new(),
        visited_adts: BTreeSet::new(),
    };

    let adt = tcx.adt_def(adt_did);
    let root_ty = tcx.type_of(adt_did).instantiate_identity().skip_norm_wip();
    if let ty::TyKind::Adt(_, args) = root_ty.kind() {
        collector.walk_adt_fields(adt, args);
    }

    collector.deps
}

struct Collector<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    deps: BTreeSet<OrderedDefId>,
    visited_adts: BTreeSet<String>,
}

impl<'tcx> Collector<'tcx> {
    fn walk_ty(&mut self, ty: ty::Ty<'tcx>) {
        let ty = self.normalize(ty);

        // These type constructors guard their contained type's layout behind a pointer-sized
        // representation, so the contained type is not an unguarded layout dependency.
        if matches!(ty.kind(), ty::TyKind::Ref(..) | ty::TyKind::RawPtr(..)) {
            return;
        }

        match ty.kind() {
            ty::TyKind::Adt(adt, args) => {
                self.deps.insert(OrderedDefId::new(self.tcx, adt.did()));
                self.walk_adt_fields(*adt, args);
            },

            ty::TyKind::Array(ty, _) => self.walk_ty(*ty),

            ty::TyKind::Tuple(args) => {
                for ty in *args {
                    self.walk_ty(ty);
                }
            },

            ty::TyKind::Closure(_, args) => {
                let closure_args = args.as_closure();
                self.walk_ty(closure_args.tupled_upvars_ty());
            },

            _ => {},
        }
    }

    fn walk_adt_fields(&mut self, adt: ty::AdtDef<'tcx>, args: ty::GenericArgsRef<'tcx>) {
        let key = format!("{}<{:?}>", adt.did().index.as_usize(), args);
        if !self.visited_adts.insert(key) {
            return;
        }

        for variant in adt.variants() {
            for field in &variant.fields {
                let field_ty = self.tcx.type_of(field.did).instantiate(self.tcx, args).skip_norm_wip();
                self.walk_ty(field_ty);
            }
        }
    }

    fn normalize(&self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        self.tcx
            .try_normalize_erasing_regions(self.typing_env, ty::Unnormalized::dummy(ty))
            .unwrap_or(ty)
    }
}
