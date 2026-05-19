// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::trace;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::type_ir::TypeFoldable as _;

use crate::base::TranslationError;
use crate::environment::mir_mapper::{MappingResult, Origin, map_drop_elaborated_to_borrow_checked};
use crate::environment::mir_utils::real_edges::RealEdges;
use crate::environment::{loops, mir_storage};
use crate::error::Message;

/// Index of a Basic Block
pub(crate) type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub(crate) struct Procedure<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    proc_def_id: DefId,
    borrowck_mir: &'tcx mir::Body<'tcx>,
    dropck_mir: mir::Body<'tcx>,
    mapping: MappingResult,
    real_edges: RealEdges,
    loop_info: loops::ProcedureLoops,
}

struct ErasedRegionDetector<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    found: bool,
}

impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for ErasedRegionDetector<'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if matches!(region.kind(), ty::RegionKind::ReErased) {
            self.found = true;
        }
        region
    }
}

impl<'tcx> Procedure<'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    pub(crate) fn new(tcx: ty::TyCtxt<'tcx>, proc_def_id: DefId) -> Self {
        trace!("Encoding procedure {:?}", proc_def_id);
        let local_def_id = proc_def_id.expect_local();
        let borrowck_mir = &mir_storage::retrieve_mir_body(tcx, local_def_id).as_ref().unwrap().body;
        let dropck_mir_ref = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
        let dropck_mir_ref = dropck_mir_ref.borrow();
        let mapping = map_drop_elaborated_to_borrow_checked(borrowck_mir, &dropck_mir_ref);
        let dropck_mir = dropck_mir_ref.clone();
        drop(dropck_mir_ref);

        let real_edges = RealEdges::new(&dropck_mir);
        let loop_info = loops::ProcedureLoops::new(&dropck_mir, &real_edges);

        Self {
            tcx,
            proc_def_id,
            borrowck_mir,
            dropck_mir,
            mapping,
            real_edges,
            loop_info,
        }
    }

    #[must_use]
    pub(crate) const fn loop_info(&self) -> &loops::ProcedureLoops {
        &self.loop_info
    }

    /// Get definition ID of the procedure.
    #[must_use]
    pub(crate) const fn get_id(&self) -> DefId {
        self.proc_def_id
    }

    /// Get the borrowck MIR of the procedure.
    #[must_use]
    pub(crate) const fn borrowck_mir(&self) -> &mir::Body<'tcx> {
        self.borrowck_mir
    }

    /// Get the drop-checked MIR used for body translation.
    #[must_use]
    pub(crate) const fn dropck_mir(&self) -> &mir::Body<'tcx> {
        &self.dropck_mir
    }

    /// Get the mapping from drop-checked MIR locations to borrowck MIR locations.
    #[must_use]
    pub(crate) const fn mapping(&self) -> &MappingResult {
        &self.mapping
    }

    /// Rewrite dropck's synthetic raw-pointer `Box` deref aliases back to the
    /// borrowck-level `Box` deref place. Only dereference uses of the alias are
    /// rewritten; the plain alias local is administrative MIR.
    pub(crate) fn normalize_box_deref_alias_place(&self, pl: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        let Some(alias) = self.mapping.box_deref_alias_for(pl.local) else {
            return *pl;
        };
        if !matches!(pl.projection.first(), Some(mir::ProjectionElem::Deref)) {
            return *pl;
        }

        mir::Place {
            local: alias.box_local(),
            projection: pl.projection,
        }
    }

    /// Get the typing context.
    #[must_use]
    pub(crate) const fn get_tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    /// Get the predecessors of a basic block.
    #[must_use]
    pub(crate) fn predecessors(&self, bbi: mir::BasicBlock) -> &[mir::BasicBlock] {
        self.real_edges.predecessors(bbi)
    }

    /// Get the successors of a basic block.
    #[must_use]
    pub(crate) fn successors(&self, bbi: mir::BasicBlock) -> &[mir::BasicBlock] {
        self.real_edges.successors(bbi)
    }

    /// Check whether a type still contains erased regions.
    pub(crate) fn contains_erased_regions(&self, ty: ty::Ty<'tcx>) -> bool {
        let mut detector = ErasedRegionDetector {
            tcx: self.tcx,
            found: false,
        };
        ty.fold_with(&mut detector);
        detector.found
    }

    pub(crate) fn ensure_region_type(
        &self,
        ty: ty::Ty<'tcx>,
        context: impl FnOnce() -> String,
    ) -> Result<ty::Ty<'tcx>, TranslationError> {
        if self.contains_erased_regions(ty) {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!("region-sensitive type contains erased regions in {}: {ty:?}", context()),
            ))));
        }
        Ok(ty)
    }

    /// Get the region-sensitive borrowck type of a local.
    pub(crate) fn region_type_of_local(&self, local: mir::Local) -> Result<ty::Ty<'tcx>, TranslationError> {
        let ty = self.borrowck_mir.local_decls.get(local).map(|decl| decl.ty).ok_or_else(|| {
            TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(format!(
                "region-sensitive type requested for synthetic dropck local {local:?}"
            ))))
        })?;
        self.ensure_region_type(ty, || format!("local {local:?}"))
    }

    /// Get the region-sensitive borrowck type of a target/dropck place.
    #[allow(dead_code, reason = "region-sensitive call sites are switched in later implementation steps")]
    pub(crate) fn region_type_of_place(
        &self,
        pl: &mir::Place<'tcx>,
    ) -> Result<mir::PlaceTy<'tcx>, TranslationError> {
        let normalized = self.normalize_box_deref_alias_place(pl);
        let pl = &normalized;
        let mut cur_ty = mir::PlaceTy::from_ty(self.region_type_of_local(pl.local)?);

        for elem in pl.projection {
            cur_ty = match elem {
                mir::ProjectionElem::Deref => {
                    let ty = cur_ty.ty.builtin_deref(true).ok_or_else(|| {
                        TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(format!(
                            "deref projection on non-dereferenceable region-sensitive place type {cur_ty:?}"
                        ))))
                    })?;
                    mir::PlaceTy::from_ty(ty)
                },
                mir::ProjectionElem::Field(field, _) => mir::PlaceTy::from_ty(
                    mir::PlaceTy::field_ty(self.tcx, cur_ty.ty, cur_ty.variant_index, field).skip_norm_wip(),
                ),
                mir::ProjectionElem::Downcast(_, variant_idx) => mir::PlaceTy {
                    ty: cur_ty.ty,
                    variant_index: Some(variant_idx),
                },
                mir::ProjectionElem::Index(_) | mir::ProjectionElem::ConstantIndex { .. } => {
                    mir::PlaceTy::from_ty(cur_ty.ty.builtin_index().ok_or_else(|| {
                        TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                            format!(
                                "index projection on non-indexable region-sensitive place type {cur_ty:?}"
                            ),
                        )))
                    })?)
                },
                mir::ProjectionElem::Subslice { from, to, from_end } => {
                    let ty = match cur_ty.ty.kind() {
                        ty::TyKind::Slice(..) => cur_ty.ty,
                        ty::TyKind::Array(inner, _) if !from_end => {
                            ty::Ty::new_array(self.tcx, *inner, to - from)
                        },
                        ty::TyKind::Array(inner, size) if from_end => {
                            let size = size.try_to_target_usize(self.tcx).ok_or_else(|| {
                                TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(format!(
                                    "cannot determine array size for region-sensitive subslice projection of {cur_ty:?}"
                                ))))
                            })?;
                            ty::Ty::new_array(self.tcx, *inner, size - from - to)
                        },
                        _ => {
                            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                                Message::UnsupportedFeature(format!(
                                    "subslice projection on unsupported region-sensitive place type {cur_ty:?}"
                                )),
                            )));
                        },
                    };
                    mir::PlaceTy::from_ty(ty)
                },
                mir::ProjectionElem::OpaqueCast(_) => {
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                        Message::UnsupportedFeature("region-sensitive OpaqueCast place typing".to_owned()),
                    )));
                },
                mir::ProjectionElem::UnwrapUnsafeBinder(_) => {
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                        Message::UnsupportedFeature(
                            "region-sensitive UnwrapUnsafeBinder place typing".to_owned(),
                        ),
                    )));
                },
            };
            self.ensure_region_type(cur_ty.ty, || format!("place {pl:?}"))?;
        }

        Ok(cur_ty)
    }

    /// Get the region-sensitive borrowck type of a target/dropck operand.
    #[allow(dead_code, reason = "region-sensitive call sites are switched in later implementation steps")]
    pub(crate) fn region_type_of_operand(
        &self,
        op: &mir::Operand<'tcx>,
    ) -> Result<ty::Ty<'tcx>, TranslationError> {
        match op {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => Ok(self.region_type_of_place(place)?.ty),
            mir::Operand::Constant(constant) => {
                let ty = constant.const_.ty();
                self.ensure_region_type(ty, || format!("constant operand {op:?}"))
            },
            mir::Operand::RuntimeChecks(_) => {
                Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                    format!("region-sensitive type requested for runtime-check operand {op:?}"),
                ))))
            },
        }
    }

    /// Get the borrowck source statement corresponding to a target/dropck statement location.
    #[allow(dead_code, reason = "region-sensitive rvalue typing is introduced before its call sites")]
    pub(crate) fn source_statement_for_target(&self, loc: mir::Location) -> Option<&mir::Statement<'tcx>> {
        let origin = self.mapping.origin_for_target((loc.block, loc.statement_index))?;
        let (source_block, source_statement_index) = match origin {
            Origin::Source(source) | Origin::FoldedFrom(source) | Origin::SplitFrom(source) => source,
            Origin::Inserted => return None,
        };

        self.borrowck_mir.basic_blocks[source_block].statements.get(source_statement_index)
    }

    /// Get the borrowck source call terminator corresponding to a target/dropck call terminator.
    pub(crate) fn source_call_for_target(&self, loc: mir::Location) -> Option<&mir::Terminator<'tcx>> {
        let origin = self.mapping.origin_for_target((loc.block, loc.statement_index))?;
        let (source_block, source_statement_index) = match origin {
            Origin::Source(source) | Origin::FoldedFrom(source) | Origin::SplitFrom(source) => source,
            Origin::Inserted => return None,
        };

        let source_block_data = &self.borrowck_mir.basic_blocks[source_block];
        if source_statement_index != source_block_data.statements.len() {
            return None;
        }

        let terminator = source_block_data.terminator();
        if matches!(terminator.kind, mir::TerminatorKind::Call { .. }) { Some(terminator) } else { None }
    }

    /// Get the region-sensitive borrowck type of a target/dropck rvalue.
    #[allow(dead_code, reason = "region-sensitive call sites are switched in later implementation steps")]
    pub(crate) fn region_type_of_rvalue(
        &self,
        loc: mir::Location,
        rval: &mir::Rvalue<'tcx>,
    ) -> Result<ty::Ty<'tcx>, TranslationError> {
        if let Some(source_stmt) = self.source_statement_for_target(loc)
            && let mir::StatementKind::Assign(source_assign) = &source_stmt.kind
        {
            let source_rval = &source_assign.as_ref().1;
            let ty = source_rval.ty(&self.borrowck_mir.local_decls, self.tcx);
            return self.ensure_region_type(ty, || format!("source rvalue for target location {loc:?}"));
        }

        let ty = match rval {
            mir::Rvalue::Use(op, _) => self.region_type_of_operand(op)?,
            mir::Rvalue::Ref(region, borrow_kind, place) => {
                let place_ty = self.region_type_of_place(place)?.ty;
                let mutability = match borrow_kind {
                    mir::BorrowKind::Shared | mir::BorrowKind::Fake(_) => ty::Mutability::Not,
                    mir::BorrowKind::Mut { .. } => ty::Mutability::Mut,
                };
                ty::Ty::new_ref(self.tcx, *region, place_ty, mutability)
            },
            mir::Rvalue::RawPtr(_, _)
            | mir::Rvalue::BinaryOp(_, _)
            | mir::Rvalue::UnaryOp(_, _)
            | mir::Rvalue::Discriminant(_)
            | mir::Rvalue::Aggregate(_, _)
            | mir::Rvalue::Cast(_, _, _)
            | mir::Rvalue::CopyForDeref(_)
            | mir::Rvalue::Repeat(_, _)
            | mir::Rvalue::ThreadLocalRef(_)
            | mir::Rvalue::Reborrow(_, _, _)
            | mir::Rvalue::WrapUnsafeBinder(_, _) => rval.ty(&self.dropck_mir.local_decls, self.tcx),
        };

        self.ensure_region_type(ty, || format!("target rvalue at {loc:?}"))
    }
}
