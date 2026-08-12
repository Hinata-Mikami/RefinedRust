// © 2026, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

mod basicblock;
mod tx_impl;

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};

use attribute_parse::parse;
use log::{info, trace};
use radium::{code, coq, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::mir_dataflow::impls::always_storage_live_locals;
use rr_rustc_interface::{abi, hir};
use typed_arena::Arena;

use crate::base::*;
use crate::body::mir_lowering::{MirTranslationCtx as _, MirTypeTranslation as _, TranslationKey};
use crate::body::panic;
use crate::environment::mir_utils::box_alias;
use crate::error::Message;
use crate::spec_parsers::parse_utils;
use crate::traits::registry;
use crate::{attrs, environment, procedures, types};

/// Translator for rustc-generated drop-glue MIR shims.
///
/// This deliberately does not reuse normal function translation state such as `Procedure`,
/// Polonius annotations, borrowck/dropck mappings, or loop handling.
pub(crate) struct DropGlueTX<'a, 'def, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    adt_did: DefId,
    mir_source_ty: ty::Ty<'tcx>,
    body: &'tcx mir::Body<'tcx>,
    procedure_registry: &'a procedures::Scope<'tcx, 'def>,
    ty_translator: &'def types::TX<'def, 'tcx>,
    generic_scope: types::scope::Params<'tcx, 'def>,
    variable_map: HashMap<mir::Local, String>,
    box_deref_aliases: HashMap<mir::Local, mir::Place<'tcx>>,
    always_live_locals: Vec<mir::Local>,
    collected_procedures: HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>>,
    panic_shim_used: bool,
    used_literals: RefCell<BTreeMap<types::scope::AdtUseKey, specs::types::LiteralUse<'def>>>,
    used_tuples: RefCell<BTreeMap<Vec<lang::SynType>, specs::types::LiteralUse<'def>>>,
    drop_glue_trait_ref: specs::traits::RefInst<'def>,
    extra_context_items: coq::binder::BinderList,
    translated_fn: code::FunctionBuilder<'def>,
    bb_queue: Vec<mir::BasicBlock>,
    processed_bbs: HashSet<mir::BasicBlock>,
}

pub(crate) struct TranslatedDropGlue<'def> {
    pub(crate) function: code::Function<'def>,
    pub(crate) trait_ref: specs::traits::RefInst<'def>,
    pub(crate) extra_context_items: coq::binder::BinderList,
}

pub(crate) struct SpeccedDropGlue<'def> {
    pub(crate) spec: specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>,
    pub(crate) trait_ref: specs::traits::RefInst<'def>,
    pub(crate) extra_context_items: coq::binder::BinderList,
}

impl<'a, 'def: 'a, 'tcx: 'def> DropGlueTX<'a, 'def, 'tcx> {
    pub(crate) fn new(
        tcx: ty::TyCtxt<'tcx>,
        meta: &procedures::Meta,
        adt_ty: ty::Ty<'tcx>,
        mir_source_ty: ty::Ty<'tcx>,
        procedure_registry: &'a procedures::Scope<'tcx, 'def>,
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
    ) -> Result<Self, TranslationError> {
        let ty::TyKind::Adt(adt_def, adt_args) = adt_ty.kind() else {
            return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                format!("drop-glue translation expected an ADT type, got {adt_ty:?}"),
            ))));
        };
        let adt_did = adt_def.did();

        let typing_env = ty::TypingEnv::post_analysis(tcx, adt_did);
        if !tcx.needs_drop_raw(typing_env.as_query_input(adt_ty)) {
            return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                format!("drop-glue translation requested for trivially droppable type {adt_ty:?}"),
            ))));
        }

        let span = tcx.def_span(adt_did);
        let drop_glue_did = tcx.require_lang_item(hir::LangItem::DropGlue, span);
        let shim = ty::ShimKind::DropGlue(drop_glue_did, Some(mir_source_ty));
        let body = tcx.mir_shims(shim);
        Self::log_mir(tcx, adt_did, adt_ty, mir_source_ty, body);

        let mut translated_fn = Self::make_function_builder(meta);
        let generic_scope = Self::setup_generic_scope(
            tcx,
            adt_did,
            adt_args,
            ty_translator,
            trait_registry,
            &mut translated_fn,
        )?;
        let extra_context_items = Self::parse_adt_context_items(tcx, adt_did, &generic_scope)?;
        for binder in extra_context_items.0.clone() {
            translated_fn.add_late_coq_param(binder);
        }
        let used_literals = RefCell::new(BTreeMap::new());
        let used_tuples = RefCell::new(BTreeMap::new());
        let translated_adt_ty = Self::translate_adt_type(
            tcx,
            adt_did,
            adt_ty,
            ty_translator,
            &generic_scope,
            &used_literals,
            &used_tuples,
        )?;
        let drop_glue_trait_ref = Self::add_drop_glue_trait_spec(
            tcx,
            trait_registry,
            adt_did,
            &mut translated_fn,
            &generic_scope,
            &translated_adt_ty,
        )?;
        let box_deref_aliases = box_alias::collect_box_deref_aliases(tcx, body);
        let (variable_map, always_live_locals) = Self::initialize_locals(tcx, body, &mut translated_fn)?;

        Ok(Self {
            tcx,
            adt_did,
            mir_source_ty,
            body,
            procedure_registry,
            ty_translator,
            generic_scope,
            variable_map,
            box_deref_aliases,
            always_live_locals,
            collected_procedures: HashMap::new(),
            panic_shim_used: false,
            used_literals,
            used_tuples,
            drop_glue_trait_ref,
            extra_context_items,
            translated_fn,
            bb_queue: vec![mir::BasicBlock::from_u32(0)],
            processed_bbs: HashSet::new(),
        })
    }

    fn log_mir(
        tcx: ty::TyCtxt<'tcx>,
        adt_did: DefId,
        adt_ty: ty::Ty<'tcx>,
        mir_source_ty: ty::Ty<'tcx>,
        body: &mir::Body<'tcx>,
    ) {
        info!(
            "Drop-glue MIR for {} ({adt_did:?}, logical {adt_ty:?}, MIR source {mir_source_ty:?}): {} locals, {} basic blocks",
            tcx.def_path_str(adt_did),
            body.local_decls.len(),
            body.basic_blocks.len()
        );
        trace!("drop-glue MIR body: {body:?}");
        for (local, decl) in body.local_decls.iter_enumerated() {
            trace!("drop-glue local {local:?}: {:?}", decl.ty);
        }
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            trace!("drop-glue {bb:?} terminator: {:?}", data.terminator().kind);
        }
    }

    fn make_function_builder(meta: &procedures::Meta) -> code::FunctionBuilder<'def> {
        code::FunctionBuilder::new(
            meta.get_name(),
            meta.get_code_name(),
            meta.get_spec_name(),
            meta.get_trait_req_incl_name(),
        )
    }

    fn setup_generic_scope(
        tcx: ty::TyCtxt<'tcx>,
        adt_did: DefId,
        adt_args: ty::GenericArgsRef<'tcx>,
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        translated_fn: &mut code::FunctionBuilder<'def>,
    ) -> Result<types::scope::Params<'tcx, 'def>, TranslationError> {
        let mut generic_scope = types::scope::Params::new_from_generics(tcx, adt_args, Some(adt_did));
        generic_scope.add_param_env(adt_did, tcx, ty_translator, trait_registry)?;
        let mut function_scope: specs::GenericScope<'_, specs::traits::LiteralSpecUseRef<'_>> =
            generic_scope.clone().into();
        function_scope.make_direct_params_surrounding();
        translated_fn.provide_generic_scope(function_scope);
        Ok(generic_scope)
    }

    fn parse_adt_context_items(
        tcx: ty::TyCtxt<'tcx>,
        adt_did: DefId,
        generic_scope: &types::scope::Params<'tcx, 'def>,
    ) -> Result<coq::binder::BinderList, TranslationError> {
        let attrs = environment::get_attributes(tcx, adt_did);
        let attrs = attrs::filter_for_tool(attrs);
        let mut context_items = Vec::new();

        for attr in attrs {
            let Some(seg) = attr.path.segments.get(1) else {
                continue;
            };
            if seg.as_str() != "context" {
                continue;
            }

            let buffer = parse::Buffer::new(&parse_utils::attr_args_tokens(&attr.args));
            let binder = parse_utils::parse_context_item(&buffer, generic_scope).map_err(|err| {
                TranslationError::ErrorReported(
                    tcx.dcx().span_err(attr.span, Message::AttributeError(parse_utils::str_err(err))),
                )
            })?;
            context_items.push(binder);
        }

        Ok(coq::binder::BinderList::new(context_items))
    }

    fn translate_adt_type(
        tcx: ty::TyCtxt<'tcx>,
        adt_did: DefId,
        adt_ty: ty::Ty<'tcx>,
        ty_translator: &'def types::TX<'def, 'tcx>,
        generic_scope: &types::scope::Params<'tcx, 'def>,
        used_literals: &RefCell<BTreeMap<types::scope::AdtUseKey, specs::types::LiteralUse<'def>>>,
        used_tuples: &RefCell<BTreeMap<Vec<lang::SynType>, specs::types::LiteralUse<'def>>>,
    ) -> Result<specs::Type<'def>, TranslationError> {
        let typing_env = ty::TypingEnv::post_analysis(tcx, adt_did);
        let mut shim_state = types::STInner::ShimTranslation(Box::new(types::ShimState::new(
            typing_env,
            generic_scope.clone(),
            used_literals,
            used_tuples,
        )));
        // Keep the shim translation pass for collecting ADT/tuple layout assumptions, but do not
        // use its result for the spec: shim translation intentionally erases regions to DUMMY.
        ty_translator.translate_type_in_state(adt_ty, &mut shim_state)?;

        ty_translator.translate_type_in_scope(generic_scope, typing_env, adt_ty)
    }

    fn make_drop_glue_trait_inst(translated_adt_ty: &specs::Type<'def>) -> specs::GenericScopeInst<'def> {
        let mut trait_inst = specs::GenericScopeInst::empty();
        // DropGlue has only Self; the ADT generics live in the impl scope.
        trait_inst.add_direct_ty_param(translated_adt_ty.clone());
        trait_inst
    }

    fn add_drop_glue_trait_spec(
        tcx: ty::TyCtxt<'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        adt_did: DefId,
        translated_fn: &mut code::FunctionBuilder<'def>,
        generic_scope: &types::scope::Params<'tcx, 'def>,
        translated_adt_ty: &specs::Type<'def>,
    ) -> Result<specs::traits::RefInst<'def>, TranslationError> {
        let impl_key = registry::VirtualImpl::DropGlueForAdt(OrderedDefId::new(tcx, adt_did));
        let trait_inst = Self::make_drop_glue_trait_inst(translated_adt_ty);

        let ref_inst = trait_registry.get_virtual_impl_info(
            impl_key,
            trait_inst,
            generic_scope.clone().into(),
            specs::traits::SpecAttrsInst::new(BTreeMap::new()),
        )?;

        translated_fn.add_trait_function_spec(specs::traits::InstantiatedFunctionSpec::new(
            ref_inst.clone(),
            "drop_glue".to_owned(),
        ));
        Ok(ref_inst)
    }

    fn initialize_locals(
        tcx: ty::TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        translated_fn: &mut code::FunctionBuilder<'def>,
    ) -> Result<(HashMap<mir::Local, String>, Vec<mir::Local>), TranslationError> {
        let ptr_local = mir::Local::from_u32(1);
        let ptr_decl = body.local_decls.get(ptr_local).ok_or_else(|| {
            TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                "drop-glue MIR does not have an argument local `_1`".to_owned(),
            )))
        })?;
        if body.local_kind(ptr_local) != mir::LocalKind::Arg {
            return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                format!("drop-glue MIR local `_1` is not an argument: {:?}", body.local_kind(ptr_local)),
            ))));
        }
        if !matches!(ptr_decl.ty.kind(), ty::TyKind::Ref(_, _, hir::Mutability::Mut)) {
            return Err(TranslationError::ErrorReported(tcx.dcx().err(Message::UnsupportedFeature(
                format!("drop-glue MIR argument `_1` is not a mutable reference: {:?}", ptr_decl.ty),
            ))));
        }

        let mut variable_map = HashMap::new();
        let always_live = always_storage_live_locals(body);
        let mut always_live_locals = Vec::new();
        for local in body.local_decls.indices() {
            let name = if local == mir::Local::from_u32(0) {
                "ret".to_owned()
            } else if local == ptr_local {
                "ptr".to_owned()
            } else {
                format!("__{}", local.index())
            };
            if body.local_kind(local) != mir::LocalKind::Arg && always_live.contains(local) {
                always_live_locals.push(local);
            }
            variable_map.insert(local, name);
        }
        translated_fn.code.add_argument("ptr", lang::SynType::Ptr);
        Ok((variable_map, always_live_locals))
    }

    pub(super) fn normalize_box_deref_alias_place(&self, place: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        box_alias::normalize_deref_alias_place(self.tcx, place, |local| {
            self.box_deref_aliases.get(&local).copied()
        })
    }

    pub(super) fn initial_always_live_stmts(&self) -> Result<Vec<code::PrimStmt>, TranslationError> {
        let mut prim_stmts = Vec::new();
        for local in &self.always_live_locals {
            let Some(local_name) = self.variable_map.get(local) else {
                continue;
            };
            let ty = self.shape_type_of_local(*local)?;
            let translated_st = self.translate_type_to_syn_type(ty)?;
            let var = code::Variable::new(local_name.to_owned(), translated_st);
            prim_stmts.push(code::PrimStmt::LocalLive(var));
        }
        Ok(prim_stmts)
    }

    /// Translate all reachable drop-glue basic blocks starting from `_bb0`.
    pub(crate) fn translate_basic_blocks(&mut self) -> Result<(), TranslationError> {
        let basic_blocks = &self.body.basic_blocks;

        while let Some(bb_idx) = self.bb_queue.pop() {
            if !self.processed_bbs.insert(bb_idx) {
                continue;
            }

            let Some(bb) = basic_blocks.get(bb_idx) else {
                return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                    Message::UnsupportedFeature(format!(
                        "drop-glue MIR refers to missing basic block {bb_idx:?}"
                    )),
                )));
            };

            let translated_bb = self.translate_basic_block(bb_idx, bb)?;
            self.translated_fn.code.add_basic_block(bb_idx.as_usize(), translated_bb);
        }

        Ok(())
    }

    /// Translate and finalize the drop-glue function.
    pub(crate) fn translate(
        mut self,
        fn_arena: &'def Arena<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,
    ) -> Result<TranslatedDropGlue<'def>, TranslationError> {
        self.translate_basic_blocks()?;

        for ty in self.generic_scope.tyvars() {
            self.translated_fn.assume_synty_layoutable(lang::SynType::Literal(ty.syn_type()));
        }
        for literal_use in self.used_literals.borrow().values() {
            self.translated_fn.assume_synty_layoutable(literal_use.generate_syn_type_term());
        }
        for tuple_use in self.used_tuples.borrow().values() {
            self.translated_fn.assume_synty_layoutable(tuple_use.generate_syn_type_term());
        }

        let mut used_procs: Vec<_> = self.collected_procedures.iter().collect();
        used_procs.sort_by(|a, b| a.0.cmp(self.tcx, b.0));
        for (_, used_proc) in used_procs {
            self.translated_fn.require_function(used_proc.clone());
        }
        if self.panic_shim_used {
            self.translated_fn.require_function(panic::used_procedure());
        }
        panic::add_strategy_link_assumption(self.tcx, &mut self.translated_fn, false);

        let trait_ref = self.drop_glue_trait_ref.clone();
        let extra_context_items = self.extra_context_items.clone();
        let function = self.translated_fn.into_function(fn_arena);
        Ok(TranslatedDropGlue {
            function,
            trait_ref,
            extra_context_items,
        })
    }

    fn call_panic_shim(&mut self, unwind: code::Stmt) -> code::Stmt {
        if !panic::local_panic_uses_shim(self.tcx) {
            return code::Stmt::Stuck;
        }
        self.panic_shim_used = true;
        panic::call(unwind)
    }

    /// Finalize only the drop-glue function spec, without translating MIR/code.
    pub(crate) fn generate_spec(self) -> Result<SpeccedDropGlue<'def>, TranslationError> {
        let trait_ref = self.drop_glue_trait_ref.clone();
        let extra_context_items = self.extra_context_items.clone();
        let spec = self.translated_fn.try_into().map_err(|err| {
            TranslationError::ErrorReported(self.tcx.dcx().err(Message::AttributeError(err)))
        })?;
        Ok(SpeccedDropGlue {
            spec,
            trait_ref,
            extra_context_items,
        })
    }

    /// Enqueue a successor block for translation if it has not been processed yet.
    pub(crate) fn enqueue_basic_block(&mut self, bb: mir::BasicBlock) {
        if !self.processed_bbs.contains(&bb) && !self.bb_queue.contains(&bb) {
            self.bb_queue.push(bb);
        }
    }

    /// Reconstruct the semantic type of a drop-glue place from the enclosing ADT type.
    ///
    /// rustc's drop-glue MIR erases regions on projected field types, so this must not use
    /// `Place::ty`. Instead, start at `_1: &mut Self` and replay the projection on `self.adt_ty`.
    pub(super) fn semantic_type_of_place(
        &self,
        place: &mir::Place<'tcx>,
    ) -> Result<ty::Ty<'tcx>, TranslationError> {
        let normalized = self.normalize_box_deref_alias_place(place);
        let place = &normalized;

        let ptr_local = mir::Local::from_u32(1);
        if place.local != ptr_local {
            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!("drop-glue semantic place typing only supports places rooted at `_1`, got {place:?}"),
            ))));
        }

        let mut current_ty = ty::Ty::new_mut_ref(self.tcx, self.tcx.lifetimes.re_erased, self.mir_source_ty);
        let mut current_variant = None;

        for projection in place.projection {
            match projection {
                mir::ProjectionElem::Deref => {
                    current_ty = match current_ty.kind() {
                        ty::TyKind::Ref(_, inner, _) | ty::TyKind::RawPtr(inner, _) => *inner,
                        ty::TyKind::Adt(adt_def, args) if adt_def.is_box() => {
                            let [inner, _alloc] = args.as_slice() else {
                                return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                                    Message::UnsupportedFeature(format!(
                                        "drop-glue semantic place typing got Box with unexpected args {args:?} in {place:?}"
                                    )),
                                )));
                            };
                            inner.expect_ty()
                        },
                        _ => {
                            return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                                Message::UnsupportedFeature(format!(
                                    "drop-glue semantic place typing cannot dereference {current_ty:?} in {place:?}"
                                )),
                            )));
                        },
                    };
                    current_variant = None;
                },

                mir::ProjectionElem::Downcast(_, variant) => {
                    if !matches!(current_ty.kind(), ty::TyKind::Adt(adt_def, _) if adt_def.is_enum()) {
                        return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                            Message::UnsupportedFeature(format!(
                                "drop-glue semantic place typing got downcast of non-enum {current_ty:?} in {place:?}"
                            )),
                        )));
                    }
                    current_variant = Some(variant);
                },

                mir::ProjectionElem::Field(field, _) => {
                    current_ty = self.semantic_type_of_field(current_ty, current_variant, field, place)?;
                    current_variant = None;
                },

                _ => {
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                        Message::UnsupportedFeature(format!(
                            "drop-glue semantic place typing does not support projection {projection:?} in {place:?}"
                        )),
                    )));
                },
            }
        }

        Ok(current_ty)
    }

    fn semantic_type_of_field(
        &self,
        current_ty: ty::Ty<'tcx>,
        current_variant: Option<abi::VariantIdx>,
        field: abi::FieldIdx,
        place: &mir::Place<'tcx>,
    ) -> Result<ty::Ty<'tcx>, TranslationError> {
        match current_ty.kind() {
            ty::TyKind::Adt(adt_def, adt_args) => {
                if adt_def.is_union() {
                    return Err(TranslationError::ErrorReported(self.tcx.dcx().err(
                        Message::UnsupportedFeature(format!(
                            "drop-glue semantic place typing does not support union field projection in {place:?}"
                        )),
                    )));
                }

                let variant = if adt_def.is_enum() {
                    current_variant.ok_or_else(|| {
                        TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                            format!(
                                "drop-glue semantic place typing needs a downcast before enum field projection in {place:?}"
                            ),
                        )))
                    })?
                } else {
                    abi::VariantIdx::from_u32(0)
                };

                let variant_def = adt_def.variant(variant);
                let field_def = variant_def.fields.get(field).ok_or_else(|| {
                    TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(format!(
                        "drop-glue semantic place typing got missing field {field:?} of {current_ty:?} in {place:?}"
                    ))))
                })?;
                Ok(field_def.ty(self.tcx, adt_args).skip_norm_wip())
            },

            ty::TyKind::Tuple(fields) => fields.get(field.as_usize()).copied().ok_or_else(|| {
                TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(format!(
                    "drop-glue semantic place typing got missing tuple field {field:?} of {current_ty:?} in {place:?}"
                ))))
            }),

            _ => Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!(
                    "drop-glue semantic place typing cannot project field {field:?} from {current_ty:?} in {place:?}"
                ),
            )))),
        }
    }

    pub(super) fn shim_state(&self) -> types::STInner<'_, 'def, 'tcx> {
        let typing_env = ty::TypingEnv::post_analysis(self.tcx, self.adt_did);
        types::STInner::ShimTranslation(Box::new(types::ShimState::new(
            typing_env,
            self.generic_scope.clone(),
            &self.used_literals,
            &self.used_tuples,
        )))
    }

    fn translate_drop_glue_region(&self, region: ty::Region<'tcx>) -> Result<specs::Lft, TranslationError> {
        match region.kind() {
            ty::RegionKind::ReEarlyParam(early) => self
                .generic_scope
                .lookup_region_idx(early.index as usize)
                .map(|x| x.lft().to_owned())
                .ok_or_else(|| {
                    TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(format!(
                        "drop-glue generic abstraction cannot resolve early region {region:?}"
                    ))))
                }),

            ty::RegionKind::ReBound(idx, r) => {
                if let ty::BoundVarIndexKind::Bound(idx) = idx {
                    self.generic_scope
                        .lookup_late_region_idx(usize::from(idx), r.var.index())
                        .map(|x| x.lft().to_owned())
                        .ok_or_else(|| {
                            TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                                format!(
                                    "drop-glue generic abstraction cannot resolve late region {region:?}"
                                ),
                            )))
                        })
                } else {
                    Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                        format!("drop-glue generic abstraction does not support canonical region {region:?}"),
                    ))))
                }
            },

            ty::RegionKind::ReStatic => Ok(coq::Ident::new("static")),

            _ => Err(TranslationError::ErrorReported(self.tcx.dcx().err(Message::UnsupportedFeature(
                format!("drop-glue generic abstraction requires preserved universal regions, got {region:?}"),
            )))),
        }
    }

    fn translate_drop_glue_spec_type(&self, ty: ty::Ty<'tcx>) -> Result<specs::Type<'def>, TranslationError> {
        let typing_env = ty::TypingEnv::post_analysis(self.tcx, self.adt_did);
        self.ty_translator.translate_type_in_scope(&self.generic_scope, typing_env, ty)
    }
}
