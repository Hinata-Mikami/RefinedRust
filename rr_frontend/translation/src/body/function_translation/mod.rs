// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

mod basicblock;
mod calls;
mod loops;
mod terminator;
mod tx_impl;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::mem;

pub(crate) use calls::get_arg_syntypes_for_procedure_call;
use log::{info, trace};
use radium::{code, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{bug, mir, ty};
use rr_rustc_interface::mir_dataflow::impls::always_storage_live_locals;
use typed_arena::Arena;

use crate::base::*;
use crate::body::mir_lowering::{MirTranslationCtx as _, ProcedureInst, TranslationKey};
use crate::environment::procedure::Procedure;
use crate::error::Message;
use crate::regions::AnnotationGenerator;
use crate::traits::registry;
use crate::{consts, procedures, types};

pub(crate) enum ExprInfo<'tcx, 'def> {
    Call(ProcedureInst<'tcx, 'def>),
}

pub(crate) type ExprWithInfo<'tcx, 'def> = (code::Expr, Option<ExprInfo<'tcx, 'def>>);

/// Struct that keeps track of all information necessary to translate a MIR Body to a `code::Function`.
/// `'a` is the lifetime of the translator and ends after translation has finished.
/// `'def` is the lifetime of the generated code (the code may refer to struct defs).
/// `'tcx` is the lifetime of the rustc tctx.
pub(crate) struct TX<'a, 'def, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    /// registry of other procedures
    procedure_registry: &'a procedures::Scope<'tcx, 'def>,
    /// scope of used consts
    const_registry: &'a consts::Scope<'def>,
    /// trait registry
    trait_registry: &'def registry::TR<'tcx, 'def>,
    /// translator for types
    ty_translator: types::LocalTX<'def, 'tcx>,

    /// this needs to be annotated with the right borrowck things
    proc: &'def Procedure<'tcx>,
    /// maps locals to variable names
    variable_map: HashMap<mir::Local, String>,

    /// name of the return variable
    return_name: String,
    /// syntactic type of the thing to return
    return_ty: ty::Ty<'tcx>,
    /// all the other procedures used by this function, and:
    /// `(code_loc_parameter_name, spec_name, type_inst, syntype_of_all_args)`
    collected_procedures: HashMap<TranslationKey<'tcx>, code::UsedProcedure<'def>>,
    /// used statics
    collected_statics: BTreeSet<OrderedDefId>,

    /// generator state for borrowck-driven annotations.
    annotations: AnnotationGenerator<'a, 'tcx>,
    /// initial Polonius annotations that hold at the start of the function
    initial_annotation_stmts: Vec<code::PrimStmt>,

    /// data structures for tracking which basic blocks still need to be translated
    /// (we only translate the basic blocks which are actually reachable, in particular when
    /// skipping unwinding)
    bb_queue: Vec<mir::BasicBlock>,
    /// set of already processed blocks
    processed_bbs: HashSet<mir::BasicBlock>,

    /// map of loop heads to their optional spec closure defid
    loop_specs: BTreeMap<mir::BasicBlock, Option<DefId>>,

    /// relevant locals: (local, kind, name, type, always live)
    fn_locals: Vec<(mir::Local, code::LocalKind, String, specs::Type<'def>, bool)>,

    /// the Caesium function buildder
    translated_fn: code::FunctionBuilder<'def>,
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    pub(crate) fn new(
        tcx: ty::TyCtxt<'tcx>,
        procedure_registry: &'a procedures::Scope<'tcx, 'def>,
        const_registry: &'a consts::Scope<'def>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        ty_translator: types::LocalTX<'def, 'tcx>,

        proc: &'def Procedure<'tcx>,
        inputs: &[ty::Ty<'tcx>],

        mut annotations: AnnotationGenerator<'a, 'tcx>,
        mut translated_fn: code::FunctionBuilder<'def>,
    ) -> Result<Self, TranslationError> {
        let body = proc.dropck_mir();

        // map to translate between locals and the string names we use in radium:
        let mut variable_map: HashMap<mir::Local, String> = HashMap::new();

        let local_decls = &body.local_decls;
        info!("Have {} local decls\n", local_decls.len());

        let debug_info = &body.var_debug_info;
        info!("using debug info: {:?}", debug_info);

        let empty_args = tcx.mk_type_list(&[]);
        let mut return_ty = tcx.mk_ty_from_kind(ty::TyKind::Tuple(empty_args));
        let mut fn_locals = Vec::new();
        let mut opt_return_name: Option<String> = None;
        let mut used_names = HashSet::new();
        let mut arg_tys = Vec::new();

        let always_live = always_storage_live_locals(body);
        // go over local_decls and create the right radium stack layout
        for (local, local_decl) in local_decls.iter_enumerated() {
            if proc.is_unmentioned_synthetic_local(local) {
                info!("skipping unmentioned synthetic local {local:?}");
                continue;
            }

            if proc.is_administrative_alias(local) {
                info!("skipping synthetic administrative alias local {local:?}");
                continue;
            }

            let kind = body.local_kind(local);
            let shape_ty: ty::Ty<'tcx> = local_decl.ty;
            // Dropck introduces temporaries whose erased MIR type is only the storage shape.
            // Synthetic drop borrows are non-null but do not carry a source-level lifetime here.
            let synthetic_drop_borrow_ty =
                proc.synthetic_drop_borrow_for_local(local).map(|_| specs::Type::AliasRef);

            let ty: ty::Ty<'tcx> = if proc.borrowck_mir().local_decls.get(local).is_some() {
                // Locals present in borrowck MIR keep their region information there; use it for
                // specs and annotations while translating dropck MIR for the executable shape.
                proc.region_type_of_local(local)
            } else {
                if proc.contains_erased_regions(shape_ty) && synthetic_drop_borrow_ty.is_none() {
                    bug!("synthetic dropck local {local:?} has erased shape type: {shape_ty:?}");
                }
                info!(
                    "using dropck shape type for synthetic local {local:?} without erased regions: {shape_ty:?}"
                );
                shape_ty
            };

            // check if the type is of a spec fn -- in this case, we can skip this temporary
            if let ty::TyKind::Closure(id, _) = ty.kind()
                && procedure_registry.lookup_function_mode(*id).is_some_and(procedures::Mode::is_ignore)
            {
                // this is a spec fn
                info!("skipping local which has specfn closure type: {:?}", local);
                continue;
            }

            // type:
            info!("Trying to translate type of local {local:?}: {:?}", ty);
            let tr_ty = if let Some(tr_ty) = synthetic_drop_borrow_ty {
                tr_ty
            } else {
                ty_translator.translate_type(ty)?
            };
            let st = (&tr_ty).into();

            let name = Self::make_local_name(body, local, &mut used_names);
            variable_map.insert(local, name.clone());

            let local_kind = Self::get_local_kind(body, local);

            fn_locals.push((local, local_kind, name.clone(), tr_ty, always_live.contains(local)));

            match kind {
                mir::LocalKind::Arg => {
                    translated_fn.code.add_argument(&name, st);
                    arg_tys.push(proc.region_type_of_local(local));
                },
                mir::LocalKind::Temp => (),
                mir::LocalKind::ReturnPointer => {
                    return_ty = proc.region_type_of_local(local);
                    opt_return_name = Some(name);
                },
            }
        }
        info!("radium name map: {:?}", variable_map);
        // create the function
        let return_name = opt_return_name.ok_or_else(|| {
            TranslationError::ErrorReported(tcx.dcx().err(Message::MissingReturnValueLocal))
        })?;

        // add lifetime parameters to the map
        let typing_env = ty::TypingEnv::post_analysis(tcx, proc.get_id());
        let initial_annotation_stmts = annotations.prepare_initial_universal_arg_annotation_stmts(
            &ty_translator,
            typing_env,
            inputs,
            arg_tys.as_slice(),
        );

        Ok(Self {
            tcx,
            proc,
            variable_map,
            translated_fn,
            return_name,
            return_ty,
            annotations,
            collected_procedures: HashMap::new(),
            procedure_registry,
            bb_queue: Vec::new(),
            processed_bbs: HashSet::new(),
            ty_translator,
            loop_specs: BTreeMap::new(),
            fn_locals,
            initial_annotation_stmts,
            const_registry,
            trait_registry,
            collected_statics: BTreeSet::new(),
        })
    }

    /// Main translation function that actually does the translation and returns a `code::Function`
    /// if successful.
    pub(crate) fn translate(
        mut self,
        spec_arena: &'def Arena<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,
    ) -> Result<code::Function<'def>, TranslationError> {
        // add loop info
        let loop_info = self.proc.loop_info();
        loop_info.dump_body_head();

        let closure_annotation_stmts =
            self.annotations.prepare_initial_closure_annotation_stmts(&self.ty_translator);

        // translate the function's basic blocks
        let basic_blocks = &self.proc.dropck_mir().basic_blocks;

        // first translate the initial basic block; we add some additional annotations to the front
        let initial_bb_idx = mir::BasicBlock::from_u32(0);
        if let Some(bb) = basic_blocks.get(initial_bb_idx) {
            let mut translated_bb = self.translate_basic_block(initial_bb_idx, bb)?;

            // push annotations for initial closure constraints
            if !closure_annotation_stmts.is_empty() {
                translated_bb = code::Stmt::Prim(closure_annotation_stmts, Box::new(translated_bb));
            }

            // push annotation for initial constraints that relate argument's place regions to universals
            translated_bb =
                code::Stmt::Prim(mem::take(&mut self.initial_annotation_stmts), Box::new(translated_bb));

            // allocate always live locals
            let mut prim_stmts = Vec::new();
            for (_, kind, name, ty, live) in &self.fn_locals {
                if *kind == code::LocalKind::Arg || !live {
                    continue;
                }
                let translated_st: lang::SynType = ty.into();
                let var = code::Variable::new(name.to_owned(), translated_st);
                prim_stmts.push(code::PrimStmt::LocalLive(var));
            }

            translated_bb = code::Stmt::Prim(prim_stmts, Box::new(translated_bb));

            self.translated_fn.code.add_basic_block(initial_bb_idx.as_usize(), translated_bb);
        } else {
            info!("No basic blocks");
        }

        while let Some(bb_idx) = self.bb_queue.pop() {
            let bb = &basic_blocks[bb_idx];
            let translated_bb = self.translate_basic_block(bb_idx, bb)?;
            self.translated_fn.code.add_basic_block(bb_idx.as_usize(), translated_bb);
        }

        // assume that all generics are layoutable
        {
            let scope = self.ty_translator.scope.borrow();
            for ty in scope.generic_scope.tyvars() {
                self.translated_fn.assume_synty_layoutable(lang::SynType::Literal(ty.syn_type()));
            }
        }
        // assume that all used literals are layoutable
        for g in self.ty_translator.scope.borrow().shim_uses.values() {
            self.translated_fn.assume_synty_layoutable(g.generate_syn_type_term());
        }
        // assume that all used tuples are layoutable
        for g in self.ty_translator.scope.borrow().tuple_uses.values() {
            self.translated_fn.assume_synty_layoutable(g.generate_syn_type_term());
        }

        // process the collected loop heads
        // - collect the relevant bb -> def_id mappings for this function (so we can eventually generate the
        //   definition)
        // - have a function that takes the def_id and then parses the attributes into a loop invariant
        for (head, did) in &self.loop_specs {
            let spec = self.parse_attributes_on_loop_spec_closure(*head, *did)?;
            self.translated_fn.register_loop_invariant(head.as_usize(), spec);
        }

        // generate dependencies on other procedures.
        let mut used_procs: Vec<_> = self.collected_procedures.iter().collect();
        used_procs.sort_by(|a, b| a.0.cmp(self.tcx, b.0));
        for (_, used_proc) in used_procs {
            self.translated_fn.require_function(used_proc.clone());
        }

        // generate dependencies on statics
        for did in &self.collected_statics {
            let s = self.const_registry.get_static(self.tcx, did)?;
            self.translated_fn.require_static(s.to_owned());
        }

        Ok(self.translated_fn.into_function(spec_arena))
    }

    /// Generate a string identifier for a Local.
    /// Tries to find the Rust source code name of the local, otherwise simply enumerates.
    /// `used_names` keeps track of the Rust source code names that have already been used.
    fn make_local_name(
        mir_body: &mir::Body<'tcx>,
        local: mir::Local,
        used_names: &mut HashSet<String>,
    ) -> String {
        if let Some(mir_name) = Self::find_name_for_local(mir_body, local, used_names) {
            let name = strip_coq_ident(&mir_name);
            used_names.insert(mir_name);
            name
        } else {
            let mut name = "__".to_owned();
            name.push_str(&local.index().to_string());
            name
        }
    }

    /// Classify the kind of a local.
    fn get_local_kind(mir_body: &mir::Body<'tcx>, local: mir::Local) -> code::LocalKind {
        let kind = mir_body.local_kind(local);
        match kind {
            mir::LocalKind::Arg => code::LocalKind::Arg,
            mir::LocalKind::Temp | mir::LocalKind::ReturnPointer => {
                let used_names = HashSet::new();
                if Self::find_name_for_local(mir_body, local, &used_names).is_some() {
                    code::LocalKind::Local
                } else {
                    code::LocalKind::CompilerTemp
                }
            },
        }
    }

    /// Find a source name for a local of a MIR body, if possible.
    fn find_name_for_local(
        body: &mir::Body<'tcx>,
        local: mir::Local,
        used_names: &HashSet<String>,
    ) -> Option<String> {
        let debug_info = &body.var_debug_info;

        for dbg in debug_info {
            let name = &dbg.name;
            let val = &dbg.value;
            if let mir::VarDebugInfoContents::Place(l) = *val {
                // make sure that the place projection is empty -- otherwise this might just
                // refer to the capture of a closure
                if let Some(this_local) = l.as_local()
                    && this_local == local
                {
                    // around closures, multiple symbols may be mapped to the same name.
                    // To prevent this from happening, we check that the name hasn't been
                    // used already
                    // TODO: find better solution
                    if !used_names.contains(name.as_str()) {
                        return Some(name.as_str().to_owned());
                    }
                }
            } else {
                // is this case used when constant propagation happens during MIR construction?
            }
        }

        None
    }

    /// Checks whether a place access descends below a reference.
    fn check_place_below_reference(&self, place: &mir::Place<'tcx>) -> bool {
        for (pl, _) in place.iter_projections() {
            // check if the current ty is a reference that we then descend under with proj
            let cur_ty_kind = pl.ty(&self.proc.dropck_mir().local_decls, self.tcx).ty.kind();
            if matches!(cur_ty_kind, ty::TyKind::Ref(_, _, _) | ty::TyKind::RawPtr(_, _)) {
                return true;
            }
        }

        false
    }

    /// Registers a drop shim for a particular type for the translation.
    /// Translate a goto-like jump to `target`.
    fn translate_goto_like(
        &mut self,
        loc: &mir::Location,
        target: mir::BasicBlock,
    ) -> Result<code::Stmt, TranslationError> {
        self.enqueue_basic_block(target);
        let mut res_stmt = code::Stmt::GotoBlock(target.as_usize());

        let loop_info = self.proc.loop_info();
        if loop_info.is_loop_head(target) && !self.loop_specs.contains_key(&target) {
            let spec_defid = self.find_loop_spec_closure(target)?;
            self.loop_specs.insert(target, spec_defid);
        }

        if loop_info.is_loop_head(target) {
            let annot_stmt = code::PrimStmt::Annot {
                a: vec![code::Annotation::StratifyContext],
                why: Some("goto to loop head".to_owned()),
            };
            res_stmt = code::Stmt::Prim(vec![annot_stmt], Box::new(res_stmt));
        }

        let mut edge_plan =
            self.annotations.prepare_cfg_edge_annotation_plan(&self.ty_translator, *loc, target);
        let edge_stmts = edge_plan.take_pre_stmts();
        if !edge_stmts.is_empty() {
            res_stmt = code::Stmt::Prim(edge_stmts, Box::new(res_stmt));
        }

        Ok(res_stmt)
    }

    /// Enqueues a basic block for processing, if it has not already been processed,
    /// and marks it as having been processed.
    fn enqueue_basic_block(&mut self, bb: mir::BasicBlock) {
        if self.processed_bbs.insert(bb) {
            self.bb_queue.push(bb);
        }
    }

    /// Check whether this statement only manages a synthetic administrative alias local.
    fn is_administrative_alias_stmt(&self, stmt: &mir::Statement<'tcx>) -> bool {
        match &stmt.kind {
            mir::StatementKind::StorageLive(local) | mir::StatementKind::StorageDead(local) => {
                self.proc.is_administrative_alias(*local)
            },
            mir::StatementKind::Assign(assign) => {
                let (place, _) = assign.as_ref();
                place.projection.is_empty() && self.proc.is_administrative_alias(place.local)
            },
            _ => false,
        }
    }

    /// Check if a local is used for a spec closure.
    fn is_spec_closure_local(&self, l: mir::Local) -> Result<Option<DefId>, TranslationError> {
        if self.proc.is_administrative_alias(l) {
            return Ok(None);
        }

        // check if we should ignore this
        let local_type = self.shape_type_of_local(l)?;

        trace!("is_spec_closure_local: checking {l:?} of type {local_type:?}");

        let ty::TyKind::Closure(did, _) = local_type.kind() else {
            return Ok(None);
        };

        let mode = self.procedure_registry().lookup_function_mode(*did);
        let res = mode.and_then(|m| m.is_ignore().then_some(*did));

        trace!("is_spec_closure_local: found closure {res:?} with mode {mode:?}");

        Ok(res)
    }
}
