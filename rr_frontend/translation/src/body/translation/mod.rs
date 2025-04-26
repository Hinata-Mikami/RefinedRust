// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

mod basicblock;
mod calls;
mod constants;
mod loops;
mod place;
mod rvalue;
mod terminator;

use std::collections::{HashMap, HashSet};

use log::{info, trace};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use typed_arena::Arena;

use crate::base::*;
use crate::body::checked_op_analysis::CheckedOpLocalAnalysis;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::environment::{polonius_info, Environment};
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::traits::registry;
use crate::{consts, procedures, regions, types};

/// Struct that keeps track of all information necessary to translate a MIR Body to a `radium::Function`.
/// `'a` is the lifetime of the translator and ends after translation has finished.
/// `'def` is the lifetime of the generated code (the code may refer to struct defs).
/// `'tcx` is the lifetime of the rustc tctx.
pub struct TX<'a, 'def, 'tcx> {
    env: &'def Environment<'tcx>,
    /// registry of other procedures
    procedure_registry: &'a procedures::Scope<'def>,
    /// scope of used consts
    const_registry: &'a consts::Scope<'def>,
    /// trait registry
    trait_registry: &'def registry::TR<'tcx, 'def>,
    /// translator for types
    ty_translator: types::LocalTX<'def, 'tcx>,

    /// this needs to be annotated with the right borrowck things
    proc: &'def Procedure<'tcx>,
    /// polonius info for this function
    info: &'a PoloniusInfo<'a, 'tcx>,

    /// maps locals to variable names
    variable_map: HashMap<mir::Local, String>,

    /// name of the return variable
    return_name: String,
    /// syntactic type of the thing to return
    return_synty: radium::SynType,
    /// all the other procedures used by this function, and:
    /// (code_loc_parameter_name, spec_name, type_inst, syntype_of_all_args)
    collected_procedures: HashMap<(DefId, types::GenericsKey<'tcx>), radium::UsedProcedure<'def>>,
    /// used statics
    collected_statics: HashSet<DefId>,

    /// tracking lifetime inclusions for the generation of lifetime inclusions
    inclusion_tracker: InclusionTracker<'a, 'tcx>,
    /// initial Polonius constraints that hold at the start of the function
    initial_constraints: Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)>,

    /// data structures for tracking which basic blocks still need to be translated
    /// (we only translate the basic blocks which are actually reachable, in particular when
    /// skipping unwinding)
    bb_queue: Vec<mir::BasicBlock>,
    /// set of already processed blocks
    processed_bbs: HashSet<mir::BasicBlock>,

    /// map of loop heads to their optional spec closure defid
    loop_specs: HashMap<mir::BasicBlock, Option<DefId>>,

    /// relevant locals: (local, name, type)
    fn_locals: Vec<(mir::Local, radium::LocalKind, String, radium::Type<'def>)>,

    /// result temporaries of checked ops that we rewrite
    /// we assume that this place is typed at (result_type, bool)
    /// and rewrite accesses to the first component to directly use the place,
    /// while rewriting accesses to the second component to true.
    /// TODO: once we handle panics properly, we should use a different translation.
    /// NOTE: we only rewrite for uses, as these are the only places these are used.
    checked_op_temporaries: HashMap<mir::Local, ty::Ty<'tcx>>,

    /// the Caesium function buildder
    translated_fn: radium::FunctionBuilder<'def>,
}

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    pub fn new(
        env: &'def Environment<'tcx>,
        procedure_registry: &'a procedures::Scope<'def>,
        const_registry: &'a consts::Scope<'def>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        ty_translator: types::LocalTX<'def, 'tcx>,

        proc: &'def Procedure<'tcx>,
        info: &'a PoloniusInfo<'a, 'tcx>,
        inputs: &[ty::Ty<'tcx>],

        mut inclusion_tracker: InclusionTracker<'a, 'tcx>,
        mut translated_fn: radium::FunctionBuilder<'def>,
    ) -> Result<Self, TranslationError<'tcx>> {
        let body = proc.get_mir();

        // analyze which locals are used for the result of checked-ops, because we will
        // override their types (eliminating the tuples)
        let mut checked_op_analyzer = CheckedOpLocalAnalysis::new(env.tcx(), body);
        checked_op_analyzer.analyze();
        let checked_op_temporaries = checked_op_analyzer.results();
        info!("Checked op temporaries: {checked_op_temporaries:?}");

        // map to translate between locals and the string names we use in radium::
        let mut variable_map: HashMap<mir::Local, String> = HashMap::new();

        let local_decls = &body.local_decls;
        info!("Have {} local decls\n", local_decls.len());

        let debug_info = &body.var_debug_info;
        info!("using debug info: {:?}", debug_info);

        let mut return_synty = radium::SynType::Unit; // default
        let mut fn_locals = Vec::new();
        let mut opt_return_name =
            Err(TranslationError::UnknownError("could not find local for return value".to_owned()));
        let mut used_names = HashSet::new();
        let mut arg_tys = Vec::new();

        // go over local_decls and create the right radium:: stack layout
        for (local, local_decl) in local_decls.iter_enumerated() {
            let kind = body.local_kind(local);
            let ty: ty::Ty<'tcx>;
            if let Some(rewritten_ty) = checked_op_temporaries.get(&local) {
                ty = *rewritten_ty;
            } else {
                ty = local_decl.ty;
            }

            // check if the type is of a spec fn -- in this case, we can skip this temporary
            if let ty::TyKind::Closure(id, _) = ty.kind() {
                if procedure_registry.lookup_function_mode(*id).map_or(false, procedures::Mode::is_ignore) {
                    // this is a spec fn
                    info!("skipping local which has specfn closure type: {:?}", local);
                    continue;
                }
            }

            // type:
            info!("Trying to translate type of local {local:?}: {:?}", ty);
            let tr_ty = ty_translator.translate_type(ty)?;
            let st = (&tr_ty).into();

            let name = Self::make_local_name(body, local, &mut used_names);
            variable_map.insert(local, name.clone());

            let local_kind = Self::get_local_kind(body, local);

            fn_locals.push((local, local_kind, name.clone(), tr_ty));

            match kind {
                mir::LocalKind::Arg => {
                    translated_fn.code.add_argument(&name, st);
                    arg_tys.push(ty);
                },
                mir::LocalKind::Temp => translated_fn.code.add_local(&name, st),
                mir::LocalKind::ReturnPointer => {
                    return_synty = st.clone();
                    translated_fn.code.add_local(&name, st);
                    opt_return_name = Ok(name);
                },
            }
        }
        info!("radium name map: {:?}", variable_map);
        // create the function
        let return_name = opt_return_name?;

        // add lifetime parameters to the map
        let param_env = env.tcx().param_env(proc.get_id());
        let initial_constraints = regions::init::get_initial_universal_arg_constraints(
            env.tcx(),
            param_env,
            info,
            &mut inclusion_tracker,
            inputs,
            arg_tys.as_slice(),
        );
        info!("initial constraints: {:?}", initial_constraints);

        Ok(Self {
            env,
            proc,
            info,
            variable_map,
            translated_fn,
            return_name,
            return_synty,
            inclusion_tracker,
            collected_procedures: HashMap::new(),
            procedure_registry,
            bb_queue: Vec::new(),
            processed_bbs: HashSet::new(),
            ty_translator,
            loop_specs: HashMap::new(),
            fn_locals,
            checked_op_temporaries,
            initial_constraints,
            const_registry,
            trait_registry,
            collected_statics: HashSet::new(),
        })
    }

    /// Main translation function that actually does the translation and returns a `radium::Function`
    /// if successful.
    pub fn translate(
        mut self,
        spec_arena: &'def Arena<radium::FunctionSpec<'def, radium::InnerFunctionSpec<'def>>>,
    ) -> Result<radium::Function<'def>, TranslationError<'tcx>> {
        // add loop info
        let loop_info = self.proc.loop_info();
        loop_info.dump_body_head();

        // translate the function's basic blocks
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // first translate the initial basic block; we add some additional annotations to the front
        let initial_bb_idx = mir::BasicBlock::from_u32(0);
        if let Some(bb) = basic_blocks.get(initial_bb_idx) {
            let translated_bb = self.translate_basic_block(initial_bb_idx, bb)?;
            // push annotation for initial constraints that relate argument's place regions to universals
            let mut annots = Vec::new();
            for (r1, r2) in &self.initial_constraints {
                annots.push(radium::Annotation::CopyLftName(
                    self.ty_translator.format_atomic_region(r1),
                    self.ty_translator.format_atomic_region(r2),
                ));
            }
            let translated_bb = radium::Stmt::Prim(
                vec![radium::PrimStmt::Annot {
                    a: annots,
                    why: Some("initialization".to_owned()),
                }],
                Box::new(translated_bb),
            );
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
                self.translated_fn.assume_synty_layoutable(radium::SynType::Literal(ty.syn_type));
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
        for used_proc in self.collected_procedures.values() {
            self.translated_fn.require_function(used_proc.clone());
        }

        // generate dependencies on statics
        for did in &self.collected_statics {
            let s = self.const_registry.get_static(*did)?;
            self.translated_fn.require_static(s.to_owned());
        }

        Ok(self.translated_fn.into_function(spec_arena))
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
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
    fn get_local_kind(mir_body: &mir::Body<'tcx>, local: mir::Local) -> radium::LocalKind {
        let kind = mir_body.local_kind(local);
        match kind {
            mir::LocalKind::Arg => radium::LocalKind::Arg,
            mir::LocalKind::Temp | mir::LocalKind::ReturnPointer => {
                let used_names = HashSet::new();
                if Self::find_name_for_local(mir_body, local, &used_names).is_some() {
                    radium::LocalKind::Local
                } else {
                    radium::LocalKind::CompilerTemp
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
                if let Some(this_local) = l.as_local() {
                    if this_local == local {
                        // around closures, multiple symbols may be mapped to the same name.
                        // To prevent this from happening, we check that the name hasn't been
                        // used already
                        // TODO: find better solution
                        if !used_names.contains(name.as_str()) {
                            return Some(name.as_str().to_owned());
                        }
                    }
                }
            } else {
                // is this case used when constant propagation happens during MIR construction?
            }
        }

        None
    }

    fn format_region(&self, r: facts::Region) -> String {
        let lft = self.info.mk_atomic_region(r);
        self.ty_translator.format_atomic_region(&lft)
    }

    /// Checks whether a place access descends below a reference.
    fn check_place_below_reference(&self, place: &mir::Place<'tcx>) -> bool {
        if self.checked_op_temporaries.contains_key(&place.local) {
            // temporaries are never below references
            return false;
        }

        for (pl, _) in place.iter_projections() {
            // check if the current ty is a reference that we then descend under with proj
            let cur_ty_kind = pl.ty(&self.proc.get_mir().local_decls, self.env.tcx()).ty.kind();
            if let ty::TyKind::Ref(_, _, _) = cur_ty_kind {
                return true;
            }
        }

        false
    }

    /// Registers a drop shim for a particular type for the translation.
    #[allow(clippy::unused_self)]
    const fn register_drop_shim_for(&self, _ty: ty::Ty<'tcx>) {
        // TODO!
        //let drop_in_place_did: DefId = search::try_resolve_did(self.env.tcx(), &["std", "ptr",
        // "drop_in_place"]).unwrap();

        //let x: ty::InstanceDef = ty::InstanceDef::DropGlue(drop_in_place_did, Some(ty));
        //let body: &'tcx mir::Body = self.env.tcx().mir_shims(x);

        //info!("Generated drop shim for {:?}", ty);
        //Self::dump_body(body);
    }

    /// Translate a goto-like jump to `target`.
    fn translate_goto_like(
        &mut self,
        _loc: &mir::Location,
        target: mir::BasicBlock,
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        self.enqueue_basic_block(target);
        let res_stmt = radium::Stmt::GotoBlock(target.as_usize());

        let loop_info = self.proc.loop_info();
        if loop_info.is_loop_head(target) && !self.loop_specs.contains_key(&target) {
            let spec_defid = self.find_loop_spec_closure(target)?;
            self.loop_specs.insert(target, spec_defid);
        }

        Ok(res_stmt)
    }

    /// Enqueues a basic block for processing, if it has not already been processed,
    /// and marks it as having been processed.
    fn enqueue_basic_block(&mut self, bb: mir::BasicBlock) {
        if !self.processed_bbs.contains(&bb) {
            self.bb_queue.push(bb);
            self.processed_bbs.insert(bb);
        }
    }

    /// Generate endlft annotations
    fn generate_endlfts<I>(&self, dying: I) -> Vec<radium::PrimStmt>
    where
        I: ExactSizeIterator<Item = facts::Loan>,
    {
        let mut stmts = Vec::new();
        for d in dying {
            let lft = self.info.atomic_region_of_loan(d);
            stmts.push(radium::PrimStmt::Annot {
                a: vec![radium::Annotation::EndLft(self.ty_translator.format_atomic_region(&lft))],
                why: Some("endlft".to_owned()),
            });
        }
        stmts
    }

    /// Make a trivial place accessing `local`.
    fn make_local_place(&self, local: mir::Local) -> mir::Place<'tcx> {
        mir::Place {
            local,
            projection: self.env.tcx().mk_place_elems(&[]),
        }
    }

    /// Get the type of a local in a body.
    fn get_type_of_local(&self, local: mir::Local) -> Result<ty::Ty<'tcx>, TranslationError<'tcx>> {
        self.proc
            .get_mir()
            .local_decls
            .get(local)
            .map(|decl| decl.ty)
            .ok_or_else(|| TranslationError::UnknownVar(String::new()))
    }

    /// Get the type of a place expression.
    fn get_type_of_place(&self, pl: &mir::Place<'tcx>) -> mir::tcx::PlaceTy<'tcx> {
        pl.ty(&self.proc.get_mir().local_decls, self.env.tcx())
    }

    /// Get the type of an operand.
    fn get_type_of_operand(&self, op: &mir::Operand<'tcx>) -> ty::Ty<'tcx> {
        op.ty(&self.proc.get_mir().local_decls, self.env.tcx())
    }

    /// Check if a local is used for a spec closure.
    fn is_spec_closure_local(&self, l: mir::Local) -> Result<Option<DefId>, TranslationError<'tcx>> {
        // check if we should ignore this
        let local_type = self.get_type_of_local(l)?;

        trace!("is_spec_closure_local: checking {l:?} of type {local_type:?}");

        let ty::TyKind::Closure(did, _) = local_type.kind() else {
            return Ok(None);
        };

        let mode = self.procedure_registry.lookup_function_mode(*did);
        let res = mode.and_then(|m| m.is_ignore().then_some(*did));

        trace!("is_spec_closure_local: found closure {res:?} with mode {mode:?}");

        Ok(res)
    }
}
