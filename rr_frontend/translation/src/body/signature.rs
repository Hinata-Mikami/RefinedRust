// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Part of the function translation responsible for translating the signature and specification.

use std::collections::HashMap;

use log::{info, trace};
use radium::{code, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{hir, span};
use typed_arena::Arena;

use crate::base::*;
use crate::body::translation;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::environment::{Environment, dump_borrowck_info};
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::spec_parsers::verbose_function_spec_parser::{
    ClosureMetaInfo, ClosureSpecInfo, FunctionRequirements, FunctionSpecParser as _,
    VerboseFunctionSpecParser,
};
use crate::traits::registry;
use crate::{consts, procedures, regions, types};

pub(crate) struct TX<'a, 'def, 'tcx> {
    env: &'def Environment<'tcx>,
    /// this needs to be annotated with the right borrowck things
    proc: &'def Procedure<'tcx>,
    /// the Caesium function buildder
    translated_fn: code::FunctionBuilder<'def>,
    /// tracking lifetime inclusions for the generation of lifetime inclusions
    inclusion_tracker: InclusionTracker<'a, 'tcx>,

    /// registry of other procedures
    procedure_registry: &'a procedures::Scope<'tcx, 'def>,
    /// registry of consts
    const_registry: &'a consts::Scope<'def>,
    /// attributes on this function
    attrs: &'a [&'a hir::AttrItem],
    /// polonius info for this function
    info: &'a PoloniusInfo<'a, 'tcx>,
    /// translator for types
    ty_translator: types::LocalTX<'def, 'tcx>,
    /// trait registry in the current scope
    trait_registry: &'def registry::TR<'tcx, 'def>,
    /// argument types (from the signature, with generics substituted)
    inputs: Vec<ty::Ty<'tcx>>,
}

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Generate a spec for a trait method.
    pub(crate) fn spec_for_trait_method(
        env: &'def Environment<'tcx>,
        proc_did: DefId,
        name: &str,
        spec_name: &str,
        trait_req_incl_name: &str,
        attrs: &'a [&'a hir::AttrItem],
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
    ) -> Result<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>, TranslationError<'tcx>> {
        // use a dummy name as we're never going to use the code.
        let mut translated_fn = code::FunctionBuilder::new(name, "dummy", spec_name, trait_req_incl_name);

        let ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = env.tcx().type_of(proc_did);
        let ty = ty.instantiate_identity();
        // substs are the generic args of this function (including lifetimes)
        // sig is the function signature
        let sig = match ty.kind() {
            ty::TyKind::FnDef(_def, _args) => {
                assert!(ty.is_fn());
                ty.fn_sig(env.tcx())
            },
            _ => panic!("can not handle non-fns"),
        };
        info!("Function signature: {:?}", sig);

        let params = Self::get_proc_ty_params(env.tcx(), proc_did);
        info!("Function generic args: {:?}", params);

        let (inputs, output, region_substitution) =
            regions::init::replace_fnsig_args_with_polonius_vars(env, params, sig);
        info!("inputs: {:?}, output: {:?}", inputs, output);

        let type_scope = Self::setup_local_scope(
            env,
            ty_translator,
            trait_registry,
            proc_did,
            params.as_slice(),
            &mut translated_fn,
            region_substitution,
            None,
        )?;
        let type_translator = types::LocalTX::new(ty_translator, type_scope);

        // get argument names
        let arg_names: &'tcx [Option<span::symbol::Ident>] = env.tcx().fn_arg_idents(proc_did);
        let arg_names: Vec<_> = arg_names
            .iter()
            .enumerate()
            .map(|(i, maybe_name)| {
                maybe_name.map(|x| x.as_str().to_owned()).unwrap_or_else(|| format!("_arg_{i}"))
            })
            .collect();
        info!("arg names: {arg_names:?}");

        let spec_builder = Self::process_attrs(
            attrs,
            &type_translator,
            &mut translated_fn,
            &arg_names,
            inputs.as_slice(),
            output,
        )?;
        translated_fn.add_function_spec_from_builder(spec_builder);

        translated_fn.try_into().map_err(TranslationError::AttributeError)
    }

    /// Compute meta information for a closure we are processing.
    /// Adds all universal regions for closure captures to the region map.
    /// Returns the upvar types with normalized regions as well as the optional region for the
    /// capture.
    fn compute_closure_meta(
        clos_args: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
        closure_arg: &mir::LocalDecl<'tcx>,
        region_substitution: &mut regions::EarlyLateRegionMap<'def>,
        info: &PoloniusInfo<'def, 'tcx>,
        env: &Environment<'tcx>,
    ) -> (ty::Ty<'tcx>, Vec<ty::Ty<'tcx>>, Option<specs::Lft>) {
        // Process the lifetime parameters that come from the captures
        // Sideeffect: adds the regions that come from the captures (which may be local to the
        // surrounding function) to the region map, so that they appear as region parameters of the
        // function.
        let upvars_tys = clos_args.upvar_tys();
        let mut fixed_upvars_tys = Vec::new();
        for ty in upvars_tys {
            let fixed_ty =
                regions::arg_folder::rename_closure_capture_regions(ty, env.tcx(), region_substitution, info);
            fixed_upvars_tys.push(fixed_ty);
        }

        // Do the same to the whole closure arg
        let fixed_closure_arg_ty = regions::arg_folder::rename_closure_capture_regions(
            closure_arg.ty,
            env.tcx(),
            region_substitution,
            info,
        );

        // find the optional lifetime for the outer reference
        let mut maybe_outer_lifetime = None;
        if let ty::TyKind::Ref(r, _, _) = fixed_closure_arg_ty.kind() {
            if let ty::RegionKind::ReVar(r) = r.kind() {
                let name = &region_substitution.region_names[&r.into()];
                maybe_outer_lifetime = Some(name.to_owned());
            } else {
                unreachable!();
            }
        }

        (fixed_closure_arg_ty, fixed_upvars_tys, maybe_outer_lifetime)
    }

    /// Create a translation instance for a closure.
    pub(crate) fn new_closure(
        env: &'def Environment<'tcx>,
        meta: &procedures::Meta,
        proc: Procedure<'tcx>,
        attrs: &'a [&'a hir::AttrItem],
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        proc_registry: &'a procedures::Scope<'tcx, 'def>,
        const_registry: &'a consts::Scope<'def>,
    ) -> Result<(Self, procedures::ClosureImplInfo<'tcx, 'def>), TranslationError<'tcx>> {
        let mut translated_fn = code::FunctionBuilder::new(
            meta.get_name(),
            meta.get_code_name(),
            meta.get_spec_name(),
            meta.get_trait_req_incl_name(),
        );

        // TODO can we avoid the leak
        let proc: &'def Procedure<'_> = &*Box::leak(Box::new(proc));
        let body = proc.get_mir();
        Self::dump_body(body);

        let clos_args = env.get_closure_args(proc.get_id());
        let closure_kind = clos_args.kind();
        let tupled_upvars_tys = clos_args.tupled_upvars_ty();
        let parent_args = clos_args.parent_args();
        let unnormalized_sig = clos_args.sig();
        let sig = unnormalized_sig;
        // Note: `captures` contains the late bounds of this closure, i.e., lifetimes that just this
        // closure is generic over.
        let captures = env.tcx().closure_captures(proc.get_id().as_local().unwrap());
        info!("closure sig: {:?}", sig);
        info!("Closure has captures: {:?}", captures);
        info!("Closure arg upvar_tys: {:?}", tupled_upvars_tys);
        info!("Function signature: {:?}", sig);
        info!("Closure generic args: {:?}", parent_args);

        let local_decls = &body.local_decls;
        // the closure arg, containing the captures
        let closure_arg = local_decls.get(mir::Local::from_usize(1)).unwrap();

        let info = PoloniusInfo::new(env, proc);

        // TODO: avoid leak
        let info: &'def PoloniusInfo<'_, '_> = &*Box::leak(Box::new(info));

        // For closures, we only handle the parent's args here!
        // We add the lifetime parameters arising from the captures of the closure (which may be
        // local to the parent) below in `Self::compute_closure_meta`.
        let params = parent_args;
        info!("Function generic args: {:?}", params);

        if rrconfig::dump_borrowck_info() {
            dump_borrowck_info(env, proc.get_id(), info);
        }

        // Note: this only treats the formal arguments of the closure, but not the closure captures
        let (tupled_inputs, output, mut region_substitution) =
            regions::init::replace_fnsig_args_with_polonius_vars(env, params, sig);

        // detuple the inputs
        assert!(tupled_inputs.len() == 1);
        let input_tuple_ty = tupled_inputs[0];
        let mut inputs = Vec::new();

        if let ty::TyKind::Tuple(args) = input_tuple_ty.kind() {
            inputs.extend(args.iter());
        }

        info!("inputs({}): {:?}, output: {:?}", inputs.len(), inputs, output);

        // fix the regions in the closure args (esp the captures) and add the regions for the
        // captures to the region map.
        let (fixed_closure_arg_ty, upvars_tys, maybe_outer_lifetime) =
            Self::compute_closure_meta(clos_args, closure_arg, &mut region_substitution, info, env);

        trace!("fixed_closure_arg_ty={fixed_closure_arg_ty:?}");

        let type_scope = Self::setup_local_scope(
            env,
            ty_translator,
            trait_registry,
            proc.get_id(),
            params,
            &mut translated_fn,
            region_substitution.clone(),
            Some(info),
        )?;

        let inclusion_tracker = regions::init::initialize_inclusion_tracker(&type_scope.lifetime_scope, info);

        let type_translator = types::LocalTX::new(ty_translator, type_scope);

        info!("tupled closure upvars: {fixed_closure_arg_ty:?}");
        let mut all_inputs = inputs.clone();
        all_inputs.insert(0, fixed_closure_arg_ty);

        let mut t = Self {
            env,
            proc,
            info,
            translated_fn,
            inclusion_tracker,
            procedure_registry: proc_registry,
            attrs,
            ty_translator: type_translator,
            trait_registry,
            const_registry,
            inputs: all_inputs,
        };

        // compute meta information needed to generate the spec
        let mut translated_upvars_types = Vec::new();
        for ty in upvars_tys {
            let translated_ty = t.ty_translator.translate_type(ty)?;
            translated_upvars_types.push(translated_ty);
        }
        let meta = ClosureMetaInfo {
            kind: closure_kind,
            captures,
            capture_tys: &translated_upvars_types,
            closure_lifetime: maybe_outer_lifetime.clone(),
        };

        // get argument names
        let arg_names: &'tcx [Option<span::symbol::Ident>] = env.tcx().fn_arg_idents(proc.get_id());
        let arg_names: Vec<_> = arg_names
            .iter()
            .enumerate()
            .map(|(i, maybe_name)| {
                maybe_name.map(|x| x.as_str().to_owned()).unwrap_or_else(|| format!("_arg_{i}"))
            })
            .collect();
        info!("arg names: {arg_names:?}");

        // process attributes
        let spec_info = t.process_closure_attrs(&inputs, output, &arg_names, meta)?;

        // compute the info needed to assemble the trait impls for this closure
        let self_var_ty = t.ty_translator.translate_type(fixed_closure_arg_ty)?;
        let self_ty = Environment::get_closure_self_ty_from_var_ty(fixed_closure_arg_ty, closure_kind);
        let args_ty = t.ty_translator.translate_type(input_tuple_ty)?;
        let output_ty = t.ty_translator.translate_type(output)?;
        let mut args_tys: Vec<specs::Type<'def>> = Vec::new();
        for arg in inputs {
            let translated: specs::Type<'def> = t.ty_translator.translate_type(arg)?;
            args_tys.push(translated);
        }

        let mut generics = t.translated_fn.spec.get_generics().to_owned();
        // remove the direct lifetime param
        if let Some(lft) = &maybe_outer_lifetime {
            generics.remove_lft_param(lft);
        }

        let info = procedures::ClosureImplInfo::new(
            closure_kind,
            generics,
            maybe_outer_lifetime,
            region_substitution,
            self_ty,
            input_tuple_ty,
            self_var_ty,
            args_ty,
            args_tys,
            output_ty,
            spec_info.pre_encoded,
            spec_info.post_encoded,
            spec_info.post_mut_encoded,
        );

        Ok((t, info))
    }

    /// Translate the body of a function.
    pub(crate) fn new(
        env: &'def Environment<'tcx>,
        meta: &procedures::Meta,
        proc: Procedure<'tcx>,
        attrs: &'a [&'a hir::AttrItem],
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        proc_registry: &'a procedures::Scope<'tcx, 'def>,
        const_registry: &'a consts::Scope<'def>,
    ) -> Result<Self, TranslationError<'tcx>> {
        let mut translated_fn = code::FunctionBuilder::new(
            meta.get_name(),
            meta.get_code_name(),
            meta.get_spec_name(),
            meta.get_trait_req_incl_name(),
        );

        // TODO can we avoid the leak
        let proc: &'def Procedure<'_> = &*Box::leak(Box::new(proc));

        let body = proc.get_mir();
        Self::dump_body(body);

        let ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = env.tcx().type_of(proc.get_id());
        let ty = ty.instantiate_identity();
        // substs are the generic args of this function (including lifetimes)
        // sig is the function signature
        assert!(ty.is_fn());
        let sig = ty.fn_sig(env.tcx());
        info!("Function signature: {:?}", sig);

        let info = PoloniusInfo::new(env, proc);
        // TODO: avoid leak
        let info: &'def PoloniusInfo<'_, '_> = &*Box::leak(Box::new(info));

        let params = Self::get_proc_ty_params(env.tcx(), proc.get_id());
        info!("Function generic args: {:?}", params);

        if rrconfig::dump_borrowck_info() {
            dump_borrowck_info(env, proc.get_id(), info);
        }

        let (inputs, output, region_substitution) =
            regions::init::replace_fnsig_args_with_polonius_vars(env, params, sig);
        info!("inputs: {:?}, output: {:?}", inputs, output);

        let type_scope = Self::setup_local_scope(
            env,
            ty_translator,
            trait_registry,
            proc.get_id(),
            params.as_slice(),
            &mut translated_fn,
            region_substitution,
            Some(info),
        )?;

        let inclusion_tracker = regions::init::initialize_inclusion_tracker(&type_scope.lifetime_scope, info);

        let type_translator = types::LocalTX::new(ty_translator, type_scope);

        // get argument names
        let arg_names: &'tcx [Option<span::symbol::Ident>] = env.tcx().fn_arg_idents(proc.get_id());
        let arg_names: Vec<_> = arg_names
            .iter()
            .enumerate()
            .map(|(i, maybe_name)| {
                maybe_name.map(|x| x.as_str().to_owned()).unwrap_or_else(|| format!("_arg_{i}"))
            })
            .collect();
        info!("arg names: {arg_names:?}");

        let mut t = Self {
            env,
            proc,
            info,
            translated_fn,
            inclusion_tracker,
            procedure_registry: proc_registry,
            attrs,
            ty_translator: type_translator,
            trait_registry,
            const_registry,
            inputs: inputs.clone(),
        };

        if env.has_tool_attribute(proc.get_id(), "default_spec") {
            // Use the default spec annotated on the trait
            let spec = t.make_trait_instance_spec()?;
            if let Some(spec) = spec {
                t.translated_fn.add_trait_function_spec(spec);
            } else {
                return Err(TranslationError::AttributeError("No valid specification provided".to_owned()));
            }
        } else {
            // process attributes
            let spec_builder = Self::process_attrs(
                attrs,
                &t.ty_translator,
                &mut t.translated_fn,
                &arg_names,
                inputs.as_slice(),
                output,
            )?;

            if spec_builder.has_spec() {
                t.translated_fn.add_function_spec_from_builder(spec_builder);
            } else {
                return Err(TranslationError::AttributeError("No valid specification provided".to_owned()));
            }
        }

        Ok(t)
    }

    /// Translate the body of the function.
    pub(crate) fn translate(
        self,
        spec_arena: &'def Arena<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,
    ) -> Result<code::Function<'def>, TranslationError<'tcx>> {
        let translator = translation::TX::new(
            self.env,
            self.procedure_registry,
            self.const_registry,
            self.trait_registry,
            self.ty_translator,
            self.proc,
            self.info,
            &self.inputs,
            self.inclusion_tracker,
            self.translated_fn,
        )?;
        translator.translate(spec_arena)
    }

    /// Translation that only generates a specification.
    pub(crate) fn generate_spec(
        self,
    ) -> Result<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>, TranslationError<'tcx>> {
        self.translated_fn.try_into().map_err(TranslationError::AttributeError)
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Get type parameters of the given procedure.
    fn get_proc_ty_params(tcx: ty::TyCtxt<'tcx>, did: DefId) -> ty::GenericArgsRef<'tcx> {
        let ty = tcx.type_of(did).instantiate_identity();
        match ty.kind() {
            ty::TyKind::FnDef(_, params) => params,
            _ => panic!("Procedure::new called on a procedure whose type is not TyKind::FnDef!"),
        }
    }

    /// Set up the local generic scope of the function, including type parameters, lifetime
    /// parameters, and trait constraints.
    fn setup_local_scope(
        env: &Environment<'tcx>,
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        proc_did: DefId,
        params: &[ty::GenericArg<'tcx>],
        translated_fn: &mut code::FunctionBuilder<'def>,
        region_substitution: regions::EarlyLateRegionMap<'def>,
        info: Option<&'def PoloniusInfo<'def, 'tcx>>,
    ) -> Result<types::FunctionState<'tcx, 'def>, TranslationError<'tcx>> {
        // enter the procedure
        let type_scope = types::FunctionState::new_with_traits(
            proc_did,
            env,
            env.tcx().mk_args(params),
            region_substitution,
            ty_translator,
            trait_registry,
            info,
        )?;

        // add generic args to the fn
        let generics = type_scope.make_params_scope();
        translated_fn.provide_generic_scope(generics.into());

        Ok(type_scope)
    }

    /// Process extra requirements annotated on a function spec.
    fn process_function_requirements(
        fn_builder: &mut code::FunctionBuilder<'def>,
        requirements: FunctionRequirements,
    ) {
        for e in requirements.early_coq_params {
            fn_builder.add_early_coq_param(e);
        }
        for e in requirements.late_coq_params {
            fn_builder.add_late_coq_param(e);
        }
        for e in requirements.proof_info.linktime_assumptions {
            fn_builder.add_linktime_assumption(e);
        }
        for e in requirements.proof_info.sidecond_tactics {
            fn_builder.add_manual_tactic(e);
        }
    }

    /// Parse and process attributes of this closure.
    fn process_closure_attrs(
        &mut self,
        inputs: &[ty::Ty<'tcx>],
        output: ty::Ty<'tcx>,
        arg_names: &[String],
        meta: ClosureMetaInfo<'_, 'tcx, 'def>,
    ) -> Result<ClosureSpecInfo, TranslationError<'tcx>> {
        trace!("entering process_closure_attrs");
        let v = self.attrs;

        // Translate signature
        info!("inputs: {:?}, output: {:?}", inputs, output);
        let mut translated_arg_types: Vec<specs::Type<'def>> = Vec::new();
        for arg in inputs {
            let translated: specs::Type<'def> = self.ty_translator.translate_type(*arg)?;
            translated_arg_types.push(translated);
        }
        let translated_ret_type: specs::Type<'def> = self.ty_translator.translate_type(output)?;
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        let ret_is_option = self.ty_translator.translator.is_builtin_option_type(output);
        let ret_is_result = self.ty_translator.translator.is_builtin_result_type(output);

        // Determine parser
        let parser = rrconfig::attribute_parser();
        if parser.as_str() != "verbose" {
            trace!("leaving process_closure_attrs");
            return Err(TranslationError::UnknownAttributeParser(parser));
        }

        let mut spec_builder = specs::functions::LiteralSpecBuilder::new();

        let ty_translator = &self.ty_translator;
        // Hack: create indirection by tracking the tuple uses we create in here.
        // (We need a read reference to the scope, so we can't write to it at the same time)
        let mut tuple_uses = HashMap::new();
        let spec_info = {
            let scope = ty_translator.scope.borrow();
            let mut parser = VerboseFunctionSpecParser::new(
                &self.translated_fn.spec.function_name,
                &translated_arg_types,
                &translated_ret_type,
                ret_is_option,
                ret_is_result,
                Some(arg_names),
                &*scope,
                |lit| ty_translator.translator.intern_literal(lit),
            );

            let spec_info = parser
                .parse_closure_spec(v, &mut spec_builder, meta, |x| {
                    ty_translator.make_tuple_use(x, Some(&mut tuple_uses))
                })
                .map_err(TranslationError::AttributeError)?;

            let x = parser.into();
            Self::process_function_requirements(&mut self.translated_fn, x);
            spec_info
        };
        let mut scope = ty_translator.scope.borrow_mut();
        scope.tuple_uses.extend(tuple_uses);
        self.translated_fn.add_function_spec_from_builder(spec_builder);

        trace!("leaving process_closure_attrs");
        Ok(spec_info)
    }

    /// Parse and process attributes of this function.
    fn process_attrs(
        attrs: &[&hir::AttrItem],
        ty_translator: &types::LocalTX<'def, 'tcx>,
        translator: &mut code::FunctionBuilder<'def>,
        arg_names: &[String],
        inputs: &[ty::Ty<'tcx>],
        output: ty::Ty<'tcx>,
    ) -> Result<specs::functions::LiteralSpecBuilder<'def>, TranslationError<'tcx>> {
        info!("inputs: {:?}, output: {:?}", inputs, output);

        let mut translated_arg_types: Vec<specs::Type<'def>> = Vec::new();
        for arg in inputs {
            let translated: specs::Type<'def> = ty_translator.translate_type(*arg)?;
            translated_arg_types.push(translated);
        }
        let translated_ret_type: specs::Type<'def> = ty_translator.translate_type(output)?;
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        let ret_is_option = ty_translator.translator.is_builtin_option_type(output);
        let ret_is_result = ty_translator.translator.is_builtin_result_type(output);

        let mut spec_builder = specs::functions::LiteralSpecBuilder::new();

        let parser = rrconfig::attribute_parser();
        match parser.as_str() {
            "verbose" => {
                {
                    let scope = ty_translator.scope.borrow();
                    let mut parser: VerboseFunctionSpecParser<'_, 'def, _, _> =
                        VerboseFunctionSpecParser::new(
                            &translator.spec.function_name,
                            &translated_arg_types,
                            &translated_ret_type,
                            ret_is_option,
                            ret_is_result,
                            Some(arg_names),
                            &*scope,
                            |lit| ty_translator.translator.intern_literal(lit),
                        );

                    parser
                        .parse_function_spec(attrs, &mut spec_builder)
                        .map_err(TranslationError::AttributeError)?;
                    Self::process_function_requirements(translator, parser.into());
                }

                Ok(spec_builder)
            },
            _ => Err(TranslationError::UnknownAttributeParser(parser)),
        }
    }

    /// Make a specification for a method of a trait impl derived from the trait's default spec.
    fn make_trait_instance_spec(
        &self,
    ) -> Result<Option<specs::traits::InstantiatedFunctionSpec<'def>>, TranslationError<'tcx>> {
        let did = self.proc.get_id();

        let Some(impl_did) = self.env.tcx().impl_of_assoc(did) else {
            return Ok(None);
        };

        let Some(trait_did) = self.env.tcx().trait_id_of_impl(impl_did) else {
            return Ok(None);
        };

        self.trait_registry
            .lookup_trait(trait_did)
            .ok_or_else(|| TranslationError::TraitResolution(format!("{trait_did:?}")))?;

        let fn_name = strip_coq_ident(self.env.tcx().item_name(self.proc.get_id()).as_str());

        let (trait_info, _) = self.trait_registry.get_trait_impl_info(impl_did)?;
        Ok(Some(specs::traits::InstantiatedFunctionSpec::new(trait_info, fn_name)))
    }

    fn dump_body(body: &mir::Body<'_>) {
        let basic_blocks = &body.basic_blocks;
        for (bb_idx, bb) in basic_blocks.iter_enumerated() {
            Self::dump_basic_block(bb_idx, bb);
        }
    }

    /// Dump a basic block as info debug output.
    fn dump_basic_block(bb_idx: mir::BasicBlock, bb: &mir::BasicBlockData<'_>) {
        info!("Basic block {:?}:", bb_idx);
        let mut i = 0;
        for s in &bb.statements {
            info!("{}\t{:?}", i, s);
            i += 1;
        }
        info!("{}\t{:?}", i, bb.terminator());
    }
}
