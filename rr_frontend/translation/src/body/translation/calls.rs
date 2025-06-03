// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use log::{info, trace};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use super::TX;
use crate::base::*;
use crate::environment::borrowck::facts;
use crate::traits::resolution;
use crate::{regions, types};

/// Get the syntypes of function arguments for a procedure call.
fn get_arg_syntypes_for_procedure_call<'tcx, 'def>(
    tcx: ty::TyCtxt<'tcx>,
    ty_translator: &types::LocalTX<'def, 'tcx>,
    callee_did: DefId,
    ty_params: &[ty::GenericArg<'tcx>],
) -> Result<Vec<radium::SynType>, TranslationError<'tcx>> {
    // Get the type of the callee, fully instantiated
    let full_ty: ty::EarlyBinder<ty::Ty<'tcx>> = tcx.type_of(callee_did);
    let full_ty = full_ty.instantiate(tcx, ty_params);

    // We create a dummy scope in order to make the lifetime lookups succeed, since we only want
    // syntactic types here.
    // Since we do the substitution of the generics above, we should translate generics and
    // traits in the caller's scope.
    let scope = ty_translator.scope.borrow();
    let param_env: ty::ParamEnv<'tcx> = tcx.param_env(scope.did);
    let callee_state = types::CalleeState::new(&param_env, &scope.generic_scope);
    let mut dummy_state = types::STInner::CalleeTranslation(callee_state);

    let mut syntypes = Vec::new();
    match full_ty.kind() {
        ty::TyKind::FnDef(_, _) => {
            let sig = full_ty.fn_sig(tcx);
            for ty in sig.inputs().skip_binder() {
                let st = ty_translator.translator.translate_type_to_syn_type(*ty, &mut dummy_state)?;
                syntypes.push(st);
            }
        },
        ty::TyKind::Closure(_, args) => {
            let clos_args = args.as_closure();
            let sig = clos_args.sig();
            let pre_sig = sig.skip_binder();
            // we also need to add the closure argument here

            let tuple_ty = clos_args.tupled_upvars_ty();
            match clos_args.kind() {
                ty::ClosureKind::Fn | ty::ClosureKind::FnMut => {
                    syntypes.push(radium::SynType::Ptr);
                },
                ty::ClosureKind::FnOnce => {
                    let st =
                        ty_translator.translator.translate_type_to_syn_type(tuple_ty, &mut dummy_state)?;
                    syntypes.push(st);
                },
            }
            for ty in pre_sig.inputs() {
                let st = ty_translator.translator.translate_type_to_syn_type(*ty, &mut dummy_state)?;
                syntypes.push(st);
            }
        },
        _ => unimplemented!(),
    }

    Ok(syntypes)
}

pub struct ProcedureInst<'def> {
    pub loc_name: String,
    pub type_hint: Vec<radium::Type<'def>>,
    pub lft_hint: Vec<radium::Lft>,
    pub mapped_early_regions: HashMap<radium::Lft, usize>,
}

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Internally register that we have used a procedure with a particular instantiation of generics, and
    /// return the code parameter name.
    /// Arguments:
    /// - `callee_did`: the `DefId` of the callee
    /// - `ty_params`: the instantiation for the callee's type parameters
    /// - `trait_spec_terms`: if the callee has any trait assumptions, these are specification parameter terms
    ///   for these traits
    /// - `trait_assoc_tys`: if the callee has any trait assumptions, these are the instantiations for all
    ///   associated types
    fn register_use_procedure(
        &mut self,
        callee_did: DefId,
        extra_spec_args: Vec<String>,
        ty_params: ty::GenericArgsRef<'tcx>,
        trait_specs: Vec<radium::TraitReqInst<'def, ty::Ty<'tcx>>>,
    ) -> Result<ProcedureInst<'def>, TranslationError<'tcx>> {
        trace!("enter register_use_procedure callee_did={callee_did:?} ty_params={ty_params:?}");
        // The key does not include the associated types, as the resolution of the associated types
        // should always be unique for one combination of type parameters, as long as we remain in
        // the same environment (which is the case within this procedure).
        // Therefore, already the type parameters are sufficient to distinguish different
        // instantiations.
        let key = types::generate_args_inst_key(self.env.tcx(), ty_params)?;

        // re-quantify
        let quantified_args = self.ty_translator.get_generic_abstraction_for_procedure(
            callee_did,
            ty_params,
            ty_params,
            trait_specs,
            true,
        )?;

        let tup = (callee_did, key);
        let res;
        if let Some(proc_use) = self.collected_procedures.get(&tup) {
            res = proc_use.loc_name.clone();
        } else {
            let meta = self
                .procedure_registry
                .lookup_function(callee_did)
                .ok_or_else(|| TranslationError::UnknownProcedure(format!("{:?}", callee_did)))?;
            // explicit instantiation is needed sometimes
            let spec_term = radium::UsedProcedureSpec::Literal(
                meta.get_spec_name().to_owned(),
                meta.get_trait_req_incl_name().to_owned(),
            );

            let code_name = meta.get_name();
            let loc_name = format!("{}_loc", types::mangle_name_with_tys(code_name, tup.1.as_slice()));

            let syntypes = get_arg_syntypes_for_procedure_call(
                self.env.tcx(),
                &self.ty_translator,
                callee_did,
                ty_params.as_slice(),
            )?;

            let fn_inst = quantified_args.fn_scope_inst;

            info!(
                "Registered procedure instance {} of {:?} with {:?} and layouts {:?}",
                loc_name, callee_did, fn_inst, syntypes
            );

            let proc_use = radium::UsedProcedure::new(
                loc_name,
                spec_term,
                extra_spec_args,
                quantified_args.scope,
                fn_inst,
                syntypes,
            );

            res = proc_use.loc_name.clone();
            self.collected_procedures.insert(tup, proc_use);
        }
        trace!("leave register_use_procedure");
        let inst = ProcedureInst {
            loc_name: res,
            type_hint: quantified_args.callee_ty_param_inst,
            lft_hint: quantified_args.callee_lft_param_inst,
            mapped_early_regions: HashMap::new(),
        };
        Ok(inst)
    }

    /// Internally register that we have used a trait method with a particular instantiation of
    /// generics, and return the code parameter name.
    fn register_use_trait_method<'c>(
        &'c mut self,
        callee_did: DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
        trait_specs: Vec<radium::TraitReqInst<'def, ty::Ty<'tcx>>>,
    ) -> Result<ProcedureInst<'def>, TranslationError<'tcx>> {
        trace!("enter register_use_trait_method did={:?} ty_params={:?}", callee_did, ty_params);
        // Does not include the associated types in the key; see `register_use_procedure` for an
        // explanation.
        let key = types::generate_args_inst_key(self.env.tcx(), ty_params)?;

        let (method_loc_name, (method_spec_term, spec_scope, spec_inst), mapped_early_regions, method_params) =
            self.ty_translator.register_use_trait_procedure(self.env, callee_did, ty_params)?;

        // re-quantify
        let mut quantified_args = self.ty_translator.get_generic_abstraction_for_procedure(
            callee_did,
            method_params,
            ty_params,
            trait_specs,
            false,
        )?;

        // we add spec_scope and spec_inst as the first lifetimes to quantify in the new scope
        let mut function_spec_scope: radium::GenericScope<'_, _> = spec_scope.into();
        function_spec_scope.append(&quantified_args.scope);

        let ty_param_hint = quantified_args.callee_ty_param_inst;
        let mut lft_param_hint = spec_inst.lft_insts;
        lft_param_hint.append(&mut quantified_args.callee_lft_param_inst);

        let tup = (callee_did, key);
        let res;
        if let Some(proc_use) = self.collected_procedures.get(&tup) {
            res = proc_use.loc_name.clone();
        } else {
            // TODO: should we use ty_params or method_params?
            let syntypes = get_arg_syntypes_for_procedure_call(
                self.env.tcx(),
                &self.ty_translator,
                callee_did,
                ty_params.as_slice(),
            )?;

            let fn_inst = quantified_args.fn_scope_inst;

            info!(
                "Registered procedure instance {} of {:?} with {:?} and layouts {:?}",
                method_loc_name, callee_did, fn_inst, syntypes
            );

            let proc_use = radium::UsedProcedure::new(
                method_loc_name,
                method_spec_term,
                vec![],
                function_spec_scope,
                fn_inst,
                syntypes,
            );

            res = proc_use.loc_name.clone();
            self.collected_procedures.insert(tup, proc_use);
        }
        trace!("leave register_use_procedure");

        let inst = ProcedureInst {
            loc_name: res,
            type_hint: ty_param_hint,
            lft_hint: lft_param_hint,
            mapped_early_regions,
        };
        Ok(inst)
    }

    /// Resolve the trait requirements of a function call.
    /// The target of the call, [did], should have been resolved as much as possible,
    /// as the requirements of a call can be different depending on which impl we consider.
    fn resolve_trait_requirements_of_call(
        &self,
        did: DefId,
        params: ty::GenericArgsRef<'tcx>,
    ) -> Result<Vec<radium::TraitReqInst<'def, ty::Ty<'tcx>>>, TranslationError<'tcx>> {
        let mut scope = self.ty_translator.scope.borrow_mut();
        let mut state = types::STInner::InFunction(&mut scope);
        self.trait_registry.resolve_trait_requirements_in_state(&mut state, did, params)
    }

    /// Translate the use of an `FnDef`, registering that the current function needs to link against
    /// a particular monomorphization of the used function.
    /// Is guaranteed to return a `radium::Expr::CallTarget` with the parameter instantiation of
    /// this function annotated.
    pub(super) fn translate_fn_def_use(
        &mut self,
        ty: ty::Ty<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        let ty::TyKind::FnDef(defid, params) = ty.kind() else {
            return Err(TranslationError::UnknownError("not a FnDef type".to_owned()));
        };

        let current_param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(self.proc.get_id());

        // Check whether we are calling into a trait method.
        // This works since we did not resolve concrete instances, so this is always an abstract
        // reference to the trait.
        let calling_trait = self.env.tcx().trait_of_item(*defid);

        // Check whether we are calling a plain function or a trait method
        let Some(_) = calling_trait else {
            // resolve the trait requirements
            let trait_spec_terms = self.resolve_trait_requirements_of_call(*defid, params)?;

            // track that we are using this function and generate the Coq location name
            let code_inst = self.register_use_procedure(*defid, vec![], params, trait_spec_terms)?;

            let ty_hint = code_inst.type_hint.into_iter().map(|x| radium::RustType::of_type(&x)).collect();

            return Ok(radium::Expr::CallTarget(
                code_inst.loc_name,
                ty_hint,
                code_inst.lft_hint,
                code_inst.mapped_early_regions,
            ));
        };

        // Otherwise, we are calling a trait method
        // Resolve the trait instance using trait selection
        let Some((resolved_did, resolved_params, kind)) = resolution::resolve_assoc_item(
            self.env.tcx(),
            current_param_env,
            *defid,
            params,
            ty::Binder::dummy(()),
        ) else {
            return Err(TranslationError::TraitResolution(format!("Could not resolve trait {:?}", defid)));
        };

        info!(
            "Resolved trait method {:?} as {:?} with substs {:?} and kind {:?}",
            defid, resolved_did, resolved_params, kind
        );

        match kind {
            resolution::TraitResolutionKind::UserDefined => {
                // We can statically resolve the particular trait instance,
                // but need to apply the spec to the instance's spec attributes

                // resolve the trait requirements
                let trait_spec_terms =
                    self.resolve_trait_requirements_of_call(resolved_did, resolved_params)?;

                let code_inst =
                    self.register_use_procedure(resolved_did, vec![], resolved_params, trait_spec_terms)?;
                let ty_hint =
                    code_inst.type_hint.into_iter().map(|x| radium::RustType::of_type(&x)).collect();

                Ok(radium::Expr::CallTarget(
                    code_inst.loc_name,
                    ty_hint,
                    code_inst.lft_hint,
                    code_inst.mapped_early_regions,
                ))
            },

            resolution::TraitResolutionKind::Param => {
                // In this case, we have already applied it to the spec attribute

                // resolve the trait requirements
                let trait_spec_terms = self.resolve_trait_requirements_of_call(*defid, params)?;

                let code_inst =
                    self.register_use_trait_method(resolved_did, resolved_params, trait_spec_terms)?;
                let ty_hint =
                    code_inst.type_hint.into_iter().map(|x| radium::RustType::of_type(&x)).collect();

                Ok(radium::Expr::CallTarget(
                    code_inst.loc_name,
                    ty_hint,
                    code_inst.lft_hint,
                    code_inst.mapped_early_regions,
                ))
            },

            resolution::TraitResolutionKind::Closure => {
                // TODO: here, we should first generate an instance of the trait
                //let body = self.env.tcx().instance_mir(middle::ty::InstanceDef::Item(resolved_did));
                //let body = self.env.tcx().instance_mir(middle::ty::InstanceDef::FnPtrShim(*defid, ty));
                //info!("closure body: {:?}", body);

                //FunctionTranslator::dump_body(body);

                //let res_result = ty::Instance::resolve(self.env.tcx(), callee_param_env, *defid, params);
                //info!("Resolution {:?}", res_result);

                // the args are just the closure args. We can ignore them.
                let _clos_args = resolved_params.as_closure();

                // resolve the trait requirements
                let trait_spec_terms = self.resolve_trait_requirements_of_call(*defid, params)?;

                let code_inst =
                    self.register_use_procedure(resolved_did, vec![], ty::List::empty(), trait_spec_terms)?;
                let ty_hint =
                    code_inst.type_hint.into_iter().map(|x| radium::RustType::of_type(&x)).collect();

                Ok(radium::Expr::CallTarget(
                    code_inst.loc_name,
                    ty_hint,
                    code_inst.lft_hint,
                    code_inst.mapped_early_regions,
                ))
            },
        }
    }

    /// Split the type of a function operand of a call expression to a base type and an instantiation for
    /// generics.
    fn call_expr_op_split_inst(
        &self,
        constant: &mir::Const<'tcx>,
    ) -> Result<
        (DefId, ty::PolyFnSig<'tcx>, ty::GenericArgsRef<'tcx>, ty::PolyFnSig<'tcx>),
        TranslationError<'tcx>,
    > {
        match constant {
            mir::Const::Ty(c) => {
                match c.ty().kind() {
                    ty::TyKind::FnDef(def, args) => {
                        let ty: ty::EarlyBinder<ty::Ty<'tcx>> = self.env.tcx().type_of(def);
                        let ty_ident = ty.instantiate_identity();
                        assert!(ty_ident.is_fn());
                        let ident_sig = ty_ident.fn_sig(self.env.tcx());

                        let ty_instantiated = ty.instantiate(self.env.tcx(), args.as_slice());
                        let instantiated_sig = ty_instantiated.fn_sig(self.env.tcx());

                        Ok((*def, ident_sig, args, instantiated_sig))
                    },
                    // TODO handle FnPtr, closure
                    _ => Err(TranslationError::Unimplemented {
                        description: "implement function pointers".to_owned(),
                    }),
                }
            },
            mir::Const::Val(_, ty) => {
                match ty.kind() {
                    ty::TyKind::FnDef(def, args) => {
                        let ty: ty::EarlyBinder<ty::Ty<'tcx>> = self.env.tcx().type_of(def);

                        let ty_ident = ty.instantiate_identity();
                        assert!(ty_ident.is_fn());
                        let ident_sig = ty_ident.fn_sig(self.env.tcx());

                        let ty_instantiated = ty.instantiate(self.env.tcx(), args.as_slice());
                        let instantiated_sig = ty_instantiated.fn_sig(self.env.tcx());

                        Ok((*def, ident_sig, args, instantiated_sig))
                    },
                    // TODO handle FnPtr, closure
                    _ => Err(TranslationError::Unimplemented {
                        description: "implement function pointers".to_owned(),
                    }),
                }
            },
            mir::Const::Unevaluated(_, _) => Err(TranslationError::Unimplemented {
                description: "implement ConstantKind::Unevaluated".to_owned(),
            }),
        }
    }

    pub(super) fn translate_function_call(
        &mut self,
        func: &mir::Operand<'tcx>,
        args: &[mir::Operand<'tcx>],
        destination: &mir::Place<'tcx>,
        target: Option<mir::BasicBlock>,
        loc: mir::Location,
        endlfts: Vec<radium::PrimStmt>,
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        let startpoint = self.info.interner.get_point_index(&facts::Point {
            location: loc,
            typ: facts::PointType::Start,
        });

        let mir::Operand::Constant(box func_constant) = func else {
            return Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of call operand (got: {:?})",
                    func
                ),
            });
        };

        // Get the type of the return value from the function
        let (target_did, sig, generic_args, inst_sig) =
            self.call_expr_op_split_inst(&func_constant.const_)?;
        info!("calling function {:?}", target_did);
        info!("call substs: {:?} = {:?}, {:?}", func, sig, generic_args);

        // for lifetime annotations:
        // 1. get the regions involved here. for that, get the instantiation of the function.
        //    + if it's a FnDef type, that should be easy.
        //    + for a function pointer: ?
        //    + for a closure: ?
        //   (Polonius does not seem to distinguish early/late bound in any way, except
        //   that they are numbered in different passes)
        // 2. find the constraints here involving the regions.
        // 3. solve for the regions.
        //    + transitively propagate the constraints
        //    + check for equalities
        //    + otherwise compute intersection. singleton intersection just becomes an equality def.
        // 4. add annotations accordingly
        //    + either a startlft
        //    + or a copy name
        // 5. add shortenlft annotations to line up arguments.
        //    + for that, we need the type of the LHS, and what the argument types (with
        //    substituted regions) should be.
        // 6. annotate the return value on assignment and establish constraints.

        let classification =
            regions::calls::compute_call_regions(self.env, &self.inclusion_tracker, generic_args, loc);

        // update the inclusion tracker with the new regions we have introduced
        // We just add the inclusions and ignore that we resolve it in a "tight" way.
        // the cases where we need the reverse inclusion should be really rare.
        for (r, c) in &classification.classification {
            match c {
                regions::calls::CallRegionKind::EqR(r2) => {
                    // put it at the start point, because the inclusions come into effect
                    // at the point right before.
                    self.inclusion_tracker.add_static_inclusion(*r, *r2, startpoint);
                    self.inclusion_tracker.add_static_inclusion(*r2, *r, startpoint);
                },
                regions::calls::CallRegionKind::Intersection(lfts) => {
                    // all the regions represented by lfts need to be included in r
                    for r2 in lfts {
                        self.inclusion_tracker.add_static_inclusion(*r2, *r, startpoint);
                    }
                },
            }
        }

        // translate the function expression.
        let func_expr = self.translate_operand(func, false)?;
        // We expect this to be an Expr::CallTarget, being annotated with the type parameters we
        // instantiate it with.
        let radium::Expr::CallTarget(func_lit, ty_param_annots, mut lft_param_annots, mapped_early_regions) =
            func_expr
        else {
            unreachable!("Logic error in call target translation");
        };
        let func_expr = radium::Expr::MetaParam(func_lit);

        // translate the arguments
        let mut translated_args = Vec::new();
        for arg in args {
            // to_ty is the type the function expects

            //let ty = arg.ty(&self.proc.get_mir().local_decls, self.env.tcx());
            let translated_arg = self.translate_operand(arg, true)?;
            translated_args.push(translated_arg);
        }

        // We have to add the late regions, since we do not requantify over them.
        for late in &classification.late_regions {
            let lft = self.format_region(*late);
            lft_param_annots.push(lft);
        }
        info!("Call lifetime instantiation (early): {:?}", classification.early_regions);
        info!("Call lifetime instantiation (late): {:?}", classification.late_regions);

        // TODO: do we need to do something with late bounds?
        let output_ty = inst_sig.output().skip_binder();
        info!("call has instantiated type {:?}", inst_sig);

        // compute the resulting annotations
        let lhs_ty = self.get_type_of_place(destination);
        let lhs_strongly_writeable = !self.check_place_below_reference(destination);
        let assignment_annots = regions::assignment::get_assignment_annots(
            self.env,
            &mut self.inclusion_tracker,
            &self.ty_translator,
            loc,
            lhs_strongly_writeable,
            lhs_ty,
            output_ty,
        );
        info!("assignment annots after call: {assignment_annots:?}");

        // build annotations for unconstrained regions
        let (unconstrained_annotations, unconstrained_regions) =
            regions::calls::compute_unconstrained_region_annots(
                &mut self.inclusion_tracker,
                &self.ty_translator,
                loc,
                assignment_annots.unconstrained_regions,
                &mapped_early_regions,
            )?;

        let (remaining_unconstrained_annots, unconstrained_hints) =
            regions::assignment::make_unconstrained_region_annotations(
                &mut self.inclusion_tracker,
                &self.ty_translator,
                unconstrained_regions,
                loc,
                None,
            )?;
        for hint in unconstrained_hints {
            self.translated_fn.add_unconstrained_lft_hint(hint);
        }

        // add annotations to initialize the regions for the call (before the call)
        let mut stmt_annots = Vec::new();
        for (r, class) in &classification.classification {
            let lft = self.format_region(*r);
            match class {
                regions::calls::CallRegionKind::EqR(r2) => {
                    let lft2 = self.format_region(*r2);
                    stmt_annots.push(radium::Annotation::CopyLftName(lft2, lft));
                },

                regions::calls::CallRegionKind::Intersection(rs) => {
                    match rs.len() {
                        0 => {
                            return Err(TranslationError::UnsupportedFeature {
                                description: "RefinedRust does currently not support unconstrained lifetime"
                                    .to_owned(),
                            });
                        },
                        1 => {
                            // this is really just an equality constraint
                            if let Some(r2) = rs.iter().next() {
                                let lft2 = self.format_region(*r2);
                                stmt_annots.push(radium::Annotation::CopyLftName(lft2, lft));
                            }
                        },
                        _ => {
                            // a proper intersection
                            let lfts: Vec<_> = rs.iter().map(|r| self.format_region(*r)).collect();
                            stmt_annots.push(radium::Annotation::AliasLftIntersection(lft, lfts));
                        },
                    };
                },
            }
        }

        let mut prim_stmts = vec![radium::PrimStmt::Annot {
            a: stmt_annots,
            why: Some("function_call".to_owned()),
        }];

        // add annotations for the assignment
        let call_expr = radium::Expr::Call {
            f: Box::new(func_expr),
            lfts: lft_param_annots,
            tys: ty_param_annots,
            args: translated_args,
        };
        let stmt = if let Some(target) = target {
            prim_stmts.push(radium::PrimStmt::Annot {
                a: remaining_unconstrained_annots,
                why: Some("function_call (unconstrained)".to_owned()),
            });

            prim_stmts.push(radium::PrimStmt::Annot {
                a: assignment_annots.new_dyn_inclusions,
                why: Some("function_call (assign)".to_owned()),
            });

            // assign stmt with call; then jump to bb
            let place_ty = self.get_type_of_place(destination);
            let place_st = self.ty_translator.translate_type_to_syn_type(place_ty.ty)?;
            let place_expr = self.translate_place(destination)?;
            let ot = place_st.into();

            let annotated_rhs = radium::Expr::with_optional_annotation(
                call_expr,
                assignment_annots.expr_annot,
                Some("function_call (assign)".to_owned()),
            );
            let assign_stmt = radium::PrimStmt::Assign {
                ot,
                e1: place_expr,
                e2: annotated_rhs,
            };
            prim_stmts.push(assign_stmt);

            prim_stmts.push(radium::PrimStmt::Annot {
                a: unconstrained_annotations,
                why: Some("post_function_call (assign, early)".to_owned()),
            });

            prim_stmts.push(radium::PrimStmt::Annot {
                a: assignment_annots.stmt_annot,
                why: Some("post_function_call (assign)".to_owned()),
            });

            // end loans before the goto, but after the call.
            // TODO: may cause duplications?
            prim_stmts.extend(endlfts);

            let cont_stmt = self.translate_goto_like(&loc, target)?;

            radium::Stmt::Prim(prim_stmts, Box::new(cont_stmt))
        } else {
            // expr stmt with call; then stuck (we have not provided a continuation, after all)
            let exprs = radium::PrimStmt::ExprS(call_expr);
            radium::Stmt::Prim(vec![exprs], Box::new(radium::Stmt::Stuck))
        };

        Ok(stmt)
    }
}
