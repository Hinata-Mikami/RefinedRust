Require Import Stdlib.Strings.String.
From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Export type.
From lithium Require Export all.
From lithium Require Import hooks.
From refinedrust.automation Require Import ident_to_string lookup_definition.
From refinedrust Require Import int programs program_rules functions mut_ref.mut_ref shr_ref struct.struct array.array enum xmap.
(* Important: import proof_state last as it overrides some Lithium tactics *)
From refinedrust.automation Require Export loops existentials simpl solvers proof_state.
From refinedrust Require Import options.

(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.


Global Hint Transparent ly_size : solve_protected_eq_db.
Ltac solve_protected_eq_hook ::=
  lazymatch goal with
  (* unfold constants for function types *)
  | |- @eq (_ → fn_params) ?a (λ x, _) =>
    lazymatch a with
    | (λ x, _) => idtac
    | _ =>
      let h := get_head a in
      unfold h;
      (* necessary to reduce after unfolding because of the strict
      opaqueness settings for unification *)
      liSimpl
    end
  (* Try to simplify as much as possible *)
  (*| |- pcons _ _ = pcons _ _ => *)
      (*repeat f_equiv;*)
      (*match goal with *)
      (*| |- @pnil _ _ = @pnil _ _ => reflexivity*)
      (*| |- _ => idtac*)
      (*end*)

  (* don't fail if nothing matches *)
  | |- _ => idtac
  end.

Ltac can_solve_hook ::= first [
  match goal with
  | |- _ ≠ _ => discriminate
  end | open_scache; solve_goal].

Ltac liTrace_hook info ::=
  add_case_distinction_info info.

Ltac rep_check_backtrack_point_hook ::=
  lazymatch goal with
  | |- BACKTRACK_POINT ?P => idtac
  | |- envs_entails _ ?P =>
      lazymatch P with
      | typed_stmt _ _ _ _ _ _ => idtac
      | typed_val_expr _ _ _ _ => idtac
      | typed_call _ _ _ _ _ _ _ _ _ => idtac
      (* TODO maybe also typed_assert etc *)
      end
  end.

Ltac liForall_hook ::=
  (* simpl RT_xt *)
  lazymatch goal with
  | |- forall e : ?A, @?P e =>
      match A with
      | RT_xt ?rt =>
          assert_fails (is_var rt);
          lazymatch rt with
          | RT_of ?ty =>
              assert_fails (is_var ty)
              (* TODO: maybe unfold the RT_of? *)
          | _ => idtac
          end;

          simpl
      end
  end.

Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | subsume_full ?E ?L ?step ?P ?Q ?T =>
      cont uconstr:(((_ : SubsumeFull E L step P Q) T))
  | relate_list ?E ?L ?ig ?l1 ?l2 ?i0 ?R ?T =>
      cont uconstr:(((_ : RelateList E L ig l1 l2 i0 R) T))
  | relate_hlist ?E ?L ?ig ?Xs ?l1 ?l2 ?i0 ?R ?T =>
      cont uconstr:(((_ : RelateHList E L ig Xs l1 l2 i0 R) T))
  | fold_list ?E ?L ?ig ?l ?i0 ?P ?T =>
      cont uconstr:(((_ : FoldList E L ig l i0 P) T))
  | typed_value ?v ?π ?T =>
      cont uconstr:(((_ : TypedValue v π) T))
  | typed_bin_op ?E ?L ?v1 ?ty1 ?v2 ?ty2 ?o ?ot1 ?ot2 ?T =>
      cont uconstr:(((_ : TypedBinOp E L v1 ty1 v2 ty2 o ot1 ot2) T))
  | typed_un_op ?E ?L ?v ?ty ?o ?ot ?T =>
      cont uconstr:(((_ : TypedUnOp E L v ty o ot) T))
  | typed_check_bin_op ?E ?L ?v1 ?ty1 ?v2 ?ty2 ?o ?ot1 ?ot2 ?T =>
      cont uconstr:(((_ : TypedCheckBinOp E L v1 ty1 v2 ty2 o ot1 ot2) T))
  | typed_check_un_op ?E ?L ?v ?ty ?o ?ot ?T =>
      cont uconstr:(((_ : TypedCheckUnOp E L v ty o ot) T))
  | typed_call ?π ?E ?L ?eκs ?etys ?v ?P ?vl ?tys ?T =>
      cont uconstr:(((_ : TypedCall π E L eκs etys v P vl tys) T))
  | typed_place ?π ?E ?L ?l ?lt ?r ?bmin0 ?b ?P ?T =>
      cont uconstr:(((_ : TypedPlace E L π l lt r bmin0 b P) T))
  | typed_if ?E ?L ?v ?P ?T1 ?T2 =>
      cont uconstr:(((_ : TypedIf E L v P) T1 T2))
  | typed_switch ?π ?E ?L ?v ?rt ?ty ?r ?it ?m ?ss ?def ?fn ?R ?ϝ =>
      cont uconstr:(((_ : TypedSwitch π E L v rt ty r it) m ss def fn R ϝ))
  | typed_assert ?π ?E ?L ?v ?ty ?r ?s ?fn ?R ?ϝ =>
      cont uconstr:(((_ : TypedAssert π E L v ty r) s fn R ϝ))
  | typed_read_end ?π ?E ?L ?l ?ty ?r ?b2 ?bmin ?ot ?T =>
      cont uconstr:(((_ : TypedReadEnd π E L l ty r b2 bmin ot) T))
  | typed_write_end ?π ?E ?L ?ot ?v1 ?ty1 ?r1 ?b2 ?bmin ?l2 ?lt2 ?r2 ?T =>
      cont uconstr:(((_ : TypedWriteEnd π E L ot v1 ty1 r1 b2 bmin l2 lt2 r2) T))
  | typed_borrow_mut_end ?π ?E ?L ?κ ?l ?orty ?lt ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedBorrowMutEnd π E L κ l orty lt r b2 bmin) T))
  | typed_borrow_shr_end ?π ?E ?L ?κ ?l ?orty ?lt ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedBorrowShrEnd π E L κ l orty lt r b2 bmin) T))
  | typed_addr_of_mut_end ?π ?E ?L ?l ?lt ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedAddrOfMutEnd π E L l lt r b2 bmin) T))
  | cast_ltype_to_type ?E ?L ?lt ?T =>
      cont uconstr:(((_ : CastLtypeToType E L lt) T))
  | typed_context_fold ?AI ?E ?L ?m ?tctx ?acc ?T =>
      cont uconstr:(((_ : TypedContextFold AI E L m tctx acc) T))
  | typed_context_fold_step ?AI ?π ?E ?L ?m ?l ?lt ?r ?tctx ?acc ?T =>
      cont uconstr:(((_ : TypedContextFoldStep AI π E L m l lt r tctx acc) T))
  | typed_annot_expr ?E ?L ?n ?a ?v ?P ?T =>
      cont uconstr:(((_ : TypedAnnotExpr E L n a v P) T))
  | prove_with_subtype ?E ?L ?step ?pm ?P ?T =>
      cont uconstr:(((_ : ProveWithSubtype E L step pm P) T))
  | @owned_subtype _ _ ?π ?E ?L ?pers ?rt1 ?rt2 ?r1 ?r2 ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : @OwnedSubtype _ _ π E L pers rt1 rt2 r1 r2 ty1 ty2) T)
  | owned_subltype_step ?π ?E ?L ?l ?r1 ?r2 ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : OwnedSubltypeStep π E L l r1 r2 lt1 lt2) T)
  | @weak_subtype _ _ ?E ?L ?rt1 ?rt2 ?r1 ?r2 ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : @Subtype _ _ E L rt1 rt2 r1 r2 ty1 ty2) T)
  | weak_subltype ?E ?L ?k ?r1 ?r2 ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : SubLtype E L k r1 r2 lt1 lt2) T)
  | mut_subtype ?E ?L ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : MutSubtype E L ty1 ty2) T)
  | mut_eqtype ?E ?L ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : MutEqtype E L ty1 ty2) T)
  | mut_subltype ?E ?L ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : MutSubLtype E L lt1 lt2) T)
  | mut_eqltype ?E ?L ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : MutEqLtype E L lt1 lt2) T)
  | stratify_ltype ?π ?E ?L ?mu ?mdu ?ma ?ml ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L mu mdu ma ml l lt r b) T))
  | stratify_ltype_unblock ?π ?E ?L ?ma ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ _ StratifyUnblockOp l lt r b) T))
  | stratify_ltype_extract ?π ?E ?L ?Ma ?l ?lt ?r ?b ?κ ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ _ (StratifyExtractOp κ) l lt r b) T))
  | stratify_ltype_resolve ?π ?E ?L ?Ma ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ _ (StratifyResolveOp) l lt r b) T))
  | stratify_ltype_post_hook ?π ?E ?L ?ml ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtypePostHook π E L ml l lt r b) T))
  | resolve_ghost ?π ?E ?L ?m ?lb ?l ?lt ?b ?r ?T =>
      cont uconstr:(((_ : ResolveGhost π E L m lb l lt b r) T))
  | find_observation ?rt ?γ ?mode ?T =>
      cont uconstr:(((_ : FindObservation rt γ mode) T))
  | typed_on_endlft ?E ?L ?κ ?worklist ?T =>
      cont uconstr:(((_ : TypedOnEndlft E L κ worklist) T))
  | typed_on_endlft_trigger ?E ?L ?key ?P ?T =>
      cont uconstr:(((_ : TypedOnEndlftTrigger E L key P) T))
  | introduce_with_hooks ?E ?L ?P ?T =>
      cont uconstr:(((_ : IntroduceWithHooks E L P) T))
  | prove_place_cond ?E ?L ?b ?lt1 ?lt2 ?T =>
      cont uconstr:(((_ : ProvePlaceCond E L b lt1 lt2) T))
  | typed_option_map ?o ?Φ ?d ?T =>
      cont uconstr:(((_ : TypedOptionMap o Φ d) T))
  | stratify_ltype_array_iter ?π ?E ?L ?mu ?mdu ?ma ?ml ?l ?ig ?def ?len ?iml ?rs ?bk ?T =>
      cont uconstr:(((_ : StratifyLtypeArrayIter π E L mu mdu ma ml l ig def len iml rs bk) T))
  | typed_array_access ?π ?E ?L ?base ?offset ?st ?lt ?r ?k ?T =>
      cont uconstr:(((_ : TypedArrayAccess π E L base offset st lt r k) T))
  | resolve_ghost_iter ?π ?E ?L ?rm ?lb ?l ?st ?lts ?b ?rs ?ig ?i0 ?T =>
      cont uconstr:(((_ : ResolveGhostIter π E L rm lb l st lts b rs ig i0) T))
  | typed_discriminant_end ?π ?E ?L ?l ?lt ?r ?b2 ?els ?T =>
      cont uconstr:(((_ : TypedDiscriminantEnd π E L l lt r b2 els) T))
  | interpret_typing_hint ?E ?L ?orty ?bmin ?ty ?r ?T =>
      cont uconstr:(((_ : InterpretTypingHint E L orty bmin ty r) T))
  end.

(** Strategy to directly unfold the instance we're applying;
  otherwise we may sometimes get massive Qed slowdown *)
Ltac liExtensible_hook ::=
lazymatch goal with
  | |- environments.envs_entails ?S ?a =>
  lazymatch a with
  | i2p_P (?a ?c) =>
    let b := eval hnf in a in
    change_no_check (environments.envs_entails S (b c))
  end; unfold i2p_P
end.


(** * Main automation tactics *)
Section automation.
  Context `{!typeGS Σ}.

  Lemma tac_simpl_subst E L xs s fn R ϝ :
    typed_stmt E L (W.to_stmt (W.subst_stmt xs s)) fn R ϝ -∗
    typed_stmt E L (subst_stmt xs (W.to_stmt s)) fn R ϝ.
  Proof. rewrite W.to_stmt_subst. auto. Qed.

  Lemma tac_trigger_tc {A} (a : A) (H : A → Type) (HP : H a) (T : A → iProp Σ) :
    T a ⊢ trigger_tc H T.
  Proof. iIntros "HT". iExists a, HP. iFrame. Qed.
  Lemma tac_find_tc_inst (H : Type) (HP : H) (T : H → iProp Σ) :
    T HP ⊢ find_tc_inst H T.
  Proof. iIntros "HT". iExists HP. iFrame. Qed.
End automation.

Ltac liRIntroduceLetInGoal :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
    let H := fresh "GOAL" in
    lazymatch P with
    | @bi_wand ?PROP ?Q ?T =>
      pose H := (LET_ID T); change_no_check (@envs_entails PROP Δ (@bi_wand PROP Q H))
    | @typed_val_expr ?Σ ?tG ?E ?L ?e ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_val_expr Σ tG E L e H))
    | @typed_write ?Σ ?tG ?π ?E ?L ?e ?ot ?v ?rt ?ty ?r ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_write Σ tG π E L e ot v rt ty r H))
    (* NOTE: these two guys really hurt Qed performance. Not a good idea at all! *)
    (*| @typed_place ?Σ ?tG ?π ?E ?L ?l ?rto ?lt ?r ?b ?bmin ?P ?T =>*)
      (*pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_place Σ tG π E L l rto lt r b bmin P H))*)
    (*| @typed_context_fold ?Σ ?tG ?Acc ?P ?M ?π ?E ?L ?m ?tcx ?acc ?T =>*)
      (*pose (H := LET_ID T);*)
      (*change_no_check (@envs_entails PROP Δ (@typed_context_fold Σ tG Acc P M π E L m tcx acc H))*)
    | @typed_bin_op ?Σ ?tG ?E ?L ?v1 ?P1 ?v2 ?P2 ?op ?ot1 ?ot2 ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_bin_op Σ tG E L v1 P1 v2 P2 op ot1 ot2 H))
    end
  end.

Ltac liRInstantiateEvars_hook := fail.
Ltac liRInstantiateEvars :=
  first [ liRInstantiateEvars_hook |
  lazymatch goal with
  | |- (_ < protected ?H)%nat ∧ _ =>
    (* We would like to use [liInst H (S (protected (EVAR_ID _)))],
      but this causes a Error: No such section variable or assumption
      at Qed. time. Maybe this is related to https://github.com/coq/coq/issues/9937 *)
    instantiate_protected H (S (protected (EVAR_ID _)))
  (* For some reason [solve_protected_eq] will sometimes not manage to do this.. *)
  | |- (protected ?a = ?b +:: ?c) ∧ _ =>
    instantiate_protected a (protected (EVAR_ID _) +:: protected (EVAR_ID _))
    (* NOTE: Important: We create new evars, instead of instantiating directly with [b] or [c].
        If [b] or [c] contains another evar, the let-definition for that will not be in scope, which can create trouble at Qed. time *)
  | |- (protected ?a = ?b -:: ?c) ∧ _ =>
    instantiate_protected a (protected (EVAR_ID _) -:: protected (EVAR_ID _))
  (* in this case, we do not want it to instantiate the evar for [a], but rather directly instantiate it with the only possible candidate.
     (if the other side also contains an evar, we would be instantiating less than we could otherwise) *)
  | |- (@eq (hlist _ []) _ (protected ?a)) ∧ _ =>
      instantiate_protected a +[]
  | |- (@eq (hlist _ []) (protected ?a) _) ∧ _ =>
      instantiate_protected a +[]

  | |- envs_entails _ (subsume_full _ _ _ (@ltype_own _ _ ?rt (◁ ?ty)%I _ _ _ _) (@ltype_own _ _ (xtype_rt (protected ?H)) (◁ xtype_ty (protected ?H))%I _ _ _ _) _) =>
      instantiate_protected H (@mk_xtype _ _ rt ty (protected (EVAR_ID _)))

  | |- envs_entails _ (subsume (@ltype_own _ _ (place_rfn ?rt1) _ _ _ _ _) (@ltype_own _ _ (place_rfn (protected ?rt2)) _ _ _ _ _) _) => liInst rt2 rt1
  | |- envs_entails _ (subsume (@ltype_own _ _ ?rt1 _ _ _ _ _) (@ltype_own _ _ (protected ?rt2) _ _ _ _ _) _) => liInst rt2 rt1

  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ (◁ ?ty)%I) (_ ◁ₗ[_, _] _ @ (◁ (protected ?H))%I) _) => liInst H ty
  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ ?lt) (_ ◁ₗ[_, _] _ @ (protected ?H)) _) => liInst H lt
  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ ?lt) (_ ◁ₗ[_, protected ?H] _ @ _) _) => liInst H b
  end].

(** Goto [goto_bb] *)
Ltac liRGoto goto_bb :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?E ?L (Goto _) ?fn ?R ?ϝ) =>
      first [
        (* try to find an inductive hypothesis we obtained previously *)
        notypeclasses refine (tac_fast_apply (type_goto_precond E L _ _ fn R ϝ) _);
        progress liFindHyp FICSyntactic
      | (* if we jump to a loop head, initiate Löb induction *)
        lazymatch goal with
        | H : bb_inv_map_marker ?LOOP_INV_MAP |- _ =>
            let loop_inv_map := eval hnf in LOOP_INV_MAP in
            (* find the loop invariant *)
            let Inv := find_bb_inv loop_inv_map goto_bb in
            let Inv := match Inv with
            | PolySome ?Inv => Inv
            | PolyNone =>
                (* we are not jumping to a loop head *)
                fail 1 "infer_loop_invariant: no loop invariant found"
            end in
            (* pose the composed loop invariant *)
            compute_loop_invariant fn Inv Δ E L ltac:(fun Inv IterVar =>
              (* finally initiate Löb *)
              match IterVar with
              | None =>
                notypeclasses refine (tac_fast_apply (typed_goto_acc E L fn R Inv goto_bb ϝ _ _) _);
                  [unfold_code_marker_and_compute_map_lookup|  ]
              | Some ?var =>
                notypeclasses refine (tac_fast_apply (typed_goto_acc' E L fn R goto_bb ϝ _ var Inv _) _);
                  [unfold_code_marker_and_compute_map_lookup|  ]
              end)
        end
      | (* do a direct jump *)
        notypeclasses refine (tac_fast_apply (type_goto E L _ fn R _ ϝ _) _);
          [unfold_code_marker_and_compute_map_lookup|]
      ]
  end.

Ltac liRStmt :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?E ?L ?s ?fn ?R ?ϝ) =>
    lazymatch s with
    | subst_stmt ?xs ?s =>
      let s' := W.of_stmt s in
      change (subst_stmt xs s) with (subst_stmt xs (W.to_stmt s'));
      refine (tac_fast_apply (tac_simpl_subst E L _ _ fn R ϝ) _); simpl; unfold W.to_stmt, W.to_expr
    | _ =>
      let s' := W.of_stmt s in
      lazymatch s' with
      | W.AssignSE _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_assign E L _ _ _ _ fn R _ ϝ) _)
      | W.Return _ => notypeclasses refine (tac_fast_apply (type_return E L _ fn R ϝ) _)
      | W.IfS _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_if E L _ _ _ fn R _ ϝ) _)
      | W.Switch _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_switch E L _ _ _ _ _ fn R ϝ) _)
      | W.Assert _ _ _ => notypeclasses refine (tac_fast_apply (type_assert E L _ _ fn R ϝ) _)
      | W.Goto ?bid => liRGoto bid
      | W.ExprS _ _ => notypeclasses refine (tac_fast_apply (type_exprs E L _ _ fn R ϝ) _)
      | W.SkipS _ => notypeclasses refine (tac_fast_apply (type_skips' E L _ fn R ϝ) _)
      | W.StuckS => exfalso
      | W.AnnotStmt _ (StartLftAnnot ?κ ?κs) _ => notypeclasses refine (tac_fast_apply (type_startlft E L κ κs _ fn R ϝ) _)
      | W.AnnotStmt _ (AliasLftAnnot ?κ ?κs) _ => notypeclasses refine (tac_fast_apply (type_alias_lft E L κ κs _ fn R ϝ) _)
      | W.AnnotStmt _ (EndLftAnnot ?κ) _ => notypeclasses refine (tac_fast_apply (type_endlft E L κ _ fn R ϝ) _)
      | W.AnnotStmt _ (StratifyContextAnnot) _ => notypeclasses refine (tac_fast_apply (type_stratify_context_annot E L _ fn R ϝ) _)
      | W.AnnotStmt _ (CopyLftNameAnnot ?n1 ?n2) _ => notypeclasses refine (tac_fast_apply (type_copy_lft_name E L n1 n2 _ fn R ϝ) _)
      | W.AnnotStmt _ (DynIncludeLftAnnot ?n1 ?n2) _ => notypeclasses refine (tac_fast_apply (type_dyn_include_lft E L n1 n2 _ fn R ϝ) _)
      | W.AnnotStmt _ (ExtendLftAnnot ?κ) _ => notypeclasses refine (tac_fast_apply (type_extendlft E L κ _ fn R ϝ) _)
      | W.AnnotStmt _ (UnconstrainedLftAnnot ?κ) _ =>
        notypeclasses refine (tac_fast_apply (type_unconstrained_lft E L κ _ fn R ϝ _) _);
          [solve [refine _] | ]
      | _ => fail "do_stmt: unknown stmt" s
      end
    end
  end.

Ltac liRIntroduceTypedStmt :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ (introduce_typed_stmt ?E ?L ?ϝ ?fn ?lsa ?lsv ?lya ?lyv ?R) =>
    iEval (rewrite /introduce_typed_stmt /to_runtime_function /subst_function !fmap_insert fmap_empty; simpl_subst);
      lazymatch goal with
      | |- @envs_entails ?PROP ?Δ (@typed_stmt ?Σ ?tG ?E ?L ?s ?fn ?R ?ϝ) =>
        let Hfn := fresh "FN" in
        let HR := fresh "R" in
        pose (Hfn := (CODE_MARKER fn));
        pose (HR := (RETURN_MARKER R));
        change_no_check (@envs_entails PROP Δ (@typed_stmt Σ tG E L s Hfn HR ϝ));
        iEval (simpl) (* To simplify f_init *)
        (*notypeclasses refine (tac_fast_apply (tac_simplify_elctx _ _ _ _ _ _ _ _ _) _); [simplify_elctx | ]*)
      end
  end.

Ltac liRExpr :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr ?E ?L ?e ?T) =>
    let e' := W.of_expr e in
    lazymatch e' with
    | W.Val _ => notypeclasses refine (tac_fast_apply (type_val E L _ T) _)
    | W.Loc _ => notypeclasses refine (tac_fast_apply (type_val E L _ T) _)
    | W.Use _ _ true _ => notypeclasses refine (tac_fast_apply (type_use E L _ _ _ T) _)
    | W.EnumDiscriminant _ _ => notypeclasses refine (tac_fast_apply (type_discriminant E L _ _ _ T _) _); [apply _ | ]
    | W.Borrow Mut _ _ _ => notypeclasses refine (tac_fast_apply (type_mut_bor E L T _ _ _) _)
    | W.Borrow Shr _ _ _ => notypeclasses refine (tac_fast_apply (type_shr_bor E L T _ _ _) _)
    | W.AddrOf _ _ => notypeclasses refine (tac_fast_apply (type_mut_addr_of E L _ T) _)
    | W.BinOp _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_bin_op E L _ _ _ _ _ T) _)
    | W.UnOp _ _ _ => notypeclasses refine (tac_fast_apply (type_un_op E L _ _ _ T) _)
    | W.CheckBinOp _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_check_bin_op E L _ _ _ _ _ T) _)
    | W.CheckUnOp _ _ _ => notypeclasses refine (tac_fast_apply (type_check_un_op E L _ _ _ T) _)
    | W.Call _ _ _ _ => notypeclasses refine (tac_fast_apply (type_call E L T _ _ _ _) _)
    | W.AnnotExpr _ ?a _ => notypeclasses refine (tac_fast_apply (type_annot_expr E L _ a _ T) _)
    | W.StructInit ?sls ?init => notypeclasses refine (tac_fast_apply (type_struct_init E L sls _ T) _)
    | W.EnumInit ?els ?variant ?rsty ?init => notypeclasses refine (tac_fast_apply (type_enum_init E L els variant rsty _ T) _)
    | W.IfE _ _ _ _ => notypeclasses refine (tac_fast_apply (type_ife E L _ _ _ T) _)
    | W.LogicalAnd _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_and E L _ _ _ _ T) _)
    | W.LogicalOr _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_or E L _ _ _ _ T) _)
    | _ => fail "do_expr: unknown expr" e
    end
  end.

(* Initialize context folding by gathering up the type context. *)
Ltac gather_location_list env :=
  match env with
  | Enil => uconstr:([])
  | Esnoc ?env' _ ?p =>
      let rs := gather_location_list env' in
      lazymatch p with
      | (?l ◁ₗ[?π, Owned false] ?r @ ?lty)%I =>
          uconstr:(l :: rs)
      | _ => uconstr:(rs)
      end
  end.
Ltac liRContextStratifyInit :=
  lazymatch goal with
  | |- envs_entails ?envs (typed_pre_context_fold ?E ?L (CtxFoldStratifyAllInit) ?T) =>
      let envs := eval hnf in envs in
      match envs with
      | Envs _ ?spatial _ =>
          let tctx := gather_location_list spatial in
          notypeclasses refine (tac_fast_apply (typed_context_fold_stratify_init tctx _ E L T) _)
      | _ => fail 1000 "gather_tctx: cannot determine Iris context"
      end
  end.

Ltac liRContextExtractInit :=
  lazymatch goal with
  | |- envs_entails ?envs (typed_pre_context_fold ?E ?L (CtxFoldExtractAllInit ?κ) ?T) =>
      let envs := eval hnf in envs in
      match envs with
      | Envs _ ?spatial _ =>
          let tctx := gather_location_list spatial in
          notypeclasses refine (tac_fast_apply (typed_context_fold_extract_init tctx _ E L κ T) _)
      | _ => fail 1000 "gather_tctx: cannot determine Iris context"
      end
  end.
Ltac liRContextResolveInit :=
  lazymatch goal with
  | |- envs_entails ?envs (typed_pre_context_fold ?E ?L (CtxFoldResolveAllInit) ?T) =>
      let envs := eval hnf in envs in
      match envs with
      | Envs _ ?spatial _ =>
          let tctx := gather_location_list spatial in
          notypeclasses refine (tac_fast_apply (typed_context_fold_resolve_init tctx _ E L T) _)
      | _ => fail 1000 "gather_tctx: cannot determine Iris context"
      end
  end.



(** Endlft trigger automation for [Inherit] context items *)
Ltac gather_on_endlft_worklist κ env :=
  match env with
  | Enil => uconstr:([])
  | Esnoc ?env' _ ?p =>
      let rs := gather_on_endlft_worklist κ env' in
      lazymatch p with
      | (Inherit κ ?key ?P)%I =>
          uconstr:(((existT _ key : sigT (@id Type)), P) :: rs)
      | _ => uconstr:(rs)
      end
  end.
Ltac liROnEndlftTriggerInit :=
  lazymatch goal with
  | |- envs_entails ?envs (typed_on_endlft_pre ?E ?L ?κ ?T) =>
      let envs := eval hnf in envs in
      match envs with
      | Envs _ ?spatial _ =>
          let worklist := gather_on_endlft_worklist κ spatial in
          notypeclasses refine (tac_fast_apply (typed_on_endlft_pre_init worklist E L κ T) _)
      | _ => fail 1000 "liROnEndlftTriggerInit: cannot determine Iris context"
      end
  end.

Ltac liRJudgement :=
  lazymatch goal with
    (* place finish *)
    | |- envs_entails _ (typed_place_finish ?π ?E ?L _ _ _ _ _ _ _ ?T) =>
      (* simplify eqcasts *)
        unfold typed_place_finish
        (*; simpl*)
    (* write *)
    | |- envs_entails _ (typed_write ?π ?E ?L _ _ _ ?ty ?r ?T) =>
        notypeclasses refine (tac_fast_apply (type_write E L T _ _ _ _ _ ty r π _) _); [ solve [refine _ ] |]
    (* read *)
    | |- envs_entails _ (typed_read ?E ?L _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_read E L T _ _ _ _) _); [ solve [refine _ ] |]
    (* borrow mut *)
    | |- envs_entails _ (typed_borrow_mut ?E ?L _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_borrow_mut E L T _ _ _ _ _) _); [solve [refine _] |]
    (* borrow shr *)
    | |- envs_entails _ (typed_borrow_shr ?E ?L _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_borrow_shr E L T _ _ _ _ _) _); [solve [refine _] |]
    (* addr_of mut *)
    | |- envs_entails _ (typed_addr_of_mut ?E ?L _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_addr_of_mut E L _ T _ _) _); [solve [refine _] |]
    (* end context folding *)
    | |- envs_entails _ (typed_context_fold_end ?AI ?E ?L ?acc ?T) =>
        notypeclasses refine (tac_fast_apply (type_context_fold_end AI E L acc T) _)
    (* initialize context folding *)
    | |- envs_entails _ (typed_pre_context_fold ?E ?L (CtxFoldStratifyAllInit) ?T) =>
        liRContextStratifyInit
    (* initialize context folding *)
    | |- envs_entails _ (typed_pre_context_fold ?E ?L (CtxFoldExtractAllInit ?κ) ?T) =>
        liRContextExtractInit
    (* initialize context folding *)
    | |- envs_entails _ (typed_pre_context_fold ?E ?L (CtxFoldResolveAllInit) ?T) =>
        liRContextResolveInit
    (* initialize OnEndlft triggers *)
    | |- envs_entails _ (typed_on_endlft_pre ?E ?L ?κ ?T) =>
        liROnEndlftTriggerInit
    (* trigger tc search *)
    | |- envs_entails _ (trigger_tc ?H ?T) =>
        notypeclasses refine (tac_fast_apply (tac_trigger_tc _ _ _ _) _); [solve [refine _] | ]
    (* find tc search *)
    | |- envs_entails _ (find_tc_inst ?H ?T) =>
        unshelve notypeclasses refine (tac_fast_apply (tac_find_tc_inst _ _ _) _); [solve [refine _] | ]
    (* stratification for structs *)
    | |- envs_entails _ (@stratify_ltype_struct_iter _ _ ?π ?E ?L ?mu ?mdu ?ma _ ?m ?l ?i ?sls ?rts ?lts ?rs ?k ?T) =>
        match rts with
        | [] =>
          notypeclasses refine (tac_fast_apply (stratify_ltype_struct_iter_nil π E L mu mdu ma m l sls k i T) _)
        | _ :: _ =>
          notypeclasses refine (tac_fast_apply (stratify_ltype_struct_iter_cons π E L mu mdu ma m l sls i _ _ _ k _) _)
        end
  end.

(* TODO Maybe this should rather be a part of Lithium? *)
Ltac unfold_introduce_direct :=
  lazymatch goal with
  | |- envs_entails ?E ?G =>
    let E' := eval unfold introduce_direct in E in
    change_no_check (envs_entails E' G)
  end.

(* Variant of [liStep] that calls [liSimpl] when necessary, but does not require the surrounding wrapper to call [liSimpl] itself. *)
Ltac liFastStep :=
  first
  [ liExtensible
  | liSep
  | liAnd
  | liWand
  | liExist
  | liImpl
  | liForall
  | liSideCond
  | liFindInContext
  | liCase
  | liTrace
  | liTactic; liSimpl
  | liPersistent
  | liBoringly
  | liTrue
  | liFalse
  | liAccu
  | liUnfoldLetGoal ].

(* This does everything *)
Ltac liRStepCore :=
  first [
    liRInstantiateEvars (* must be before do_side_cond and do_extensible_judgement *)
  | liRStmt
  | liRIntroduceTypedStmt
  | liRExpr
  | liRJudgement
  | liFastStep
  | lazymatch goal with | |- BACKTRACK_POINT ?P => change_no_check P end
 ].

Ltac liRStep :=
  liEnsureInvariant;
  try liRIntroduceLetInGoal;
  first [liRStepCore | simpl; liRStepCore ]
.

Tactic Notation "liRStepUntil" open_constr(id) :=
  repeat lazymatch goal with
         | |- @environments.envs_entails _ _ ?P =>
           lazymatch P with
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ => fail
           | id _ _ _ _ _ => fail
           | id _ _ _ _ => fail
           | id _ _ => fail
           | id _ => fail
           | id => fail
           | _  => liRStep
           end
         | _ => liRStep
  end; liShow.

(** * Tactics for starting a function *)
Ltac prepare_initial_coq_context :=
  (* The automation assumes that all products in the context are destructed, see liForall *)
  repeat match goal with
  | H : fn_A _ |- _ => simpl in H
  (*| H : struct_xt _ |- _ => unfold struct_xt in H; simpl in H*)
  | H : plist _ _ |- _ => destruct_product_hypothesis H H
  | H : (_ * _)%type |- _ => destruct_product_hypothesis H H
  (*| H : named_binder ?n |- _ =>*)
                      (*let temp := fresh "tmp" in*)
                      (*destruct H as [tmp];*)
                      (*rename_by_string tmp n*)
  | H : unit |- _ => destruct H
  | H : RT_xt _ |- _ => progress (simpl in H)
  end.

Section tac.
  Context `{!typeGS Σ}.

  Lemma intro_typed_function {rts : list RT} (n : nat) π (fn : function) (local_sts : list syn_type) (fp : (eq rts rts) * (prod_vec lft n → plist type rts → fn_spec)) :
    (∀ κs tys x (ϝ : lft),
      □ (
      let lya := fn.(f_args).*2 in
      let lyv := fn.(f_local_vars).*2 in
      ⌜fn_arg_layout_assumptions ((fp.2 κs tys).(fn_p) x).(fp_atys) lya⌝ -∗
      ⌜fn_local_layout_assumptions local_sts lyv⌝ -∗
      ∀ (lsa : vec loc (length ((fp.2 κs tys).(fn_p) x).(fp_atys))) (lsv : vec loc (length fn.(f_local_vars))),
        let Qinit :=
          (* sidecondition first *)
          ((fp.2 κs tys).(fn_p) x).(fp_Sc) π ∗
          ((fp.2 κs tys).(fn_p) x).(fp_Pa) π ∗
          ([∗list] l;t∈lsa;((fp.2 κs tys).(fn_p) x).(fp_atys), let '(existT rt (ty, r)) := t in l ◁ₗ[π, Owned false] #r @ (◁ ty)) ∗
          ([∗list] l;p∈lsv;local_sts, (l ◁ₗ[π, Owned false] .@ (◁ (uninit p))))
           in
      let E := (((fp.2 κs tys).(fn_p) x).(fp_elctx) ϝ) in
      let L := [ϝ ⊑ₗ{0} []] in
      ∃ E', ⌜E' ⊆+ E⌝ ∗ ⌜E' = E'⌝ ∗
      (credit_store 0 0 -∗ na_own π ⊤ -∗ introduce_with_hooks E' L (Qinit) (λ L2,
        introduce_typed_stmt E' L2 ϝ fn lsa lsv lya lyv (
        λ v L2,
            prove_with_subtype E L2 false ProveDirect (fn_ret_prop π ((fp.2 κs tys).(fn_p) x).(fp_fr) v) (λ L3 _ R3,
            introduce_with_hooks E L3 R3 (λ L4,
            (* we don't really kill it here, but just need to find it in the context *)
            li_tactic (llctx_find_llft_goal L4 ϝ LlctxFindLftFull) (λ _,
            find_in_context FindCreditStore (λ _,
              find_in_context (FindNaOwn) (λ '(π', mask), ⌜π' = π⌝ ∗ ⌜mask = ⊤⌝ ∗ True))
          )))
        ))))) -∗
    typed_function π fn local_sts fp.
  Proof.
    iIntros "#Ha".
    rewrite /typed_function.
    iIntros (????) "!# Hx1 Hx2".
    iIntros (lsa lsv) "(Hstore & Hna & Hinit)".
    rewrite /introduce_typed_stmt /typed_stmt.
    iIntros (?) "#CTX #HE HL Hcont".
    iApply fupd_wps.
    iPoseProof ("Ha" with "Hx1 Hx2") as "HT".
    iDestruct ("HT" $! lsa lsv) as "(%E' & %Hsub & _ & HT)".
    iPoseProof (elctx_interp_submseteq _ _ Hsub with "HE") as "HE'".
    rewrite /introduce_with_hooks.
    iMod ("HT" with "Hstore Hna [] HE' HL [Hinit]") as "(%L2 & HL & HT)"; first done.
    { iDestruct "Hinit" as "($ & $ & $)". }
    iApply ("HT" with "CTX HE' HL").
    iModIntro. done.
  Qed.
End tac.


Tactic Notation "prepare_parameters" "(" ident_list(i) ")" :=
  revert i; repeat liForall.

(* Put function assumptions into the persistent context *)
Global Instance intro_pers_fn `{!typeGS Σ} {rts : list RT} v π l sts lfts (fnspec : (rts = rts) * (prod_vec lft lfts → plist type rts → fn_spec)) :
  IntroPersistent (v ◁ᵥ{π} l @ function_ptr sts fnspec) (v ◁ᵥ{π} l @ function_ptr sts fnspec).
Proof.
  constructor. iIntros "#HA". done.
Qed.

(* IMPORTANT: We need to make sure to never call simpl while the code
(fn) is part of the goal, because simpl seems to take exponential time
in the number of blocks!

TODO: does this still hold? we've since started doing this...
*)
(* TODO: don't use i... tactics here *)
Tactic Notation "start_function" constr(fnname) ident(ϝ) "(" simple_intropattern(κs) ")" "(" simple_intropattern(tys) ")" "(" simple_intropattern(x) ")" "(" ident_list(params) ")" :=
  intros;
  init_jcache;
  inv_layout_alg;
  iStartProof;
  repeat (liEnsureInvariant || liWand || liSimpl || liForall || liPersistent || liImpl);
  li_unfold_lets_in_context;
  lazymatch goal with
  | |- envs_entails _ (typed_function _ _ _ _) =>
    iApply (intro_typed_function);
    (* simpl in order to simplify the projection in the type of type variables, e.g.
       T_ty : type (T_rt, T_st).1
       otherwise we can't substitute equalities on the T_st later. *)
    simpl;
    iIntros ( κs tys x ϝ ) "!#";
    let Harg_ly := fresh "Harg_ly" in
    let Hlocal_ly := fresh "Hlocal_ly" in
    iIntros (_ _);
    let lsa := fresh "lsa" in let lsv := fresh "lsv" in
    iIntros (lsa lsv);
    simpl in lsa;
    revert params;
    repeat liForall;
    prepare_initial_coq_context;
    iExists _; iSplitR;
    [iPureIntro; solve [preprocess_elctx] | ];
    match goal with
    | |- envs_entails _ (⌜?E1 = ?E2⌝ ∗ _) =>
        (*remember E1 as _E eqn:Helctx;*)
        (*eapply mk_elctx_eqn in Helctx;*)
        iSplitR; first done
    end;
    inv_vec lsv; inv_vec lsa;
    simpl;
    unfold typarams_wf, typaram_wf;
    init_cache
  end
.

(* TODO : more sideconditions *)
Ltac sidecond_hook_init :=
  unfold_no_enrich;
  open_cache;
  intros;
  prepare_initial_coq_context;
  repeat match goal with
  | |- _ ∧ _ => split
  | |- Forall ?P ?l =>
    notypeclasses refine (proj2 (Forall_Forall_cb _ _) _); simpl; (first
   [ exact I | split_and ! ])
  end
.
Ltac sidecond_hook_core :=
  lazymatch goal with
  | |- lctx_lft_alive ?E ?L ?κ =>
      solve_lft_alive
  | |- Forall (lctx_lft_alive ?E ?L) ?κs =>
      solve_lft_alive
  | |- lctx_lft_incl ?E ?L ?κ1 ?κ2 =>
      solve_lft_incl
  | |- lctx_lft_list_incl ?E ?L ?κ1 ?κ2 =>
      solve_lft_list_incl
  | |- lctx_place_update_kind_incl ?E ?L ?b1 ?b2 =>
      solve_place_update_kind_incl
  | |- lctx_bor_kind_alive ?E ?L ?b =>
      solve_bor_kind_alive
  | |- lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      solve_bor_kind_direct_incl
  | |- elctx_sat ?E ?L ?E' =>
      solve_elctx_sat
  | |- fn_arg_layout_assumptions ?L1 ?L2 =>
      repeat first [constructor | done]
  | |- lctx_place_update_kind_outlives ?E ?L ?b ?κs =>
      solve_place_update_kind_outlives
  | |- ty_has_op_type _ _ _ =>
      solve_ty_has_op_type
  | |- layout_wf _ =>
      solve_layout_wf
  | |- ly_align_in_bounds _ =>
      solve_ly_align_ib
  | |- syn_type_compat _ _ =>
      solve_syn_type_compat
  | |- ty_allows_reads _ =>
      solve_ty_allows
  | |- ty_allows_writes _ =>
      solve_ty_allows
  | |- Copyable _ =>
      apply _
  | |- trait_incl_marker _ =>
      solve_trait_incl
  | |- use_op_alg _ = _ =>
      solve_op_alg
  | |- _ ## _ =>
      solve_ndisj
  | |- _ ∪ _ = _ =>
      solve_ndisj
  | |- _ => idtac
  end;
  try solve_layout_alg
.
Ltac sidecond_hook ::=
  sidecond_hook_init;
  sidecond_hook_core
.

Ltac liSidecond_hook P ::=
lazymatch P with
  | shelve_hint _ => split; [ unfold shelve_hint; shelve_sidecond |]
  | trait_incl_marker _ => split; [shelve_sidecond |]
end.

(** ** Hints for automation *)
Global Hint Extern 0 (LayoutSizeEq _ _) => rewrite /LayoutSizeEq; solve_layout_size : typeclass_instances.
Global Hint Extern 0 (LayoutSizeLe _ _) => rewrite /LayoutSizeLe; solve_layout_size : typeclass_instances.

(* This should instead be solved by [solve_ty_has_op_type]. *)
Global Arguments ty_has_op_type : simpl never.

(* Simplifying this can lead to problems in some cases when used in specifications. *)
Global Arguments replicate : simpl nomatch.
(* We don't want this to simplify away the zero case, as that can be a valuable hint. *)
Global Arguments freeable_nz : simpl never.

(* should not be visible for automation *)
Global Typeclasses Opaque ty_shr.
Global Typeclasses Opaque ty_own_val.
Global Typeclasses Opaque ty_has_op_type.

(* Even though we seal it, we should still make this opaque so it doesn't simplify. *)
Global Opaque ty_has_op_type.

Global Typeclasses Opaque find_in_context.

Global Arguments ty_lfts : simpl nomatch.
Global Arguments ty_wf_E : simpl nomatch.

Global Arguments layout_of : simpl never.
(*Global Arguments ly_size : simpl never.*)

Global Arguments plist : simpl never.

Global Arguments lft_intersect_list : simpl never.

Global Typeclasses Opaque Rel2.
Global Arguments Rel2 : simpl never.

Global Hint Unfold OffsetLocSt : core.

Hint Unfold els_lookup_tag : lithium_rewrite.

Global Typeclasses Opaque loc.
Global Instance loc_inh : Inhabited loc.
Proof. unfold loc. apply _. Qed.

#[global] Typeclasses Opaque layout_wf.

(* In my experience, this has led to more problems with [normalize_autorewrite] rewriting below definitions too eagerly. *)
#[export] Unset Keyed Unification.

(** Lithium hook *)
Ltac normalize_hook ::=
  rewrite /size_of_st;
  simplify_layout_normalize;
  normalize_autorewrite.

Ltac after_intro_hook H ::=
  try match type of H with
  | enter_cache_hint ?P =>
      unfold enter_cache_hint in H;
      enter_cache H
  | ty_is_xrfn ?ty ?r =>
        first [
          is_var r;
          (let r2 := fresh r in
           rename r into r2;
           destruct H as (r, ->);
           simpl in r)
        | let Heq := fresh in
          let r2 := fresh "xr" in
          destruct H as (r2 & Heq);
          simpl in Heq;
          simpl in r2;
          simplify_eq ]
  end;
  try (inv_layout_alg_in H)
.

(* TODO: put a name_hint to preserve names? *)
Ltac before_revert_hook H ::=
  match type of H with
  | CACHED _ =>
      (* don't alter this *)
      fail 2
      (*unfold CACHED in H*)
  | _ => idtac
  end.

Ltac enter_cache_hook H cont ::=
  first [
    check_for_cached_layout H
  |
    lazymatch type of H with
    | ?ty =>
        lazymatch goal with
        | H2 : CACHED ty |- _ =>
            clear H
        end
    end
  | cont H].

(** Lithium hooks for [solve_goal]: called for remaining sideconditions *)
Lemma unfold_int_elem_of_it (z : Z) (it : int_type) :
  z ∈ it = (MinInt it ≤ z ∧ z ≤ MaxInt it)%Z.
Proof. done. Qed.

Ltac unfold_common_defs :=
  unfold_common_caesium_defs;
  unfold xmap, xmap_id in *;
  unfold num_cred in *;
  unfold unit_sl in *.

Ltac solve_goal_normalized_prepare_hook ::=
  try rewrite -> unfold_int_elem_of_it in *;
  autounfold in *;
  simplify_layout_goal;
  open_cache;
  unfold_no_enrich;
  simpl in *;
  idtac
.

Lemma ty_lfts_unfold_lem `{!typeGS Σ} {rt} (ty : type rt) :
  ty_lfts ty = _ty_lfts _ ty.
Proof. rewrite ty_lfts_unfold. done. Qed.
Lemma ty_wf_E_unfold_lem `{!typeGS Σ} {rt} (ty : type rt) :
  ty_wf_E ty = _ty_wf_E _ ty.
Proof. rewrite ty_wf_E_unfold. done. Qed.

(** Enum-related tactic calls *)
(* TODO better inclusion solvers *)
Ltac ty_lfts_incl_solver :=
  repeat match goal with
  | |- ?a ⊆ ?b =>
    match a with
    | context[ty_lfts ?ty] =>
        assert_fails (is_var ty);
        rewrite (ty_lfts_unfold_lem ty)
    end;
    (*match b with*)
    (*| context[ty_lfts ?ty] =>*)
        (*assert_fails (is_var ty);*)
        (*rewrite (ty_lfts_unfold_lem ty)*)
    (*end;*)
    simpl;
    try set_solver
  end.
Ltac solve_mk_enum_ty_lfts_incl :=
  simpl; intro_adt_params;
  intros []; ty_lfts_incl_solver.
Ltac ty_wf_E_incl_solver :=
  repeat match goal with
  | |- ?a ⊆ ?b =>
    match a with
    | context[ty_wf_E ?ty] =>
        assert_fails (is_var ty);
        rewrite (ty_wf_E_unfold_lem ty)
    end;
    (*match b with*)
    (*| context[ty_wf_E ?ty] =>*)
        (*assert_fails (is_var ty);*)
        (*rewrite (ty_wf_E_unfold_lem ty)*)
    (*end;*)
    simpl;
    try set_solver
  end.
Ltac solve_mk_enum_ty_wf_E :=
  simpl; intro_adt_params;
  intros []; ty_wf_E_incl_solver.
Ltac solve_mk_enum_tag_consistent :=
  simpl; intro_adt_params;
  (*intros []; naive_solver.*)
  intros [] ? [=<-]; eexists _; done.


Ltac enum_contractive_solve_dist :=
    repeat match goal with
    | |- ∀ (_ : type _), _ => intros ?
    end;
    let r := fresh "r" in
    intros r;
    intros;
    simpl;
    unfold spec_instantiated;
    unfold spec_instantiate_typaram_fst;
    unfold spec_instantiate_lft_fst;
    match goal with
    | |- TypeDist _ (?Hx ?ty1 ?lfts ?tys ?r) (?Hx ?ty2 ?lfts ?tys ?r) =>
        eapply (type_contractive_dist _ _ (λ ty, Hx ty lfts tys r)); last done;
        destruct r; simpl; apply _
    | |- TypeDist2 _ (?Hx ?ty1 ?lfts ?tys ?r) (?Hx ?ty2 ?lfts ?tys ?r) =>
        eapply (type_contractive_dist2 _ _ (λ ty, Hx ty lfts tys r)); last done;
        destruct r; simpl; apply _
    end.

(** User facing tactic calls *)
Ltac sidecond_hammer_it :=
  prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
Ltac sidecond_hammer :=
  (* the first run may spawn further sideconditions *)
  unshelve sidecond_hammer_it;
  (* hence run another iteration *)
  sidecond_hammer_it
.
Ltac sidecond_solver :=
  unshelve_sidecond; liSimpl; sidecond_hook.

(* Solve this sidecondition within Lithium *)
Ltac solve_function_subtype_hook ::=
  rewrite /function_subtype;
  iStartProof;
  unshelve (repeat liRStep; solve[fail]);
  unshelve (sidecond_solver);
  sidecond_hammer
.

Ltac normalized_rt_of_spec_ty_rec ty :=
  match ty with
  | ∀ x: _, ?B =>
      normalized_rt_of_spec_ty_rec B
  | spec_with _ _ (type ?ty) =>
      let hnf_ty := eval hnf in ty in
      constr:(ty)
  end.
  Ltac normalized_rt_of_spec_ty ty :=
  match type of ty with
  | ?B => normalized_rt_of_spec_ty_rec B
  end.

Ltac unfold_generic_inst :=
  unfold spec_instantiate_lft_fst;
  unfold spec_instantiate_typaram_fst;
  unfold spec_instantiated.

Ltac print_remaining_goal :=
  match goal with
  | H := FUNCTION_NAME ?s |- _ =>
    print_typesystem_goal s
  end.
Ltac print_remaining_sidecond :=
  try done; try apply: inhabitant;
  match goal with
  | H := FUNCTION_NAME ?s |- _ =>
    print_remaining_shelved_goal s
  end.

(* Prelude for trait incl files *)
Ltac solve_trait_incl_prelude :=
  solve_trait_incl_prepare;
  solve_trait_incl_core;
  first [
    rewrite /function_subtype;
    iStartProof
  | fast_done].
Ltac print_remaining_trait_goal :=
  match goal with
  | |- _ =>
  idtac "Type system got stuck while proving trait inclusion"; print_goal; admit
  end.
