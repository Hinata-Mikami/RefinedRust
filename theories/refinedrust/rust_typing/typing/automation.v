Require Import Stdlib.Strings.String.
From iris.proofmode Require Import rocq_tactics reduction string_ident.
From refinedrust Require Export type.
From lithium Require Export all.
From lithium Require Import hooks.
From refinedrust.automation Require Import lookup_definition.
From refinedrust.base Require Import int programs xmap value.
From refinedrust.primitive Require Import functions unit alias_ptr mutual_fixpoint.
From refinedrust Require Import primitive.existentials_na mut_ref.mut_ref shr_ref struct.struct array.array enum primitive.existentials.
From refinedrust.typing Require Import program_rules.
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
  | |- _ =>
      unfold reverse_coercion
  end.

Ltac liTrace_hook inf ::=
  match inf with
  | ProgramIsUnwinding =>
    generalize inf
  | _ =>
    add_case_distinction_info inf
  end.

Ltac liExist_hook A protect ::=
  lazymatch A with
  | prod_vec _ 0 => exists nil_tt
  end.

Ltac rep_check_backtrack_point_hook ::=
  lazymatch goal with
  | |- BACKTRACK_POINT ?P => idtac
  | |- envs_entails _ ?P =>
      lazymatch P with
       | typed_stmt _ _ _ _ _ _ _ _ => idtac
      | typed_val_expr _ _ _ _ _ => idtac
       | typed_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
      (* TODO maybe also typed_assert etc *)
      end
  end.

Global Arguments RT_xt : simpl nomatch.
Ltac hooks.liForall_hook ::=
  lazymatch goal with
  | |- forall e : ?A, @?P e =>
      match A with
      (* This doesn't work well with instances *)
      | plist _ [] =>
          intros []
      | prod_vec _ 0 =>
          intros []
          (*
      | RT_xt ?rt =>
  assert_fails (is_var rt);
lazymatch rt with
          | RT_of ?ty =>
              assert_fails (is_var ty)
              (* TODO: maybe unfold the RT_of? *)
          | _ => idtac
          end
           *)
      end
  end.


Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | subsume_full ?step ?P ?Q ?E ?L ?T =>
      cont uconstr:(((_ : SubsumeFull step P Q) E L T))
  | relate_list ?E ?L ?ig ?l1 ?l2 ?i0 ?R ?T =>
      cont uconstr:(((_ : RelateList E L ig l1 l2 i0 R) T))
  | relate_hlist ?E ?L ?ig ?Xs ?l1 ?l2 ?i0 ?R ?T =>
      cont uconstr:(((_ : RelateHList E L ig Xs l1 l2 i0 R) T))
  | fold_list ?E ?L ?ig ?l ?i0 ?P ?T =>
      cont uconstr:(((_ : FoldList E L ig l i0 P) T))
  | typed_value ?π ?v ?T =>
      cont uconstr:(((_ : TypedValue π v) T))
  | typed_bin_op ?E ?L ?f ?v1 ?ty1 ?v2 ?ty2 ?o ?ot1 ?ot2 ?T =>
      cont uconstr:(((_ : TypedBinOp E L f v1 ty1 v2 ty2 o ot1 ot2) T))
  | typed_un_op ?E ?L ?f ?v ?ty ?o ?ot ?T =>
      cont uconstr:(((_ : TypedUnOp E L f v ty o ot) T))
  | typed_check_bin_op ?E ?L ?f ?v1 ?ty1 ?v2 ?ty2 ?o ?ot1 ?ot2 ?T =>
      cont uconstr:(((_ : TypedCheckBinOp E L f v1 ty1 v2 ty2 o ot1 ot2) T))
  | typed_check_un_op ?E ?L ?f ?v ?ty ?o ?ot ?T =>
      cont uconstr:(((_ : TypedCheckUnOp E L f v ty o ot) T))
  | typed_call ?E ?L ?f ?eκs ?etys ?v ?P ?vl ?tys ?destination ?normal ?unwind ?T ?U =>
      cont uconstr:(((_ : TypedCall E L f eκs etys v P vl tys destination normal unwind) T U))
  | typed_place ?E ?L ?f ?l ?lt ?r ?bmin0 ?b ?P ?T =>
      cont uconstr:(((_ : TypedPlace E L f l lt r bmin0 b P) T))
  | typed_if ?E ?L ?π ?v ?P ?T1 ?T2 =>
      cont uconstr:(((_ : TypedIf E L π v P) T1 T2))
  | typed_annot_stmt ?π ?n ?a ?E ?L ?T =>
      cont uconstr:(((_ : TypedAnnotStmt π n a) E L T))
  | typed_switch ?E ?L ?f ?v ?ty ?r ?it ?m ?ss ?def ?fn ?R ?U ?ϝ =>
      cont uconstr:(((_ : TypedSwitch E L f v ty r it) m ss def fn R U ϝ))
  | typed_assert ?E ?L ?f ?v ?ty ?r ?s ?fn ?R ?U ?ϝ =>
      cont uconstr:(((_ : TypedAssert E L f v ty r) s fn R U ϝ))
  | typed_read_end ?π ?E ?L ?l ?ty ?r ?b2 ?bmin ?ot ?m ?T =>
      cont uconstr:(((_ : TypedReadEnd π E L l ty r b2 bmin ot m) T))
  | typed_write_end ?π ?E ?L ?ot ?v1 ?ty1 ?r1 ?b2 ?bmin ?l2 ?lt2 ?r2 ?T =>
      cont uconstr:(((_ : TypedWriteEnd π E L ot v1 ty1 r1 b2 bmin l2 lt2 r2) T))
  | typed_borrow_mut_end ?π ?E ?L ?κ ?l ?orty ?lt ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedBorrowMutEnd π E L κ l orty lt r b2 bmin) T))
  | typed_borrow_shr_end ?π ?E ?L ?κ ?l ?orty ?lt ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedBorrowShrEnd π E L κ l orty lt r b2 bmin) T))
  | typed_addr_of_mut_end ?pk ?π ?E ?L ?l ?lt ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedAddrOfMutEnd pk π E L l lt r b2 bmin) T))
  | cast_ltype_to_type ?E ?L ?lt ?T =>
      cont uconstr:(((_ : CastLtypeToType E L lt) T))
  | typed_pre_context_fold ?π ?E ?L ?m ?T =>
      cont uconstr:(((_ : TypedPreContextFold π E L m) T))
  | typed_context_fold ?AI ?E ?L ?m ?tctx ?acc ?T =>
      cont uconstr:(((_ : TypedContextFold AI E L m tctx acc) T))
  | typed_context_fold_step ?AI ?π ?E ?L ?m ?l ?lt ?r ?tctx ?acc ?T =>
      cont uconstr:(((_ : TypedContextFoldStep AI π E L m l lt r tctx acc) T))
  | typed_annot_expr ?E ?L ?n ?a ?v ?P ?T =>
      cont uconstr:(((_ : TypedAnnotExpr E L n a v P) T))
  | prove_with_subtype ?E ?L ?step ?pm ?P ?A ?T =>
      cont uconstr:(((_ : ProveWithSubtype E L step pm P A) T))
  | @owned_subtype _ _ ?π ?E ?L ?pers ?rt1 ?rt2 ?r1 ?r2 ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : @OwnedSubtype _ _ π E L pers rt1 rt2 r1 r2 ty1 ty2) T)
  | owned_subltype_step ?π ?E ?L ?step ?l ?r1 ?r2 ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : OwnedSubltypeStep π E L step l r1 r2 lt1 lt2) T)
  | @weak_subtype _ _ ?E ?L ?rt1 ?rt2 ?r1 ?r2 ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : @Subtype _ _ E L rt1 rt2 r1 r2 ty1 ty2) T)
  | weak_subltype ?E ?L ?k ?r1 ?r2 ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : SubLtype E L k r1 r2 lt1 lt2) T)
  | @strong_subtype _ _ ?E ?L ?rt1 ?rt2 ?r1 ?r2 ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : @StrongSubtype _ _ E L rt1 rt2 r1 r2 ty1 ty2) T)
  | strong_subltype ?E ?L ?k ?r1 ?r2 ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : StrongSubLtype E L k r1 r2 lt1 lt2) T)
  | mut_subtype ?E ?L ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : MutSubtype E L ty1 ty2) T)
  | mut_eqtype ?E ?L ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : MutEqtype E L ty1 ty2) T)
  | subtype_adt ?E ?L ?P1 ?P2 ?T =>
      cont uconstr:((_ : SubtypeADT E L P1 P2) T)
  | mut_eqltype ?E ?L ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : MutEqLtype E L lt1 lt2) T)
  | stratify_ltype ?π ?E ?L ?mdu ?ma ?ml ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L mdu ma ml l lt r b) T))
  | stratify_ltype_unblock ?π ?E ?L ?ma ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ StratifyUnblockOp l lt r b) T))
  | stratify_ltype_extract ?π ?E ?L ?Ma ?l ?lt ?r ?b ?κ ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ (StratifyExtractOp κ) l lt r b) T))
  | stratify_ltype_resolve ?π ?E ?L ?Ma ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ (StratifyResolveOp) l lt r b) T))
  | stratify_ltype_close_inv ?κs ?π ?E ?L ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ (StratifyCloseOp κs) l lt r b) T))
  | stratify_ltype_post_hook ?π ?E ?L ?ml ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtypePostHook π E L ml l lt r b) T))
  | resolve_ghost ?π ?E ?L ?m ?lb ?l ?lt ?b ?r ?T =>
      cont uconstr:(((_ : ResolveGhost π E L m lb l lt b r) T))
  | resolve_ghost_adt ?π ?E ?L ?m ?r ?ty ?T =>
      cont uconstr:(((_ : ResolveGhostADT π E L m r ty) T))
  | find_observation ?rt ?γ ?mode ?T =>
      cont uconstr:(((_ : FindObservation rt γ mode) T))
  | find_delayed_observation ?E ?L ?rt ?γ ?mode ?κ ?T =>
      cont uconstr:(((_ : FindDelayedObservation E L rt γ mode κ) T))
  | introduce_with_hooks ?E ?L ?P ?T =>
      cont uconstr:(((_ : IntroduceWithHooks E L P) T))
  | iterate_with_hooks ?E ?L ?m ?T =>
      cont uconstr:(((_ : IterateWithHooks E L m) T))
  | prove_place_cond ?E ?L ?b ?lt1 ?lt2 ?T =>
      cont uconstr:(((_ : ProvePlaceCond E L b lt1 lt2) T))
  | stratify_ltype_array_iter ?π ?E ?L ?mdu ?ma ?ml ?l ?ig ?def ?len ?iml ?rs ?bk ?T =>
      cont uconstr:(((_ : StratifyLtypeArrayIter π E L mdu ma ml l ig def len iml rs bk) T))
  | typed_array_access ?π ?E ?L ?base ?offset ?st ?lt ?r ?k ?T =>
      cont uconstr:(((_ : TypedArrayAccess π E L base offset st lt r k) T))
  | resolve_ghost_iter ?π ?E ?L ?rm ?lb ?l ?st ?lts ?b ?rs ?ig ?i0 ?T =>
      cont uconstr:(((_ : ResolveGhostIter π E L rm lb l st lts b rs ig i0) T))
  | typed_discriminant_end ?π ?E ?L ?l ?lt ?r ?b2 ?els ?T =>
      cont uconstr:(((_ : TypedDiscriminantEnd π E L l lt r b2 els) T))
  | interpret_typing_hint ?E ?L ?π ?orty ?bmin ?ty ?r ?T =>
      cont uconstr:(((_ : InterpretTypingHint E L π orty bmin ty r) T))
  | simplify_hyp_value ?E ?L ?π ?P ?T =>
      cont uconstr:(((_ : SimplifyHypValue E L π P) T))
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

Ltac interpret_rust_type_core lfts env ty ::=
  lazymatch ty with
  | RSTTyVar ?name =>
      let sty := eval vm_compute in (env !! name) in
      match sty with
      | Some (existT _ ?sty) =>
          exact sty
      | None =>
          fail 3 "Failed to find type variable " name " in the context"
      end
  | RSTLitType ?name ?inst =>
      (* CAVEAT: This only works if a unique identifier can be found! *)
      lookup_definition
        ltac:(fun term =>
          apply_rust_scope_inst lfts env inst term
          || fail 1000 "processing for " name " failed"
        )
        name || fail 1000 "definition lookup for " name " failed"
  | RSTInt ?it =>
      exact (int it)
  | RSTBool =>
      exact bool_t
  | RSTAliasPtr =>
      exact alias_ptr_t
  | RSTAliasRef =>
      exact alias_ref_t
  | RSTUnit =>
      exact unit_t
  | RSTArray ?len ?ty =>
      refine (array_t len _); interpret_rust_type_core lfts env ty
  | RSTRef ?mut ?κ ?ty =>
      match mut with
      | Mut =>
          refine (mut_ref _ _)
      | Shr =>
          refine (shr_ref _ _)
      end;
      [ interpret_rust_lft lfts env κ | interpret_rust_type_core lfts env ty ]
  end.

(** * Main automation tactics *)
Section automation.
  Context `{!typeGS Σ}.

  Lemma tac_trigger_tc {A} (a : A) (H : A → Type) (HP : H a) (T : A → iProp Σ) :
    T a ⊢ trigger_tc H T.
  Proof. iIntros "HT". iExists a, HP. iFrame. Qed.
  Lemma tac_find_tc_inst (H : Type) (HP : H) (T : H → iProp Σ) :
    T HP ⊢ find_tc_inst H T.
  Proof. iIntros "HT". iExists HP. iFrame. Qed.


  (** Machinery for context normalization *)
  Lemma tac_normalize_revert_hypothesis Δ i P E L R T :
    envs_lookup i Δ = Some (false, P) →
    envs_entails (envs_delete false i false Δ) (normalize_spatial_context E L (P ∗ R) T) →
    envs_entails Δ (normalize_spatial_context E L R T).
  Proof.
    rewrite envs_entails_unseal. intros ? HQ.
    rewrite (envs_lookup_sound' _ false) // bi.intuitionistically_if_elim.
    iIntros "(HP & Hctx)".
    iPoseProof (HQ with "Hctx") as "HT".
    rewrite /normalize_spatial_context/introduce_with_hooks.
    iIntros (??) "CTX HE HL HR".
    iApply ("HT" with "[//] CTX HE HL"). iFrame.
  Qed.
  Lemma tac_normalize_done Δ E L R T :
    envs_entails Δ (introduce_with_hooks E L R T) →
    envs_entails Δ (normalize_spatial_context E L R T).
  Proof. done. Qed.
End automation.

(** Determines whether an assumption in the spatial context should be reverted for normalization *)
Ltac should_normalize term :=
  match term with
  | if_iNone None _ =>
      idtac
  | if_iNone Some _ =>
      idtac
  | if_iSome (Some _) _ =>
      idtac
  | if_iSome None _ =>
      idtac
  | if_iOk (Ok _) _ =>
      idtac
  | if_iOk (Err _) _ =>
      idtac
  | if_iErr (Err _) _ =>
      idtac
  | if_iErr (Ok _) _ =>
      idtac
  | if_iTrue true _ =>
      idtac
  | if_iTrue false _ =>
      idtac
  | if_iFalse true _ =>
      idtac
  | if_iFalse false _ =>
      idtac
  | _ =>
      let term := eval simpl in term in
      match term with
      | (_ ∗ _)%I =>
          idtac
      | (∃ _, _)%I =>
          idtac
      | True%I =>
          idtac
      end
  end.

Ltac liRNormalizeSpatialContext :=
  lazymatch goal with
  | |- envs_entails _ (normalize_spatial_context ?E ?L ?R ?T) =>
    (* Recursive Ltac to revert all the hypotheses we should normalize *)
    let rec go Hs :=
    lazymatch Hs with
    | Esnoc ?Hs2 ?id ?Q => first [
      should_normalize Q;
      notypeclasses refine (tac_normalize_revert_hypothesis _ id Q _ _ _ _ _ _); [li_pm_reflexivity | li_pm_reduce ]
      | go Hs2 ]
    | Enil =>
        notypeclasses refine (tac_normalize_done _ _ _ _ _ _)
    end in
    lazymatch goal with
    | |- envs_entails (Envs ?Hi ?Hs _) _ => go Hs
    | H := (Envs ?Hi ?Hs _) |- envs_entails _ _ => go Hs
    end
  end.

Ltac liRIntroduceLetInGoal :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
    let H := fresh "GOAL" in
    lazymatch P with
    (*
    | @bi_wand ?PROP ?Q ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@bi_wand PROP Q H)))
    | @typed_val_expr ?Σ ?tG ?E ?L ?f ?e ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@typed_val_expr Σ tG E L f e H)))
      *)

    | @typed_write ?Σ ?tG ?E ?L ?f ?e ?ot ?v ?rt ?ty ?r ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@typed_write Σ tG E L f e ot v rt ty r H)))
    | @typed_read ?Σ ?tG ?E ?L ?f ?e ?ot ?rm ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@typed_read Σ tG E L f e ot rm H)))
    | @typed_borrow_mut ?Σ ?tG ?E ?L ?f ?e ?κ ?ort ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@typed_borrow_mut Σ tG E L f e κ ort H)))
    | @typed_borrow_shr ?Σ ?tG ?E ?L ?f ?e ?κ ?ort ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@typed_borrow_shr Σ tG E L f e κ ort H)))
    (* NOTE: these two guys really hurt Qed performance. Not a good idea at all! *)
    (*| @typed_place ?Σ ?tG ?π ?E ?L ?l ?rto ?lt ?r ?b ?bmin ?P ?T =>*)
      (*pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_place Σ tG π E L l rto lt r b bmin P H))*)
    (*| @typed_context_fold ?Σ ?tG ?Acc ?P ?M ?π ?E ?L ?m ?tcx ?acc ?T =>*)
      (*pose (H := LET_ID T);*)
      (*change_no_check (@envs_entails PROP Δ (@typed_context_fold Σ tG Acc P M π E L m tcx acc H))*)

    | @typed_pre_context_fold ?Σ ?tG ?π ?E ?L ?M ?m ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@typed_pre_context_fold Σ tG π E L M m H)))
      (*
    | @typed_bin_op ?Σ ?tG ?E ?L ?f ?v1 ?P1 ?v2 ?P2 ?op ?ot1 ?ot2 ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@typed_bin_op Σ tG E L f v1 P1 v2 P2 op ot1 ot2 H)))

    | @prove_with_subtype ?Σ ?tG ?E ?L ?b ?pm ?P ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@prove_with_subtype Σ tG E L b pm P H)))
      *)
    (* This one isn't beneficial for performance, because we often get lots of True * True * ... intros.
    | @introduce_with_hooks ?Σ ?tG ?E ?L ?P ?T =>
      li_let_bind T (fun H => constr:(@envs_entails PROP Δ (@introduce_with_hooks Σ tG E L P H))) *)
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

  | |- envs_entails _ (subsume_full _ (@ltype_own _ _ ?rt (◁ ?ty)%I _ _ _ _) (@ltype_own _ _ (xtype_rt (protected ?H)) (◁ xtype_ty (protected ?H))%I _ _ _ _) _ _ _) =>
      instantiate_protected H (@mk_xtype _ _ rt ty (protected (EVAR_ID _)) _)

  | |- envs_entails _ (subsume (@ltype_own _ _ (place_rfn ?rt1) _ _ _ _ _) (@ltype_own _ _ (place_rfn (protected ?rt2)) _ _ _ _ _) _) => liInst rt2 rt1
  | |- envs_entails _ (subsume (@ltype_own _ _ ?rt1 _ _ _ _ _) (@ltype_own _ _ (protected ?rt2) _ _ _ _ _) _) => liInst rt2 rt1

  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ (◁ ?ty)%I) (_ ◁ₗ[_, _] _ @ (◁ (protected ?H))%I) _) => liInst H ty
  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ ?lt) (_ ◁ₗ[_, _] _ @ (protected ?H)) _) => liInst H lt
  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ ?lt) (_ ◁ₗ[_, protected ?H] _ @ _) _) => liInst H b
  end].

(** Goto [goto_bb] *)
Ltac liRGoto goto_bb :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?E ?L ?f (Goto _) ?fn ?R ?U ?ϝ) =>
      first [
        (* try to find an inductive hypothesis we obtained previously *)
        notypeclasses refine (tac_fast_apply (type_goto_precond E _ L f _ _ fn R U ϝ) _);
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
            compute_loop_invariant f fn Inv Δ L ltac:(fun Inv IterVar =>
              (* finally initiate Löb *)
              match IterVar with
              | None =>
                notypeclasses refine (tac_fast_apply (typed_goto_acc E L f fn R U Inv goto_bb ϝ _ _) _);
                  [unfold_code_marker_and_compute_map_lookup|  ]
              | Some ?var =>
                notypeclasses refine (tac_fast_apply (typed_goto_acc' E L f fn R U goto_bb ϝ _ var Inv _) _);
                  [unfold_code_marker_and_compute_map_lookup|  ]
              end)
        end
      | (* do a direct jump *)
        notypeclasses refine (tac_fast_apply (type_goto E L f _ fn R U _ ϝ _) _);
          [unfold_code_marker_and_compute_map_lookup|]
      ]
  end.

Ltac liRStmt :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?E ?L ?f ?s ?fn ?R ?U ?ϝ) =>
    let s' := W.of_stmt s in
    lazymatch s' with
    | W.AssignSE _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_assign E L f _ _ _ _ fn R U _ ϝ) _)
    | W.Call _ _ _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_call E L f _ _ _ _ _ _ _ fn R U ϝ) _)
    | W.Return _ => notypeclasses refine (tac_fast_apply (type_return E L f _ fn R U ϝ) _)
    | W.Unwind => notypeclasses refine (tac_fast_apply (type_unwind E L f fn R U ϝ) _)
    | W.UnwindTerminate => notypeclasses refine (tac_fast_apply (type_unwind_terminate E L f fn R U ϝ) _)
    | W.Abort => notypeclasses refine (tac_fast_apply (type_abort E L f fn R U ϝ) _)
    | W.IfS _ _ _ _ => notypeclasses refine (tac_fast_apply (type_if E L f _ _ _ fn R U ϝ) _)
    | W.Switch _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_switch E L f _ _ _ _ _ fn R U ϝ) _)
    | W.Assert _ _ _ => notypeclasses refine (tac_fast_apply (type_assert E L f _ _ fn R U ϝ) _)
    | W.Goto ?bid => liRGoto bid
    | W.ExprS _ _ => notypeclasses refine (tac_fast_apply (type_exprs E L f _ _ fn R U ϝ) _)
    | W.LocalLive ?x ?st _ => notypeclasses refine (tac_fast_apply (type_local_live E L f st x _ fn R U ϝ) _)
    | W.LocalDead ?x _ => notypeclasses refine (tac_fast_apply (type_local_dead E L f x _ fn R U ϝ) _)
    | W.SkipS _ => notypeclasses refine (tac_fast_apply (type_skips' E L f _ fn R U ϝ) _)
    | W.StuckS => exfalso
    | W.AnnotStmt _ _ _ => notypeclasses refine (tac_fast_apply (type_annot_stmt E L f _ _ _ fn R U ϝ) _)
    | _ => fail "do_stmt: unknown stmt" s
    end
  end.

Ltac liRIntroduceTypedStmt :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ (introduce_typed_stmt ?E ?L ?f ?ϝ ?fn ?R ?U) =>
    iEval (rewrite /introduce_typed_stmt);
      lazymatch goal with
      | |- @envs_entails ?PROP ?Δ (@typed_stmt ?Σ ?tG ?E ?L ?f ?s ?fn ?R ?U ?ϝ) =>
        let Hfn := fresh "FN" in
        let HR := fresh "R" in
        let HU := fresh "U" in
        pose (Hfn := (CODE_MARKER fn));
        pose (HR := (RETURN_MARKER R));
        pose (HU := (UNWIND_MARKER U));
        change_no_check (@envs_entails PROP Δ (@typed_stmt Σ tG E L f s Hfn HR HU ϝ));
        iEval (simpl) (* To simplify f_init *)
      end
  end.

Ltac liRExpr :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr ?E ?L ?f ?e ?T) =>
    let e' := W.of_expr e in
    lazymatch e' with
    | W.Val _ => notypeclasses refine (tac_fast_apply (type_val E L f _ T) _)
    | W.Loc _ => notypeclasses refine (tac_fast_apply (type_val E L f _ T) _)
    | W.Copy _ _ _ => notypeclasses refine (tac_fast_apply (type_copy E L f _ _ _ T) _)
    | W.Move _ _ _ => notypeclasses refine (tac_fast_apply (type_move E L f _ _ _ T) _)
    | W.EnumDiscriminant _ _ => notypeclasses refine (tac_fast_apply (type_discriminant E L f _ _ _ T _) _); [apply _ | ]
    | W.Borrow Mut _ _ _ => notypeclasses refine (tac_fast_apply (type_mut_bor E L f T _ _ _) _)
    | W.Borrow Shr _ _ _ => notypeclasses refine (tac_fast_apply (type_shr_bor E L f T _ _ _) _)
    | W.Raw ?pk _ _ => notypeclasses refine (tac_fast_apply (type_mut_addr_of pk E L f _ T) _)
    | W.BinOp _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_bin_op E L f _ _ _ _ _ T) _)
    | W.UnOp _ _ _ => notypeclasses refine (tac_fast_apply (type_un_op E L f _ _ _ T) _)
    | W.CheckBinOp _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_check_bin_op E L f _ _ _ _ _ T) _)
    | W.CheckUnOp _ _ _ => notypeclasses refine (tac_fast_apply (type_check_un_op E L f _ _ _ T) _)
    | W.AnnotExpr _ ?a _ => notypeclasses refine (tac_fast_apply (type_annot_expr E L f _ a _ T) _)
    | W.StructInit ?sls ?init => notypeclasses refine (tac_fast_apply (type_struct_init E L f sls _ T) _)
    | W.EnumInit ?els ?variant ?rsty ?init => notypeclasses refine (tac_fast_apply (type_enum_init E L f els variant rsty _ T) _)
    | W.ArrayInit ?rty ?es => notypeclasses refine (tac_fast_apply (type_array_init E L f rty _ T) _)
    | W.Repeat ?st _ ?n => notypeclasses refine (tac_fast_apply (type_array_repeat E L f st n _ T) _)
    | W.IfE _ _ _ _ => notypeclasses refine (tac_fast_apply (type_ife E L f _ _ _ T) _)
    | W.LogicalAnd _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_and E L f _ _ _ _ T) _)
    | W.LogicalOr _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_or E L f _ _ _ _ T) _)
    | _ => fail "do_expr: unknown expr" e
    end
  end.

Ltac liRJudgement :=
  lazymatch goal with
    | |- envs_entails _ (normalize_spatial_context ?E ?L _ ?T) =>
        liRNormalizeSpatialContext
    (* place finish *)
    | |- envs_entails _ (typed_place_finish ?π ?E ?L _ _ _ _ _ _ _ ?T) =>
      (* simplify eqcasts *)
        unfold typed_place_finish
        (*; simpl*)
    (* write *)
    | |- envs_entails _ (typed_write ?E ?L ?f _ _ _ ?ty ?r ?T) =>
        notypeclasses refine (tac_fast_apply (type_write E L f T _ _ _ _ _ ty r _) _); [ solve [refine _ ] |]
    (* read *)
    | |- envs_entails _ (typed_read ?E ?L ?f _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_read E L f T _ _ _ _ _) _); [ solve [refine _ ] |]
    (* borrow mut *)
    | |- envs_entails _ (typed_borrow_mut ?E ?L ?f _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_borrow_mut E L f T _ _ _ _ _) _); [solve [refine _] |]
    (* borrow shr *)
    | |- envs_entails _ (typed_borrow_shr ?E ?L ?f _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_borrow_shr E L f T _ _ _ _ _) _); [solve [refine _] |]
    (* addr_of mut *)
    | |- envs_entails _ (typed_addr_of_mut ?pk ?E ?L ?f _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_addr_of_mut pk E L f _ T _ _) _); [solve [refine _] |]
    (* end context folding *)
    | |- envs_entails _ (typed_context_fold_end ?AI ?E ?L ?acc ?T) =>
        notypeclasses refine (tac_fast_apply (type_context_fold_end AI E L acc T) _)
    (* trigger tc search *)
    | |- envs_entails _ (trigger_tc ?H ?T) =>
        notypeclasses refine (tac_fast_apply (tac_trigger_tc _ _ _ _) _); [solve [refine _] | ]
    (* find tc search *)
    | |- envs_entails _ (find_tc_inst ?H ?T) =>
        unshelve notypeclasses refine (tac_fast_apply (tac_find_tc_inst _ _ _) _); [solve [refine _] | ]
    (* stratification for structs *)
    | |- envs_entails _ (@stratify_ltype_struct_iter _ _ ?π ?E ?L ?mdu ?ma _ ?m ?l ?i ?sls ?rts ?lts ?rs ?k ?T) =>
        match rts with
        | [] =>
          notypeclasses refine (tac_fast_apply (stratify_ltype_struct_iter_nil π E L mdu ma m l sls k i T) _)
        | _ :: _ =>
          notypeclasses refine (tac_fast_apply (stratify_ltype_struct_iter_cons π E L mdu ma m l sls i _ _ _ k _) _)
        end
  end.

(** [liRBinder] explicitly handles binder transformations to preserve names. *)
Section tac.
  Context `{!typeGS Σ}.

  Lemma tac_introduce_with_hooks_exists name Δ {X} E L (Φ : X → iProp Σ) T :
    envs_entails Δ (∀ x : name_hint_ty name X, introduce_with_hooks E L (Φ x) T) →
    envs_entails Δ (introduce_with_hooks E L (∃ x, Φ x) T).
  Proof.
    apply tac_fast_apply.
    apply introduce_with_hooks_exists.
  Qed.

  Lemma tac_introduce_with_hooks_boringly_exists name Δ E L {X} (P : X → iProp Σ) T :
    envs_entails Δ (∀ x : name_hint_ty name X, introduce_with_hooks E L (☒ P x) T) →
    envs_entails Δ (introduce_with_hooks E L (☒ (∃ x : X, P x)) T).
  Proof.
    apply tac_fast_apply.
    apply introduce_with_hooks_boringly_exist.
  Qed.
  Lemma tac_prove_with_subtype_exists name Δ {X} E L step pm (Φ : X → iProp Σ) A T :
    envs_entails Δ (∃ x : name_hint_ty name X, prove_with_subtype E L step pm (Φ x) A T) →
    envs_entails Δ (prove_with_subtype E L step pm (∃ x, Φ x) A T).
  Proof.
    apply tac_fast_apply.
    apply prove_with_subtype_exists.
  Qed.
End tac.
Ltac liRBinder :=
  lazymatch goal with
  | |- envs_entails _ (introduce_with_hooks _ _ ?P _) =>
    let P := eval simpl in P in
    match P with
    | @bi_exist _ ?T ?Φ =>
      match T with
      | name_hint_ty _ _ =>
        notypeclasses refine (tac_fast_apply (introduce_with_hooks_exists _ _ _ _) _)
      | _ =>
        match Φ with
        | (fun x => _) =>
          let ident := constr:(ident_to_string! x) in
          notypeclasses refine (tac_introduce_with_hooks_exists ident _ _ _ _ _ _)
        end
      end
    | boringly (@bi_exist _ ?T ?Φ) =>
      match T with
      | name_hint_ty _ _ =>
        notypeclasses refine (tac_fast_apply (introduce_with_hooks_boringly_exist _ _ _ _) _)
      | _ =>
        match Φ with
          | (fun x => _) =>
            let ident := constr:(ident_to_string! x) in
            notypeclasses refine (tac_introduce_with_hooks_boringly_exists ident _ _ _ _ _ _)
        end
      end
    end
  | |- envs_entails _ (prove_with_subtype _ _ _ _ ?P _ _) =>
      let P := eval simpl in P in
      match P with
      | @bi_exist _ ?T ?Φ =>
        match T with
        | name_hint_ty _ _ =>
          notypeclasses refine (tac_fast_apply (prove_with_subtype_exists _ _ _ _ _ _ _) _)
        | _ =>
          match Φ with
          | (fun x => _) =>
            let ident := constr:(ident_to_string! x) in
            notypeclasses refine (tac_prove_with_subtype_exists ident _ _ _ _ _ _ _ _ _)
          end
        end
      end
  end.

(** ** Filters for context folding *)
(** *** Extract *)
Ltac gather_location_list_extract_filter_rec κ ltype :=
  idtac.
Ltac gather_location_list_extract_filter_hlist κ ltys :=
  match ltys with
  | +[] => fail
  | ?lty +:: ?ltys =>
    first [
      gather_location_list_extract_filter_rec κ lty
    | gather_location_list_extract_filter_hlist κ ltys ]
  end.
Ltac gather_location_list_extract_filter_array_list κ ltys :=
  match ltys with
  | [] => fail
  | (_, ?lty) :: ?ltys =>
    first [
      gather_location_list_extract_filter_rec κ lty
    | gather_location_list_extract_filter_array_list κ ltys ]
  end.

Ltac gather_location_list_extract_filter_ty_rec κ ty :=
  idtac.
Ltac gather_location_list_extract_filter_ty_list κ tys :=
  match tys with
  | [] => fail
  | ?ty :: ?tys =>
    first [
      gather_location_list_extract_filter_ty_rec κ ty
    | gather_location_list_extract_filter_ty_list κ tys ]
  end.
Ltac gather_location_list_extract_filter_ty_rec κ ty ::=
  match ty with
  | mut_ref ?κ1 ?ty  =>
    first [ unify κ1 κ | gather_location_list_extract_filter_ty_rec κ ty]
  | shr_ref ?κ1 ?ty =>
    first [ unify κ1 κ | gather_location_list_extract_filter_ty_rec κ ty]
  | struct_t _ ?tys =>
    gather_location_list_extract_filter_ty_list κ tys
  (* TODO: structurally descend *)
  | _ => fail
  end.

Ltac gather_location_list_extract_filter_rec κ ltype ::=
  (* check if *)
  match ltype with
  | MutLtype ?lt ?κ1 =>
    first [ unify κ1 κ | gather_location_list_extract_filter_rec κ lt]
  | ShrLtype ?lt ?κ1 =>
    first [unify κ κ1 | gather_location_list_extract_filter_rec κ lt]
  | StructLtype ?ltys _ =>
    gather_location_list_extract_filter_hlist κ ltys
  | EnumLtype _ None =>
    (* overapproximate; it's unclear what the current variant is *)
    idtac
  | EnumLtype _ (Some (mk_enum_ltype_variant _ _ ?lte _)) =>
    gather_location_list_extract_filter_rec κ lte
  | ArrayLtype _ _ ?tys _ =>
    gather_location_list_extract_filter_array_list κ tys
  | OpenedLtype ?cur _ _ _ _ =>
    gather_location_list_extract_filter_rec κ cur
  | CoreableLtype _ _ =>
    fail
  | ShadowedLtype _ _ _ =>
    fail
  | OpenedNaLtype ?cur _ _ _ =>
    gather_location_list_extract_filter_rec κ cur
  | BlockedLtype _ ?κ1 =>
    unify κ κ1
  | ShrBlockedLtype _ ?κ1 =>
    unify κ κ1
  | OfTy ?ty =>
    gather_location_list_extract_filter_ty_rec κ ty
  end.

Ltac gather_location_list_extract_filter κ rt ltype r :=
  gather_location_list_extract_filter_rec κ ltype.


(** *** Close Inv *)
Ltac gather_location_list_closeinv_filter_rec κ ltype :=
  idtac.
Ltac gather_location_list_closeinv_filter_hlist κ ltys :=
  match ltys with
  | +[] => fail
  | ?lty +:: ?ltys =>
    first [
      gather_location_list_closeinv_filter_rec κ lty
    | gather_location_list_closeinv_filter_hlist κ ltys ]
  end.
Ltac gather_location_list_closeinv_filter_array_list κ ltys :=
  match ltys with
  | [] => fail
  | (_, ?lty) :: ?ltys =>
    first [
      gather_location_list_closeinv_filter_rec κ lty
    | gather_location_list_closeinv_filter_array_list κ ltys ]
  end.

Ltac gather_location_list_closeinv_filter_rec κs ltype ::=
  (* check if *)
  match ltype with
  | MutLtype (OpenedLtype ?lt _ _ _ _) ?κ1 =>
    first [ check_list_elem_of_lctx κ1 κs ltac:(fun _ => idtac) | gather_location_list_closeinv_filter_rec κs lt]
  | ShrLtype ?lt ?κ1 =>
    gather_location_list_closeinv_filter_rec κs lt
  | StructLtype ?ltys _ =>
    gather_location_list_closeinv_filter_hlist κs ltys
  | EnumLtype _ None =>
    (* overapproximate; it's unclear what the current variant is *)
    idtac
  | EnumLtype _ (Some (mk_enum_ltype_variant _ _ ?lte _)) =>
    gather_location_list_closeinv_filter_rec κs lte
  | ArrayLtype _ _ ?tys _ =>
    gather_location_list_closeinv_filter_array_list κs tys
  | OpenedLtype ?cur _ _ _ _ =>
    gather_location_list_closeinv_filter_rec κs cur
  | CoreableLtype _ _ =>
    fail
  | ShadowedLtype _ _ _ =>
    fail
  | OpenedNaLtype ?cur _ _ _ =>
    gather_location_list_closeinv_filter_rec κs cur
  (*| BlockedLtype _ ?κ1 =>*)
    (*unify κ κ1*)
  (*| ShrBlockedLtype _ ?κ1 =>*)
    (*unify κ κ1*)
  | OfTy ?ty =>
    fail
  end.

Ltac gather_location_list_closeinv_filter κs rt ltype r :=
  gather_location_list_closeinv_filter_rec κs ltype.

(** *** Resolve *)
Ltac gather_location_list_resolve_filter_rec ltype r :=
  idtac.
Ltac gather_location_list_resolve_filter_hlist ltys rs :=
  match ltys with
  | +[] => fail
  | ?lty +:: ?ltys =>
    match rs with
    | ?r :: ?rs =>
      first [
        gather_location_list_resolve_filter_rec lty r
      | gather_location_list_resolve_filter_hlist ltys rs ]
    end
  end.

Ltac gather_location_list_resolve_filter_ty_rec ty r :=
  idtac.
Ltac gather_location_list_resolve_filter_ty_list tys rs :=
  match tys with
  | [] => fail
  | ?ty :: ?tys =>
    lazymatch rs with
    | ?r :: ?rs =>
      lazymatch r with
      | #?r =>
        first [
          gather_location_list_resolve_filter_ty_rec ty r
        | gather_location_list_resolve_filter_ty_list tys rs ]
      | 👻 _ => idtac
      end
    end
  end.
Ltac gather_location_list_resolve_filter_ty_rec ty r ::=
  match ty with
  | mut_ref ?κ1 ?ty  =>
    match r with
    | (👻 _, _) =>
      idtac
    | (#?r, _) =>
      gather_location_list_resolve_filter_ty_rec ty r
    end
  | shr_ref ?κ1 ?ty =>
    match r with
    | (👻 _, _) =>
      idtac
    | (#?r, _) =>
      gather_location_list_resolve_filter_ty_rec ty r
    end
  | struct_t _ ?tys =>
    gather_location_list_resolve_filter_ty_list tys r
  | ex_plain_t _ _ _ _ =>
    (* we want to trigger the ADT resolution instances *)
    idtac
  (* TODO: structurally descend *)
  | _ =>
    match r with
    | 👻 _ => idtac
    end
  end.

Ltac gather_location_list_resolve_filter_rec ltype r ::=
  match ltype with
  | MutLtype ?lt ?κ1 =>
    match r with
    | #(?r, _) =>
      gather_location_list_resolve_filter_rec lt r
    | 👻 _ =>
      idtac
    end
  | ShrLtype ?lt ?κ1 =>
    match r with
    | #?r =>
      gather_location_list_resolve_filter_rec lt r
    | 👻 _ =>
      idtac
    end
  | StructLtype ?ltys _ =>
    match r with
    | #?r =>
      gather_location_list_resolve_filter_hlist ltys r
    | 👻 _ =>
      idtac
    end
  | EnumLtype _ None =>
    (* overapproximate; it's unclear what the current variant is *)
    idtac
  | EnumLtype _ (Some (mk_enum_ltype_variant _ _ ?lte ?re)) =>
    gather_location_list_resolve_filter_rec lte constr:(#re)
  | ArrayLtype _ _ ?tys _ =>
    (* hard to check precisely, therefore underapproximate *)
    idtac
  | OpenedLtype ?cur _ _ _ _ =>
    gather_location_list_resolve_filter_rec cur r
  | CoreableLtype _ _ =>
    fail
  | ShadowedLtype _ _ _ =>
    fail
  | OpenedNaLtype ?cur _ _ _ =>
    gather_location_list_resolve_filter_rec cur r
  | BlockedLtype _ _ =>
    lazymatch r with
    | 👻 _ => idtac
    end
  | ShrBlockedLtype _ ?κ1 =>
    lazymatch r with
    | 👻 _ => idtac
    end
  | OfTy ?ty =>
    lazymatch r with
    | 👻 _ => idtac
    | # ?r =>
      gather_location_list_resolve_filter_ty_rec ty r
    end
  end.

Ltac gather_location_list_resolve_filter rt ltype r :=
  gather_location_list_resolve_filter_rec ltype r.

(** Stratify *)
Ltac gather_location_list_stratify_filter_rec ltype :=
  match ltype with
  | OfTy ?ty =>
    (* a top-level OfTy doesn't have to be stratified *)
    fail
  | _ => idtac
  end.

Ltac gather_location_list_stratify_filter rt ltype r :=
  gather_location_list_stratify_filter_rec ltype.

Ltac gather_location_list_get_filter m ::=
  lazymatch m with
  | CtxFoldExtractAllInit ?κ =>
    ltac:(gather_location_list_extract_filter κ)
  | CtxFoldCloseInvAllInit ?κs =>
    ltac:(gather_location_list_closeinv_filter κs)
  | CtxFoldStratifyAllInit ?ma =>
    ltac:(gather_location_list_stratify_filter)
  | CtxFoldResolveAllInit =>
    ltac:(gather_location_list_resolve_filter)
  | _ =>
    ltac:(gather_location_list_default_filter)
  end
.

(** ** Main stepping tactics *)

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
  | liClear
  | liUnfoldLetGoal ].

(* This does everything *)
Ltac liRStepCore :=
  first [
    liRInstantiateEvars (* must be before do_side_cond and do_extensible_judgement *)
  | liRStmt
  | liRIntroduceTypedStmt
  | liRExpr
  | liRBinder
  | lazymatch goal with
    | |- envs_entails _ (fn_body_end_prop _ _ _ _ _) => unfold fn_body_end_prop
    end
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
  (*| H : struct_xt _ |- _ => unfold struct_xt in H; simpl in H*)
  | H : plist _ _ |- _ => destruct_product_hypothesis H H
  | H : (_ * _)%type |- _ => destruct_product_hypothesis H H
  (*| H : named_binder ?n |- _ =>*)
                      (*let temp := fresh "tmp" in*)
                      (*destruct H as [tmp];*)
                      (*rename_by_string tmp n*)
  | H : unit |- _ => destruct H
  | H : fn_A _ |- _ => progress (simpl in H)
  | H : RT_xt _ |- _ => progress (simpl in H)
  end.

Section tac.
  Context `{!typeGS Σ}.

  Definition function_body {rts : list RT} (n : nat) π (fn : function) (fp : (eq rts rts) * (prod_vec lft n → plist type rts → fn_spec)) (fps : fn_params) (κs : prod_vec lft n) (tys : plist type rts) (lsa : vec loc (length fps.(fp_atys))) (sta : list syn_type) (x : _) (f : frame_id) (ϝ : lft) (E : elctx) (L : llctx) : iProp Σ :=
    let Qinit :=
        (* sidecondition first *)
        (fps.(fp_Sc) π ∗
        fps.(fp_Pa) π ∗
        ([∗ list] l;'(existT rt (ty, r)) ∈ lsa;fp_atys fps, l ◁ₗ[ π, Owned] # r @ (◁ ty)) ∗
        ([∗ list] xl;synty ∈ zip (f_args fn).*1 lsa;sta, xl.1 is_live{ (π, f), synty} xl.2))%I in
        (credit_store 0 0 -∗ na_own π ⊤ -∗ allocated_locals (π, f) (f_args fn).*1 -∗ introduce_with_hooks E L (Qinit) (λ L2,
        introduce_typed_stmt E L2 (π, f) ϝ fn
          (λ v L3, fn_body_end_prop E L3 ϝ π
            (fn_ret_prop π ((fp.2 κs tys).(fn_p) x).(fp_fr) v))
          (λ L3, fn_body_end_prop E L3 ϝ π
            (⌜effective_unwind_condition ((fp.2 κs tys).(fn_p) x).(fp_unwind)⌝)%I))).

  Lemma intro_typed_function {rts : list RT} (n : nat) π (fn : function) (fp : (eq rts rts) * (prod_vec lft n → plist type rts → fn_spec)) :
    (∀ κs tys x (ϝ : lft) (f : frame_id),
      □ (
      let lya := fn.(f_args).*2 in
      let fps := fn_p (fp.2 κs tys) x in
      let sta := fn_arg_syntys (fp_atys fps) in
      ⌜Forall2 syn_type_has_layout sta lya⌝ -∗
      ∀ (lsa : vec loc (length fps.(fp_atys))),
      let E := (fps.(fp_elctx) ϝ) in
      let L := [ϝ ⊑ₗ{0} []] in
      ∃ E', ⌜E' ⊆+ E⌝ ∗
      function_body n π fn fp fps κs tys lsa sta x f ϝ E' L
      )) -∗
    typed_function π fn fp.
  Proof.
    iIntros "#Ha".
    rewrite /typed_function/function_body.
    iIntros (?????) "!# Hx1".
    iIntros (lsa) "(Hstore & Hna & Halloc & Hinit)".
    rewrite /introduce_typed_stmt /typed_stmt.
    iIntros (Φ Φunwind) "#CTX #HE HL Hf Hcont".
    iApply fupd_wps.
    iPoseProof ("Ha" with "Hx1") as "HT".
    iDestruct ("HT" $! lsa) as "(%E' & %Hsub & HT)".
    iPoseProof (elctx_interp_submseteq _ _ Hsub with "HE") as "HE'".
    rewrite /introduce_with_hooks.
    iMod ("HT" with "Hstore Hna Halloc [] CTX HE' HL [Hinit]") as "(%L2 & HL & HT)"; first done.
    { iDestruct "Hinit" as "($ & $ & $)". }
    iApply ("HT" with "CTX HE' HL Hf").
    iModIntro. iSplit.
    - unfold typed_stmt_post_cond.
      iIntros (???) "HL Hf Halloc Hb".
      iDestruct "Hcont" as "[Hcont _]".
      iSpecialize ("Hcont" with "HL Hf Halloc Hb").
      unfold fn_body_end_prop, prove_with_subtype.
      iIntros "Hcont2".
      iApply "Hcont".
      iIntros (?????) "_ _ HL HA".
      iMod ("Hcont2" with "[] [] [] [//] [//] HL HA") as "Hx"; [done.. | ].
      iDestruct "Hx" as "(% & % & % & ? & ? & HT)". iFrame.
      iExists []. iModIntro. unfold introduce_with_hooks.
      iIntros (F0 Hmask) "CTX0 HE0 HL0 HR".
      iPoseProof (elctx_interp_submseteq _ _ Hsub with "HE0") as "HE0'".
      iApply ("HT" with "[] CTX0 HE0' HL0 HR"); done.
    - unfold typed_stmt_unwind_post_cond.
      iIntros (??) "HL Hf Halloc Hb".
      iDestruct "Hcont" as "[_ Hcont]".
      iSpecialize ("Hcont" with "HL Hf Halloc Hb").
      unfold fn_body_end_prop, prove_with_subtype.
      iIntros "Hcont2".
      iApply "Hcont".
      iIntros (?????) "_ _ HL HA".
      iMod ("Hcont2" with "[] [] [] [//] [//] HL HA") as "Hx"; [done.. | ].
      iDestruct "Hx" as "(% & % & % & ? & ? & HT)". iFrame.
      iExists []. iModIntro. unfold introduce_with_hooks.
      iIntros (F0 Hmask) "CTX0 HE0 HL0 HR".
      iPoseProof (elctx_interp_submseteq _ _ Hsub with "HE0") as "HE0'".
      iApply ("HT" with "[] CTX0 HE0' HL0 HR"); done.
  Qed.
End tac.


Tactic Notation "prepare_parameters" "(" ident_list(i) ")" :=
  revert i; repeat liForall.

(* Put function assumptions into the persistent context *)
Global Instance intro_pers_fn `{!typeGS Σ} {rts : list RT} v π l sts lfts (fnspec : (rts = rts) * (prod_vec lft lfts → plist type rts → fn_spec)) m :
  IntroPersistent (v ◁ᵥ{π, m} l @ function_ptr sts fnspec) (v ◁ᵥ{π, m} l @ function_ptr sts fnspec).
Proof.
  constructor. iIntros "#HA". done.
Qed.
Global Instance intro_pers_inline_fn `{!typeGS Σ} v π l sts fn m :
  IntroPersistent (v ◁ᵥ{π, m} l @ inline_function_ptr sts fn) (v ◁ᵥ{π, m} l @ inline_function_ptr sts fn).
Proof.
  constructor. iIntros "#HA". done.
Qed.

(* IMPORTANT: We need to make sure to never call simpl while the code
(fn) is part of the goal, because simpl seems to take exponential time
in the number of blocks!

TODO: does this still hold? we've since started doing this...
*)
(* TODO: don't use i... tactics here *)
Ltac start_function_prepare :=
  intros;
  init_jcache;
  inv_layout_alg;
  iStartProof;
  set_function_types;
  repeat (liEnsureInvariant || liWand || liSimpl || liForall || liPersistent || liImpl || liUnfoldLetGoal);
  li_unfold_lets_in_context
.

(* An extensible hook for augmenting the context *)
Ltac2 mutable start_function_hook () :=
  ().
Ltac start_function_finish lsa :=
  repeat liForall;
  iExists _; iSplitR;
  [iPureIntro; solve [preprocess_elctx] | ];
  (* let-bind E *)
  match goal with
  | |- envs_entails ?Δ (function_body ?n ?π ?fn ?fp ?fps ?κs ?tys ?lsa ?sta ?x ?f ?ϝ ?E ?L) =>
      let H := fresh "E" in
      pose (H := ELCTX E);
      simpl in H;
      change_no_check (envs_entails Δ (function_body n π fn fp fps κs tys lsa sta x f ϝ H L))
  end;
  inv_vec lsa;
  unfold function_body;
  simpl;
  unfold typaram_wf;
  init_cache;
  ltac2:(start_function_hook ())
.
Tactic Notation "start_function" constr(fnname) ident(ϝ) "(" simple_intropattern(κs) ")" "(" simple_intropattern(tys) ")" "(" simple_intropattern(x) ")" "(" ident_list(params) ")" :=
  start_function_prepare;
  lazymatch goal with
  | |- envs_entails _ (typed_function _ _ _) =>
    iApply (intro_typed_function);
    (* simpl in order to simplify the projection in the type of type variables, e.g.
       T_ty : type (T_rt, T_st).1
       otherwise we can't substitute equalities on the T_st later. *)
    simpl;
    iIntros ( κs tys x ϝ _fid) "!#";

    iIntros (_);
    let lsa := fresh "lsa" in
    iIntros (lsa);
    (* before [revert params], as the unsimplified type of [params] mentions [lsa] *)
    simpl in lsa;

    revert params;
    prepare_initial_coq_context;

    start_function_finish lsa
  end
.
Tactic Notation "start_function" constr(fnname) ident(ϝ) "(" simple_intropattern(κs) ")" "(" simple_intropattern(tys) ")" "(" simple_intropattern(x) ")" :=
  start_function_prepare;
  lazymatch goal with
  | |- envs_entails _ (typed_function _ _ _) =>
    iApply (intro_typed_function);
    (* simpl in order to simplify the projection in the type of type variables, e.g.
       T_ty : type (T_rt, T_st).1
       otherwise we can't substitute equalities on the T_st later. *)
    simpl;
    iIntros ( κs tys x ϝ _fid) "!#";

    (* important: to destruct [x] *)
    prepare_initial_coq_context;

    iIntros (_);
    let lsa := fresh "lsa" in
    iIntros (lsa);
    (* before [revert params], as the unsimplified type of [params] mentions [lsa] *)
    simpl in lsa;

    start_function_finish lsa
  end
.

(** ** Hints for automation *)
Global Hint Extern 0 (LayoutSizeEq _ _) => rewrite /LayoutSizeEq; solve_layout_size : typeclass_instances.
Global Hint Extern 0 (LayoutSizeLe _ _) => rewrite /LayoutSizeLe; solve_layout_size : typeclass_instances.

Global Hint Unfold size_of_array_in_bytes : solve_goal_unfold.

(* This should instead be solved by [solve_ty_has_op_type]. *)
Global Arguments ty_has_op_type : simpl never.
Global Typeclasses Opaque ty_has_op_type.
(* Even though we seal it, we should still make this opaque so it doesn't simplify. *)
Global Opaque ty_has_op_type.

Global Arguments is_value_ot : simpl never.
Global Arguments is_array_ot : simpl never.
Global Arguments is_struct_ot : simpl never.


(* Simplifying this can lead to problems in some cases when used in specifications. *)
Global Arguments replicate : simpl nomatch.
(* We don't want this to simplify away the zero case, as that can be a valuable hint. *)
Global Arguments freeable_nz : simpl never.

(* should not be visible for automation *)
Global Typeclasses Opaque ty_shr.
Global Typeclasses Opaque ty_own_val.

Global Typeclasses Opaque find_in_context.

Global Arguments layout_of : simpl never.

Global Arguments plist : simpl never.

Global Arguments lft_intersect_list : simpl never.

Hint Unfold els_lookup_tag : lithium_rewrite.

#[global] Typeclasses Opaque layout_wf.

Global Instance simpl_exist_tysized `{!typeGS Σ} {rt} (ty : type rt) `{!TySized ty} :
  SimplExist (TySized ty) (λ Q, Q _).
Proof.
  intros ??. eauto.
Qed.

(** Unfold [ty_ghost_drop] if necessary *)
Class TyIsNotVar `{!typeGS Σ} {rt} (ty : type rt) := {}.
Global Hint Mode TyIsNotVar + + + + : typeclass_instances.
Global Hint Extern 10 (TyIsNotVar ?ty) =>
  ty_is_not_var ty; constructor : typeclass_instances.

Global Program Instance simplify_hyp_ty_ghost_drop `{!typeGS Σ} {rt} (ty : type rt) `{!TyIsNotVar ty} π r :
  SimplifyHyp (ty_ghost_drop ty π r) (Some 0%N) := {|
  simplify_hyp_Q := _ty_ghost_drop ty π r;
|}.
Next Obligation.
  iIntros (???????) "?".
  rewrite ty_ghost_drop_unfold. done.
Qed.
Global Program Instance simplify_hyp_ty_ghost_drop'_1 `{!typeGS Σ} {rt} (ty : type rt) π r `{!TCFastDone (ty.(ty_trivial_drop) = false)} :
  SimplifyHyp (ty_ghost_drop' ty π r) (Some 0%N) := {|
  simplify_hyp_Q := True%I;
|}.
Next Obligation.
  iIntros (???????) "?".
  done.
Qed.
Global Program Instance simplify_hyp_ty_ghost_drop'_2 `{!typeGS Σ} {rt} (ty : type rt) π r `{Heq : !TCFastDone (ty.(ty_trivial_drop) = true)} :
  SimplifyHyp (ty_ghost_drop' ty π r) (Some 0%N) := {|
  simplify_hyp_Q := ty_ghost_drop ty π r;
|}.
Next Obligation.
  iIntros (???????) "?".
  rewrite /ty_ghost_drop' Heq.
  done.
Qed.
Global Program Instance simplify_hyp_mut_fixpoint_project_ty_ghost_drop `{!typeGS Σ}
    {rts : list RT} (F : mut_type_fun rts) {Hne : MutTypeNonExpansive F}
    {Hctr : MutTypeContractive (mut_iter F (length rts))}
    {Hrts : base.TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} {Hinh : Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) π r :
  SimplifyHyp (_ty_ghost_drop
    (@mut_type_project _ _ rts (@mut_fixpoint _ _ rts F Hne Hctr Hrts) rt Hinh i Hlook) π r) (Some 0%N) := {|
  simplify_hyp_Q := True%I;
|}.
Next Obligation.
  iIntros (?????????????). rewrite mut_fixpoint_project_ty_ghost_drop.
  iIntros "?"; done.
Qed.
Lemma simplify_goal_ty_ghost_drop_concrete `{!typeGS Σ} {rt} (ty : type rt) π r `{!IsNotVar ty} T :
  (_ty_ghost_drop ty π r) ∗ T ⊢
  simplify_goal (ty_ghost_drop ty π r) T.
Proof.
  iIntros "(Ha & $)". rewrite ty_ghost_drop_unfold//.
Qed.
Definition simplify_goal_ty_ghost_drop_concrete_inst := [instance @simplify_goal_ty_ghost_drop_concrete with 10%N].
Global Existing Instance simplify_goal_ty_ghost_drop_concrete_inst.

Lemma simplify_goal_mut_fixpoint_project_ty_ghost_drop `{!typeGS Σ}
    {rts : list RT} (F : mut_type_fun rts)
    {Hne : TCNoResolve (MutTypeNonExpansive F)}
    {Hctr : TCNoResolve (MutTypeContractive (mut_iter F (length rts)))}
    {Hrts : base.TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} {Hinh : Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) π r T :
  T ⊢ simplify_goal (_ty_ghost_drop
    (@mut_type_project _ _ rts (@mut_fixpoint _ _ rts F Hne Hctr Hrts) rt Hinh i Hlook) π r) T.
Proof.
  rewrite mut_fixpoint_project_ty_ghost_drop. iIntros "$".
Qed.
Definition simplify_goal_mut_fixpoint_project_ty_ghost_drop_inst := [instance @simplify_goal_mut_fixpoint_project_ty_ghost_drop with 5%N].
Global Existing Instance simplify_goal_mut_fixpoint_project_ty_ghost_drop_inst.


(* In my experience, this has led to more problems with [normalize_autorewrite] rewriting below definitions too eagerly. *)
#[export] Unset Keyed Unification.

(** Lithium hook *)
Ltac hooks.normalize_hook ::=
  (* also simpl *)
  rewrite /size_of_st/=;
  simplify_layout_normalize;
  autounfold with lithium_rewrite;
  match goal with
  | |- fast_subst_hint _ _ = _ =>
    idtac
  | |- (use_layout_alg (ltype_st _) = Some _) = _ =>
    idtac
  | |- _ => autorewrite with lithium_rewrite
  end;
  exact: eq_refl
.

Ltac after_intro_hook H ::=
  try match type of H with
  | enter_cache_hint ?P =>
      unfold enter_cache_hint in H;
      enter_cache H
  | fast_subst_hint ?a ?b =>
    unfold fast_subst_hint in H; subst a
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

Lemma apply_name_hint name (P : Prop) :
  P → name_hint name P.
Proof. done. Qed.
Ltac before_revert_hook H ::=
  match type of H with
  | CACHED _ =>
      (* don't alter this *)
      fail 2
  | JCACHED _ =>
      fail 2
  | bb_inv_map_marker _ =>
      fail 2
  | TYVAR_MAP _ =>
      fail 2
  | _ =>
      (* put a name hint to preserve names *)
      let Hident_str := constr:(ident_to_string! H) in
      apply (apply_name_hint Hident_str _) in H
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

Lemma ty_lfts_unfold_lem `{!typeGS Σ} {rt} (ty : type rt) :
  ty_lfts ty = _ty_lfts _ ty.
Proof. rewrite ty_lfts_unfold. done. Qed.
Lemma ty_wf_E_unfold_lem `{!typeGS Σ} {rt} (ty : type rt) :
  ty_wf_E ty = _ty_wf_E _ ty.
Proof. rewrite ty_wf_E_unfold. done. Qed.

(** Enum-related tactic calls *)
Ltac solve_mk_enum_tag_consistent :=
  simpl; intro_adt_params;
  intros [] ? [=<-]; eexists _; done.

Ltac enum_contractive_solve_eq := intros; simpl; done.
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
    | Hdist : TypeDist2 ?n ?ty ?ty' |-
        TypeDist ?n (enum_ty ?E ?r) (enum_ty ?E' ?r) =>
        let P := eval pattern ty in E in
        lazymatch P with
        | ?F _ =>
            eapply (type_contractive_dist _ _ (λ ty, enum_ty (F ty) r));
            [ destruct r; simpl; apply _
            | first [apply _ | done ] ]
        end
    | Hdist : TypeDistLater2 ?n ?ty ?ty' |-
        TypeDist2 ?n (enum_ty ?E ?r) (enum_ty ?E' ?r) =>
        let P := eval pattern ty in E in
        lazymatch P with
        | ?F _ =>
            eapply (type_contractive_dist2 _ _ (λ ty, enum_ty (F ty) r));
            [ destruct r; simpl; apply _
            | first [apply _ | done ] ]
        end
    end.

Ltac rewrite_type_ctr_syn_type_once ty ty' :=
  lazymatch goal with
  | |- context[ty_syn_type (?F ty) ?m] =>
      rewrite (type_ctr_syn_type (F := F) ty ty' m)
  | |- context[st_of (?F ty) ?m] =>
      rewrite (type_ctr_syn_type (F := F) ty ty' m)
  end.
Ltac rewrite_type_ctr_syn_types ty ty' :=
  repeat progress rewrite_type_ctr_syn_type_once ty ty'.
Ltac solve_enum_t_contr_has_op_type ty ty':=
  split; [done | ];
  simpl;
  intros ?;
  first [done
  | repeat rewrite ty_has_op_type_unfold/=;
    rewrite_type_ctr_syn_types ty ty'
  ];
  match goal with
  | |- is_struct_ot ?sls ?tys ?ot ↔ is_struct_ot ?sls' ?tys' ?ot =>
      unify sls sls';
      match goal with
      | ty : type _ , ty' : type _ |- _ =>
          let P := eval pattern ty in tys in
          lazymatch P with
          | ?Ts _ =>
              change (is_struct_ot sls (Ts ty) ot ↔ is_struct_ot sls (Ts ty') ot);
              eapply is_struct_ot_htype_proper_contr;
              apply _
          end
      end
  end.
Ltac solve_enum_t_contr_op_type :=
  let ty := fresh "ty" in
  let ty' := fresh "ty" in
  intros ty ty';
  unfold enum_tag_tys_has_op_type_rel;
  simpl;
  repeat match goal with
  | |- Forall2 _ (_ :: _) (_ :: _) =>
    econstructor
  | |- Forall2 _ [] [] =>
    econstructor
  end;
  solve_enum_t_contr_has_op_type ty ty'
  .

Ltac rewrite_type_ne_syn_type_once ty ty' :=
  lazymatch goal with
  | |- context[ty_syn_type (?F ty) ?m] =>
      rewrite (type_ne_syn_type (F := F) ty ty' _ m); last done
  | |- context[st_of (?F ty) ?m] =>
      rewrite (type_ne_syn_type (F := F) ty ty' _ m); last done
  end.
Ltac rewrite_type_ne_syn_types ty ty' :=
  repeat progress rewrite_type_ne_syn_type_once ty ty'.
Ltac solve_enum_t_ne_has_op_type ty ty' :=
  split; [done | ];
  simpl;
  intros ?;
  first [done
  | repeat rewrite ty_has_op_type_unfold/=;
    rewrite_type_ne_syn_types ty ty'
  ];
  match goal with
  | |- is_struct_ot ?sls ?tys ?ot ↔ is_struct_ot ?sls' ?tys' ?ot =>
      unify sls sls';
      match goal with
      | ty : type _ , ty' : type _ |- _ =>
          let P := eval pattern ty in tys in
          lazymatch P with
          | ?Ts _ =>
              change (is_struct_ot sls (Ts ty) ot ↔ is_struct_ot sls (Ts ty') ot);
              eapply is_struct_ot_htype_proper_ne; [apply _ | done | done | done]
          end
      end
  end.
Ltac solve_enum_t_ne_op_type :=
  let ty := fresh "ty" in
  let ty' := fresh "ty" in
  intros ty ty' ? ? ?;
  unfold enum_tag_tys_has_op_type_rel;
  simpl;
  repeat match goal with
  | |- Forall2 _ (_ :: _) (_ :: _) =>
    econstructor
  | |- Forall2 _ [] [] =>
    econstructor
  end;
  solve_enum_t_ne_has_op_type ty ty'.


Global Hint Extern 100 (TypeContractive _) =>
  simpl;
  match goal with
  | |- TypeContractive (λ x, enum_t _) =>
    apply enum_t_contr;
    unshelve econstructor;
    [ enum_contractive_solve_eq
    | enum_contractive_solve_eq
    | enum_contractive_solve_eq
    | enum_contractive_solve_eq
    | enum_contractive_solve_dist
    | enum_contractive_solve_dist
    | solve_enum_t_contr_op_type ]
  end
  : typeclass_instances.
Global Hint Extern 100 (TypeNonExpansive _) =>
  simpl;
  match goal with
  | |- TypeNonExpansive (λ x, enum_t _) =>
    apply enum_t_ne;
    unshelve econstructor;
    [ enum_contractive_solve_eq
    | enum_contractive_solve_eq
    | enum_contractive_solve_eq
    | enum_contractive_solve_eq
    | enum_contractive_solve_dist
    | enum_contractive_solve_dist
    | solve_enum_t_ne_op_type ]
  end
  : typeclass_instances.

Ltac els_not_elem_solver :=
    repeat (apply not_elem_of_cons; split; first discriminate);
    apply not_elem_of_nil.
Ltac solve_enum_layout_spec_variants_nodup :=
  simpl; repeat first [econstructor | els_not_elem_solver ].
Ltac solve_enum_layout_spec_variants_eq :=
  simpl; reflexivity.
Ltac solve_enum_layout_spec_discriminant_nodup :=
  simpl; repeat first [econstructor | els_not_elem_solver].
Ltac solve_enum_layout_spec_discriminant_in_range :=
  init_cache; repeat first [econstructor | solve_goal ]; unsafe_unfold_common_radium_defs; simpl; lia.

Ltac solve_fixpoint_ne :=
  unfold TCNoResolve; apply _.
Ltac solve_fixpoint_contr :=
  unfold TCNoResolve; apply _.

(* Special ty_has_op_type hooks *)
Lemma ty_has_op_type_value_canonical `{!typeGS Σ} st ly :
  syn_type_has_layout st ly →
  ty_has_op_type (value_t true st) (use_op_alg' st).
Proof.
  rewrite ty_has_op_type_unfold.
  apply is_value_ot_typed_use_op_alg.
Qed.
Lemma ty_has_op_type_typed_value_canonical `{!typeGS Σ} st ly :
  syn_type_has_layout st ly →
  ty_has_op_type (typed_value_t st) (use_op_alg' st).
Proof.
  rewrite ty_has_op_type_unfold.
  apply is_value_ot_typed_use_op_alg.
Qed.
Lemma ty_has_op_type_ex_plain_t_canonical `{!typeGS Σ} {X Y} P ty ot :
  ty_has_op_type ty ot →
  ty_has_op_type (ex_plain_t X Y P ty) ot.
Proof.
  intros ?. rewrite ty_has_op_type_unfold. done.
Qed.
Lemma ty_has_op_type_ex_na_t_canonical `{!typeGS Σ} {X Y} P ty ot :
  ty_has_op_type ty ot →
  ty_has_op_type (na_ex_plain_t X Y P ty) ot.
Proof.
  intros ?. rewrite ty_has_op_type_unfold. done.
Qed.
Lemma mut_fixpoint_project_ty_has_op_type_2 `{!typeGS Σ} {rt1} (ty : type rt1) {rts : list RT} (F : mut_type_fun rts) `{Hne : !MutTypeNonExpansive F} `{Hcontr : !MutTypeContractive (mut_iter F (length rts))} `{Hinh : !base.TCTForall (λ rt, Inhabited (RT_xt rt)) rts} {rt : RT} `{!Inhabited (RT_xt rt)} i (Hlook : rts !! i = Some rt) m :
  ty_has_op_type ty
    (use_op_alg' (st_of (mut_type_project_simpl (mut_Fn_canon (mut_iter F (length rts)) Hinh 0) i Hlook) m)) →
  ty_has_op_type ty (use_op_alg' (st_of (mut_type_project (mut_fixpoint (Hne:=Hne) (Hcontr:=Hcontr) F) i Hlook) m)).
Proof.
  intros Ha. rewrite mut_fixpoint_project_ty_syn_type//.
Qed.

Ltac solve_ty_has_op_type_struct_fields :=
  simpl;
  match goal with
  | |- Forall2 _ (_ :: _)  (_ :: _) =>
    apply Forall2_cons; split;
    [simpl | solve_ty_has_op_type_struct_fields]
  | |- Forall2 _ [] [] =>
    by apply Forall2_nil
  end
.
Ltac solve_ty_has_op_type_enum_variants :=
  simpl;
  match goal with
  | |- Forall2 _ (_ :: _)  (_ :: _) =>
    apply Forall2_cons; split;
    [simpl; split; first done | solve_ty_has_op_type_enum_variants]
  | |- Forall2 _ [] [] =>
    by apply Forall2_nil
  end
.
Ltac solve_ty_has_op_type_cases ::=
  lazymatch goal with
  | |- ty_has_op_type (value_t true ?st) (use_op_alg' _) =>
        refine (ty_has_op_type_value_canonical st _ _);
        [ solve_layout_alg]
  | |- ty_has_op_type (typed_value_t ?st) (use_op_alg' _) =>
        refine (ty_has_op_type_typed_value_canonical st _ _);
        [ solve_layout_alg]
  | |- ty_has_op_type (array_t ?len ?ty) (use_op_alg' _) =>
        refine (ty_has_op_type_array_canonical' ty len _ _ _);
        [ solve_layout_alg |]
  | |- ty_has_op_type (array_t ?len ?ty) (ArrayOp ?element_ot _) =>
        refine (ty_has_op_type_array_canonical ty len element_ot _ _ _ _);
        [ solve_op_alg | solve_ot_eq |]
  | |- ty_has_op_type (mut_type_project _ _ _) _ =>
        refine (mut_fixpoint_project_ty_has_op_type_1 _ _ _ _ _)
  | |- ty_has_op_type _ (use_op_alg' (st_of (mut_type_project (mut_fixpoint _) _ _) _)) =>
        refine (mut_fixpoint_project_ty_has_op_type_2 _ _ _ _ _ _)
  | |- _ =>
    first [
      fast_done
    | refine (ty_has_op_type_struct_canonical' _ _ _ _ _ );
      [ solve_layout_alg
      | solve_ty_has_op_type_struct_fields]
    | refine (ty_has_op_type_enum_canonical' _ _ _ _ _ _ );
      [ simpl; solve_layout_alg
      | simpl; solve_syn_type_eq
      | solve_ty_has_op_type_enum_variants]
    | refine (ty_has_op_type_ex_plain_t_canonical _ _ _ _)
    | refine (ty_has_op_type_ex_na_t_canonical _ _ _ _)
    (*
    | refine (ty_has_op_type_struct_canonical _ _ _ _ _ _ _ _);
      [ solve_op_alg
      | solve_ot_eq
      | solve_ty_has_op_type_struct_fields]
    | refine (ty_has_op_type_enum_canonical _ _ _ _ _ _ _ _);
      [ solve_op_alg
      | solve_ot_eq
      | solve_ty_has_op_type_enum_variants]
      *)
    ]
  end.

(* Fast function type equality *)
Ltac solve_fast_function_spec_eq :=
    match goal with
    | |- FastFunctionSpecEq  _ _ =>
      unfold FastFunctionSpecEq;
      intros ??; prepare_initial_coq_context;
      simpl; exists eq_refl;
      intros ?; prepare_initial_coq_context;
      simpl; split_and!; try done;
      [exists eq_refl; done]
    end.
Hint Extern 2 (FastFunctionSpecEq _ _) => solve_fast_function_spec_eq : typeclass_instances.

(** ** Sideconditions *)
Ltac shelve_sidecond_hook ::=
  unfold name_hint, discriminate_hint.

Ltac sidecond_hook_init :=
  intros;
  prepare_initial_coq_context;
  unfold name_hint_ty, name_hint in *;
  repeat match goal with
  | |- _ ∧ _ => split
  | |- Forall ?P (_ :: ?l) =>
      apply Forall_cons; split
  | |- Forall _ [] =>
      apply Forall_nil; exact I
  | |- True =>
      exact I
  end
.
Ltac sidecond_hook_core :=
  lazymatch goal with
  | |- lctx_lft_alive ?E ?L ?κ =>
      solve_lft_alive
  | |- Forall (lctx_lft_alive ?E ?L) ?κs =>
      solve_lft_alive
  | |- lctx_lft_dead ?E ?L ?κ =>
      solve_lft_dead
  | |- Forall (lctx_lft_dead ?E ?L) ?κs =>
      solve_lft_dead
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
  | |- local_fresh _ _ =>
      (* for local variables *)
      solve_local_fresh
  | |- lctx_place_update_kind_outlives ?E ?L ?b ?κs =>
      solve_place_update_kind_outlives
  | |- ty_has_op_type _ _ =>
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
  | |- use_layout_alg ?st = Some ?ly =>
    solve_layout_alg
  | |- use_layout_alg' ?st = ?ly =>
    solve_layout_alg
  | |- syn_type_has_layout ?st ?ly =>
    solve_layout_alg
  | |- use_struct_layout_alg ?sls = ?Some ?sl =>
    solve_layout_alg
  | |- struct_layout_spec_has_layout ?sls ?sl =>
    solve_layout_alg
  | |- use_enum_layout_alg ?els = ?Some ?el =>
    solve_layout_alg
  | |- enum_layout_spec_has_layout ?els ?el =>
    solve_layout_alg
  | |- use_union_layout_alg ?uls = ?Some ?ul =>
    solve_layout_alg
  | |- union_layout_spec_has_layout ?uls ?ul =>
    solve_layout_alg
  end.
Ltac sidecond_hook :=
  sidecond_hook_init;
  sidecond_hook_core
.

Ltac is_builtin_sidecond P :=
  lazymatch P with
  | lctx_lft_alive ?E ?L ?κ =>
      idtac
  | Forall (lctx_lft_alive ?E ?L) ?κs =>
      idtac
  | lctx_lft_dead ?E ?L ?κ =>
      idtac
  | Forall (lctx_lft_dead ?E ?L) ?κs =>
      idtac
  | lctx_lft_incl ?E ?L ?κ1 ?κ2 =>
      idtac
  | lctx_lft_list_incl ?E ?L ?κ1 ?κ2 =>
      idtac
  | lctx_place_update_kind_incl ?E ?L ?b1 ?b2 =>
      idtac
  | lctx_bor_kind_alive ?E ?L ?b =>
      idtac
  | lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      idtac
  | elctx_sat ?E ?L ?E' =>
      idtac
  | local_fresh _ _ =>
      (* for local variables *)
      idtac
  | lctx_place_update_kind_outlives _ _ _ _ =>
      idtac
  | ty_has_op_type _ _ =>
      idtac
  | layout_wf _ =>
      idtac
  | ly_align_in_bounds _ =>
      idtac
  | syn_type_compat _ _ =>
      idtac
  | ty_allows_reads _ =>
      idtac
  | ty_allows_writes _ =>
      idtac
  | Copyable _ =>
      idtac
  | trait_incl_marker _ =>
      idtac
  | use_op_alg _ = _ =>
      idtac
  | ∀ x, elctx_sat ?E ?L ?E' =>
      idtac
  | ∀ x y, elctx_sat ?E ?L ?E' =>
      idtac
  | ∀ x y z, elctx_sat ?E ?L ?E' =>
      idtac
  | ∀ x y z w, elctx_sat ?E ?L ?E' =>
      idtac
  | ∀ x y z w u, elctx_sat ?E ?L ?E' =>
      idtac
  | ?P ∧ ?Q =>
      first [is_builtin_sidecond P | is_builtin_sidecond Q]
  end.

Ltac is_fast_builtin_sidecond P :=
  lazymatch P with
  | lctx_lft_alive ?E ?L ?κ =>
      idtac
  | Forall (lctx_lft_alive ?E ?L) ?κs =>
      idtac
  | lctx_lft_dead ?E ?L ?κ =>
      idtac
  | Forall (lctx_lft_dead ?E ?L) ?κs =>
      idtac
  | lctx_lft_incl ?E ?L ?κ1 ?κ2 =>
      idtac
  | lctx_lft_list_incl ?E ?L ?κ1 ?κ2 =>
      idtac
  | lctx_place_update_kind_incl ?E ?L ?b1 ?b2 =>
      idtac
  | lctx_bor_kind_alive ?E ?L ?b =>
      idtac
  | lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      idtac
  | local_fresh _ _ =>
      (* for local variables *)
      idtac
  | syn_type_compat _ _ =>
      idtac
  | lctx_place_update_kind_outlives _ _ _ _ =>
      idtac
  | Copyable _ =>
      idtac
  | ty_has_op_type _ _ =>
      idtac
  | ty_allows_reads _ =>
      idtac
  | ty_allows_writes _ =>
      idtac
  end.

Lemma cache_sidecond P P' T :
  (∀ (P'':=P'), P = P'') →
  P ∧ (enter_cache_hint P' → T) →
  P ∧ T.
Proof.
  intros <- [HP HT].
  split; first done.
  by apply HT.
Qed.

Ltac prepare_sideconditions_fast :=
  li_unfold_lets_in_context;
  unfold_instantiated_evars;
  repeat match goal with | H : BLOCK_PRECOND _ _ |- _ => clear H end;
  (* get rid of Q *)
  repeat match goal with | H := CODE_MARKER _ |- _ => clear H end;
  repeat match goal with | H := RETURN_MARKER _ |- _ => clear H end;
  repeat match goal with | H := UNWIND_MARKER _ |- _ => clear H end
.
Ltac prepare_sideconditions :=
  prepare_sideconditions_fast;
  clear_unused_vars
.

Ltac solve_sublist_step :=
  first [apply sublist_nil | apply sublist_skip | apply sublist_cons].
Ltac solve_sublist :=
  solve [repeat solve_sublist_step].

(** specialized handlers for some sideconditions for which we want to bypass the standard normalization *)
Ltac liSidecond_hook P ::=
  lazymatch P with
  | trait_incl_marker _ =>
      (* terms here are huge, and normalizing is very expensive *)
      split; [shelve_sidecond |]
  | fast_lia_hint _ => split; [clear; unfold fast_lia_hint, num_cred; simpl; lia | ]
  | fast_set_hint _ => split; [clear; unfold fast_set_hint; simpl; set_solver | ]
  | fast_eq_hint _ =>
      split; [
        first [unfold spec_instantiate_typaram_fst, spec_instantiate_lft_fst, spec_instantiated; simpl; reflexivity | fail 10] | ]
  | fast_sublist_hint _ => split; [clear; unfold fast_sublist_hint; simpl; solve_sublist | ]
  | fast_syntype_eq_hint _ => split; [clear; unfold fast_syntype_eq_hint; simpl; solve_syn_type_eq | ]
  | _ =>
      is_builtin_sidecond P;
      tryif is_fast_builtin_sidecond P
      then
        (split;
        [ first [
            fast_done
            | prepare_sideconditions_fast;
              liSimpl;
              solve [sidecond_hook_core]
            | fail 100 "unsolvable builtin sidecondition"
            (*| shelve_sidecond*)
            ]
        | ])
      else
        (* TODO: we should cache ty_has_op_type as it can be expensive *)
        (split; first shelve_sidecond)
end.
(** If this is not a built-in sidecond, cache it so we don't have to solve it again in the future *)
Ltac hooks.liAfterSidecond_hook P ::=
  refine (cache_sidecond _ _ _ _ _); [simpl; reflexivity | ].

Ltac sidecond_solver :=
  (* These simplifications stay around even if this doesn't solve the goal. *)
  unshelve_sidecond;
  prepare_sideconditions;
  liSimpl;
  (* This should not stay around for unsolved goals. *)
  try solve[sidecond_hook].

(** Lithium hooks for [solve_goal]: called for remaining sideconditions *)
Lemma unfold_int_elem_of_it (z : Z) (it : int_type) :
  (z ∈ it) = (MinInt it ≤ z ∧ z ≤ MaxInt it)%Z.
Proof. done. Qed.
Lemma unfold_nat_elem_of_it (n : nat) (it : int_type) :
  (n ∈ it) = (MinInt it ≤ n ∧ n ≤ MaxInt it)%Z.
Proof. done. Qed.

(** Normalization that should be done to all goals -- even ones that will be presented to the user. *)
Ltac sidecond_hammer_normalize :=
  autounfold with lithium_rewrite;
  autounfold with lithium_rewrite in *;
  try rewrite -> unfold_int_elem_of_it in *;
  try rewrite -> unfold_nat_elem_of_it in *;
  simpl in *;
  normalize_and_simpl_goal.

(** Clear info that is not needed for a successful [solve_goal] run.
  These simplifications don't stay around if [solve_goal] fails. *)
Ltac solve_goal_prepare_hook ::=
  repeat match goal with | H : CASE_DISTINCTION_INFO _ |- _ =>  clear H end;
  clear_layout;
  (* also normalize by unfolding a bit *)
  autounfold with solve_goal_unfold;
  autounfold with solve_goal_unfold in *
.

(** Called to normalize the goal after running [normalize_and_simpl_goal].
  These simplifications don't stay around if [solve_goal] fails. *)
Ltac solve_goal_normalized_prepare_hook ::=
  simplify_layout_goal;
  open_cache;
  idtac
.

(** The main automation tactic after normalizing *)
Ltac solve_goal_final_hook ::=
  unfold reverse_coercion in *; simpl in *;
  refined_solver lia
.

(** The main sidecondition tactic, called after [sidecond_solver]: basically, an adaptation of [solve_goal].
  Important: does not change the goal if it doesn't fully solve it. *)
Ltac sidecond_hammer_it :=
  solve_goal_prepare_hook;
  normalize_and_simpl_goal;
  solve_goal_normalized_prepare_hook; reduce_closed_Z; enrich_context;
  repeat case_bool_decide => //; repeat case_decide => //; repeat case_match => //;

  solve_goal_final_hook.
Ltac sidecond_hammer :=
  open_cache;
  sidecond_hammer_normalize;
  simpl;
  try fast_done;
  try sidecond_hammer_it;
  (* if the goal isn't solved yet, try harder to normalize *)
  (* NB [normalize_aggressively] needs the layout facts still in the goal *)
  try (normalize_aggressively; sidecond_hammer_it)
.

(** For solving [CanSolve] conditions *)
Ltac can_solve_hook ::=
  first [
    match goal with
    | |- _ ≠ _ => discriminate
    end
 | (* pruning the context first makes this have a much better worst-case behavior *)
  open_scache; prepare_sideconditions; solve_goal].

(* Solve this sidecondition within Lithium *)
Ltac solve_function_subtype_hook ::=
  rewrite /function_subtype;
  iStartProof;
  unshelve (repeat liRStep; solve[fail]);
  unshelve (sidecond_solver);
  sidecond_hammer
.

(** **  Generics / Traits *)
Ltac normalized_rt_of_spec_ty_rec ty :=
  match ty with
  | context[spec_with _ _ (type ?ty)] =>
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
  intros;
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

(** For starting Lithium on manual subgoals *)
Lemma tac_li_start {Σ} Δ (P : iProp Σ) :
  envs_entails Δ (P ∗ True)%I →
  envs_entails Δ P.
Proof.
  rewrite right_id. done.
Qed.
Ltac liStart :=
  match goal with
  | |- envs_entails _ _ =>
      notypeclasses refine (tac_li_start _ _ _)
  end.
