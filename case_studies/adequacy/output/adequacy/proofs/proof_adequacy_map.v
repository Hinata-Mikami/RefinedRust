From radium Require Import lang notation.
From refinedrust Require Import typing shims adequacy.
From rrstd.option.option.proofs Require Import proof_Option_T_map.
From rrstd.iterator.iterator.proofs Require Import
  proof_adapters_map_Map_IF_new proof_traits_iterator_Iterator_map
  proof_adapters_map_MapMIMFastraits_iterator_Iterator_next.
From rrstd.closures.closures.proofs Require Import proof_REFmutFasFnOnceA_call_once.
From rrstd.option.option.generated Require Import generated_code_option.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator.
From rrstd.closures.closures.generated Require Import generated_code_closures.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy.
From refinedrust.examples.adequacy.proofs Require Import
  proof_main_map proof_Oneasstd_iter_Iterator_next
  proof_main_map_closure0 proof_main_map_closure0_call_mut.

Section adequate.
Context `{!LayoutAlg}.
Arguments trait_ctx_wf : clear simpl.
Context (addr_main addr_next addr_map addr_new addr_one addr_option
  addr_borrowed addr_mut addr_body addr_drop_ref : addr).

Definition functions : list function := [
  main_map_def (fn_loc addr_next) (fn_loc addr_map);
  adapters_map_MapMIMFastraits_iterator_Iterator_next_def
    (fn_loc addr_option) (fn_loc addr_one) (IntSynType i32) One_st UnitSynType (IntSynType i32);
  traits_iterator_Iterator_map_def (fn_loc addr_new) One_st (IntSynType i32) (IntSynType i32) UnitSynType;
  adapters_map_Map_IF_new_def One_st UnitSynType;
  Oneasstd_iter_Iterator_next_def;
  Option_T_map_def (fn_loc addr_drop_ref) (fn_loc addr_borrowed) (IntSynType i32) (IntSynType i32) RefSynType;
  REFmutFasFnOnceA_call_once_def (fn_loc addr_mut) (tuple1_sls (IntSynType i32)) UnitSynType (IntSynType i32);
  main_map_closure0_call_mut_code (fn_loc addr_body);
  main_map_closure0_def;
  drop_glue_trivial_def RefSynType
].
Definition function_addrs := [addr_main; addr_next; addr_map; addr_new; addr_one;
  addr_option; addr_borrowed; addr_mut; addr_body; addr_drop_ref].

(* experiment *)
Arguments trait_incl_of_REFmutFasFnOnceA_call_once : simpl never.
Arguments typaram_wf : simpl never.

Lemma main_map_adequate (config : RadiumConfig) hs σ n κs t2 σ2
  (Hunit : syn_type_is_layoutable UnitSynType)
  (Hone : syn_type_is_layoutable One_st)
  (Hmap : syn_type_is_layoutable (adapters_map_Map_sls One_st UnitSynType))
  (Htuple : syn_type_is_layoutable (tuple1_sls (IntSynType i32)))
  (Hopt : syn_type_is_layoutable (Option_els (IntSynType i32)))
  (Hsome : syn_type_is_layoutable (Option_Some_sls (IntSynType i32)))
  (Hnone : syn_type_is_layoutable (Option_None_sls (IntSynType i32))) :
  alloc_new_blocks initial_heap_state GlobalAlloc [] [] hs →
  σ = initial_state hs 1 (fn_lists_to_fns function_addrs functions) →
  NoDup function_addrs →
  Forall (λ a, a ∈ USize) function_addrs →
  nsteps (Λ := c_lang config) n (initial_prog AllowUnwind <$> [(0, fn_loc addr_main)], σ) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  move => ? -> HNDfns HRANfns.
  adequacy_invert_forall HRANfns.
  set Σ : gFunctors := #[typeΣ].
  eapply (refinedrust_adequacy config AllowUnwind Σ [fn_loc addr_main]) => //.
  { adequacy_split_forall; done. }
  move => ? Halg. unfold functions in *. subst H.
  exists (∅ : gmap string loc), (∅ : gmap string btype).
  set (Hstatics := {| static_locs := ∅; static_types := ∅ |} : staticGS Σ).
  set (RRGS := {| refinedrust_typeGS := _; refinedrust_staticGS := Hstatics |}).
  have HOneOps : ty_allows_ops (One_inv_t (RRGS:=RRGS) -[] -[]).
  { destruct Hone as [ly Hly].
    destruct (use_layout_alg_struct_Some_inv _ _ Hly) as (sl & Hsl & _).
    solve_ty_allows. }
  iIntros "Hstatics Hfn".
  have Hin := I.
  repeat (move: {Hin} HNDfns => /NoDup_cons[Hin HNDfns];
    iDestruct (fn_lists_to_fns_cons with "Hfn") as "[#? Hfn]" => //).
  iAssert (typed_function 0 main_map_closure0_def (<tag_type> type_of_main_map_closure0)) as "#Hbody".
  { adequacy_solve_typed_function (main_map_closure0_proof (RRGS:=RRGS) 0); done. }
  iPoseProof (main_map_closure0_call_mut_proof (RRGS:=RRGS) 0 (fn_loc addr_body)
    (spec! ( *[_]) : 1 | ( *[]) : [], λ _, True%I)
    Hunit Htuple ltac:(eexists; solve_layout_alg) with "[]") as "#HmutLate".
  {
      unfold from_assumption_hint.
      adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
  }
  iAssert (typed_function 0 (main_map_closure0_call_mut_code (fn_loc addr_body))
    (<tag_type> main_map_closure0_call_mut_spec)) as "#Hmut".
  { iApply (typed_function_late_pre_discharge _ _ _ _ main_map_closure0_call_mut_spec
      (spec! ( *[κ]) : 1 | ( *[]) : [], λ π,
        (True ∗ main_map_closure0_call_mut_trait_req_incl -[κ] -[] π ∗
          □ (∀ _ : lft, True))%I)).
    { rewrite /typed_function. iIntros (lfts tys).
      destruct lfts as [κ []]. destruct tys.
      iApply ("HmutLate" $! -[κ] -[]). }
    iModIntro. iIntros (lfts tys). destruct lfts as [κ []]. destruct tys.
    simpl. rep liRStep.
  }
  iAssert (typed_function 0 Oneasstd_iter_Iterator_next_def
    (<tag_type> type_of_Oneasstd_iter_Iterator_next)) as "#Hone".
  { adequacy_solve_typed_function (Oneasstd_iter_Iterator_next_proof (RRGS:=RRGS) 0); done. }
  set (DropZ := drop_glue_trivial_realization (RRGS:=RRGS) ZRT (IntSynType i32)).
  set (DropUnit := drop_glue_trivial_realization (RRGS:=RRGS) unit UnitSynType).
  set (TupleAttrs := drop_glue_tuple1_spec_attrs ZRT (drop_glue_trivial_spec_attrs ZRT)).
  set (DropTuple := drop_glue_tuple1_realization (RRGS:=RRGS)
    ZRT (IntSynType i32) (drop_glue_trivial_spec_attrs ZRT) DropZ).
  iPoseProof (REFmutFasFnOnceA_call_once_proof (RRGS:=RRGS) 0
    (plist place_rfnRT [ZRT]) unit ZRT
    (tuple1_sls (IntSynType i32)) UnitSynType (IntSynType i32)
    main_map_closure0_FnOnce_spec_attrs main_map_closure0_FnOnce_realization
    main_map_closure0_FnMut_spec_attrs main_map_closure0_FnMut_realization
    TupleAttrs DropTuple
    (drop_glue_trivial_spec_attrs _) DropUnit
    (drop_glue_trivial_spec_attrs _) DropZ (fn_loc addr_mut)
    Htuple Hunit ltac:(eexists; solve_layout_alg) with "[]") as "#Hborrowed".
  { adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ _ => -[]). }
  set (BorrowAttrs := REFmutFasFnOnceA_spec_attrs (RRGS:=RRGS)
    (plist place_rfnRT [ZRT]) unit ZRT
    main_map_closure0_FnOnce_spec_attrs main_map_closure0_FnMut_spec_attrs
    TupleAttrs (drop_glue_trivial_spec_attrs _) (drop_glue_trivial_spec_attrs _)).
  set (BorrowReal := REFmutFasFnOnceA_realization (RRGS:=RRGS)
    (plist place_rfnRT [ZRT]) unit ZRT
    (tuple1_sls (IntSynType i32)) UnitSynType (IntSynType i32)
    main_map_closure0_FnOnce_spec_attrs main_map_closure0_FnOnce_realization
    main_map_closure0_FnMut_spec_attrs main_map_closure0_FnMut_realization
    TupleAttrs DropTuple
    (drop_glue_trivial_spec_attrs _) DropUnit
    (drop_glue_trivial_spec_attrs _) DropZ).
  set (DropRef := drop_glue_trivial_realization (RRGS:=RRGS)
    ((place_rfnRT unit * gname)%type) RefSynType).
  iPoseProof (drop_glue_trivial_proof (RRGS:=RRGS) 0
    ((place_rfnRT unit * gname)%type) RefSynType
    ltac:(eexists; solve_layout_alg)) as "#Hdrop".
  iPoseProof (Option_T_map_proof (RRGS:=RRGS) 0 ZRT ZRT
    ((place_rfnRT unit * gname)%type) (IntSynType i32) (IntSynType i32) RefSynType
    (drop_glue_trivial_spec_attrs _) DropZ BorrowAttrs BorrowReal
    (drop_glue_trivial_spec_attrs _) DropZ (drop_glue_trivial_spec_attrs _) DropRef
    (fn_loc addr_drop_ref) (fn_loc addr_borrowed)
    ltac:(eexists; solve_layout_alg) ltac:(eexists; solve_layout_alg)
    ltac:(eexists; solve_layout_alg) Hopt Hopt Hnone Hsome Hsome Htuple
    with "[] []") as "#Hoption".
  { adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x). }
  { Arguments trait_ctx_wf : simpl never.
    adequacy_solve_function_ptr uconstr:(fun x => x)
      uconstr:(fun _ (tys : plist type [(plist place_rfnRT [ZRT] : RT); (unit : RT); ZRT; ZRT; ZRT; ((place_rfnRT unit * gname)%type : RT)]) =>
        let '( *[A; F; Out; _; _; _]) := tys in -[A; F; Out]).
    liInst Hevar_a0 b.
    (* Expose type validity, but retain the existential trait requirements as a package. *)
    liShow.
    iRename select (trait_ctx_wf _ _ _ _)%I into "Hwf".
    iDestruct "Hwf" as "((HA & HF & HOut) & Hreq)".
    rep liRStep.
  }
  Arguments trait_ctx_wf : clear simpl.
  Arguments typaram_wf _ _ _ _ _ /.
  set (DropOne := drop_glue_trivial_realization (RRGS:=RRGS) bool One_st).
  iPoseProof (adapters_map_Map_IF_new_proof (RRGS:=RRGS) 0 bool unit One_st UnitSynType
    (drop_glue_trivial_spec_attrs _) DropOne (drop_glue_trivial_spec_attrs _) DropUnit
    Hone Hunit Hmap) as "#Hnew".
  set (NewLink := trait_incl_of_adapters_map_Map_IF_new (RRGS:=RRGS)
    bool unit One_st UnitSynType (drop_glue_trivial_spec_attrs _) DropOne
    (drop_glue_trivial_spec_attrs _) DropUnit).
  iPoseProof (traits_iterator_Iterator_map_proof (RRGS:=RRGS) 0 bool ZRT ZRT unit
    One_st (IntSynType i32) (IntSynType i32) UnitSynType
    (drop_glue_trivial_spec_attrs _) DropOne (drop_glue_trivial_spec_attrs _) DropZ
    Oneasstd_iter_Iterator_spec_attrs Oneasstd_iter_Iterator_realization
    main_map_closure0_FnOnce_spec_attrs main_map_closure0_FnOnce_realization
    main_map_closure0_FnMut_spec_attrs main_map_closure0_FnMut_realization
    (drop_glue_trivial_spec_attrs _) DropZ (drop_glue_trivial_spec_attrs _) DropUnit
    (fn_loc addr_new) NewLink Hone ltac:(eexists; solve_layout_alg)
    ltac:(eexists; solve_layout_alg) Hunit Hmap with "[]") as "#Hmap".
  { unfold from_assumption_hint, NewLink.
    adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
    liInst Hevar_p DropGlue_I_tys_inst. split; [assumption | rep liRStep].
    liInst Hevar_p DropGlue_F_tys_inst. split; [assumption | rep liRStep].
  }
  set (OptionLink := spec! ( *[κ]) : 1 | ( *[B; F; Item]) : [ZRT; (unit : RT); ZRT],
    trait_incl_of_Option_T_map (RRGS:=RRGS) ZRT ZRT
      ((place_rfnRT unit * gname)%type) (IntSynType i32) (IntSynType i32) RefSynType
      (drop_glue_trivial_spec_attrs _) DropZ BorrowAttrs BorrowReal
      (drop_glue_trivial_spec_attrs _) DropZ (drop_glue_trivial_spec_attrs _) DropRef
      -[] -[Item; B; mut_ref κ F]).
  iPoseProof (adapters_map_MapMIMFastraits_iterator_Iterator_next_proof (RRGS:=RRGS)
    0 ZRT bool unit ZRT (IntSynType i32) One_st UnitSynType (IntSynType i32)
    Oneasstd_iter_Iterator_spec_attrs Oneasstd_iter_Iterator_realization
    main_map_closure0_FnOnce_spec_attrs main_map_closure0_FnOnce_realization
    main_map_closure0_FnMut_spec_attrs main_map_closure0_FnMut_realization
    (drop_glue_trivial_spec_attrs _) DropZ (drop_glue_trivial_spec_attrs _) DropOne
    (drop_glue_trivial_spec_attrs _) DropUnit (drop_glue_trivial_spec_attrs _) DropZ
    (fn_loc addr_option) (fn_loc addr_one) OptionLink
    ltac:(eexists; solve_layout_alg) Hone Hunit ltac:(eexists; solve_layout_alg)
    Hmap Hopt Hopt with "[] []") as "#Hnext".
  { unfold from_assumption_hint, OptionLink.
    adequacy_solve_function_ptr uconstr:(fun _ => -[] : prod_vec lft 0)
      uconstr:(fun (κs : prod_vec lft 1) (tys : plist type [ZRT; (unit : RT); ZRT]) =>
        let '( *[κ]) := κs in let '( *[B; F; Item]) := tys in -[Item; B; mut_ref κ F]).
    liInst Hevar_x1 b. rep liRStep.
    liInst Hevar_p DropGlue_T_tys_inst. split; [assumption | rep liRStep].
    liInst Hevar_p FnOnce_F_T_lfts_inst.
    liInst Hevar_p0 FnOnce_F_T_tys_inst.
    liInst Hevar_p1 s1. liInst Hevar_p2 s2.
    split; [assumption | rep liRStep].
    liInst Hevar_p DropGlue_A_tys_inst. split; [assumption | rep liRStep].
    liInst Hevar_p DropGlue_F_tys_inst. split; [assumption | rep liRStep].
    liInst Hevar_p DropGlue_FasFnOnceA_Output_tys_inst. split; [assumption | rep liRStep].
    liInst Hevar_p DropGlue_U_tys_inst. split; [assumption | rep liRStep].
    liInst Hevar_p DropGlue_F_tys_inst0. split; [assumption | rep liRStep].
  }
  { adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ _ => -[]). }
  iAssert (typed_function 0 (main_map_def (fn_loc addr_next) (fn_loc addr_map))
    (<tag_type> type_of_main_map)) as "#Hmain".
  { iApply typed_function_equiv; iSplit.
    { iApply (main_map_proof (RRGS:=RRGS) 0 (fn_loc addr_next) (fn_loc addr_map)
        Hone Hmap Hopt).
      - iPoseProof (typed_function_specialize _ _ _ _ _ (fun x => x)
          (fun _ (_ : plist type []) => -[int i32; One_inv_t -[] -[]; unit_t; int i32])
          with "Hnext") as "HnextConcrete".
        rewrite /ty_own_val/=; iR. iExists _.
        iSplitR; [iPureIntro; by apply val_to_loc_Some_l2v|].
        iSplitR; [done|].
        iSplitR; [iPureIntro; simpl; repeat first [by apply Forall2_nil | apply Forall2_cons; split; [shelve_sidecond|]]|].
        iNext; simpl. iApply typed_function_equiv; iSplit.
        { iExact "HnextConcrete". }
        rep liRStep.
        liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
        liInst Hevar_p (One_inv_t -[] -[]). split; [solve_trait_incl | rep liRStep].
        liInst Hevar_p unit_t. split; [solve_trait_incl | rep liRStep].
        liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
        { liShow. iSplit; [iIntros (κ) | done]. liFromSyntaxGoal. rep liRStep.
          liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
          liInst Hevar_p κ.
          liInst Hevar_p0 (tuple1_ty ZRT -[] -[int i32]).
          liInst Hevar_p1 unit_t. liInst Hevar_p2 (int i32).
          split; [solve_trait_incl | rep liRStep].
          split.
          { destruct Htuple as [ly Hly].
            destruct (use_layout_alg_struct_Some_inv _ _ Hly) as (sl & Hsl & _).
            solve_ty_allows. }
          rep liRStep.
          liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
          unfold drop_glue_realization_incl. rep liRStep.
          liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
          liInst Hevar_p unit_t. split; [solve_trait_incl | rep liRStep].
          liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
          liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
          liInst Hevar_p (mut_ref κ unit_t). split; [solve_trait_incl | rep liRStep].
          liShow; done.
        }
        liShow; iSplit.
        { iModIntro; iIntros (?) "[]". }
        iIntros (vr a) "Hp Hv"; iExists a; iFrame.
      - iPoseProof (typed_function_specialize _ _ _ _ _ (fun x => x)
          (fun _ (_ : plist type []) => -[One_inv_t -[] -[]; int i32; int i32; unit_t])
          with "Hmap") as "HmapConcrete".
        rewrite /ty_own_val/=; iR. iExists _.
        iSplitR; [iPureIntro; by apply val_to_loc_Some_l2v|].
        iSplitR; [done|].
        iSplitR; [iPureIntro; simpl; repeat first [by apply Forall2_nil | apply Forall2_cons; split; [shelve_sidecond|]]|].
        iNext; simpl. iApply typed_function_equiv; iSplit.
        { iExact "HmapConcrete". }
        (* Preserve the caller's invariant and closure-parameter predicate. *)
        do 27 liRStep. liShow. liFromSyntaxGoal.
        iExists ((), b, b0, b1, tt).
        rep liRStep.
        liInst Hevar_p (One_inv_t -[] -[]). split; [solve_trait_incl | rep liRStep].
        liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
        liInst Hevar_p (int i32). split; [solve_trait_incl | rep liRStep].
        liInst Hevar_p unit_t. split; [solve_trait_incl | rep liRStep].
        { liInst Hevar_p (One_inv_t -[] -[]). split; [solve_trait_incl | rep liRStep].
          liInst Hevar_p unit_t. split; [solve_trait_incl | rep liRStep]. }
        liShow; iSplit.
        { iModIntro; iIntros (?) "[]". }
        iIntros (vr a) "Hp Hv"; iExists a; iFrame.
    }
    unfold introduce_direct. rep liRStep.
  }
  iModIntro. iSplitL => //.
  iExists True%I; iSplitR.
  { adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x). }
  done.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: match goal with
  | Hlayout : syn_type_is_layoutable ?st |- syn_type_has_layout ?st _ =>
      destruct Hlayout as [ly Hly];
      rewrite (use_layout_alg_eq' _ _ Hly); exact Hly
  end.
Qed.
End adequate.
