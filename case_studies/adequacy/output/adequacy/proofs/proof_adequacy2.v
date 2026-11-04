From radium Require Import lang notation.
From refinedrust Require Import typing shims adequacy.
From rrstd.option.option.generated Require Import generated_code_option.
From rrstd.option.option.proofs Require Import proof_drop_glue_Option.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy.
From refinedrust.examples.adequacy.proofs Require Import proof_main2.
From refinedrust.examples.adequacy.proofs Require Import proof_call_foo.
From refinedrust.examples.adequacy.proofs Require Import proof_foo.
From refinedrust.examples.adequacy.proofs Require Import proof_REFTasIter_next.

(* The concrete linking condition is selected here, not by the frontend. *)
Section linking.
Context `{RRGS : !refinedrustGS Σ}.
Definition foo_REFW_linking_requirement (W_rt : RT) (W_st : syn_type)
    (DropGlue_W_spec_attrs : DropGlue_spec_attrs W_rt)
    (DropGlue_W_realization : trait_spec_realization (spec_with 0 [] (DropGlue_spec W_rt)))
    (vlft3 : lft) (W_ty : type W_rt) (π : thread_id) : iProp Σ :=
  (trait_incl_of_foo (place_rfnRT W_rt) unit RefSynType UnitSynType
    (REFTasIter_spec_attrs W_rt DropGlue_W_spec_attrs)
    (REFTasIter_realization W_rt W_st DropGlue_W_spec_attrs DropGlue_W_realization)
    (drop_glue_trivial_spec_attrs (place_rfnRT W_rt))
    (drop_glue_trivial_realization (place_rfnRT W_rt) RefSynType)
    (drop_glue_trivial_spec_attrs unit)
    (drop_glue_trivial_realization unit UnitSynType)
    -[] -[shr_ref vlft3 W_ty; unit_t]) π ∗
  introduce_direct
    ((drop_glue_Option_realization unit UnitSynType
      (drop_glue_trivial_spec_attrs unit)
      (drop_glue_trivial_realization unit UnitSynType)).(trait_ctx_wf)
      -[] -[unit_t] π).
End linking.

Section adequate.
  Context `{!LayoutAlg}.

  Context (
    addr_main2
    addr_call_foo
    addr_foo
    addr_next
    addr_drop_option
    addr_drop_ref
    addr_drop_unit
    addr_drop_i32
    : addr).

  Definition functions : list function := [
    main2_def (fn_loc addr_call_foo);
    call_foo_def (fn_loc addr_drop_i32) (fn_loc addr_foo) (IntSynType i32);
    foo_def (fn_loc addr_drop_ref) (fn_loc addr_next) (fn_loc addr_drop_option) RefSynType UnitSynType;
    REFTasIter_next_def (IntSynType i32);
    drop_glue_Option_def (fn_loc addr_drop_unit) UnitSynType;
    drop_glue_trivial_def RefSynType;
    drop_glue_trivial_def UnitSynType;
    drop_glue_trivial_def (IntSynType i32)
  ].
  Definition function_addrs : list addr := [
    addr_main2; addr_call_foo; addr_foo; addr_next;
    addr_drop_option; addr_drop_ref; addr_drop_unit; addr_drop_i32
  ].

  Definition initial_heap_locs : list loc := [].
  Definition initial_heap_values : list val.val := [].
  Definition static_locs : gmap string loc := ∅.
  Definition static_types `{!typeGS Σ} : gmap string btype := ∅.
  Definition thread_mains : list loc := [fn_loc addr_main2].

  Arguments trait_ctx_wf : clear simpl.

  Lemma main2_adequate (config : RadiumConfig) hs σ n κs t2 σ2
    (Hopt0 : syn_type_is_layoutable UnitSynType)
    (Hopt1 : syn_type_is_layoutable (Option_els UnitSynType))
    (Hopt2 : syn_type_is_layoutable (Option_Some_sls UnitSynType))
    (HoptNone : syn_type_is_layoutable (Option_None_sls UnitSynType)) :
    alloc_new_blocks initial_heap_state GlobalAlloc initial_heap_locs initial_heap_values hs →
    σ = initial_state hs 1 (fn_lists_to_fns function_addrs functions) →
    NoDup function_addrs →
    Forall (λ a, a ∈ USize) function_addrs →
    nsteps (Λ := c_lang config) n (initial_prog AllowUnwind <$> [(0, fn_loc addr_main2)], σ) κs (t2, σ2) →
    (∀ e2, e2 ∈ t2 → not_stuck e2 σ2).
  Proof.
    move => ? -> HNDfns HRANfns.
    adequacy_invert_forall HRANfns.

    set Σ : gFunctors := #[typeΣ].
    eapply (refinedrust_adequacy config AllowUnwind Σ thread_mains) => //.
    { adequacy_split_forall; done. }
    move => ? ?.
    exists static_locs, static_types => Hstatics.
    set (RRGS := {| refinedrust_typeGS := _; refinedrust_staticGS := Hstatics |}).
    iIntros "Hstatics Hfn".

    set (DropGlue_i32 := drop_glue_trivial_realization (RRGS:=RRGS) ZRT (IntSynType i32)).
    set (DropGlue_ref := drop_glue_trivial_realization (RRGS:=RRGS) (place_rfnRT ZRT) RefSynType).
    set (DropGlue_unit := drop_glue_trivial_realization (RRGS:=RRGS) unit UnitSynType).
    set (DropGlue_option := drop_glue_Option_realization (RRGS:=RRGS) unit UnitSynType
      (drop_glue_trivial_spec_attrs unit) DropGlue_unit).
    set (Iter_ref := REFTasIter_realization (RRGS:=RRGS) ZRT (IntSynType i32)
      (drop_glue_trivial_spec_attrs ZRT) DropGlue_i32).

    have Hin := I.
    repeat (
      move: {Hin} HNDfns => /NoDup_cons[Hin HNDfns];
      iDestruct (fn_lists_to_fns_cons with "Hfn") as "[#? Hfn]" => //
    ).

    iAssert (
      typed_function 0%nat (functions !!! 7%nat) (eq_refl, spec! ( *[]) : 0 | ( *[T_ty]) : [_],
        fn_spec_add_late_pre (type_of_drop_glue_trivial Z (IntSynType I32) <TY> T_ty <INST!>)
          (λ π, DropGlue_i32.(trait_ctx_wf) -[] -[T_ty] π)) ∗
      typed_function 0%nat (functions !!! 6%nat) (eq_refl, spec! ( *[]) : 0 | ( *[T_ty]) : [_],
        fn_spec_add_late_pre (type_of_drop_glue_trivial unit UnitSynType <TY> T_ty <INST!>)
          (λ π, DropGlue_unit.(trait_ctx_wf) -[] -[T_ty] π)) ∗
      typed_function 0%nat (functions !!! 5%nat) (eq_refl, spec! ( *[]) : 0 | ( *[T_ty]) : [_],
        fn_spec_add_late_pre (type_of_drop_glue_trivial (place_rfnRT Z) RefSynType <TY> T_ty <INST!>)
          (λ π, DropGlue_ref.(trait_ctx_wf) -[] -[T_ty] π)) ∗
      typed_function 0%nat (functions !!! 4%nat) (eq_refl, spec! ( *[]) : 0 | ( *[T_ty]) : [_],
        fn_spec_add_late_pre (type_of_drop_glue_Option unit UnitSynType
          (drop_glue_trivial_spec_attrs unit) <TY> T_ty <INST!>)
          (λ π, DropGlue_option.(trait_ctx_wf) -[] -[T_ty] π)) ∗
      typed_function 0%nat (functions !!! 3%nat) (eq_refl, spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : [_],
        fn_spec_add_late_pre (type_of_REFTasIter_next Z (IntSynType I32)
          (drop_glue_trivial_spec_attrs Z) <TY> T_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>)
          (λ π, typaram_wf _ (IntSynType i32) T_ty ∗
            (trait_incl_of_REFTasIter_next Z (IntSynType i32) (drop_glue_trivial_spec_attrs Z) DropGlue_i32
              -[ulft_1; ulft_2] -[T_ty]) π)) ∗
      typed_function 0%nat (functions !!! 2%nat) (eq_refl, spec! ( *[]) : 0 | ( *[T_ty; Item_ty]) : [_; _],
        fn_spec_add_late_pre (type_of_foo (place_rfnRT Z) unit RefSynType UnitSynType
          (REFTasIter_spec_attrs Z (drop_glue_trivial_spec_attrs Z))
          (drop_glue_trivial_spec_attrs (place_rfnRT Z)) (drop_glue_trivial_spec_attrs unit)
          <TY> T_ty <TY> Item_ty <INST!>)
          (λ π, typaram_wf _ RefSynType T_ty ∗ typaram_wf _ UnitSynType Item_ty ∗
            (trait_incl_of_foo (place_rfnRT Z) unit RefSynType UnitSynType
              (REFTasIter_spec_attrs Z (drop_glue_trivial_spec_attrs Z)) Iter_ref
              (drop_glue_trivial_spec_attrs (place_rfnRT Z)) DropGlue_ref
              (drop_glue_trivial_spec_attrs unit) DropGlue_unit -[] -[T_ty; Item_ty]) π ∗
            introduce_direct (DropGlue_option.(trait_ctx_wf) -[] -[Item_ty] π))) ∗
      typed_function 0%nat (functions !!! 1%nat) (eq_refl, spec! ( *[]) : 0 | ( *[]) : [],
        fn_spec_add_late_pre (type_of_call_foo Z (IntSynType I32)
          (drop_glue_trivial_spec_attrs Z) <TY> (int i32) <INST!>)
          (λ _, True)%I) ∗
      typed_function 0%nat (functions !!! 0%nat) (eq_refl, type_of_main2)
    )%I as "Ha".
    { simpl.
      iLöb as "IH". iDestruct "IH" as "(? & ? & ? & ? & ? & ? & ? & ?)".
      subst H.
      repeat iSplit.
      - iApply (drop_glue_trivial_proof (RRGS:=RRGS)).
        1: eexists; solve_layout_alg.
      - iApply (drop_glue_trivial_proof (RRGS:=RRGS)).
        1: eexists; solve_layout_alg.
      - iApply (drop_glue_trivial_proof (RRGS:=RRGS)).
        1: eexists; solve_layout_alg.
      - iApply typed_function_equiv; iSplit.
        { iApply (drop_glue_Option_proof (RRGS:=RRGS) 0 unit UnitSynType
            (drop_glue_trivial_spec_attrs unit) DropGlue_unit).
          1-3: done.
          1: adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
          all: try (split; [assumption | idtac]);
            try (liInst Hevar_p DropGlue_T_tys_inst); rep liRStep. }
        rep liRStep.
        liInst Hevar_p DropGlue_T_tys_inst.
        split; [exact H9 | rep liRStep].
      - iApply typed_function_equiv; iSplit.
        { iApply (REFTasIter_next_proof (RRGS:=RRGS) 0 Z (IntSynType i32)
            (drop_glue_trivial_spec_attrs Z) DropGlue_i32).
          1: eexists; solve_layout_alg.
          1: exact Hopt1.
          1: exact HoptNone. }
        rep liRStep.
        liInst Hevar_p DropGlue_T_tys_inst.
        split; [exact H9 | rep liRStep].
      - iApply typed_function_equiv; iSplit.
        { iApply (foo_proof (RRGS:=RRGS) 0 (place_rfnRT Z) unit RefSynType UnitSynType
            (REFTasIter_spec_attrs Z (drop_glue_trivial_spec_attrs Z)) Iter_ref
            (drop_glue_trivial_spec_attrs (place_rfnRT Z)) DropGlue_ref
            (drop_glue_trivial_spec_attrs unit) DropGlue_unit).
          1: eexists; solve_layout_alg.
          1: exact Hopt0.
          1: exact Hopt1.
          1: adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
          1: adequacy_solve_function_ptr uconstr:(fun x => x)
            uconstr:(λ _ (tys : plist type [ZRT; place_rfnRT ZRT; (unit : RT)]),
              let '( *[T_ty; _; _]) := tys in -[T_ty]).
          1: liInst Hevar_p DropGlue_T_tys_inst; split; [exact H13 | rep liRStep].
          1: adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
          1: liInst Hevar_p DropGlue_T_tys_inst; split; [exact H9 | rep liRStep]. }
        rep liRStep.
        liInst Hevar_p Iter_T_lfts_inst.
        liInst Hevar_p0 Iter_T_tys_inst.
        split; [exact H11 | rep liRStep].
        liInst Hevar_p DropGlue_T_tys_inst.
        split; [exact H14 | rep liRStep].
        liInst Hevar_p DropGlue_T_tys_inst0.
        split; [exact H18 | rep liRStep].
        liInst Hevar_p DropGlue_TasIter_Item_tys_inst.
        split; [exact H22 | rep liRStep].
      - iApply typed_function_equiv; iSplit.
        { iApply (typed_function_specialize _ _ _ _ _
          (λ _, -[] : prod_vec lft 0) (λ _ _, -[int i32])).
        iApply (call_foo_proof (RRGS:=RRGS) 0 Z (IntSynType i32)
            (drop_glue_trivial_spec_attrs Z) DropGlue_i32 _ _
            (spec! ( *[κ]) : 1 | ( *[T]) : [ZRT],
              foo_REFW_linking_requirement ZRT
                (IntSynType i32) (drop_glue_trivial_spec_attrs ZRT) DropGlue_i32 κ T)).
          1: eexists; solve_layout_alg.
          1: adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
          (* Expose the supplied witnesses before Lithium creates target evars. *)
           1: unfold from_assumption_hint, foo_REFW_linking_requirement.
          1: adequacy_solve_function_ptr uconstr:(λ _, -[] : prod_vec lft 0)
            uconstr:(λ (κ : prod_vec lft 1) (tys : plist type [ZRT]),
              let '( *[vlft3]) := κ in let '( *[W_ty]) := tys in
              -[shr_ref vlft3 W_ty; unit_t]).
          liInst Hevar_p Iter_T_lfts_inst.
          liInst Hevar_p0 Iter_T_tys_inst.
          split; [exact H9 | rep liRStep].
          liInst Hevar_p DropGlue_T_tys_inst.
          split; [exact H12 | rep liRStep].
          liInst Hevar_p DropGlue_T_tys_inst0.
          split; [exact H16 | rep liRStep].
          liInst Hevar_p DropGlue_TasIter_Item_tys_inst.
          split; [exact H20 | rep liRStep]. }
        simpl. rep liRStep.
        liInst Hevar_p (int i32).
        split; [solve_trait_incl | rep liRStep].
        1: iSplit; [iIntros (vlft3) | done].
         1: unfold foo_REFW_linking_requirement.
        1: rep liRStep.
        1: liInst Hevar_p vlft3.
        1: liInst Hevar_p0 (int i32).
        1: split; [solve_trait_incl | rep liRStep].
        1: liInst Hevar_p (int i32).
        1: split; [solve_trait_incl | rep liRStep].
        1: liInst Hevar_p (shr_ref vlft3 (int i32)).
        1: split; [solve_trait_incl | rep liRStep].
        1: liInst Hevar_p unit_t.
        1: split; [solve_trait_incl | rep liRStep].
        1: unfold introduce_direct.
        1: rep liRStep.
        1: liInst Hevar_p unit_t.
        1: split; [solve_trait_incl | rep liRStep].
        1: liFromSyntaxGoal.
        1: iPureIntro; reflexivity.
        1: liShow.
        1: iSplit; [iModIntro; iIntros (π) "_ _"; repeat iSplit; done
                   | iIntros (vr a2) "_ Hvr"; iExists a2; iFrame; done].
      - adequacy_solve_typed_function (main2_proof (RRGS:=RRGS) 0 (fn_loc addr_call_foo)
          (spec! ( *[]) : 0 | ( *[]) : [], λ _, True%I)).
        1: adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
        all: rep liRStep.
    }
    iEval (try rewrite !bi.sep_assoc) in "Ha".
    iDestruct "Ha" as "(_ & Hmain)".
    iModIntro. iSplitL => //.
    all: iExists True%I; iSplitR.
    { adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x). }
    done.

    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
  Qed.
End adequate.
