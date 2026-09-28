From radium Require Import lang notation.
From refinedrust Require Import typing shims adequacy.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy.
From refinedrust.examples.adequacy.proofs Require Import proof_main proof_callee.


Section adequate.
  Context `{!LayoutAlg}.

  (** addresses for all monomorphized functions *)
  Context (
    addr_main
    addr_callee
    addr_drop_glue_tuple_i32_i32
    addr_drop_glue_trivial_i32
    : addr).

  (** All monormorphized function source codes of the program *)
  Definition functions : list function := [
    main_def (fn_loc addr_callee);
    callee_def (fn_loc addr_drop_glue_tuple_i32_i32) (IntSynType i32);
    drop_glue_tuple2_def (fn_loc addr_drop_glue_trivial_i32) (fn_loc addr_drop_glue_trivial_i32) (IntSynType i32) (IntSynType i32);
    drop_glue_trivial_def (IntSynType i32)
  ].
  Definition function_addrs : list addr := [
    addr_main;
    addr_callee;
    addr_drop_glue_tuple_i32_i32;
    addr_drop_glue_trivial_i32
  ].

  (** Initial heap values *)
  Definition initial_heap_locs : list loc := [

  ].
  Definition initial_heap_values : list val.val := [
  ].

  (** Static variables *)
  Definition static_locs : gmap string loc :=
    ∅
.
  Definition static_types `{!typeGS Σ} : gmap string btype :=
    ∅
  .

  Ltac unfold_defs :=
    idtac
  .

  (** Main functions of different threads *)
  Definition thread_mains : list loc := [
    fn_loc addr_main
  ].

  Arguments trait_ctx_wf : clear simpl.

  Lemma main_adequate (config : RadiumConfig) unwind_policy hs σ n κs t2 σ2
    (Halg1 : syn_type_is_layoutable (tuple2_sls (IntSynType i32) (IntSynType i32))) :
    alloc_new_blocks initial_heap_state GlobalAlloc initial_heap_locs initial_heap_values hs →
    σ = initial_state hs 1 (fn_lists_to_fns function_addrs functions) →

    (** the function addresses have been picked to be distinct *)
    NoDup function_addrs →
    (** the function addresses have to be in USize *)
    Forall (λ a, a ∈ USize) function_addrs →

    nsteps (Λ := c_lang config) n (initial_prog unwind_policy <$> [(0, fn_loc addr_main)], σ) κs (t2, σ2) →
    (∀ e2, e2 ∈ t2 → not_stuck e2 σ2).
  Proof.
    move => ? -> HNDfns HRANfns.
    adequacy_invert_forall HRANfns.

    set Σ : gFunctors := #[typeΣ].
    eapply (refinedrust_adequacy config unwind_policy Σ thread_mains) => //.
    { adequacy_split_forall; done. }
    move => ? ?.
    exists static_locs, static_types => Hstatics.
    set (RRGS := {| refinedrust_typeGS := _; refinedrust_staticGS := Hstatics |}).
    iIntros "Hstatics Hfn".

    (* used trait realizations *)
    set (DropGlue_T_realization :=
      drop_glue_trivial_realization (RRGS:=RRGS) ZRT (IntSynType i32)).
    set (DropGlue_i32_realization :=
      trait_spec_realization_instantiate DropGlue_T_realization -[] -[int i32]).
    set (DropGlue_tuple_realization :=
      drop_glue_tuple2_realization (RRGS:=RRGS)
        ZRT ZRT (IntSynType i32) (IntSynType i32)
        (drop_glue_trivial_spec_attrs ZRT) DropGlue_T_realization
        (drop_glue_trivial_spec_attrs ZRT) DropGlue_i32_realization).

    (* split [fntbl_entry] for all functions *)
    have Hin := I.
    repeat (
        move: {Hin} HNDfns => /NoDup_cons[Hin HNDfns];
        iDestruct (fn_lists_to_fns_cons with "Hfn") as "[#? Hfn]" => //
    ).

    (* assert typed functions *)
    iAssert (
      typed_function 0%nat (functions !!! 3%nat) (eq_refl, spec! ( *[]) : 0 | ( *[T_ty]) : [_],
        fn_spec_add_late_pre
          (type_of_drop_glue_trivial Z (IntSynType I32) <TY> T_ty <INST!>)
          (λ π, DropGlue_T_realization.(trait_ctx_wf) -[] -[T_ty] π)) ∗
      typed_function 0%nat (functions !!! 2%nat) (eq_refl, spec! ( *[]) : 0 | ( *[T_ty]) : [_],
        fn_spec_add_late_pre
          (type_of_drop_glue_tuple2 Z Z (IntSynType I32) (IntSynType I32)
            (drop_glue_trivial_spec_attrs ZRT) (drop_glue_trivial_spec_attrs ZRT)
            <TY> T_ty <TY> int i32 <INST!>)
          (λ π, DropGlue_tuple_realization.(trait_ctx_wf) -[] -[T_ty; int i32] π)) ∗
      typed_function 0%nat (functions !!! 1%nat) (eq_refl, spec! ( *[]) : 0 | ( *[T_ty]) : [_],
        fn_spec_add_late_pre (type_of_callee Z (IntSynType I32) (drop_glue_trivial_spec_attrs ZRT) <TY> T_ty <INST!>) (λ π,
          typaram_wf _ (IntSynType i32) T_ty ∗
           (((trait_incl_of_callee ZRT (IntSynType i32) (drop_glue_trivial_spec_attrs ZRT) DropGlue_T_realization)
            -[] -[T_ty]) π) ∗
          introduce_direct
            (DropGlue_tuple_realization.(trait_ctx_wf) -[] -[T_ty; int i32] π))) ∗
      typed_function 0%nat (functions !!! 0%nat) (eq_refl, type_of_main)
    )%I as "Ha".
    { simpl.
      iLöb as "IH". iDestruct "IH" as "(? & ? & ? & ?)".
      subst H.
      repeat iSplit.
      - (* drop_glue_trivial I32 *)
        iApply typed_function_equiv; iSplit.
        { iApply (drop_glue_trivial_proof (RRGS:=RRGS)).
          1: eexists; solve_layout_alg.
        }
        rep liRStep.
      - (* drop_glue_tuple2 I32 I32 *)
        iApply typed_function_equiv; iSplit.
        { iApply (typed_function_specialize _ _ _ _ _
            (λ _, -[] : prod_vec lft 0)
            (λ _ (tys : plist type [ZRT]),
              let '( *[T_ty]) := tys in -[T_ty; int i32])).
          iApply (drop_glue_tuple2_proof (RRGS:=RRGS) 0
            ZRT ZRT (IntSynType i32) (IntSynType i32)
            (drop_glue_trivial_spec_attrs ZRT) (drop_glue_trivial_spec_attrs ZRT)
            DropGlue_T_realization DropGlue_i32_realization).
          1: done.
          1: adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
          1: adequacy_solve_function_ptr uconstr:(λ _, -[] : prod_vec lft 0) uconstr:(λ _ _, -[int i32]).
        }
        simpl.
        rep liRStep.
        all: liInst Hevar_p tys0.
        all: rep liRStep.
      - (* callee I32 *)
        iApply typed_function_equiv; iSplit.
        { iApply (callee_proof (RRGS:=RRGS) 0
            ZRT (IntSynType i32) (drop_glue_trivial_spec_attrs ZRT) DropGlue_T_realization).
          1: eexists; solve_layout_alg.
          1: done.
          1: adequacy_solve_function_ptr uconstr:(fun x => x) uconstr:(fun _ x => x).
          all: liInst Hevar_p tys0; rep liRStep.
        }
        rep liRStep.
        all: liInst Hevar_p DropGlue_T_tys_inst.
        all: rep liRStep.
      - (* main *)
        adequacy_solve_typed_function (main_proof (RRGS:=RRGS)).
        1: adequacy_solve_function_ptr uconstr:(λ _, -[] : prod_vec lft 0) uconstr:(λ _ _, -[int i32]).
        all: try (liInst Hevar_p (int i32)).
        all: rep liRStep.
        all: unfold introduce_direct.
        all: rep liRStep.
        all: try (liInst Hevar_p (int i32)).
        all: rep liRStep.
        iSplitL; [iExists -[], -[int i32]; iSplit;
          [iPureIntro; solve_trait_incl
          |simpl; iSplit;
            [iExists _; repeat iSplit;
              try (iPureIntro; solve [unshelve solve_ty_allows; init_cache; solve_goal]);
              try (iPureIntro; done); try done
            |iPureIntro; done]] | idtac].
        iSplitL; [iExists -[], -[]; iSplit;
          [iPureIntro; solve_trait_incl
          |simpl; iSplit;
            [iExists _; repeat iSplit;
              try (iPureIntro; solve [unshelve solve_ty_allows; init_cache; solve_goal]);
              try (iPureIntro; done); try done
            |iPureIntro; done]] | idtac].
        rep liRStep.
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
(*Print Assumptions main_adequate.*)
