From radium Require Import lang notation.
From refinedrust Require Import typing shims adequacy.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy.
From refinedrust.examples.adequacy.proofs Require Import proof_main.


Section adequate.
  Context `{!LayoutAlg}.

  (** addresses for all monomorphized functions *)
  Context (
    addr_main
    : addr).

  (** All monormorphized function source codes of the program *)
  Definition functions : list function := [
    main_def
  ].
  Definition function_addrs : list addr := [
    addr_main
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

  Ltac adequacy_invert_forall H :=
    repeat match type of H with
    | Forall _ [] =>
      clear H
    | Forall _ _ =>
      apply Forall_cons in H;
      destruct H as [? H]
    end.
  Ltac adequacy_split_forall :=
    repeat first [apply Forall_cons; split | by apply Forall_nil].

  Ltac adequacy_solve_typed_function lemma :=
    iApply typed_function_equiv; iSplit;
      [ iApply (lemma ) => //
        (*; iExists _; repeat iSplit => //*)
      | rep liRStep
      ].

  Ltac adequacy_solve_function_ptr :=
    rewrite /ty_own_val/=; iR;
    iExists _;
    iSplitR; [ iPureIntro; by apply val_to_loc_Some_l2v| ];
    iSplitR; [ done | ];
    iSplitR; [ iPureIntro; simpl; repeat first [by apply Forall2_nil | apply Forall2_cons; split; [shelve_sidecond | ]] | ];
    iNext; simpl;
    iApply typed_function_equiv; iSplit; first done;
    rep liRStep.

  Lemma main_adequate hs σ n κs t2 σ2 :
    alloc_new_blocks initial_heap_state GlobalAlloc initial_heap_locs initial_heap_values hs →
    σ = initial_state hs 1 (fn_lists_to_fns function_addrs functions) →

    (** the function addresses have been picked to be distinct *)
    NoDup function_addrs →
    (** the function addresses have to be in USize *)
    Forall (λ a, a ∈ USize) function_addrs →

    nsteps (Λ := c_lang) n (initial_prog <$> [(0, fn_loc addr_main)], σ) κs (t2, σ2) →
    (∀ e2, e2 ∈ t2 → not_stuck e2 σ2).
  Proof.
    move => ? -> HNDfns HRANfns.
    adequacy_invert_forall HRANfns.

    set Σ : gFunctors := #[typeΣ].
    eapply (refinedrust_adequacy Σ thread_mains) => //.
    { adequacy_split_forall; done. }
    move => ? ?.
    exists static_locs, static_types => Hstatics.
    set (RRGS := {| refinedrust_typeGS := _; refinedrust_staticGS := Hstatics |}).
    iIntros "Hstatics Hfn".

    (* split [fntbl_entry] for all functions *)
    have Hin := I.
    repeat (
        move: {Hin} HNDfns => /NoDup_cons[Hin HNDfns];
        iDestruct (fn_lists_to_fns_cons with "Hfn") as "[#? Hfn]" => //
    ).

    (* assert typed functions *)
    iAssert (
      typed_function 0%nat (functions !!! 0%nat) (eq_refl, type_of_main)
    )%I as "Ha".
    { simpl.
      iLöb as "IH". iDestruct "IH" as "?".
      subst H.
      repeat iSplit.
      - (* main *)
        adequacy_solve_typed_function (main_proof (RRGS:=RRGS)).
    }
    iEval (try rewrite !bi.sep_assoc) in "Ha".
    iDestruct "Ha" as "Hmain".
    iModIntro. iSplitL => //.
    all: iExists True%I; iSplitR.
    { adequacy_solve_function_ptr. }
    done.

    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
  Qed.
End adequate.
(*Print Assumptions main_adequate.*)

