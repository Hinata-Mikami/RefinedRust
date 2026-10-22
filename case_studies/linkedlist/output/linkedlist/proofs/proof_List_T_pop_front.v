From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_pop_front.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma List_T_pop_front_proof (π : thread_id) :
  List_T_pop_front_lemma π.
Proof.
  List_T_pop_front_prelude.

  rep <-! liRStep; liShow.
  move: Hlocs.
  rep <-! liRStep; liShow.
  iRename select ([∗ list] _ ↦ _ ∈ _, _)%I into "Hels".
  destruct self as [ | head_el self]; first done.
  rename select (head locs = Some _) into Hhead.
  apply head_Some in Hhead as (locs' & ->).
  (* Remove and deallocate the old head. *)
  iEval (unfold linkedlist_node) in "Hels".
  iRevert "Hels". simpl.
  liRStepUntil typed_call.
  apply_update updateable_strip_guards.

  rep <-! liRStep. liShow.
  iRename select ([∗ list] _ ↦ _ ∈ _, _)%I into "Hels_tail".
  rename select (if bool_decide _ then _ else _) into Hnext_case.
  have Hlocs_nonempty : (0 < length locs')%nat.
  { destruct (decide (0 < length locs'))%nat as [Hnonempty | Hempty]; first exact Hnonempty.
    move: Hnext_case. rewrite bool_decide_false; last lia.
    intros [= Hnull]. subst lnext. done. }
  have Hnext_head : locs' !! 0%nat = Some lnext.
  { move: Hnext_case. rewrite bool_decide_true; last exact Hlocs_nonempty. done. }
  odestruct (lookup_lt_is_Some_2 self 0 _) as (next_elem & Hlook_next).
  { rewrite -Hlen_eq. exact Hlocs_nonempty. }
  iPoseProof (big_sepL_delete _ _ 0 with "Hels_tail") as "(Hnew_first & Hrest)".
  { rewrite list_lookup_fmap Hlook_next //. }
  (* Isolate and update the new head's prev pointer. *)
  iRevert "Hnew_first".
  rep <-! liRStep; liShow.
  apply_update (updateable_strip_guards).
  rep <-! liRStep; liShow.
  iAcquireCredits as "Hcred1".
  iAcquireCredits as "Hcred2".
  rep liRStep; liShow.

  rename select (if bool_decide _ then _ = Some lnext0 else _ = Some lnext0)
    into Hfirst_next_case.
  have Hnext_first : (locs' ++ [NULL_loc]) !! 1%nat = Some lnext0.
  { apply (proj2 (simpl_lookup_app locs' [NULL_loc] 1%nat lnext0)).
    exact Hfirst_next_case. }
  liInst Hevar_rf (<$#@{ T_rt }> self).
  liInst Hevar_locs locs'.
  rep liRStep; liShow.
  iApply (prove_with_subtype_stratify l0).
  rep liRStep; liShow.
  iApply prove_with_subtype_default.
  iRename select (freeable_nz l0 _ _ _) into "Hfree_first".
  iSplitL "Hrest Hfree_first Hcred1".
  { iIntros "Hfirst_updated".
    (* Shift predecessor lookups and rebuild the shortened list. *)
    iAssert ([∗ list] k ↦ xk ∈ <$#@{ T_rt }> self,
      if decide (k = 0%nat) then emp else
        ∃ lk lnextk lprevk : loc,
          ⌜locs' !! k = Some lk⌝ ∗
          ⌜(locs' ++ [NULL_loc]) !! S k = Some lnextk⌝ ∗
          ⌜(NULL_loc :: locs') !! k = Some lprevk⌝ ∗
          guarded true (lk ◁ₗ[π, Owned]
            #( *[#xk; #lnextk; #lprevk]) @ ◁(Link_ty T_rt <TY> T_ty <INST!>)) ∗
          freeable_nz lk
            (sum_list
              (ly_size <$> (sl_members
                (use_struct_layout_alg' (Link_sls (st_of T_ty MetaNone)))).*2))
            1 HeapAlloc)%I with "[Hrest]" as "Hrest_new".
    { iApply (big_sepL_impl with "Hrest").
      iModIntro. iIntros (k xk Hxk) "Hnode".
      destruct (decide (k = 0%nat)); first done.
      iDestruct "Hnode" as (lk lnextk lprevk)
        "(%Hloc_lookup & %Hnext_lookup & %Hprev_lookup & Hguard & Hfree_node)".
      have Hprev_lookup_new : (NULL_loc :: locs') !! k = Some lprevk.
      { destruct k as [|k]; first done. simpl. exact Hprev_lookup. }
      iExists lk, lnextk, lprevk.
      iSplit; first (iPureIntro; exact Hloc_lookup).
      iSplit; first (iPureIntro; exact Hnext_lookup).
      iSplit; first (iPureIntro; exact Hprev_lookup_new).
      iFrame. }
    rep liRStep; liShow.
    iAssert (guarded true
      (l0 ◁ₗ[π, Owned] #( *[#$#@{ T_rt } next_elem; #lnext0; #NULL_loc]) @
        ◁(Link_ty T_rt <TY> T_ty <INST!>)))%I
      with "[Hcred1 Hfirst_updated]" as "Hfirst_guarded".
    { iApply guarded_intro. iFrame. }
    iAssert (∃ lk lnextk lprevk : loc,
      ⌜locs' !! 0%nat = Some lk⌝ ∗
      ⌜(locs' ++ [NULL_loc]) !! 1%nat = Some lnextk⌝ ∗
      ⌜(NULL_loc :: locs') !! 0%nat = Some lprevk⌝ ∗
      guarded true (lk ◁ₗ[π, Owned]
        #( *[#$#@{ T_rt } next_elem; #lnextk; #lprevk]) @
        ◁(Link_ty T_rt <TY> T_ty <INST!>)) ∗
      freeable_nz lk
        (sum_list
          (ly_size <$> (sl_members
            (use_struct_layout_alg' (Link_sls (st_of T_ty MetaNone)))).*2))
        1 HeapAlloc)%I
      with "[Hfirst_guarded Hfree_first]" as "Hfirst_node".
    { iExists l0, lnext0, NULL_loc. rep liRStep. done. }
    iApply (big_sepL_delete _ _ 0).
    { rewrite list_lookup_fmap Hlook_next //. }
    rep liRStep; liShow.
    iApply (big_sepL_impl with "Hrest_new").
    iModIntro. iIntros (k xk Hxk) "Hnode".
    destruct (decide (k = 0%nat)); first done.
    iDestruct "Hnode" as (lk lnextk lprevk)
      "(%Hloc_lookup & %Hnext_lookup & %Hprev_lookup & Hguard & Hfree_node)".
    iExists lk, lnextk, lprevk.
    iSplit; first (iPureIntro; exact Hloc_lookup).
    iSplit; first (iPureIntro; exact Hnext_lookup).
    iSplit; first (iPureIntro; exact Hprev_lookup).
    iFrame. }
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: try rename select (if bool_decide _ then _ else _) into Hcase.
  - move: Hlocs. solve_goal.
  - move: Hlocs. solve_goal.
  - move: Hcase.
    case_bool_decide.
    + (* A null location contradicts ownership of the remaining node. *)
      intros Hlook.
      opose proof (Forall_lookup_1 _ _ _ _ _ Hlook) as Hnull; first done.
      done.
    + solve_goal.
  - move: Hcase.
    case_bool_decide.
    + intros Hlook.
      opose proof (Forall_lookup_1 _ _ _ _ _ Hlook) as Hnull; first done.
      done.
    + intros [= <-].
      destruct self; first done.
      destruct locs' as [ | l' locs']; simpl in *; lia.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  - rename select (locs' !! 0%nat = Some _) into Hfirst_loc.
    rewrite head_lookup. exact Hfirst_loc.
  - rename select (last (_ :: locs') = Some tl_ptr) into Hlast_loc.
    destruct locs' as [|next_loc locs']; first done.
    simpl in Hlast_loc |-*. exact Hlast_loc.
  all: print_remaining_sidecond.
Qed.
End proof.
