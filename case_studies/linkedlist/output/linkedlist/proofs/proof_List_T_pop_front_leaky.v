From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_pop_front_leaky.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma List_T_pop_front_leaky_proof (π : thread_id) :
  List_T_pop_front_leaky_lemma π.
Proof.
  List_T_pop_front_leaky_prelude.

  rep <-! liRStep; liShow.
  move: Hlocs.
  rep <-! liRStep. liShow.
  iRename select ([∗ list] _ ↦ _ ∈ _, _)%I into "Hels".
  destruct self as [ | head_el self]; first done.
  rename select (head locs = Some _) into Hhead.
  apply head_Some in Hhead as (locs' & ->).
  (* Extract the old head's value while intentionally retaining its allocation. *)
  iRevert "Hels". simpl.
  rep <-! liRStep; liShow.
  apply_update updateable_strip_guards.
  liRStepUntil typed_call.

  apply_update (updateable_extract_typed_value (l atst{Link_sls (st_of T_ty MetaNone)}ₗ "value")).
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
  (* Preserve stable names for the new head across the guarded update. *)
  iDestruct "Hnew_first" as (new_first next_next old_prev)
    "(%Hnew_first_lookup & %Hnext_next_lookup & %Hold_prev_lookup & Hnew_first_guard & Hnew_first_free)".
  have Hnew_first_eq : new_first = lnext by congruence.
  subst lnext.
  have Hold_prev_eq : old_prev = l.
  { simpl in Hold_prev_lookup. congruence. }
  subst old_prev.
  pose (new_first_loc := new_first).
  iAssert (∃ lk lnextk lprevk : loc,
    ⌜locs' !! 0%nat = Some lk⌝ ∗
    ⌜(locs' ++ [NULL_loc]) !! 1%nat = Some lnextk⌝ ∗
    ⌜(l :: locs') !! 0%nat = Some lprevk⌝ ∗
    guarded true (lk ◁ₗ[π, Owned]
      #( *[#$#@{ T_rt } next_elem; #lnextk; #lprevk]) @
      ◁(Link_ty T_rt <TY> T_ty <INST!>)))%I
    with "[Hnew_first_guard]" as "Hnew_first".
  { iExists new_first, next_next, l.
    iSplit; first (iPureIntro; exact Hnext_head).
    iSplit; first (iPureIntro; exact Hnext_next_lookup).
    iSplit; first (iPureIntro; done).
    iFrame. }
  iRevert "Hnew_first".
  rep <-! liRStep; liShow.
  apply_update (updateable_strip_guards).
  rep <-! liRStep; liShow.
  iAcquireCredits as "Hcred1".
  iAcquireCredits as "Hcred2".
  rep liRStep; liShow.

  liInst Hevar_rf (<$#@{ T_rt }> self).
  liInst Hevar_locs locs'.
  rep liRStep; liShow.
  iApply (prove_with_subtype_stratify new_first_loc).
  rep liRStep; liShow.
  iApply prove_with_subtype_default.
  iRename "Hnew_first_free" into "Hfree_first".
  iSplitL "Hrest Hfree_first Hcred1".
  { iIntros "Hfirst_updated".
    (* Rebuild the shortened list with a null predecessor at its head. *)
    have Hfirst_loc_eq : lk = new_first_loc.
    { unfold new_first_loc. congruence. }
    rename select (locs' !! 0%nat = Some lk) into Htarget_loc.
    rename select (if bool_decide _ then _ = Some lnextk else _ = Some lnextk)
      into Htarget_next_case.
    have Htarget_next : (locs' ++ [NULL_loc]) !! 1%nat = Some lnextk.
    { apply (proj2 (simpl_lookup_app locs' [NULL_loc] 1%nat lnextk)).
      exact Htarget_next_case. }
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
      iDestruct "Hnode" as (rest_loc rest_next rest_prev)
        "(%Hloc_lookup & %Hnext_lookup & %Hprev_lookup & Hguard & Hfree_node)".
      have Hprev_lookup_new : (NULL_loc :: locs') !! k = Some rest_prev.
      { destruct k as [|k]; first done. simpl. exact Hprev_lookup. }
      iExists rest_loc, rest_next, rest_prev.
      iSplit; first (iPureIntro; exact Hloc_lookup).
      iSplit; first (iPureIntro; exact Hnext_lookup).
      iSplit; first (iPureIntro; exact Hprev_lookup_new).
      iFrame. }
    rep liRStep; liShow.
    iAssert (guarded true
      (lk ◁ₗ[π, Owned] #( *[#$#@{ T_rt } next_elem; #lnextk; #NULL_loc]) @
        ◁(Link_ty T_rt <TY> T_ty <INST!>)))%I
      with "[Hcred1 Hfirst_updated]" as "Hfirst_guarded".
    { iApply guarded_intro.
      iSplitL "Hcred1"; first (simpl; iExact "Hcred1").
      iExact "Hfirst_updated". }
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
    { iExists lk, lnextk, NULL_loc.
      iSplit; first (iPureIntro; exact Htarget_loc).
      iSplit; first (iPureIntro; exact Htarget_next).
      iSplit; first (iPureIntro; done).
      iFrame. }
    iApply (big_sepL_delete _ _ 0).
    { rewrite list_lookup_fmap Hlook_next //. }
    rep liRStep; liShow.
    iApply (big_sepL_impl with "Hrest_new").
    iModIntro. iIntros (k xk Hxk) "Hnode".
    destruct (decide (k = 0%nat)); first done.
    iDestruct "Hnode" as (rest_loc rest_next rest_prev)
      "(%Hloc_lookup & %Hnext_lookup & %Hprev_lookup & Hguard & Hfree_node)".
    iExists rest_loc, rest_next, rest_prev.
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

  Unshelve.
  - rewrite head_lookup. done.
  - rename select (last (_ :: locs') = Some tl_ptr) into Hlast_loc.
    destruct locs' as [|next_loc locs']; first done.
    simpl in Hlast_loc |-*. exact Hlast_loc.
  all: print_remaining_sidecond.
Qed.
End proof.
