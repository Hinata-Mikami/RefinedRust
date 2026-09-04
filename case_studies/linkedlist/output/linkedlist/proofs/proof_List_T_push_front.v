From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_push_front.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma List_T_push_front_proof (π : thread_id) :
  List_T_push_front_lemma π.
Proof.
  List_T_push_front_prelude.

  rep <-! liRStep.
  { rep liRStep.
    liInst Hevar_locs (x' :: locs).
    liInst Hevar_rf ($#@{ T_rt } value :: <$#@{ T_rt }>self).
    move: Hlocs.
    rep liRStep. }
  { revert Hlocs.
    rep <-! liRStep; liShow.
    (* Isolate the old head before changing its backlink. *)
    iRename select ([∗ list] i ↦ _ ∈ _, _)%I into "Hold".
    odestruct (lookup_lt_is_Some_2 self 0 _) as (first_elem & Hlook_first).
    { lia. }
    iPoseProof (big_sepL_delete _ _ 0 with "Hold") as "(Hfirst & Hrest)".
    { rewrite list_lookup_fmap Hlook_first //. }
    iRevert "Hfirst".
    rep <-! liRStep; liShow.
    apply_update (updateable_strip_guards).
    rep <-! liRStep; liShow.
    iAcquireCredits as "Hcred1".
    iAcquireCredits as "Hcred2".
    rename select (head locs = Some hd_ptr) into Hhead_loc.
    have Hhead_eq : hd_ptr = l0.
    { rewrite head_lookup in Hhead_loc. congruence. }
    subst hd_ptr.
    rename select (if bool_decide _ then _ = Some lnext else _ = Some lnext)
      into Hfirst_next_case.
    have Hnext_first : (locs ++ [NULL_loc]) !! 1%nat = Some lnext.
    { apply (proj2 (simpl_lookup_app locs [NULL_loc] 1%nat lnext)).
      exact Hfirst_next_case. }
    rep liRStep; liShow.
    liInst Hevar_locs (x' :: locs).
    liInst Hevar_rf ($#@{ T_rt } value :: <$#@{ T_rt }>self).
    rep liRStep; liShow.
    iApply (prove_with_subtype_stratify l0).
    rep liRStep; liShow.
    iApply prove_with_subtype_default.
    iRename select (freeable_nz l0 _ _ _) into "Hfree_first".
    iSplitL "Hrest Hfree_first Hcred1".
    { iIntros "Hfirst_updated".
      (* Transport untouched nodes to the prepended location list. *)
      iAssert ([∗ list] k ↦ xk ∈ <$#@{ T_rt }> self,
        if decide (k = 0%nat) then emp else
          ∃ lk lnextk lprevk : loc,
            ⌜locs !! k = Some lk⌝ ∗
            ⌜(locs ++ [NULL_loc]) !! S k = Some lnextk⌝ ∗
            ⌜(x' :: locs) !! k = Some lprevk⌝ ∗
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
        have Hprev_lookup_new : (x' :: locs) !! k = Some lprevk.
        { destruct k as [|k]; first done. simpl. exact Hprev_lookup. }
        iExists lk, lnextk, lprevk.
        iSplit; first (iPureIntro; exact Hloc_lookup).
        iSplit; first (iPureIntro; exact Hnext_lookup).
        iSplit; first (iPureIntro; exact Hprev_lookup_new).
        iFrame. }
      rep liRStep; liShow.
      (* Re-guard and insert the updated old head at index zero. *)
      iAssert (guarded true
        (l0 ◁ₗ[π, Owned] #( *[#$#@{ T_rt } first_elem; #lnext; #x']) @
          ◁(Link_ty T_rt <TY> T_ty <INST!>)))%I
        with "[Hcred1 Hfirst_updated]" as "Hfirst_guarded".
      { iApply guarded_intro. iFrame. }
      iAssert (∃ lk lnextk lprevk : loc,
        ⌜locs !! 0%nat = Some lk⌝ ∗
        ⌜(locs ++ [NULL_loc]) !! 1%nat = Some lnextk⌝ ∗
        ⌜(x' :: locs) !! 0%nat = Some lprevk⌝ ∗
        guarded true (lk ◁ₗ[π, Owned]
          #( *[#$#@{ T_rt } first_elem; #lnextk; #lprevk]) @
          ◁(Link_ty T_rt <TY> T_ty <INST!>)) ∗
        freeable_nz lk
          (sum_list
            (ly_size <$> (sl_members
              (use_struct_layout_alg' (Link_sls (st_of T_ty MetaNone)))).*2))
          1 HeapAlloc)%I
        with "[Hfirst_guarded Hfree_first]" as "Hfirst_node".
      { iExists l0, lnext, x'.
        rep liRStep. done. }
      iApply (big_sepL_delete _ _ 0).
      { rewrite list_lookup_fmap. rewrite Hlook_first //. }
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
    }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - match goal with H : last locs = Some _ |- _ => rewrite last_cons H // end.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
