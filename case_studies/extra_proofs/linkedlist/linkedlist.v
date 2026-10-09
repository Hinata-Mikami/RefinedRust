From refinedrust Require Import typing.

Section linkedlist.
  Context `{!typeGS Σ} {rt : RT}.

  Definition linkedlist_node π (ty : type rt) sls (locs : list loc) i x : iProp Σ :=
    ∃ l next prev : loc, ⌜locs !! i = Some l⌝ ∗
      ⌜(locs ++ [NULL_loc]) !! S i = Some next⌝ ∗
      ⌜(NULL_loc :: locs) !! i = Some prev⌝ ∗
      guarded true (l ◁ₗ[π, Owned] #( *[#x; #next; #prev]) @
        ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t]) ∗
      freeable_nz l (ly_size (use_struct_layout_alg' sls)) 1 HeapAlloc.

  Definition linkedlist_node_shared π κ (ty : type rt) sls (locs : list loc) i x : iProp Σ :=
    ∃ l next prev : loc, ⌜locs !! i = Some l⌝ ∗
      ⌜(locs ++ [NULL_loc]) !! S i = Some next⌝ ∗
      ⌜(NULL_loc :: locs) !! i = Some prev⌝ ∗
      guarded false (l ◁ₗ[π, Shared κ] #( *[#x; #next; #prev]) @
        ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t]) ∗ True.

  Global Program Instance linkedlist_nodes_shareable π κ (ty : type rt) sls locs xs :
    Shareable π κ (ty_lfts ty) xs
      ([∗ list] i ↦ x ∈ xs, linkedlist_node π ty sls locs i x) := {|
      shareable_prop := ([∗ list] i ↦ x ∈ xs,
        ∃ l next prev : loc, ⌜locs !! i = Some l⌝ ∗
          ⌜(locs ++ [NULL_loc]) !! S i = Some next⌝ ∗
          ⌜(NULL_loc :: locs) !! i = Some prev⌝ ∗
          guarded false (l ◁ₗ[π, Shared κ] #( *[#x; #next; #prev]) @
            ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t]) ∗ True)%I
    |}.
  Next Obligation.
    intros π κ ty sls locs xs Houter F G q HF.
    iIntros "#[LFT LLCTX] #Hna Htok Htoki Hb HT".
    iCombine ("Htok Htoki") as "Htok".
    iEval (rewrite lft_tok_sep) in "Htok".
    iPoseProof (Fractional_split_big_sepL (λ q, (q.[_])%I)
      (length xs) with "Htok") as "(%qs & %Hlen & Htoks & Hclose)".
    set (κ' := κ ⊓ lft_intersect_list (ty_lfts ty)).
    iApply fupd_logical_step.
    iMod (bor_big_sepL with "LFT Hb") as "Hb"; first done.
    iAssert ([∗ list] i ↦ x; q' ∈ xs; qs,
      &{κ} (linkedlist_node π ty sls locs i x) ∗ q'.[κ'])%I
      with "[Htoks Hb]" as "Hb".
    { iApply big_sepL2_sep_sepL_r. iFrame "Htoks".
      iApply big_sepL2_const_sepL_l. iSplit; first by iPureIntro; lia. done. }
    iAssert ([∗ list] i ↦ x; q' ∈ xs; qs,
      logical_step F (linkedlist_node_shared π κ ty sls locs i x ∗ q'.[κ']))%I
      with "[Hb]" as "Hb".
    { iApply (big_sepL2_wand with "Hb"). iApply big_sepL2_intro; first by lia.
      iModIntro. iIntros (i x q' Hlook Hlookq) "(Hb & Htok)".
      have Hxc : is_xrfn x.
      { apply is_xrfn_list_iff in Houter. eapply Forall_lookup_1; eauto. }
      have Hx : IsXrfn x by constructor.
      pose (Shr := (_ : Shareable π κ (ty_lfts ty) xs
        (linkedlist_node π ty sls locs i x))).
      subst κ'. rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htoki)".
      iApply (Shr.(shareable_proof) Houter
        with "[$LFT $LLCTX] Hna Htok Htoki Hb"); first done.
      iApply logical_step_intro. iIntros "(Hnode & Htok & Htoki)".
      iFrame "Htok Htoki". iExact "Hnode". }
    iPoseProof (logical_step_big_sepL2 with "Hb") as "Hb".
    iModIntro. iApply (logical_step_compose with "Hb").
    iApply (logical_step_wand with "HT"). iIntros "HT Hb".
    iPoseProof (big_sepL2_sep_sepL_r with "Hb") as "(Hb & Htoks)".
    iPoseProof ("Hclose" with "Htoks") as "Htok".
    iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & Hb)".
    iApply "HT". rewrite lft_tok_sep. iFrame.
  Qed.
End linkedlist.
