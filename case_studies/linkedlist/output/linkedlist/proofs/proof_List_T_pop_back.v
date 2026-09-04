From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_pop_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma List_T_pop_back_proof (π : thread_id) :
  List_T_pop_back_lemma π.
Proof.
  List_T_pop_back_prelude.

  rep <-! liRStep; liShow.
  move: Hlocs.
  rep <-! liRStep; liShow.
  (* Isolate the old tail so Box::from_raw can consume its allocation. *)
  iRename select ([∗ list] i ↦ _ ∈ _, _)%I into "Hels".
  odestruct (lookup_lt_is_Some_2 self (length self - 1) _) as
    (last_elem & Hlook_last_elem).
  { lia. }
  iPoseProof (big_sepL_delete _ _ (length self - 1) with "Hels") as
    "(Hlast & Hrest)".
  { rewrite list_lookup_fmap Hlook_last_elem //. }
  rename select (last locs = Some tl_ptr) into Hlast_loc.
  rewrite last_lookup in Hlast_loc.
  iRevert "Hlast".
  rep <-! liRStep; liShow.
  apply_update updateable_strip_guards.
  rep <-! liRStep; liShow.
  have Htail_index : (length self - 1 = Nat.pred (length locs))%nat.
  { rewrite Hlen_eq. lia. }
  have Htail_eq : l = tl_ptr.
  { rename select (locs !! (length self - 1)%nat = Some _) into Hlast. rewrite Htail_index in Hlast. congruence. }
  subst l.
  liRStepUntil typed_write.
  liRStep.
  rep <-! liRStep; liShow.
  rename select ((NULL_loc :: locs) !! (length self - 1)%nat = Some lprev)
    into Htail_prev_lookup.
  rename select (loc_a lprev ≠ 0) into Hlprev_nonnull.
  (* In the non-singleton branch, the old tail's predecessor is the new tail. *)
  have Hlen_two : (2 <= length self)%nat.
  { destruct (decide (2 <= length self)%nat) as [Htwo | Hshort]; first exact Htwo.
    have Hlen_one : length self = 1%nat by lia.
    rewrite Hlen_one in Htail_prev_lookup. simpl in Htail_prev_lookup.
    have Hlprev_null : lprev = NULL_loc by congruence.
    exfalso. apply Hlprev_nonnull. rewrite Hlprev_null. done. }
  have Hprev_loc : locs !! (length self - 2)%nat = Some lprev.
  { move: Htail_prev_lookup.
    replace (length self - 1)%nat with (S (length self - 2)) by lia.
    done. }
  odestruct (lookup_lt_is_Some_2 self (length self - 2) _) as
    (prev_elem & Hlook_prev_elem).
  { lia. }
  iPoseProof (big_sepL_delete _ _ (length self - 2) with "Hrest") as
    "(Hnew_last & Hrest_other)".
  { rewrite list_lookup_fmap Hlook_prev_elem //. }
  iRevert "Hnew_last".
  rewrite decide_False; last lia.
  (* Strip the predecessor's guard at the write backtracking point. *)
  rep <-! liRStep; liShow.
  apply_update (updateable_strip_guards).
  rep <-! liRStep; liShow.
  iAcquireCredits as "Hcred1".
  iAcquireCredits as "Hcred2".
  rep liRStep; liShow.
  liInst Hevar_rf (<$#@{ T_rt }> (removelast self)).
  liInst Hevar_locs (removelast locs).
  rep liRStep; liShow.
  iApply (prove_with_subtype_stratify l0).
  rep liRStep; liShow.
  iApply prove_with_subtype_default.
  iRename select (freeable_nz l0 _ _ _) into "Hfree_new_last".
  iSplitL "Hrest_other Hfree_new_last Hcred1".
  { iIntros "Hnew_last_updated".
    rep liRStep; liShow.
    (* Restrict untouched ownership to the list prefix before the removed tail. *)
    have Hrem_self_len : length (removelast self) = (length self - 1)%nat.
    { rewrite removelast_firstn_len length_take Nat.min_l; lia. }
    have Hrem_locs_len : length (removelast locs) = (length locs - 1)%nat.
    { rewrite removelast_firstn_len length_take Nat.min_l; lia. }
    have Hprefix_eq :
        take (length self - 1) (<$#@{ T_rt }> self) =
        <$#@{ T_rt }> (removelast self).
    { rewrite removelast_firstn_len.
      replace (Nat.pred (length self)) with (length self - 1)%nat by lia.
      apply symmetry, fmap_take. }
    iEval (rewrite (big_sepL_take_drop _ _ (length self - 1))) in "Hrest_other".
    iDestruct "Hrest_other" as "(Hprefix & Hremoved_tail)".
    iEval (rewrite Hprefix_eq) in "Hprefix".
    iAssert ([∗ list] k ↦ xk ∈ <$#@{ T_rt }> (removelast self),
      if decide (k = (length self - 2)%nat) then emp else
        ∃ node_loc node_next node_prev : loc,
          ⌜removelast locs !! k = Some node_loc⌝ ∗
          ⌜(removelast locs ++ [NULL_loc]) !! S k = Some node_next⌝ ∗
          ⌜(NULL_loc :: removelast locs) !! k = Some node_prev⌝ ∗
          guarded true (node_loc ◁ₗ[π, Owned]
            #( *[#xk; #node_next; #node_prev]) @
            ◁(Link_ty T_rt <TY> T_ty <INST!>)) ∗
          freeable_nz node_loc
            (sum_list
              (ly_size <$> (sl_members
                (use_struct_layout_alg' (Link_sls (st_of T_ty MetaNone)))).*2))
            1 HeapAlloc)%I with "[Hprefix]" as "Hprefix_new".
    { iApply (big_sepL_impl with "Hprefix").
      iModIntro. iIntros (k xk Hxk) "Hnode".
      destruct (decide (k = (length self - 2)%nat)); first done.
      have Hxk_bound : (k < length self - 2)%nat.
      { have Hbound := lookup_lt_Some _ _ _ Hxk.
        rewrite length_fmap Hrem_self_len in Hbound. lia. }
      have Hnot_tail : k ≠ (length self - 1)%nat by lia.
      iEval (rewrite decide_False; last exact Hnot_tail) in "Hnode".
      iDestruct "Hnode" as (node_loc node_next node_prev)
        "(%Hnode_loc & %Hnode_next & %Hnode_prev & Hnode_guard & Hnode_free)".
      have Hnode_loc_new : removelast locs !! k = Some node_loc.
      { rewrite removelast_firstn_len lookup_take_lt; first exact Hnode_loc.
        rewrite Hlen_eq. lia. }
      have Hnode_next_locs : locs !! S k = Some node_next.
      { rewrite lookup_app_l in Hnode_next; last lia. exact Hnode_next. }
      have Hnode_next_new :
          (removelast locs ++ [NULL_loc]) !! S k = Some node_next.
      { apply lookup_app_l_Some.
        rewrite removelast_firstn_len lookup_take_lt; first exact Hnode_next_locs.
        rewrite Hlen_eq. lia. }
      have Hnode_prev_new :
          (NULL_loc :: removelast locs) !! k = Some node_prev.
      { destruct k as [|k]; first done. simpl in Hnode_prev |- *.
        rewrite removelast_firstn_len lookup_take_lt; first exact Hnode_prev.
        rewrite Hlen_eq. lia. }
      iExists node_loc, node_next, node_prev.
      iSplit; first (iPureIntro; exact Hnode_loc_new).
      iSplit; first (iPureIntro; exact Hnode_next_new).
      iSplit; first (iPureIntro; exact Hnode_prev_new).
      iFrame. }
    have Hnew_last_loc :
        removelast locs !! (length self - 2)%nat = Some l0.
    { rewrite removelast_firstn_len lookup_take_lt; first exact Hprev_loc.
      rewrite Hlen_eq. lia. }
    have Hnew_last_next :
        (removelast locs ++ [NULL_loc]) !! S (length self - 2) =
        Some NULL_loc.
    { rewrite lookup_app_r; last (rewrite Hrem_locs_len Hlen_eq; lia).
      rewrite Hrem_locs_len Hlen_eq. replace (S (length self - 2) - (length self - 1))%nat with 0%nat by lia. done. }
    have Hnew_last_prev :
        (NULL_loc :: removelast locs) !! (length self - 2)%nat = Some lprev0.
    { rename select
        ((NULL_loc :: locs) !! (length self - 2)%nat = Some lprev0)
        into Hnew_last_prev_old.
      destruct (length self - 2)%nat as [|k] eqn:Hidx; first done.
      simpl in Hnew_last_prev_old |- *.
      rewrite removelast_firstn_len lookup_take_lt;
        first exact Hnew_last_prev_old.
      rewrite Hlen_eq. lia. }
    (* Re-guard the updated new tail and insert it at the end of the prefix. *)
    iAssert (guarded true
      (l0 ◁ₗ[π, Owned] #( *[#$#@{ T_rt } prev_elem; #NULL_loc; #lprev0]) @
        ◁(Link_ty T_rt <TY> T_ty <INST!>)))%I
      with "[Hcred1 Hnew_last_updated]" as "Hnew_last_guarded".
    { iApply guarded_intro. iFrame. }
    iAssert (∃ node_loc node_next node_prev : loc,
      ⌜removelast locs !! (length self - 2)%nat = Some node_loc⌝ ∗
      ⌜(removelast locs ++ [NULL_loc]) !! S (length self - 2) = Some node_next⌝ ∗
      ⌜(NULL_loc :: removelast locs) !! (length self - 2)%nat = Some node_prev⌝ ∗
      guarded true (node_loc ◁ₗ[π, Owned]
        #( *[#$#@{ T_rt } prev_elem; #node_next; #node_prev]) @
        ◁(Link_ty T_rt <TY> T_ty <INST!>)) ∗
      freeable_nz node_loc
        (sum_list
          (ly_size <$> (sl_members
            (use_struct_layout_alg' (Link_sls (st_of T_ty MetaNone)))).*2))
        1 HeapAlloc)%I
      with "[Hnew_last_guarded Hfree_new_last]" as "Hnew_last_node".
    { iExists l0, NULL_loc, lprev0.
      iSplit; first (iPureIntro; exact Hnew_last_loc).
      iSplit; first (iPureIntro; exact Hnew_last_next).
      iSplit; first (iPureIntro; exact Hnew_last_prev).
      iFrame. }
    iApply (big_sepL_delete _ _ (length self - 2)).
    { rewrite list_lookup_fmap.
      rewrite removelast_firstn_len lookup_take_lt; last lia.
      rewrite Hlook_prev_elem //. }
    rep liRStep; liShow.
    iApply (big_sepL_impl with "Hprefix_new").
    iModIntro. iIntros (k xk Hxk) "Hnode".
    destruct (decide (k = (length self - 2)%nat)); first done.
    iDestruct "Hnode" as (node_loc node_next node_prev)
      "(%Hnode_loc & %Hnode_next & %Hnode_prev & Hnode_guard & Hnode_free)".
    iExists node_loc, node_next, node_prev.
    iSplit; first (iPureIntro; exact Hnode_loc).
    iSplit; first (iPureIntro; exact Hnode_next).
    iSplit; first (iPureIntro; exact Hnode_prev).
    iFrame. }
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  all: try match goal with
    | Hzero : loc_a ?tl = 0,
      Hinv : (if decide (loc_a ?tl = 0) then ?mapped = [] ∧ _ else _)
      |- _ =>
        rewrite decide_True in Hinv; last exact Hzero;
        destruct Hinv as (Hxs & _);
        match type of Hxs with
        | ?f <$> ?xs = [] => apply fmap_nil_inv in Hxs; subst xs; done
        end
    end.
  all: try match goal with
    | |- last ?xs = None => destruct xs; done
    end.
  all: try match goal with
    | Hlookup : ?xs !! (length ?xs - 1)%nat = Some ?last |- ∃ x', last ?xs = Some x' ∧ _ =>
        exists last; split; last done;
        rewrite last_lookup;
        replace (Nat.pred (length xs)) with (length xs - 1)%nat by lia;
        exact Hlookup
    end.
  all: try match goal with
    | Hrem : length (removelast ?xs) = (length ?xs - 1)%nat
      |- length (removelast ?xs) > 0 => rewrite Hrem; lia
    end.
  all: try match goal with
    | Hrem1 : length (removelast ?xs) = (length ?xs - 1)%nat,
      Hrem2 : length (removelast ?ys) = (length ?ys - 1)%nat,
      Hlen : length ?xs = length ?ys
      |- length (removelast ?xs) = length (removelast ?ys) =>
        rewrite Hrem1 Hrem2 Hlen
    end.
  all: try match goal with
    | Hall : Forall ?P ?xs |- Forall ?P (removelast ?xs) =>
        rewrite removelast_firstn_len; apply Forall_take; exact Hall
    end.
  - rename select (length self > 0) into Hself_nonempty.
    rename select ((NULL_loc :: locs) !! (length self - 1)%nat = Some lprev)
      into Htail_prev_lookup.
    rename select (loc_a lprev = 0) into Hlprev_null_addr.
    destruct self as [|first rest]; first (simpl in Hself_nonempty; lia).
    destruct rest as [|second rest].
    { simpl in Htail_prev_lookup. congruence. }
    simpl in Htail_prev_lookup.
    have Hlprev_nonnull :=
      Forall_lookup_1 _ _ _ _ Hnot_null Htail_prev_lookup.
    congruence.
  - rename select (length self > 0) into Hself_nonempty.
    rename select ((NULL_loc :: locs) !! (length self - 1)%nat = Some lprev)
      into Htail_prev_lookup.
    rename select (loc_a lprev = 0) into Hlprev_null_addr.
    destruct self as [|first rest]; first (simpl in Hself_nonempty; lia).
    destruct rest as [|second rest]; first done.
    simpl in Htail_prev_lookup.
    have Hlprev_nonnull :=
      Forall_lookup_1 _ _ _ _ Hnot_null Htail_prev_lookup.
    congruence.
  - rewrite removelast_firstn_len length_take Nat.min_l; lia.
  - rewrite removelast_firstn_len.
    rename select (head locs = Some hd_ptr) into Hhead_loc.
    destruct locs as [|first_loc locs]; first (simpl in Hlen_eq; lia).
    destruct locs as [|second_loc locs]; first (simpl in Hlen_eq; lia).
    simpl in Hhead_loc. simpl. exact Hhead_loc.
  - rewrite last_lookup removelast_firstn_len length_take Nat.min_l; last lia.
    replace (Nat.pred (Nat.pred (length locs))) with (length self - 2)%nat by lia.
    rewrite lookup_take_lt; first exact Hprev_loc. lia.
  - rewrite !removelast_firstn_len !length_take.
    rewrite Hlen_eq. done.
  all: print_remaining_sidecond.
Qed.
End proof.
