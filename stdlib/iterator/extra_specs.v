Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.

Section trans.
  
  (* Note: Depends on the whole attrs instead of the Next projection so that the projection doesn't simplify away, which is a problem for [LearnFromHyp] rules. *)
  Fixpoint IteratorNextFusedTrans {Self_rt Item_rt : RT} 
    (attrs : traits_iterator_Iterator_spec_attrs Self_rt Item_rt)
    (π : thread_id)
    (s1 : RT_xt Self_rt) (els : list (RT_xt Item_rt)) (s2 : RT_xt Self_rt) : iProp Σ
    :=
    match els with
    | [] => ⌜s1 = s2⌝
    | (e1 :: els) => 
      ∃ s1', 
        attrs.(traits_iterator_Iterator_Next) π s1 (Some e1) s1' ∗
        IteratorNextFusedTrans attrs π s1' els s2
    end.

  Lemma iterator_next_fused_trans_app {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π s1 hist s2 x :
    IteratorNextFusedTrans A π s1 (hist ++ [x]) s2 ⊣⊢ (∃ s2', IteratorNextFusedTrans A π s1 hist s2' ∗ A.(traits_iterator_Iterator_Next) π s2' (Some x) s2).
  Proof.
    iInduction hist as [ | y hist] "IH" forall (s1 s2); simpl.
    - iSplit.
      + iIntros "(%s1' & ? & <-)". by iFrame.
      + iIntros "(%s2' & -> & ?)". by iFrame.
    - iSplit.
      + iIntros "(%s1' & Ha & Hb)".
        iPoseProof ("IH" with "Hb") as "(%s2' & Hb & Hc)".
        iFrame.
      + iIntros "(%s2' & (%s1' & ? & ?) & ?)".
        iFrame. iApply "IH". iFrame.
  Qed.

  Lemma simplify_goal_iterator_next_fused_trans_app {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π s1 hist s2 s1' hist' `{!CheckOwnInContext (IteratorNextFusedTrans A π s1 hist' s1')} T :
    (∃ x, 
      ⌜hist = hist' ++ [x]⌝ ∗
      IteratorNextFusedTrans A π s1 hist' s1' ∗
      A.(traits_iterator_Iterator_Next) π s1' (Some x) s2) ∗ T ⊢ simplify_goal (IteratorNextFusedTrans A π s1 hist s2) T.
  Proof.
    rewrite /simplify_goal. 
    iIntros "((%x & -> & Ha & Hb) & $)".
    rewrite iterator_next_fused_trans_app.
    iFrame.
  Qed.
  Definition simplify_goal_iterator_next_fused_trans_app_inst := [instance @simplify_goal_iterator_next_fused_trans_app with 50%N].
  Global Existing Instance simplify_goal_iterator_next_fused_trans_app_inst.

  Lemma simplify_goal_iterator_next_fused_trans_nil {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π s1 hist T :
    (⌜hist = []⌝) ∗ T ⊢ simplify_goal (IteratorNextFusedTrans A π s1 hist s1) T.
  Proof.
    rewrite /simplify_goal.
    iIntros "(-> & $)".
    eauto.
  Qed.
  Definition simplify_goal_iterator_next_fused_trans_nil_inst := [instance @simplify_goal_iterator_next_fused_trans_nil with 10%N].
  Global Existing Instance simplify_goal_iterator_next_fused_trans_nil_inst.


End trans.

End extra_specs.
