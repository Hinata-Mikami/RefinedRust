From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.verifythis2026.generated Require Import generated_code_verifythis2026 generated_specs_verifythis2026 generated_template_update.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma update_proof (π : thread_id) :
  update_lemma π.
Proof.
  update_prelude.

  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: pose proof (proj1 Hhindex) as Hfeasible.
  all: pose proof (proj2 Hhindex) as Hmaximal.
  - assert (Hindex_eq : j = Z.to_nat i) by lia. subst j.
    apply lookup_total_is_Some. lia.
  - opose proof (lookup_total_is_Some a j _) as Hlookup.
    { lia. }
    rewrite Hlookup.
    opose proof (revsorted_lookup_mono a
      (Z.to_nat (lo + (hi - lo) `quot` 2)) j Hsorted _ _) as Hmid_to_j.
    { lia. }
    { lia. }
    opose proof (revsorted_lookup_mono a j (Z.to_nat i) Hsorted _ _) as Hj_to_i.
    { lia. }
    { lia. }
    f_equal. lia.
  - opose proof (revsorted_lookup_mono a j
      (Z.to_nat (lo + (hi - lo) `quot` 2)) Hsorted _ _) as Hj_to_mid.
    { lia. }
    { lia. }
    opose proof (revsorted_lookup_mono a
      (Z.to_nat (lo + (hi - lo) `quot` 2)) (Z.to_nat i) Hsorted _ _) as Hmid_to_i.
    { lia. }
    { lia. }
    lia.
  - opose proof (revsorted_increment_first a
      (Z.to_nat (a !!! Z.to_nat i)) Hsorted _ _) as Hupdated_sorted.
    { lia. }
    { intros j Hj.
      opose proof (Hbefore j _) as Hj_before.
      { lia. }
      opose proof (Hat_or_after (Z.to_nat (a !!! Z.to_nat i)) _) as Hselected.
      { lia. }
      lia. }
    exact Hupdated_sorted.
  - unfold citation_update.
    exists (Z.to_nat (a !!! Z.to_nat i)).
    opose proof (Hat_or_after (Z.to_nat (a !!! Z.to_nat i)) _) as Hselected.
    { lia. }
    assert (Hupdated_in_bounds :
      (Z.to_nat (a !!! Z.to_nat i) < length a)%nat) by lia.
    exact (conj (conj Hupdated_in_bounds (conj Hselected eq_refl)) I).
  - unfold hindex. split.
    + opose proof (count_ge_increment_at a (Z.to_nat (a !!! Z.to_nat i))
        (Z.succ (a !!! Z.to_nat i)) _) as Hcount_update.
      { lia. }
      rewrite Hcount_update.
      case_decide as Hdec.
      * opose proof (count_ge_prefix a (Z.succ (a !!! Z.to_nat i))
          (Z.to_nat (a !!! Z.to_nat i)) _ _) as Hprefix_count.
        { lia. }
        { intros j Hj.
          opose proof (Hbefore j _) as Hj_before.
          { lia. }
          lia. }
        assert (Hlt : a !!! Z.to_nat i < Z.succ (a !!! Z.to_nat i)) by
          (unfold Z.succ; lia).
        opose proof (Hmaximal (Z.succ (a !!! Z.to_nat i)) Hlt)
          as Hnext_infeasible.
        lia.
      * exfalso. apply Hdec.
        opose proof (Hat_or_after (Z.to_nat (a !!! Z.to_nat i)) _)
          as Hselected.
        { lia. }
        lia.
    + intros k Hthreshold.
      opose proof (count_ge_increment_at a
        (Z.to_nat (a !!! Z.to_nat i)) k _) as Hcount_update.
      { lia. }
      rewrite Hcount_update.
      case_decide as Hdec.
      * opose proof (Hat_or_after (Z.to_nat (a !!! Z.to_nat i)) _)
          as Hselected.
        { lia. }
        lia.
      * apply Hmaximal. lia.
  - opose proof (revsorted_increment_first a (Z.to_nat h) Hsorted _ _)
      as Hupdated_sorted.
    { lia. }
    { intros j Hj.
      opose proof (Hbefore j _) as Hj_before.
      { lia. }
      opose proof (Hat_or_after (Z.to_nat h) _) as Hselected.
      { lia. }
      lia. }
    exact Hupdated_sorted.
  - unfold citation_update.
    exists (Z.to_nat h).
    opose proof (Hat_or_after (Z.to_nat h) _) as Hselected.
    { lia. }
    assert (Hupdated_in_bounds : (Z.to_nat h < length a)%nat) by lia.
    exact (conj (conj Hupdated_in_bounds (conj Hselected eq_refl)) I).
  - unfold hindex. split.
    + opose proof (count_ge_increment_at a (Z.to_nat h) h _) as Hcount_update.
      { lia. }
      rewrite Hcount_update.
      case_decide; lia.
    + intros k Hthreshold.
      opose proof (Hat_or_after (Z.to_nat h) _) as Hselected.
      { lia. }
      opose proof (revsorted_hindex_boundary a h Hsorted Hhindex _ _)
        as Hboundary.
      { lia. }
      { lia. }
      opose proof (count_ge_increment_at a (Z.to_nat h) k _) as Hcount_update.
      { lia. }
      rewrite Hcount_update.
      case_decide.
      * lia.
      * apply Hmaximal. lia.
  - opose proof (revsorted_increment_first a (Z.to_nat lo) Hsorted _ _)
      as Hupdated_sorted.
    { lia. }
    { intros j Hj.
      opose proof (Hbefore j _) as Hj_before.
      { lia. }
      opose proof (Hat_or_after (Z.to_nat lo) _) as Hselected.
      { lia. }
      lia. }
    exact Hupdated_sorted.
  - unfold citation_update.
    exists (Z.to_nat lo).
    opose proof (Hat_or_after (Z.to_nat lo) _) as Hselected.
    { lia. }
    solve_goal.
  - unfold hindex. split.
    + opose proof (count_ge_increment_at a (Z.to_nat lo) h _) as Hcount_update.
      { lia. }
      rewrite Hcount_update.
      case_decide; lia.
    + intros k Hthreshold_bound.
      opose proof (Hat_or_after (Z.to_nat lo) _) as Hselected.
      { lia. }
      opose proof (count_ge_increment_at a (Z.to_nat lo) k _) as Hcount_update.
      { lia. }
      rewrite Hcount_update.
      case_decide as Hthreshold.
      * assert (Hlo_lt : lo < a !!! Z.to_nat i).
      { destruct (decide (h = a !!! Z.to_nat i)) as [Heq|Hneq].
        - assert (~ h < lo).
          { intros Hhlt.
            opose proof (count_ge_prefix a (Z.succ h) (S (Z.to_nat h)) _ _)
              as Hprefix_count.
            { lia. }
            { intros j Hj.
              opose proof (Hbefore j _) as Hj_before.
              { lia. }
              lia. }
            opose proof (Hmaximal (Z.succ h) _) as Hnext_infeasible.
            { lia. }
            lia. }
          lia.
        - assert (Hhx : h < a !!! Z.to_nat i) by lia.
          opose proof (count_ge_prefix a (a !!! Z.to_nat i)
            (S (Z.to_nat lo)) _ _) as Hprefix_count.
          { lia. }
          { intros j Hj.
            destruct (decide (j < Z.to_nat lo)%nat).
            - opose proof (Hbefore j _) as Hj_before.
              { lia. }
              lia.
            - assert (j = Z.to_nat lo)%nat by lia. subst j. lia. }
          opose proof (Hmaximal (a !!! Z.to_nat i) Hhx) as Hx_infeasible.
          lia. }
        opose proof (count_ge_suffix a k (Z.to_nat lo) _ _) as Hsuffix_count.
        { lia. }
        { intros j Hj.
          opose proof (revsorted_lookup_mono a (Z.to_nat lo) j Hsorted _ _)
            as Hlo_to_j.
          { lia. }
          { lia. }
          lia. }
        lia.
      * apply Hmaximal. lia.
Qed.
End proof.
