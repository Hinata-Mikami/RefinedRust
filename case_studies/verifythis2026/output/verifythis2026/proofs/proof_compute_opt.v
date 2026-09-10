From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.verifythis2026.generated Require Import generated_code_verifythis2026 generated_specs_verifythis2026 generated_template_compute_opt.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma compute_opt_proof (π : thread_id) :
  compute_opt_lemma π.
Proof.
  compute_opt_prelude.

  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - destruct (decide (Z.of_nat i < hi)).
    + opose proof (revsorted_lookup_mono a
        (Z.to_nat (lo + (hi - lo) `quot` 2)) i _ _ _) as Hmono.
      { exact Hsorted. }
      { lia. }
      { lia. }
      lia.
    + opose proof (Hafter i _) as Hi_after.
      { lia. }
      lia.
  - destruct (decide (Z.of_nat i < lo)).
    + opose proof (Hbefore i _) as Hi_before.
      { lia. }
      lia.
    + opose proof (revsorted_lookup_mono a i
        (Z.to_nat (lo + (hi - lo) `quot` 2)) _ _ _) as Hmono.
      { exact Hsorted. }
      { lia. }
      { lia. }
      lia.
  - unfold hindex. split.
    + opose proof (count_ge_prefix a lo (Z.to_nat lo) _ _) as Hprefix_count.
      { lia. }
      { intros i Hi.
        opose proof (Hbefore (Z.to_nat (lo - 1)) _) as Hlast_before.
        { lia. }
        opose proof (revsorted_lookup_mono a i (Z.to_nat (lo - 1)) _ _ _)
          as Hmono.
        { exact Hsorted. }
        { lia. }
        { lia. }
        lia. }
      lia.
    + intros k Hthreshold.
      enough (count_ge a k <= Z.to_nat lo)%nat by lia.
      apply count_ge_suffix; first lia.
      intros i Hi.
      destruct (decide (lo < n)).
      * opose proof (Hafter (Z.to_nat lo) _) as Hfirst_after.
        { lia. }
        opose proof (revsorted_lookup_mono a (Z.to_nat lo) i _ _ _) as Hmono.
        { exact Hsorted. }
        { lia. }
        { lia. }
        lia.
      * lia.
Qed.
End proof.
