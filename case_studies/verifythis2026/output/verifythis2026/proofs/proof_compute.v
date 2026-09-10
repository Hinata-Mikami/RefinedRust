From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.verifythis2026.generated Require Import generated_code_verifythis2026 generated_specs_verifythis2026 generated_template_compute.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma compute_proof (π : thread_id) :
  compute_lemma π.
Proof.
  compute_prelude.

  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  - intros Hlt.
    opose proof (revsorted_lookup_mono a i (Z.to_nat h) _ _ _) as Hmono.
    { exact Hsorted. }
    { lia. }
    { lia. }
    lia.
  - unfold hindex. split.
    + opose proof (count_ge_prefix a h (Z.to_nat h) _ _) as Hprefix_count.
      { lia. }
      { intros i Hi.
        opose proof (Hprefix i _) as Hi_prefix.
        { lia. }
        lia. }
      lia.
    + intros k Hthreshold.
      enough (count_ge a k <= Z.to_nat h)%nat by lia.
      apply count_ge_suffix; first lia.
      intros i Hi.
      opose proof (revsorted_lookup_mono a (Z.to_nat h) i _ _ _) as Hmono.
      { exact Hsorted. }
      { lia. }
      { lia. }
      lia.
  - unfold hindex. split.
    + opose proof (count_ge_prefix a h (Z.to_nat h) _ _) as Hprefix_count.
      { lia. }
      { intros i Hi.
        opose proof (Hprefix i _) as Hi_prefix.
        { lia. }
        lia. }
      lia.
    + intros k Hthreshold.
      enough (count_ge a k <= Z.to_nat h)%nat by lia.
      apply count_ge_suffix; first lia.
      intros i Hi. lia.
Qed.
End proof.
