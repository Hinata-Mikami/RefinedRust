From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.verifythis2026.generated Require Import generated_code_verifythis2026 generated_specs_verifythis2026 generated_template_compute_opt_rsorted.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma compute_opt_rsorted_proof (π : thread_id) :
  compute_opt_rsorted_lemma π.
Proof.
  compute_opt_rsorted_prelude.

  1: rep <-! <3000 liRStep.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rename select (length a = Z.to_nat n) into Hinput_length.
    rename select (Permutation a x') into Hpermutation.
    opose proof (Permutation_length Hpermutation) as Hpermutation_length.
    lia.
  - rename select (Permutation a x') into Hpermutation.
    rename select (hindex x' x'0) into Hcomputed.
    unfold hindex. split.
    + opose proof (count_ge_Permutation a x' x'0 Hpermutation) as Hcount.
      rewrite Hcount. exact (proj1 Hcomputed).
    + intros k Hthreshold.
      opose proof (count_ge_Permutation a x' k Hpermutation) as Hcount.
      rewrite Hcount. apply (proj2 Hcomputed). exact Hthreshold.
Qed.
End proof.
