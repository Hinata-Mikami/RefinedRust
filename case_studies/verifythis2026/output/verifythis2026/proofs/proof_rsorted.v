From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.verifythis2026.generated Require Import generated_code_verifythis2026 generated_specs_verifythis2026 generated_template_rsorted.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma rsorted_proof (π : thread_id) :
  rsorted_lemma π.
Proof.
  rsorted_prelude.

  1: rep liRStep.
  1: liInst Hevar_params a.
  1: rep <-! <3000 liRStep.
  1: rep liRStep.
  1: liInst Hevar_params x.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - unfold revsorted_prefix. intros. lia.
  - assert (k = Z.to_nat i) as -> by lia. lia.
  - rewrite swap_at_length.
    rename select (length x0 = Z.to_nat n) into Hlength.
    exact Hlength.
  - rename select (Permutation x x0) into Hinner_permutation.
    opose proof (swap_at_Permutation x0 (Z.to_nat x1) (Z.to_nat j) _ _ _)
      as Hswap_permutation.
    { lia. }
    { lia. }
    { lia. }
    etrans; first exact Hinner_permutation.
    exact Hswap_permutation.
  - rename select (revsorted_prefix x0 (Z.to_nat x1)) into Hprefix.
    apply revsorted_prefix_swap_at; first exact Hprefix.
    lia.
  - rename select (∀ k0 : nat, _ → x0 !!! k0 ≤ x0 !!! Z.to_nat x1) into Hscanned.
    rename select (x0 !!! Z.to_nat x1 < x0 !!! Z.to_nat j) into Hlarger.
    opose proof (scanned_max_swap_at x0 (Z.to_nat x1) (Z.to_nat j) _ _
      Hlarger k _) as Hresult.
    { lia. }
    { intros k0 Hk0. apply Hscanned. lia. }
    { lia. }
    exact Hresult.
  - rename select (∀ k0 : nat, _ → x0 !!! k0 ≤ x0 !!! Z.to_nat x1) into Hscanned.
    rename select (¬ x0 !!! Z.to_nat x1 < x0 !!! Z.to_nat j) into Hnot_larger.
    opose proof (scanned_max_keep x0 (Z.to_nat x1) (Z.to_nat j) _
      Hnot_larger k _) as Hresult.
    { intros k0 Hk0. apply Hscanned. lia. }
    { lia. }
    exact Hresult.
  - rename select (Permutation a x) into Houter_permutation.
    rename select (Permutation x x0) into Hinner_permutation.
    etrans; first exact Houter_permutation.
    exact Hinner_permutation.
  - rename select (revsorted_prefix x0 (Z.to_nat x1)) into Hprefix.
    rename select (∀ k0 : nat, _ → x0 !!! k0 ≤ x0 !!! Z.to_nat x1) into Hscanned.
    assert (Z.to_nat (Z.succ x1) = S (Z.to_nat x1)) as Hsucc.
    { apply Z2Nat.inj_succ. lia. }
    rewrite Hsucc.
    apply revsorted_prefix_extend.
    + exact Hprefix.
    + intros k Hk. apply Hscanned. lia.
  - rename select (revsorted_prefix x (Z.to_nat i)) into Hprefix.
    rename select (length x = Z.to_nat n) into Hlength.
    apply (revsorted_prefix_complete x (Z.to_nat i)); first exact Hprefix.
    lia.
Qed.
End proof.
