From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.verifythis2026.generated Require Import generated_code_verifythis2026 generated_specs_verifythis2026 generated_template_update_k.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma update_k_proof (π : thread_id) :
  update_k_lemma π.
Proof.
  update_k_prelude.

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
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.
  1: rep liRStep.
  1: rep <-! <3000 liRStep.
  1: rep liRStep.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - unfold citation_update_k, add_at. reflexivity.
  - apply revsorted_add_at_except; assumption || lia.
  - rewrite swap_at_length.
    exact Hlength.
  - unfold citation_update_k in Hupdate |- *.
    etrans; last exact Hupdate.
    symmetry. apply swap_at_Permutation; lia.
  - rename select (x !!! (Z.to_nat j - Z.to_nat 1)%nat < x !!! Z.to_nat j)
      into Hmove.
    opose proof (revsorted_except_swap_left x (Z.to_nat j) Halmost _ Hmove)
      as Hsorted_except. { lia. }
    exact Hsorted_except.
  - rename select (~ x !!! (Z.to_nat j - Z.to_nat 1)%nat < x !!! Z.to_nat j)
      into Hstop.
    apply (revsorted_except_complete x (Z.to_nat j)); first exact Halmost.
    right.
    change (~ x !!! (Z.to_nat j - 1)%nat < x !!! Z.to_nat j) in Hstop.
    lia.
  - opose proof* (hindex_update_k_succ a x h (Z.to_nat i) k) as Hnew;
      [done.. |].
    exact Hnew.
  - rename select (~ x !!! (Z.to_nat j - Z.to_nat 1)%nat < x !!! Z.to_nat j)
      into Hstop.
    apply (revsorted_except_complete x (Z.to_nat j)); first exact Halmost.
    right.
    change (~ x !!! (Z.to_nat j - 1)%nat < x !!! Z.to_nat j) in Hstop.
    lia.
  - opose proof* (hindex_update_k_same a x h (Z.to_nat i) k) as Hnew;
      [done.. | naive_solver |].
    exact Hnew.
  - rename select (~ x !!! (Z.to_nat j - Z.to_nat 1)%nat < x !!! Z.to_nat j)
      into Hstop.
    apply (revsorted_except_complete x (Z.to_nat j)); first exact Halmost.
    right.
    change (~ x !!! (Z.to_nat j - 1)%nat < x !!! Z.to_nat j) in Hstop.
    lia.
  - opose proof* (hindex_update_k_same a x h (Z.to_nat i) k) as Hnew;
      [done.. | naive_solver |].
    exact Hnew.
  - apply (revsorted_except_complete x (Z.to_nat j)); first exact Halmost.
    left. lia.
  - opose proof* (hindex_update_k_succ a x h (Z.to_nat i) k) as Hnew;
      [done.. |].
    exact Hnew.
  - apply (revsorted_except_complete x (Z.to_nat j)); first exact Halmost.
    left. lia.
  - opose proof* (hindex_update_k_same a x h (Z.to_nat i) k) as Hnew;
      [done.. | naive_solver |].
    exact Hnew.
  - apply (revsorted_except_complete x (Z.to_nat j)); first exact Halmost.
    left. lia.
  - opose proof* (hindex_update_k_same a x h (Z.to_nat i) k) as Hnew;
      [done.. | naive_solver |].
    exact Hnew.
Qed.
End proof.
