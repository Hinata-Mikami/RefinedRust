From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_loops_loop4_myrange_2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.


Program Instance learn_from_hyp_range_it π s1 hist s2 :
  LearnFromHyp (IteratorNextFusedTrans loops_MyRangeasstd_iter_Iterator_spec_attrs π s1 hist s2) :=
  {| learn_from_hyp_Q := ⌜s1.2 = s2.2 ∧ s1.1 ≤ s2.1 ∧ (* s2.1 ≤ s2.2 ∧ *) hist = seqZ s1.1 (s2.1 - s1.1)⌝%I |}.
Next Obligation.
  iIntros (??????) "Hx".
  iModIntro.
  iInduction hist as [ | x hist] "IH" forall (s1 s2); simpl.
  { iDestruct "Hx" as "%". subst. iPureIntro.
    rewrite Z.sub_diag. done. }
  iDestruct "Hx" as "(%s1' & %Ha & Hx)".
  iPoseProof ("IH" with "Hx") as "($ & %Hb)".
  iPureIntro.
  destruct Ha as (? & _ & <- & ? & ?). destruct Hb as (? & ? & ->).
  destruct s1, s2, s1'; simpl in *.
  subst. split_and!; try solve_goal.
  assert (1 ≤ r1 - r) as Hge by lia.
  rewrite Z.sub_add_distr.
  assert ((r1 - 1 -r)%Z = ((r1 - r) - 1)%Z) as -> by lia.
  move: Hge. generalize (r1 - r) as x.
Admitted.

Lemma loops_loop4_myrange_2_proof (π : thread_id) :
  loops_loop4_myrange_2_lemma π.
Proof.
  loops_loop4_myrange_2_prelude.

  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { simpl.
    admit. }
  { admit. }
  Unshelve. all: print_remaining_sidecond.
(*Qed.*)
Admitted.
End proof.
