Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.

(* Proved by manual induction: inductive property about the emitted elements *)
Global Program Instance learn_from_hyp_list_it π T_rt s1 hist s2 :
  LearnFromHyp (IteratorNextFusedTrans (ListIteraTasstd_iter_Iterator_spec_attrs T_rt) π s1 hist s2) :=
  {| learn_from_hyp_Q := ⌜s1 = hist ++ s2⌝%I |}.
Next Obligation.
  iIntros (???????) "Hx".
  iModIntro.
  iInduction hist as [ | x hist] "IH" forall (s1 s2); simpl.
  { iDestruct "Hx" as "->". iPureIntro. done. } 
  iDestruct "Hx" as "(%s1' & (_ & ->) & Hx)".
  iPoseProof ("IH" with "Hx") as "($ & ->)".
  done.
Qed.

End extra_specs.
