From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.typing Require Import adequacy.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy.
From refinedrust.examples.adequacy.proofs Require Import proof_recurse.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Definition linking_recursive_spec (P : thread_id → iProp Σ) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),
    fn_spec_add_late_pre (type_of_recurse -[] -[]) P.

(* Close the self edge with R := □ A, rather than a recursive definition of R. *)
Lemma linking_recursive_link π addr (A : thread_id → iProp Σ) :
  addr ∈ usize →
  fntbl_entry (fn_loc addr) (recurse_def (fn_loc addr)) -∗
  typed_function π (recurse_def (fn_loc addr))
    (<tag_type> linking_recursive_spec (λ π, (□ A π)%I)).
Proof.
  intros Haddr.
  iIntros "#Hentry".
  iLöb as "Hself".
  iApply typed_function_equiv; iSplit.
  { iApply (recurse_proof π (fn_loc addr)
      (spec! ( *[]) : 0 | ( *[]) : [], λ π, (□ A π)%I)).
    rewrite /ty_own_val/=; iR.
    iExists (recurse_def (fn_loc addr)).
    iSplitR; [iPureIntro; by apply val_to_loc_Some_l2v |].
    iFrame "Hentry".
    iSplitR; [iPureIntro; constructor |].
    iExact "Hself". }
  rep liRStep.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.

End proof.
