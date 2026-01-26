From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.hillel.generated Require Import generated_code_hillel generated_specs_hillel generated_template_unique.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma unique_proof (π : thread_id) :
  unique_lemma π.
Proof.
  unique_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(unique) *)
  all: try set_solver.
  - by apply NoDup_nil.
  - opose proof (NoDup_list_subseteq_length_le unique _iter_hist_7  _ _); try done; lia.
  - opose proof (NoDup_list_subseteq_length_le unique _iter_hist_7  _ _); try done.
    unfold size_of_array_in_bytes in *. simpl in *. nia.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
