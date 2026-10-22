From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_collect.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_collect_proof (π : thread_id) :
  traits_iterator_Iterator_collect_lemma π.
Proof.
  traits_iterator_Iterator_collect_prelude.

  rep liRStep; liShow.
  liInst Hevar_x2 x'0.
  liInst Hevar_x0 x'1.
  liInst Hevar_x3 x'2.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
