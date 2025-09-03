From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_adapters_map_Map_BIF_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma adapters_map_Map_BIF_new_proof (π : thread_id) :
  adapters_map_Map_BIF_new_lemma π.
Proof.
  adapters_map_Map_BIF_new_prelude.

  repeat liRStep; liShow.
  liInst Hevar Inv.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
