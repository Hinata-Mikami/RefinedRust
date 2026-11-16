From radium Require Import lang notation.
From refinedrust Require Import typing.

(** Discarding an Iris ownership assertion does not execute a program step.
    In particular, even the non-zero-size deallocation token can be forgotten.
    A postcondition omitting this token is not a certificate of Free. *)
Section ownership.
Context `{RRGS : !refinedrustGS Σ}.

Lemma deallocation_permission_can_be_discarded l size :
  freeable l size 1 HeapAlloc -∗ emp.
Proof. iIntros "_". done. Qed.
End ownership.

(** By contrast, the operational free_block transition really changes the
    allocation metadata to dead. FreeS requires exactly such a transition. *)
Lemma free_block_marks_allocation_dead hs l ly hs' :
  free_block hs HeapAlloc l ly hs' →
  ∃ aid, l.(loc_p) = ProvAlloc aid ∧
    hs'.(hs_allocs) !! aid =
      Some (Allocation l.(loc_a) ly.(ly_size) false HeapAlloc).
Proof.
  intros Hfree.
  apply free_block_inv in Hfree as
    (aid & bytes & Hprovenance & Halive & Hsize & Hlookup & ->).
  exists aid. split; first exact Hprovenance.
  simpl. by rewrite lookup_insert_eq.
Qed.
