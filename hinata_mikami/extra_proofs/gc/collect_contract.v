From radium Require Import lang notation.
From refinedrust Require Import typing.
From hinata_mikami.extra_proofs.gc Require Import gc_defs sweep_contract.

(** Pure composition of mark and sweep. The Rust annotation states these
    facts directly, without a collect_post wrapper. Actual program verification
    is Heap_collect_proof; its observe clause connects alive to the mutable Heap.
    Liveness here is membership in that Heap, not a deallocation trace. *)
Theorem collect_mark_sweep_contract locs nexts before after :
  NoDup locs → length nexts = length locs → length before = length locs →
  all_unmarked before → mark_from_rel locs nexts before 0%nat after →
  let alive := keep_marked locs after in
  (∀ l, reachable_loc locs nexts l ↔ l ∈ alive) ∧
  (∀ l, reachable_loc alive (keep_marked nexts after) l ↔
    reachable_loc locs nexts l) ∧
  all_unmarked (replicate (length alive) false).
Proof.
  intros Hnodup Hnext_len Hmark_len Hunmarked Hmark.
  split.
  - intros l. symmetry. eapply mark_sweep_exact; eassumption.
  - split.
    + eapply mark_sweep_reachability_preserved; eassumption.
    + apply sweep_reset_all_unmarked.
Qed.

(** The requested implication: initially unmarked implies reachable iff alive. *)
Theorem collect_reachable_iff_alive locs nexts before after l :
  NoDup locs → all_unmarked before →
  mark_from_rel locs nexts before 0%nat after →
  (reachable_loc locs nexts l ↔ l ∈ keep_marked locs after).
Proof.
  intros Hnodup Hunmarked Hmark.
  symmetry. eapply mark_sweep_exact; eassumption.
Qed.
