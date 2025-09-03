From refinedrust Require Import typing.

(* TODO upstream *)

Lemma seqZ_pos_seq start count :
  0 ≤ start →
  seqZ start count = Z.of_nat <$> seq (Z.to_nat start) (Z.to_nat count).
Proof.
  intros Hge.
  set (start' := Z.to_nat start).
  assert (start = Z.of_nat start') as Heq by lia.
  rewrite Heq in Hge.
  rewrite Heq.
  generalize start'.
  clear. intros start.
  unfold seqZ.
  generalize (Z.to_nat count) as count'. 
  clear. intros count.
  unfold fmap.
  (*induction count as [ | ? IH] in start |-*; simpl; try solve_goal.*)
  (*f_equiv; first lia.*)
  (*rewrite -IH.*)
  (*solve_goal.*)
Admitted.
Global Hint Rewrite -> seqZ_pos_seq using lia : lithium_rewrite.

(* Idea more generally: split at 0 *)

Lemma sum_list_Z_of_nat xs :
  sum_list_Z (Z.of_nat <$> xs) = sum_list xs.
Proof.
Admitted.
Global Hint Rewrite -> sum_list_Z_of_nat : lithium_rewrite.
