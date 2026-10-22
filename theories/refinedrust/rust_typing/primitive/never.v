From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** ** Never type *)
Section never.
  Context `{!typeGS Σ}.

  Program Definition never_t : type unit := {|
    st_own π _ v := False;
    st_syn_type := NeverSynType;
    st_has_op_type ot := is_never_ot ot;
  |}%I.
  Next Obligation.
    iIntros (π _ v []).
  Qed.
  Next Obligation.
    intros ot ->%is_never_ot_layout.
    by apply syn_type_has_layout_never.
  Qed.
  Next Obligation.
    intros ot Hot.
    destruct ot; simpl in Hot; try done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    simpl. iIntros (ot st π [] v Hot []).
  Qed.
  Next Obligation.
    simpl. iIntros (ot st π [] v v' Hot Hsame []).
  Qed.
  Next Obligation.
    intros ly Hst.
    apply syn_type_has_layout_never_inv in Hst as ->.
    done.
  Qed.

  Global Instance never_copyable : Copyable never_t.
  Proof. apply _. Qed.
  Global Instance never_sized : TySized never_t.
  Proof. apply _. Qed.

  Global Instance never_timeless l z π m :
    Timeless (l ◁ᵥ{π, m} z @ never_t)%I.
  Proof. apply _. Qed.
End never.

Global Hint Unfold never_t : tyunfold.
