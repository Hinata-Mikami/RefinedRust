(** From the CPP'26 paper "Building Blocks for Step-Indexed Program Logics",
    by Thomas Somers, Jonas Kastberg Hinrichsen, Lennard Gäher, and Robbert Krebbers. 
    
    Upstream: https://gitlab.mpi-sws.org/tlsomers/iris-contrib/-/tree/8a482f0a60295cb016c5a39b2ec5f602b74e3514
*)
From iris.algebra Require Export view frac numbers.
From iris.algebra Require Import proofmode_classes big_op dfrac proofmode_classes.
From iris.prelude Require Import options.

Section rel.
  Context {SI : sidx}.

(** Authoritative CMRA for time receipts combining nat and max_nat, where the
    authoritative consists of nat and the fragment over a non-persistent part
    nat and persistent part max_nat, of which the sum is a lower bound of the
    authoritative. It is defined in terms of view. *)

(** * Definition of the view relation *)
Definition tr_view_rel_raw (n : SI) (auth : nat) (frag : nat * max_nat) : Prop :=
  ∃ auth₁ auth₂, auth = auth₁ + auth₂ ∧ auth₁ ≤ auth₂ ∧ frag.1 ≤ auth₁ ∧ max_nat_car frag.2 ≤ auth₂.

Lemma tr_view_rel_raw_mono n1 n2 (a1 a2 : nat) (b1 b2 : nat * max_nat) :
  tr_view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%sidx →
  tr_view_rel_raw n2 a2 b2.
Proof.
    intros (auth₁ & auth₂ & H) Haeq Hble Hnle. exists auth₁, auth₂.
    destruct b1 as [? [?]]. destruct b2 as [? [?]]. simpl in *.
    rewrite pair_includedN in Hble. rewrite -!cmra_discrete_included_iff in Hble.
    rewrite nat_included max_nat_included /= in Hble. rewrite -discrete_iff leibniz_equiv_iff in Haeq.
    simplify_eq. repeat split; lia.
Qed.

Lemma tr_view_rel_raw_valid n a b :
  tr_view_rel_raw n a b → ✓{n} b.
Proof. done. Qed.
Lemma tr_view_rel_raw_unit n :
  ∃ a : nat, tr_view_rel_raw n a ε.
Proof. exists 0. unfold tr_view_rel_raw. exists 0,0. by replace ε with (0, MaxNat 0) by done. Qed.
Canonical Structure tr_view_rel : view_rel natUR (prodUR natUR max_natUR) :=
  ViewRel tr_view_rel_raw tr_view_rel_raw_mono
          tr_view_rel_raw_valid tr_view_rel_raw_unit.

Lemma tr_view_rel_unit n (a : natUR) : tr_view_rel n a ε ↔ ✓{n} a.
Proof.
  split; [by intros|].
  replace ε with (0, MaxNat 0) by done.
  rewrite /tr_view_rel /= /tr_view_rel_raw /=. intros. exists 0, a. lia.
Qed.

Lemma tr_view_rel_exists n b :
  (∃ a, tr_view_rel n a b) ↔ ✓{n} b.
Proof.
  split.
  - intros [a Hrel]. eapply tr_view_rel_raw_valid, Hrel.
  - intros; destruct b as [b₁ [b₂]]. exists (b₁ + max b₁ b₂), b₁, (max b₁ b₂).
      rewrite /tr_view_rel /= /tr_view_rel_raw /=; lia.
Qed.

Global Instance tr_view_rel_discrete :
  ViewRelDiscrete tr_view_rel.
Proof.
  by intros n a b ?.
Qed.

End rel.

Section definitions.
  Context {SI : sidx}.

(** * Definition and operations on the time receipt camera *)
Definition tr_view := (view tr_view_rel_raw).
Definition tr_viewO : ofe := viewO tr_view_rel.
Definition tr_viewR : cmra := viewR tr_view_rel.
Definition tr_viewUR : ucmra := viewUR tr_view_rel.

Definition tr_view_auth (m : nat) : tr_view := view_auth (DfracOwn 1) m.
Definition tr_view_frag (n : nat) : tr_view := view_frag (n, MaxNat 0).
Definition tr_view_frag_persistent (n : nat) : tr_view := view_frag (0, MaxNat n).

Global Typeclasses Opaque tr_view_auth tr_view_frag tr_view_frag_persistent.

Global Instance: Params (tr_view_auth) 0 := {}.
Global Instance: Params (tr_view_frag) 0 := {}.
Global Instance: Params (tr_view_frag_persistent) 0 := {}.

End definitions.

Notation "'●⧗V' m" := (tr_view_auth m)
  (at level 20, format "●⧗V m").
Notation "'◯⧗V' n" := (tr_view_frag n) (at level 20).
Notation "'◯⧖V' n" := (tr_view_frag_persistent n) (at level 20).


Section tr_view.
  Implicit Types (n n₁ n₂ m : nat).
  Context {SI : sidx}.


  Global Instance tr_view_frag_persistent_core_id n : CoreId (◯⧖V n).
  Proof. by constructor. Qed.

  Global Instance tr_view_frag_0_core_id : CoreId (◯⧗V 0).
  Proof. by constructor. Qed.

  Lemma tr_view_frag_op n₁ n₂ :
    ◯⧗V (n₁ + n₂) = ◯⧗V n₁ ⋅ ◯⧗V n₂.
  Proof. done. Qed.

  Lemma tr_view_frag_persistent_op n₁ n₂ :
    ◯⧖V (n₁ `max` n₂) = ◯⧖V n₁ ⋅ ◯⧖V n₂.
  Proof. done. Qed.

  Global Instance tr_view_frag_is_op n₁ n₂ n₃ :
    IsOp n₁ n₂ n₃ → IsOp' (◯⧗V n₁) (◯⧗V n₂) (◯⧗V n₃).
  Proof. done. Qed.

  Global Instance tr_view_frag_persistent_is_op n n₁ n₂ :
    IsOp (MaxNat n) (MaxNat n₁) (MaxNat n₂) → IsOp' (◯⧖V n) (◯⧖V n₁) (◯⧖V n₂).
  Proof. done. Qed.

  Lemma tr_view_tr_valid m n :
    ✓ (●⧗V m ⋅ ◯⧗V n) ↔ n + n ≤ m.
  Proof.
    rewrite view_both_valid /tr_view_rel /= /tr_view_rel_raw /=.
    split.
    - intros H. specialize (H 0ᵢ) as (a & b & C); repeat split; try lia.
    - intros H _. exists n, (m - n). lia.
  Qed.

  Lemma tr_view_tr_persistent_valid m n :
    ✓ (●⧗V m ⋅ ◯⧖V n) ↔ n ≤ m.
  Proof.
    rewrite view_both_valid /tr_view_rel /= /tr_view_rel_raw /=.
    split.
    - intros H. specialize (H 0ᵢ) as (a & b & C); lia.
    - intros H _. exists 0, m. lia.
  Qed.

  Lemma tr_view_both_valid m n₁ n₂ :
    ✓ (●⧗V m ⋅ (◯⧗V n₁ ⋅ ◯⧖V n₂)) → n₁ + n₂ ≤ m.
  Proof.
    rewrite view_both_valid /tr_view_rel /= /tr_view_rel_raw /=.
    intros H. specialize (H 0ᵢ) as (a & b & -> & _ & H & ?).
    rewrite nat_op in H. lia.
  Qed.

  Lemma tr_view_tr_persistent_increase n₁ n₂ :
    ◯⧖V n₁ ⋅ ◯⧗V n₂ ~~> ◯⧖V (n₁ + n₂).
  Proof.
    rewrite -view_frag_op.
    apply view_update_frag=> [a] d [m₁ [m₂]].
    rewrite /tr_view_rel /= /tr_view_rel_raw /=.
    rewrite !nat_op.
    intros (a₁ & a₂ & -> & Hale & Hnle₁ & Hnle₂).
    exists (a₁ - n₂), (a₂ + n₂); lia.
  Qed.

  Lemma tr_view_tr_persist n:
    ◯⧗V n ~~> ◯⧗V n ⋅ ◯⧖V n.
  Proof.
    apply view_update_frag=> [a] d [? [?]].
    rewrite /tr_view_rel /= /tr_view_rel_raw /= !nat_op.
    intros (a₁ & a₂ & -> & Hale & Hnle₁ & Hnle₂).
    exists a₁, a₂; lia.
  Qed.

  Lemma tr_view_auth_incr m n₁ n₂ :
    ●⧗V m ⋅ ◯⧖V n₁ ~~> ●⧗V (m + n₂ + n₂) ⋅ ◯⧖V (n₁ + n₂) ⋅ ◯⧗V n₂.
  Proof.
    rewrite -assoc.
    apply view_update=> [a] [b₁ [b₂]].
    rewrite /tr_view_rel /tr_view_rel_raw /= !nat_op.
    intros (a₁ & a₂ & -> & Hale & Hnle₁ & Hnle₂).
    exists (a₁ + n₂), (a₂ + n₂). lia.
  Qed.

  Lemma tr_view_tr_persistent_mono n₂ n₁ :
    n₁ ≤ n₂ → ◯⧖V n₁ ≼ ◯⧖V n₂.
  Proof.
    intros. eapply ( @view_frag_mono _ ).
    rewrite prod_included nat_included max_nat_included //.
  Qed.

End tr_view.

Global Typeclasses Opaque tr_view_auth tr_view_frag tr_view_frag_persistent.
