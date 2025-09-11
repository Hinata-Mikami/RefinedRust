From refinedrust Require Import typing.
From rrstd.iterator.theories Require Import iterator.

Record MapX (I : RT) (F : RT) : Type := mk_map_x {
  map_it : RT_xt I;
  map_clos : RT_xt F;
}.
Global Arguments map_it {_ _}.
Global Arguments map_clos {_ _}.
Global Arguments mk_map_x {_ _}.
Canonical Structure MapXRT (I F : RT) := directRT (MapX I F).

Global Instance MapX_inh I F :
Inhabited (RT_xt I) → Inhabited (RT_xt F) → Inhabited (MapX I F).
Proof.
  intros Ha Hb. exact (populate (mk_map_x inhabitant inhabitant)).
Qed.

Global Instance MapX_simpl_exist I F H :
  SimplExist (MapX I F) H (∃ (i : RT_xt I) (f : RT_xt F), H (mk_map_x i f)).
Proof.
  intros (i & f & Ha).
  eexists _. done.
Qed.
Global Instance MapX_simpl_forall I F H :
  SimplForall (MapX I F) 2 H (∀ (i : RT_xt I) (f : RT_xt F), H (mk_map_x i f)).
Proof.
  intros Ha (i & f). apply Ha.
Qed.

Global Instance simpl_both_mapX {I F} (m1 m2 : MapX I F) :
  SimplBothRel (=) m1 m2 (m1.(map_it) = m2.(map_it) ∧ (m1.(map_clos) = m2.(map_clos))).
Proof.
  unfold SimplBothRel.
  destruct m1, m2; naive_solver.
Qed.


(* TODO move *)
Definition li_sealed `{!refinedrustGS Σ} (P : iProp Σ) : iProp Σ :=
  P.
Global Typeclasses Opaque li_sealed.

Lemma li_sealed_use_pers `{!refinedrustGS Σ} (P : iProp Σ) `{!Persistent P} :
  li_sealed P -∗ □ P.
Proof.
  unfold li_sealed. iIntros "#Ha". iModIntro. done.
Qed.
