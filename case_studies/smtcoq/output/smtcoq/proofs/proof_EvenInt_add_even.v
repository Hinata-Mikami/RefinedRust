From Sniper Require Import Sniper.
From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.smtcoq.generated Require Import generated_code_smtcoq generated_specs_smtcoq generated_template_EvenInt_add_even.
From refinedrust_smtcoq Require Import smtcoq.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

(** SMTCoq lemmas *)

(* The lemma Zeven relies on the internal representation of Z *)
(* As this is too complicated, let's instead use a witness *)
Lemma Zeven_div2_equiv (z: Z) : Zeven z ↔ z = 2 * (Z.div2 z).
Proof.
  by induction z; [| split; destruct p.. ].
Qed.

Lemma Zeven_div2_linearity: ∀ (x y: Z),
  Zeven x ∨ Zeven y →
  Z.div2 (x + y) = Z.div2 x + Z.div2 y.
Proof.
  destruct 1; destruct x, y; try lia; destruct p, p0; try done; lia.
Qed.


(** Filters + Triggers *)
Ltac my_Zeven_rewrite_hyps H :=
  setoid_rewrite Zeven_div2_equiv in H.

Ltac my_Zeven_rewrite_goal :=
  let H := fresh "H_Zeven_div2_linearity" in
  generalize Zeven_div2_linearity;
  setoid_rewrite Zeven_div2_equiv;
  intros H.


Ltac2 my_Zeven_hyp_trigger () :=
  TContains (TSomeHyp, Arg id) (TConstant (Init.Some "Zeven") NotArg).

Ltac2 my_Zeven_goal_trigger () :=
  TContains (TGoal, NotArg) (TConstant (Init.Some "Zeven") NotArg).

Ltac2 Set sniper_transformations as st := fun () =>
  ((my_Zeven_hyp_trigger (), Init.false, Init.None), "my_Zeven_rewrite_hyps", trivial_filter) ::
  ((my_Zeven_goal_trigger (), Init.false, Init.None), "my_Zeven_rewrite_goal", trivial_filter) ::
  (st ()).



(** The proof *)

Lemma EvenInt_add_even_proof (π : thread_id) :
  EvenInt_add_even_lemma π.
Proof.
  EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: try solve [ sidecond_solver ].
  Unshelve.
    all: unshelve_sidecond.
    all: clear_unused_vars.
    all: clear FN_NAME.
    all: repeat match goal with
    | H : JCACHED _ |- _ => clear H
    | H : CACHED _ |- _ => clear H
    | H : bb_inv_map_marker _ |- _ => clear H
    end.
    all: snipe.

  Unshelve. all: print_remaining_sidecond.
Qed.

End proof.
