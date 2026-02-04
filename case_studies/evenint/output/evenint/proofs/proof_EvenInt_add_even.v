From Sniper Require Import Sniper.
From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint.generated Require Import generated_code_evenint generated_specs_evenint generated_template_EvenInt_add_even.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

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

Lemma EvenInt_add_even_proof (π : thread_id) :
  EvenInt_add_even_lemma π.
Proof.
  EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { (* Currently, the environment needs to be cleared because `snipe` will try to unfold definitions. *)
    (* It is not yet possible to register new definitions. *)

    (* The filters are defined in the file `sniper/orchestrator/triggers_tactics.v`, *)
    (* in those lists: `filter_reflexivity` and `filter_algebraic_types` *)
    clear -H8 H9.

    (* Due to the above limitations, let's do manual rewriting *)
    (* Command idea: Snipe Register Zeven [Zeven_div2_linearity; ...] *)
    revert H8 H9.
    generalize Zeven_div2_linearity.

    (* Command idea: Snipe Rewrite Zeven Zeven_div2_equiv. *)
    setoid_rewrite Zeven_div2_equiv.

    (* Finally ! *)
    verit. }

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
