From Sniper Require Import Sniper.
From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint.generated Require Import generated_code_evenint generated_specs_evenint generated_template_EvenInt_add_even.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

(* The lemma Zeven relies on the internal representation of Z *)
(* As this is too complicated, let's rewrite Zeven *)
Variable f: Z → Z.
Variable transport: ∀ (x: Z), Zeven x ↔ x = 2 * f x.
Variable transport_lemma: ∀ (x y: Z), f (x + y) = f x + f y.

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
    clear -transport transport_lemma H8 H9.

    (* Due to the above limitations, let's do manual rewriting *)
    revert H8 H9. rewrite !transport. clear transport.

    (* Finally ! *)
    smt. }

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
