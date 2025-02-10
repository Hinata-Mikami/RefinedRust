From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_client_get_mut_client.

Set Default Proof Using "Type".

  (*
Axiom fixme : ∀ P : Prop, P.
Ltac fixme := apply fixme.


Section proof.
Context `{!refinedrustGS Σ}.
Lemma client_get_mut_client_proof (π : thread_id) :
  client_get_mut_client_lemma π.
Proof.
  client_get_mut_client_prelude.

  (*rep liRStep; liShow.*)
  (* 7013 *)
  rep 500 liRStep; liShow.
  rep 100 liRStep; liShow.
  rep 50 liRStep; liShow.
  rep 20 liRStep; liShow.
  rep 10 liRStep; liShow.

  liRStep; liShow.

  (* this step is problematic, in particular the simpl *)
  (*liRStep; liShow.*)
  liEnsureInvariant; liStep.
  cbn.

  unfold spec_collapse_params.
  unfold replicate.
  cbn - [tyl_wf_E tyl_outlives_E ty_wf_E].

  rep liRStep; liShow.


  (*fixme.*)


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: unsafe_unfold_common_caesium_defs; solve_goal.
  Unshelve. all: print_remaining_sidecond.
Timeout 30 Qed.
*)

Section proof.
Context `{!refinedrustGS Σ}.
Lemma client_get_mut_client_proof (π : thread_id) :
  client_get_mut_client_lemma π.
Proof.
  client_get_mut_client_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: unsafe_unfold_common_caesium_defs; solve_goal.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
