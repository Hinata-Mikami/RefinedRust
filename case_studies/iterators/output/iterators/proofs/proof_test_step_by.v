From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.iterators.generated Require Import generated_code_iterators generated_specs_iterators generated_template_test_step_by.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma test_step_by_proof (π : thread_id) :
  test_step_by_lemma π.
Proof.
  test_step_by_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve.
  all: lazymatch goal with
  | Hnone : if_None ?result _, Hsome : if_Some ?result _ |- SHELVED_SIDECOND ?sidecond =>
      lazymatch sidecond with
      | context [result] =>
          destruct result as [e |]; simpl in Hnone, Hsome;
          [ destruct Hsome as (He & _); subst e
          | destruct Hnone as (_ & Hcontra); lia ]
      | _ => idtac
      end
  | _ => idtac
  end.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
  all: print_remaining_sidecond.
Qed.
End proof.
