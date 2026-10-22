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
  all: rename select (Some _ = (if bool_decide (Z.succ 0 ∈ i32) then _ else _)) into Hfirst.
  all: have Hrange : Z.succ 0 ∈ i32 by solve_goal.
  all: rewrite bool_decide_true in Hfirst; last done.
  all: simplify_eq.
  - rename select (Z.to_nat (_ - _) = 1%nat) into Hskip.
    apply (f_equal Z.of_nat) in Hskip.
    rewrite Z2Nat.id in Hskip; lia.
  - lia.
  all: print_remaining_sidecond.
Qed.
End proof.
