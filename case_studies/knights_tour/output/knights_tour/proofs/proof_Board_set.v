From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_Board_set.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Board_set_proof (π : thread_id) :
  Board_set_lemma π.
Proof.
  Board_set_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(knights_tour.set) *)
  rep <- 2 liRStep; liShow.
  liInst Hevar_x2 (<[Z.to_nat (wrap_to_it p usize) := (<[Z.to_nat (wrap_to_it p0 usize):= v]> (self0 !!! Z.to_nat (wrap_to_it p usize))) ]> self0).
  rep liRStep. 
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  (* !start proof(knights_tour.set) *)
  - rewrite Hnestedlen; solve_goal.
  - apply list_subequiv_fmap.
    apply list_subequiv_insert_in_r; first solve_goal.
    done.
  - eexists. split; first solve_goal.
    f_equiv.
    rewrite list_lookup_total_insert_eq; last solve_goal.
    rewrite !list_fmap_insert. done.
  - rewrite list_lookup_total_insert.
    case_decide; first rewrite length_insert.
    all: apply Hnestedlen; solve_goal.
  - rewrite list_lookup_total_insert.
    case_decide; first last.
    { apply Hnonnegative. solve_goal. }
    rename select (Z.to_nat p = i ∧ _) into Hpeqi.
    destruct Hpeqi as [->].
    rewrite list_lookup_total_insert.
    case_decide; first done.
    apply Hnonnegative. solve_goal.
  - case_decide.
    + rewrite list_lookup_total_insert.
      case_decide.
      all: rename select ((_,_) = (_,_)) into Heq.
      all: injection Heq as Hi Hj.
      { 
        rewrite <-Hj.
        rewrite list_lookup_total_insert.
        case_decide; first done.
        solve_goal.
      } 
      solve_goal.
    + rewrite list_lookup_total_insert.
      case_decide; last done.
      rewrite list_lookup_total_insert.
      rename select (_ ≠ _) into Hpairneq.
      rename select (_ p = i ∧ _) into Hpeqi.
      case_decide.
      {
        rename select (_ p0 = j ∧ _) into Hp0eqj.
        destruct Hpeqi as [Hi _]. destruct Hp0eqj as [Hj _].
        exfalso. apply Hpairneq. solve_goal.
      }
      destruct Hpeqi as [-> _]. done.
  (* !end proof *)
Qed.
End proof.
