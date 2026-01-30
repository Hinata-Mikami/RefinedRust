From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.hillel.generated Require Import generated_code_hillel generated_specs_hillel generated_template_fulcrum.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* !start proof(fulcrum) *)
Lemma take_S_r_total {A} `{!Inhabited A} (l : list A) (n : nat) :
  (n < length l)%nat →
  take (S n) l = take n l ++ [l !!! n].
Proof.
  intros Hlt.
  apply take_S_r.
  by apply list_lookup_lookup_total_lt.
Qed.
(* !end proof *)

Lemma fulcrum_proof (π : thread_id) :
  fulcrum_lemma π.
Proof.
  fulcrum_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  (* !start proof(fulcrum) *)
  all: try rename x'0 into j.
  all: try specialize (sum_list_Z_with_split id (Z.to_nat j) _iter_hist_7) as ?.
  all: try (opose proof (Hbounded _iter_hist_7 _); first solve_goal).
  all: try solve_goal.
  { opose proof (Hbounded (_iter_hist_7 ++ [x'1]) _) as Ha; first solve_goal.
    move: Ha. solve_goal. }
  { opose proof (Hbounded ((take (Z.to_nat j) _iter_hist_7)) _) as ?; first solve_goal.
    opose proof (Hbounded ((drop (Z.to_nat j) _iter_hist_7)) _) as ?; first solve_goal.
    solve_goal. }
  { opose proof (Hbounded (take (S (Z.to_nat j)) _iter_hist_7) _) as Ha; first solve_goal.
    move: Ha. rewrite take_S_r_total; solve_goal. }
  { opose proof (Hbounded (take (S (Z.to_nat j)) _iter_hist_7) _) as Ha; first solve_goal.
    move: Ha. rewrite take_S_r_total; solve_goal. }
  { rewrite take_S_r_total; solve_goal. }
  { destruct (decide (i = Z.to_nat j)) as [-> | ]; first lia.
    ospecialize (Hsmallest i _); solve_goal. }
  { opose proof (Hbounded (take (S (Z.to_nat j)) _iter_hist_7) _) as Ha; first solve_goal.
    move: Ha. rewrite take_S_r_total; solve_goal. }
  { opose proof (Hbounded (take (S (Z.to_nat j)) _iter_hist_7) _) as Ha; first solve_goal.
    move: Ha. rewrite take_S_r_total; solve_goal. }
  { rewrite take_S_r_total; solve_goal. }
  { destruct (decide (i = Z.to_nat j)) as [-> | ]; first lia.
    ospecialize (Hsmallest i _); solve_goal. }
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
