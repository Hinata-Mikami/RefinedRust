From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint_new.generated Require Import generated_code_evenint_new generated_specs_evenint_new generated_template_EvenInt_add_two.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma EvenInt_add_two_proof (π : thread_id) :
  EvenInt_add_two_lemma π.
Proof.
  EvenInt_add_two_prelude.

  (* repeat liRStep; liShow. *) (* Lithium(RefinedC由来)の自動証明エンジン *)
                                (* 型検査を自動で行い，sideconditions を抽出 *)
                                (* repeat : エラーが出るまでリピート？ *)
  rep <-! liRStep; liShow.      (* rep <-! : fail しても backtracking point *)

  (* 1回目の self.add() で可変再借用しようとして停止 : invariant を満たさない *)
  liRStepUntil interpret_typing_hint. (* the given judgment "interpret_typing_hint" までステップを進める *)
                                      (* interpreting the typing hint for the borrow and establishing it*)
  iApply interpret_typing_hint_ignore. (* typing hint を無視する規則を適用 *)

  (* 2回目の self.add() の処理 ：同様 *)
  rep <-! liRStep; liShow.
  liRStepUntil interpret_typing_hint.
  iApply interpret_typing_hint_ignore.

  (* 最後まで型検査を進める *)
  rep <-! liRStep; liShow.

  (* sidecondition solvers を呼び出す *)
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rewrite -Z.add_assoc; apply Zeven_plus_Zeven; solve_goal. } (* Zeven (x + 1 + 1) *)
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
