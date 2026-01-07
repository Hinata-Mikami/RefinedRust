From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export proofmode.
From iris.program_logic Require Import lifting.
From caesium Require Export tactics lifting.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wps_bind `{refinedcG Σ} `{!LayoutAlg} e Ks π Q Ψ E s:
  W.find_stmt_fill s = Some (Ks, e) →
  WPe{π} (W.to_expr e) @ E {{ λ v, WPs{π} W.to_stmt (W.stmt_fill Ks (W.Val v)) @ E {{ Q, Ψ }} }} ⊢
  WPs{π} (W.to_stmt s) @ E {{ Q, Ψ }}.
Proof.
  move => /W.find_stmt_fill_correct ->. iIntros "He".
  rewrite stmt_wp_eq. iIntros (? rf ->) "?".
  have [Ks' HKs']:= W.stmt_fill_correct Ks π rf. rewrite HKs'.
  iApply wp_bind.
  rewrite expr_wp_unfold.
  iApply (wp_wand with "He"). iIntros (v) "HWP".
  rewrite -(HKs' (W.Val _)) /W.to_expr. by iApply "HWP".
Qed.

Tactic Notation "wps_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (stmt_wp ?E ?π ?Q ?Ψ ?s) =>
    let s' := W.of_stmt s in change (stmt_wp E π Q Ψ s) with (stmt_wp E π Q Ψ (W.to_stmt s'));
    iApply tac_wps_bind; [done |];
    unfold W.to_expr, W.to_stmt; simpl; unfold W.to_expr; simpl
  | _ => fail "wps_bind: not a 'wp'"
  end.

Lemma tac_wpe_bind' `{refinedcG Σ} `{!LayoutAlg} π e Ks Φ E:
  WPe{π} (W.to_expr e) @ E {{ λ v, WPe{π} (W.to_expr (W.fill Ks (W.Val v))) @ E{{ Φ }} }} ⊢
  WPe{π} (W.to_expr (W.fill Ks e)) @ E {{ Φ }}.
Proof.
  iIntros "HWP".
  have [Ks' HKs']:= W.ectx_item_correct π Ks.
  rewrite !expr_wp_unfold/expr_wp_def.
  rewrite HKs'. iApply wp_bind.
  iApply (wp_wand with "HWP"). iIntros (v) "HWP".
  rewrite expr_wp_unfold /expr_wp_def.
  by rewrite HKs'.
Qed.

Lemma tac_wpe_bind `{refinedcG Σ} `{!LayoutAlg} π e Ks e' Φ E:
  W.find_expr_fill e false = Some (Ks, e') →
  WPe{π} (W.to_expr e') @ E {{ λ v, if Ks is [] then Φ v else WPe{π} (W.to_expr (W.fill Ks (W.Val v))) @ E{{ Φ }} }} ⊢
  WPe{π} (W.to_expr e) @ E {{ Φ }}.
Proof.
  move => /W.find_expr_fill_correct ->. move: Ks => [|K Ks] //.
  move: (K::Ks) => {K}Ks. by iApply tac_wpe_bind'.
Qed.

Tactic Notation "wpe_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (expr_wp ?E ?π ?Φ ?e) =>
    let e' := W.of_expr e in change (expr_wp E π Φ e) with (expr_wp E π Φ (W.to_expr e'));
    iApply tac_wpe_bind; [done |];
    unfold W.to_expr; simpl
  | _ => fail "wp_bind: not a 'wp'"
  end.

