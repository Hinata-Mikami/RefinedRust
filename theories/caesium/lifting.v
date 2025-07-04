From iris.proofmode Require Import proofmode.
From caesium.program_logic Require Export weakestpre.
From caesium.program_logic Require Import ectx_lifting.
From caesium Require Export lang ghost_state notation.
From caesium Require Import tactics.
Export logical_step.
Set Default Proof Using "Type".
Import uPred.

Class refinedcG Σ := RefinedCG {
  refinedcG_invG :: invGS Σ;
  refinedcG_gen_heapG :: heapG Σ;
  refinedcG_trGS :: trGS Σ;
}.

Definition num_laters_per_step (n : nat) : nat := (n+n+n+n+n)%nat.
Arguments num_laters_per_step _ /.

Program Definition refinedc_trgen : tr_generation :=
  TrGeneration num_laters_per_step _.
Next Obligation.
  unfold num_laters_per_step.
  intros; simpl. lia.
Qed.

Global Program Instance c_irisG `{!refinedcG Σ} : irisGS c_lang Σ := {
  iris_invGS := refinedcG_invG;
  state_interp σ n κs _ := state_ctx σ;
  fork_post _ := True%I;
  iris_trGen := refinedc_trgen;
}.
Next Obligation.
  intros. simpl. by iIntros "$".
Defined.
Global Opaque iris_invGS.

Section logical_steps.
  Context `{!refinedcG Σ}.

  Lemma logical_step_intro_tr F P n :
    ⧗ n -∗ (⧗ (tr_f n) -∗ £ (tr_f n) ={F}=∗ P) -∗ logical_step F P.
  Proof.
    iApply logical_step_intro_tr.
  Qed.

  Lemma logical_step_intro_maybe F P n (b : bool) :
    (if b then tr n else True) -∗
    ((if b then £ (num_laters_per_step n) ∗ tr n else True) ={F}=∗ P) -∗
    logical_step F P.
  Proof.
    destruct b.
    - iIntros "Hat Hvs".
      iPoseProof (logical_step_intro_tr F with "Hat") as  "Ha".
      iApply "Ha".
      iIntros "Ha Hb".
      iApply ("Hvs" with "[$Hb Ha]").
      simpl. unfold num_laters_per_step.
      iApply tr_weaken; last done. lia.
    - iIntros "_ HP". iApply fupd_logical_step. iApply logical_step_intro. by iApply "HP".
  Qed.

  Definition maybe_logical_step (b : bool) F (P : iProp Σ) : iProp Σ :=
    if b then logical_step F P else (|={F}=> P)%I.
  Lemma maybe_logical_step_wand (b : bool) F P Q :
    (P -∗ Q) -∗
    maybe_logical_step b F P -∗ maybe_logical_step b F Q.
  Proof.
    iIntros "Hvs Hstep". destruct b; simpl.
    - iApply (logical_step_wand with "Hstep Hvs").
    - iMod "Hstep". by iApply "Hvs".
  Qed.
  Lemma maybe_logical_step_intro b F P :
    P -∗ maybe_logical_step b F P.
  Proof.
    iIntros "HP". rewrite /maybe_logical_step.
    destruct b; first iApply logical_step_intro; eauto.
  Qed.

  Lemma maybe_logical_step_fupd step F P :
    maybe_logical_step step F (|={F}=> P) -∗
    maybe_logical_step step F P.
  Proof.
    destruct step; simpl.
    - iApply logical_step_fupd.
    - rewrite fupd_trans; auto.
  Qed.

  Lemma maybe_logical_step_compose (E : coPset) step (P Q : iProp Σ) :
    maybe_logical_step step E P -∗ maybe_logical_step step E (P -∗ Q) -∗ maybe_logical_step step E Q.
  Proof.
    iIntros "Ha Hb". destruct step; simpl.
    - iApply (logical_step_compose with "Ha Hb").
    - iMod "Ha". iMod "Hb". by iApply "Hb".
  Qed.
End logical_steps.

Section physical_step.
  Context `{!refinedcG Σ}.

  (** Derived rules as sanity check *)
  Lemma physical_step_intro_tr n P E :
    ⧗ n -∗
    ▷ (⧗ (tr_f (S n)) -∗ £ (tr_f (S n)) ={E}=∗ P) -∗
    |={E}⧗=> P.
  Proof.
    iIntros "Htr Ha".
    iApply (physical_step_tr_use with "Htr").
    iApply physical_step_step.
    iSplit.
    { iMod (tr_persistent_zero) as "$".
      iMod (fupd_mask_subseteq) as "_"; last done. set_solver. }
    iIntros "Hcred1 Htr1".
    iMod (fupd_mask_subseteq ∅) as "Hcl"; first set_solver.
    iModIntro. simpl.
    iModIntro.
    iNext. iModIntro. iMod "Hcl".
    iModIntro.
    iIntros "Htr Hcred".
    iCombine "Hcred1 Hcred" as "Hcred".
    iCombine "Htr1 Htr" as "Htr".
    iApply ("Ha" with "[Htr] [Hcred]").
    - iApply (tr_weaken with "Htr").
      simpl. unfold num_laters_per_step. lia.
    - iApply (lc_weaken with "Hcred").
      simpl. unfold num_laters_per_step. lia.
  Qed.

  Lemma physical_step_intro_lc E P :
    (£ (num_laters_per_step 1) ={E}=∗ ▷ P) -∗
    |={E}⧗=> P.
  Proof.
    iIntros "Ha".
    iApply physical_step_step.
    iSplit. { iMod (tr_persistent_zero) as "$". iMod (fupd_mask_subseteq) as "_"; last done. set_solver. }
    iIntros "Hcred Hreceipt".
    iMod ("Ha" with "Hcred") as "Ha".
    iMod (fupd_mask_subseteq ∅) as "Hcl"; first set_solver.
    iModIntro. simpl.
    iModIntro.
    iNext. iModIntro. iMod "Hcl". done.
  Qed.
End physical_step.

Global Instance into_val_val v : IntoVal (to_rtexpr (Val v)) v.
Proof. done. Qed.

Local Hint Extern 0 (reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Unfold heap_at : core.


Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; unfold coerce_rtexpr in *; simplify_eq; inv_expr_step; naive_solver
    |unfold coerce_rtexpr in *;apply ectxi_language_sub_redexes_are_values; intros [[]|[]] **; naive_solver].

Global Instance cas_atomic s ot (v1 v2 v3 : val) : Atomic s (coerce_rtexpr (CAS ot v1 v2 v3)).
Proof. solve_atomic. Qed.
Global Instance skipe_atomic s (v : val) : Atomic s (coerce_rtexpr (SkipE v)).
Proof. solve_atomic. Qed.
Global Instance deref_atomic s (l : loc) ly mc : Atomic s (coerce_rtexpr (Deref ScOrd ly mc l)).
Proof. solve_atomic. Qed.
(*Global Instance use_atomic s (l : loc) ly : Atomic s (coerce_rtexpr (Use ScOrd ly l)).*)
(*Proof. solve_atomic. Qed.*)

(*** General lifting lemmas *)

Section lifting.
  Context `{!refinedcG Σ}.

  Lemma wp_logical_step (e : runtime_expr) E1 E2 P Φ :
    TCEq (to_val e) None → E1 ⊆ E2 →
    logical_step E1 P -∗
    WP e @ E2 {{ v, P -∗ Φ v }} -∗
    WP e @ E2 {{ Φ }}.
  Proof.
    iIntros (??) "Hstep Hwp".
    iApply (wp_step_update_strong _ _ _ _ _ Φ with "[Hstep] Hwp"); first done.
    iApply (logical_step_mask_mono with "Hstep"); done.
  Qed.

  Lemma wp_maybe_logical_step e E1 E2 P b Φ :
    TCEq (to_val e) None →
    E1 ⊆ E2 →
    maybe_logical_step b E1 P -∗
    WP e @ E2 {{ v, P -∗ Φ v }} -∗ WP e @ E2 {{ v, Φ v }}.
  Proof.
    iIntros (??) "Hstep". destruct b => /=.
    - iApply (wp_logical_step with "Hstep"); done.
    - iIntros "Hwp".
      iApply fupd_wp. iMod (fupd_mask_mono with "Hstep") as "HP"; first done.
      iModIntro. iApply wp_fupd. iApply (wp_wand with "Hwp [HP]").
      iIntros (v) "Hv". iApply ("Hv" with "HP").
  Qed.

  (** Mask-changing + physical step *)
  Lemma wp_c_lift_step_fupd E e step_rel Φ:
    ((∃ e', e = to_rtexpr e' ∧ step_rel = expr_step e') ∨
     (∃ rf s, e = to_rtstmt rf s ∧ step_rel = stmt_step s rf)) →
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, step_rel σ1 os e2 σ2 tsl⌝ ∗
         (∀ os e2 σ2 tsl, ⌜step_rel σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={∅}⧗=> |={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He ?) "HWP".
    iApply wp_lift_base_step_physical_step => //.
    iIntros (σ1 ns κ κs nt) "[[% Hhctx] Hfnctx]".
    iMod ("HWP" $! σ1 with "[$Hhctx $Hfnctx//]") as (Hstep) "HWP".
    iModIntro. iSplit. {
      iPureIntro. destruct Hstep as (?&?&?&?&?).
      naive_solver eauto using ExprStep, StmtStep.
    }
    clear Hstep. iIntros (??? Hstep).
    move: (Hstep) => /runtime_step_preserves_invariant?.
    destruct He as [[e' [??]]|[? [s [??]]]]; inversion Hstep; simplify_eq.
    all: try by [destruct e'; discriminate].
    all: try match goal with | H : to_rtexpr ?e = to_rtstmt _ _ |- _ => destruct e; discriminate end.
    all: iSpecialize ("HWP" with "[//] [%]"); first naive_solver.
    all: iApply (physical_step_wand with "HWP"); iIntros "HWP".
    all: iMod "HWP" as (->) "[$ HWP]".
    all: iFrame.
    all: by iModIntro => /=.
  Qed.
  Lemma wp_lift_expr_step_fupd E (e : expr) Φ:
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, expr_step e σ1 os e2 σ2 tsl⌝ ∗
        (∀ os e2 σ2 tsl, ⌜expr_step e σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={∅}⧗=> |={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtexpr e @ E {{ Φ }}.
  Proof. iIntros (?) "HWP". iApply (wp_c_lift_step_fupd) => //. naive_solver. Qed.
  Lemma wp_lift_stmt_step_fupd E s rf Φ:
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, stmt_step s rf σ1 os e2 σ2 tsl⌝ ∗
         (∀ os e2 σ2 tsl, ⌜stmt_step s rf σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={∅}⧗=> |={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtstmt rf s @ E {{ Φ }}.
  Proof. iIntros "HWP". iApply (wp_c_lift_step_fupd) =>//. naive_solver. Qed.

  (** Not mask-changing + physical step*)
  Lemma wp_c_lift_step E e step_rel Φ:
    ((∃ e', e = to_rtexpr e' ∧ step_rel = expr_step e') ∨
     (∃ rf s, e = to_rtstmt rf s ∧ step_rel = stmt_step s rf)) →
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E}=∗
       ⌜∃ os e2 σ2 tsl, step_rel σ1 os e2 σ2 tsl⌝ ∗
         (∀ os e2 σ2 tsl, ⌜step_rel σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={E}⧗=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (??) "HWP".
    iApply (wp_c_lift_step_fupd) => //.
    iIntros (?) "Hσ". iMod ("HWP" with "Hσ") as "[$ HWP]".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iIntros (??????).
    iSpecialize ("HWP" with "[//] [//]").
    iMod "HE".
    iApply (physical_step_wand with "HWP"). iIntros "$".
    iApply fupd_mask_intro_subseteq; first set_solver.
    done.
  Qed.
  Lemma wp_lift_expr_step E (e : expr) Φ:
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E}=∗
       ⌜∃ os e2 σ2 tsl, expr_step e σ1 os e2 σ2 tsl⌝ ∗
        (∀ os e2 σ2 tsl, ⌜expr_step e σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={E}⧗=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtexpr e @ E {{ Φ }}.
  Proof. iIntros (?) "HWP". iApply (wp_c_lift_step) => //. naive_solver. Qed.
  Lemma wp_lift_stmt_step E s rf Φ:
    (∀ (σ1 : state), state_ctx σ1 ={E}=∗
       ⌜∃ os e2 σ2 tsl, stmt_step s rf σ1 os e2 σ2 tsl⌝ ∗
         (∀ os e2 σ2 tsl, ⌜stmt_step s rf σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={E}⧗=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtstmt rf s @ E {{ Φ }}.
  Proof. iIntros "HWP". iApply (wp_c_lift_step) =>//. naive_solver. Qed.
End lifting.

(*** Lifting of expressions *)
Global Instance wp_expr_wp `{!refinedcG Σ} : Wp (iProp Σ) expr val stuckness :=
  λ s E e Φ, (WP (coerce_rtexpr e) @ s; E {{ Φ }})%I.

Lemma to_expr_wp `{!refinedcG Σ} (e : expr) s E Φ :
  WP e @ s; E {{ Φ }} -∗
  WP (coerce_rtexpr e) @ s; E {{ Φ }}.
Proof. auto. Qed.

Section expr_lifting.
Context `{!refinedcG Σ}.

Lemma ewp_logical_step (e : expr) E1 E2 P Φ :
  TCEq (to_val e) None → E1 ⊆ E2 →
  logical_step E1 P -∗
  WP e @ E2 {{ v, P -∗ Φ v }} -∗
  WP e @ E2 {{ Φ }}.
Proof.
  rewrite /wp /wp_expr_wp. eapply wp_logical_step.
Qed.

Lemma ewp_fupd s E (e : expr) Φ :
  WP e @ s; E {{ v, |={E}=> Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof. rewrite /wp /wp_expr_wp. iApply wp_fupd. Qed.

Lemma wp_alloc_failed E Φ:
  ⊢ WP AllocFailed @ E {{ Φ }}.
Proof.
  iLöb as "IH".
  iApply wp_lift_pure_det_base_step_no_fork'; [done|by eauto using AllocFailedStep| | by iIntros "!> _"].
  move => ????? . inversion 1; simplify_eq => //.
  match goal with | H: to_rtexpr ?e = AllocFailed |- _ => destruct e; discriminate end.
Qed.


Lemma wp_binop v1 v2 Φ op E ot1 ot2:
  (∀ σ, state_ctx σ ={E, ∅}=∗
    ⌜∃ v', eval_bin_op op ot1 ot2 σ v1 v2 v'⌝ ∗
     |={∅}⧗=> (∀ v', ⌜eval_bin_op op ot1 ot2 σ v1 v2 v'⌝ -∗ |={∅, E}=> state_ctx σ ∗ Φ v')) -∗
  WP BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_expr_step_fupd; auto.
  iIntros (σ1) "Hctx".
  iMod ("HΦ" with "Hctx") as ([v' Heval]) "HΦ". iModIntro.
  iSplit; first by eauto 8 using BinOpS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ").
  iIntros "Ha".
  iMod ("Ha" with "[//]") as "($ & ?)".
  iModIntro. iSplit => //. by iApply wp_value.
Qed.

Lemma wp_binop_det v' v1 v2 Φ op E ot1 ot2:
  (∀ σ, state_ctx σ ={E, ∅}=∗ ⌜∀ v, eval_bin_op op ot1 ot2 σ v1 v2 v ↔ v = v'⌝ ∗ |={∅}⧗=> (|={∅, E}=> state_ctx σ ∗ Φ v')) -∗
    WP BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_binop. iIntros (σ) "Hctx".
  iMod ("H" with "Hctx") as (Hv) "HΦ". iModIntro.
  iSplit.
  { iExists v'. by rewrite Hv. }
  iApply (physical_step_wand with "HΦ").
  by iIntros "Ha" (v ->%Hv).
Qed.

Lemma wp_binop_det_pure v' v1 v2 Φ op E ot1 ot2:
  (∀ σ v, eval_bin_op op ot1 ot2 σ v1 v2 v ↔ v = v') →
  (|={E}⧗=> Φ v') -∗
  WP BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hop) "HΦ". iApply (wp_binop_det v').
  iIntros (σ) "Hσ". iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iSplit; [done|].
  iMod "He".
  iApply (physical_step_wand with "HΦ").
  iIntros "$". iApply fupd_mask_intro_subseteq; first set_solver. done.
Qed.

Lemma wp_check_binop v1 v2 Φ op E ot1 ot2:
  (⌜∃ b, check_bin_op op ot1 ot2 v1 v2 b⌝ ∗
    |={E}⧗=> (∀ b, ⌜check_bin_op op ot1 ot2 v1 v2 b⌝ -∗ Φ (val_of_bool b))) -∗
  WP CheckBinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros "((%b & %Hcheck) & HΦ)".
  iApply wp_lift_expr_step_fupd; auto.
  iIntros (σ1) "Hctx".
  iMod (fupd_mask_subseteq ∅) as "Hcl"; first set_solver.
  iModIntro.
  iSplit; first by eauto 8 using CheckBinOpS.
  clear Hcheck.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iMod "Hcl".
  iApply (physical_step_wand with "HΦ").
  iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iPoseProof ("HΦ" with "[//]") as "HΦ".
  iSplit => //. iFrame. by iApply wp_value.
Qed.

Lemma wp_check_binop_det_pure b' v1 v2 Φ op E ot1 ot2:
  (∀ b, check_bin_op op ot1 ot2 v1 v2 b ↔ b = b') →
  (|={E}⧗=> Φ (val_of_bool b')) -∗
  WP CheckBinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (H) "H".
  iApply wp_check_binop.
  iSplitR. { iPureIntro. exists b'. by apply H. }
  iApply (physical_step_wand with "H").
  by iIntros "?" (b <-%H).
Qed.

Lemma wp_unop v1 Φ op E ot:
  (∀ σ, state_ctx σ ={E, ∅}=∗
    ⌜∃ v', eval_un_op op ot σ v1 v'⌝ ∗
    |={∅}⧗=> (∀ v', ⌜eval_un_op op ot σ v1 v'⌝ ={∅, E}=∗ state_ctx σ ∗ Φ v')) -∗
   WP UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_expr_step_fupd; auto.
  iIntros (σ1) "Hctx".
  iMod ("HΦ" with "Hctx") as ([v' Heval]) "HΦ". iModIntro.
  iSplit; first by eauto 8 using UnOpS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iMod ("HΦ" with "[//]") as "[$ HΦ]".
  iModIntro. iSplit => //. by iApply wp_value.
Qed.

Lemma wp_unop_det v' v1 Φ op E ot:
  (∀ σ, state_ctx σ ={E, ∅}=∗ ⌜∀ v, eval_un_op op ot σ v1 v ↔ v = v'⌝ ∗ |={∅}⧗=> (|={∅, E}=> state_ctx σ ∗ Φ v')) -∗
  WP UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_unop. iIntros (σ) "Hctx".
  iMod ("H" with "Hctx") as (Hv) "HΦ". iModIntro.
  iSplit.
  { iExists v'. by rewrite Hv. }
  iApply (physical_step_wand with "HΦ").
  by iIntros "?" (v ->%Hv).
Qed.

Lemma wp_unop_det_pure v' v1 Φ op E ot:
  (∀ σ v, eval_un_op op ot σ v1 v ↔ v = v') →
  (|={E}⧗=> Φ v') -∗
  WP UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros (Hop) "HΦ". iApply (wp_unop_det v').
  iIntros (σ) "Hσ". iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iSplit; [done|].
  iMod "He".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_check_unop v1 Φ op E ot:
  (⌜∃ b', check_un_op op ot v1 b'⌝ ∗
    |={E}⧗=> (∀ b', ⌜check_un_op op ot v1 b'⌝ -∗ Φ (val_of_bool b'))) -∗
   WP CheckUnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros "((%b' & %Hb') & HΦ)".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "Hctx".
  iModIntro.
  iSplit; first by eauto 8 using CheckUnOpS.
  clear Hb'. iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame. iApply wp_value.
  by iApply "HΦ".
Qed.

Lemma wp_check_unop_det_pure b' v1 Φ op E ot:
  (∀ b, check_un_op op ot v1 b ↔ b = b') →
  (|={E}⧗=> (Φ (val_of_bool b'))) -∗
  WP CheckUnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros (H) "H".
  iApply wp_check_unop.
  iSplitR. { iPureIntro. exists b'. by apply H. }
  iApply (physical_step_wand with "H"). iIntros "H".
  by iIntros (b <-%H).
Qed.

Lemma wp_deref v Φ vl l ot q E o:
  o = ScOrd ∨ o = Na1Ord →
  val_to_loc vl = Some l →
  l `has_layout_loc` ot_layout ot →
  v `has_layout_val` ot_layout ot →
  l↦{q}v -∗ (|={E}⧗=> (∀ st, l ↦{q} v -∗ Φ (mem_cast v ot st))) -∗ WP !{ot, o} (Val vl) @ E {{ Φ }}.
Proof.
  iIntros (Ho Hl Hll Hlv) "Hmt HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros ([[h ub] fn]) "((%&Hhctx&Hactx)&Hfctx)/=".
  iDestruct (heap_pointsto_is_alloc with "Hmt") as %Haid.
  destruct o; try by destruct Ho.
  - iModIntro. iDestruct (heap_pointsto_lookup_q (λ st, ∃ n, st = RSt n) with "Hhctx Hmt") as %Hat. { naive_solver. }
    iSplit; first by eauto 11 using DerefS.
    iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
    iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
    iSplit => //. unfold end_st, end_expr.
    have <- : (v = v') by apply: heap_at_inj_val.
    rewrite /heap_fmap/=. erewrite heap_upd_heap_at_id => //.
    iFrame. iSplit; first done. iApply wp_value.
    by iApply ("HΦ" with "Hmt").
  - iMod (heap_read_na with "Hhctx Hmt") as "(% & Hσ & Hσclose)" => //. iModIntro.
    iSplit; first by eauto 11 using DerefS.
    iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
    iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
    iSplit => //. unfold end_st, end_expr.
    have ? : (v = v') by apply: heap_at_inj_val. subst v'.
    iFrame => /=. iSplit; first done.
    iApply wp_lift_expr_step; auto.
    iIntros ([[h2 ub2] fn2]) "((%&Hhctx&Hactx)&Hfctx)/=".
    iMod ("Hσclose" with "Hhctx") as (?) "(Hσ & Hv)".
    iModIntro; iSplit; first by eauto 11 using DerefS.
    iIntros (? e2 σ2 efs Hst ?).
    iApply physical_step_intro.
    inv_expr_step. iSplit => //.
    have ? : (v = v') by apply: (heap_at_inj_val _ _ h2). subst.
    iFrame. iSplit; first done.
    iApply wp_value. by iApply ("HΦ" with "Hv").
Qed.

(*
  Alternative version of the CAS rule which does not rely on the Atomic infrastructure:
  Lemma wp_cas vl1 vl2 vd Φ l1 l2 it E:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  (bytes_per_int it ≤ bytes_per_addr)%nat →
  (|={E, ∅}=> ∃ (q1 q2 : Qp) vo ve z1 z2,
     ⌜val_to_Z vo it = Some z1⌝ ∗ ⌜val_to_Z ve it = Some z2⌝ ∗
     ⌜l1 `has_layout_loc` it_layout it⌝ ∗ ⌜l2 `has_layout_loc` it_layout it⌝ ∗
     ⌜length vd = bytes_per_int it⌝ ∗ ⌜if bool_decide (z1 = z2) then q1 = 1%Qp else q2 = 1%Qp⌝ ∗
     l1↦{q1}vo ∗ l2↦{q2}ve ∗ ▷ (
       l1↦{q1} (if bool_decide (z1 = z2) then vd else vo) -∗
       l2↦{q2} (if bool_decide (z1 = z2) then ve else vo)
       ={∅, E}=∗ Φ (val_of_bool (bool_decide (z1 = z2))))) -∗
   WP CAS (IntOp it) (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
*)

Lemma wp_cas_fail vl1 vl2 vd vo ve z1 z2 Φ l1 l2 ot q E:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  l1 `has_layout_loc` ot_layout ot →
  l2 `has_layout_loc` ot_layout ot →
  val_to_Z_ot vo ot = Some z1 →
  val_to_Z_ot ve ot = Some z2 →
  length vd = (ot_layout ot).(ly_size) →
  ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
  z1 ≠ z2 →
  l1↦{q}vo -∗ l2↦ve -∗
  (|={E}⧗=> (l1 ↦{q} vo -∗ l2↦vo -∗ Φ (val_of_bool false))) -∗
   WP CAS ot (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Hneq) "Hl1 Hl2 HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "((%&Hhctx&?)&Hfctx)".
  iDestruct (heap_pointsto_is_alloc with "Hl1") as %Haid1.
  iDestruct (heap_pointsto_is_alloc with "Hl2") as %Haid2.
  move: (Hvo) (Hve) => /val_to_Z_ot_length ? /val_to_Z_ot_length ?.
  iDestruct (heap_pointsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl1") as %? => //. { naive_solver. }
  iDestruct (heap_pointsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl2") as %? => //.
  iModIntro. iSplit; first by eauto 15 using CasFailS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step;
    have ? : (vo = vo0) by [apply: heap_lookup_loc_inj_val => //; congruence];
    have ? : (ve = ve0) by [apply: heap_lookup_loc_inj_val => //; congruence]; simplify_eq.
  have ? : (length ve0 = length vo0) by congruence.
  iApply physical_step_fupd.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iMod (heap_write with "Hhctx Hl2") as "[$ Hl2]" => //. iModIntro.
  iFrame. iSplit => //. iSplit; first done.
  iApply wp_value. by iApply ("HΦ" with "[$] [$]").
Qed.

Lemma wp_cas_suc vl1 vl2 vd vo ve z1 z2 Φ l1 l2 ot E q:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  l1 `has_layout_loc` ot_layout ot →
  l2 `has_layout_loc` ot_layout ot →
  val_to_Z_ot vo ot = Some z1 →
  val_to_Z_ot ve ot = Some z2 →
  length vd = (ot_layout ot).(ly_size) →
  ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
  z1 = z2 →
  l1↦vo -∗ l2↦{q}ve -∗
  (|={E}⧗=> (l1 ↦ vd -∗ l2↦{q}ve -∗ Φ (val_of_bool true))) -∗
  WP CAS ot (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Hneq) "Hl1 Hl2 HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "((%&Hhctx&?)&Hfctx)".
  iDestruct (heap_pointsto_is_alloc with "Hl1") as %Haid1.
  iDestruct (heap_pointsto_is_alloc with "Hl2") as %Haid2.
  move: (Hvo) (Hve) => /val_to_Z_ot_length ? /val_to_Z_ot_length ?.
  iDestruct (heap_pointsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl1") as %? => //.
  iDestruct (heap_pointsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl2") as %? => //. { naive_solver. }
  iModIntro. iSplit; first by eauto 15 using CasSucS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step;
      have ? : (ve = ve0) by [apply: heap_lookup_loc_inj_val => //; congruence];
      have ? : (vo = vo0) by [apply: heap_lookup_loc_inj_val => //; congruence]; simplify_eq.
  have ? : (length vo0 = length vd) by congruence.
  iApply physical_step_fupd.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iMod (heap_write with "Hhctx Hl1") as "[$ Hmt]" => //. iModIntro.
  iFrame. iSplit => //. iSplit; first done.
  iApply wp_value. by iApply ("HΦ" with "[$] [$]").
Qed.

Lemma wp_neg_int Φ v v' n E it:
  val_to_Z v it = Some n →
  val_of_Z (wrap_to_it (-n) it) it None = Some v' →
  (|={E}⧗=> Φ (v')) -∗ WP UnOp NegOp (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply (wp_unop_det_pure v'); [|done].
  move => ??. split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_int Φ v v' i i' E its itt:
  val_to_Z v its = Some i →
  wrap_to_it i itt = i' →
  val_of_Z i' itt (val_to_byte_prov v) = Some v' →
  (|={E}⧗=> Φ (v')) -∗ WP UnOp (CastOp (IntOp itt)) (IntOp its) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv ? Hv') "HΦ".
  iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_loc Φ v l E:
  val_to_loc v = Some l →
  (|={E}⧗=> Φ v) -∗ WP UnOp (CastOp PtrOp) PtrOp (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_bool_int Φ b v v' E it:
  val_to_bool v = Some b →
  val_of_Z (bool_to_Z b) it None = Some v' →
  (|={E}⧗=> Φ v') -∗
  WP UnOp (CastOp (IntOp it)) (BoolOp) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hb) "HΦ". iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_ptr_int Φ v v' l E it:
  val_to_loc v = Some l →
  val_of_Z l.2 it None = Some v' →
  (|={E}⧗=> Φ (v')) -∗
  WP UnOp (CastOp (IntOp it)) PtrOp (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply (wp_unop_det v').
  iIntros (σ) "Hctx".
  iMod (fupd_mask_subseteq ∅) as "Hcl"; first set_solver.
  iModIntro.
  iSplit. {
    iPureIntro. split.
    - inversion 1; by simplify_eq/=.
    - move => ->. by econstructor.
  }
  iMod "Hcl".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_cast_null_int Φ v E it:
  val_of_Z 0 it None = Some v →
  (|={E}⧗=> Φ v) -∗
  WP UnOp (CastOp (IntOp it)) PtrOp (Val NULL) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_cast_ptr_int.
  { apply val_to_of_loc. }
  { done. }
  done.
Qed.

Lemma wp_cast_int_ptr_weak Φ v a E it:
  val_to_Z v it = Some a →
  (|={E}⧗=> ∀ i, Φ (val_of_loc (i, a))) -∗
  WP UnOp (CastOp PtrOp) (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop.
  iIntros (σ) "Hctx". iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iSplit; [iPureIntro; eexists _; by econstructor |].
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iIntros (v' Hv'). iMod "HE". iModIntro. iFrame.
  inversion Hv'; simplify_eq.
  case_bool_decide; [ iApply ("HΦ")|].
  case_bool_decide; simplify_eq; [ iApply "HΦ" |].
  case_bool_decide; simplify_eq; iApply "HΦ".
Qed.

Lemma wp_cast_int_ptr_alive Φ v a p l it:
  val_to_Z v it = Some a →
  val_to_byte_prov v = Some p →
  l = (ProvAlloc (Some p), a) →
  loc_in_bounds l 0 0 -∗
  alloc_alive_loc l ∧ (|={⊤}⧗=> Φ (val_of_loc l)) -∗
  WP UnOp (CastOp PtrOp) (IntOp it) (Val v) {{ Φ }}.
Proof.
  iIntros (Hv Hp ->) "#Hlib HΦ".
  iApply wp_unop_det. iIntros (σ) "Hctx".
  destruct (decide (valid_ptr (ProvAlloc (Some p), a) σ.(st_heap))).
  2: { iDestruct "HΦ" as "[Ha _]". by iMod (alloc_alive_loc_to_valid_ptr with "Hlib Ha Hctx") as %Hb. }
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE". iDestruct "HΦ" as "[_ HΦ]".
  iSplit. {
    iPureIntro. split.
    - inversion 1; simplify_eq; case_bool_decide; by rewrite ->Hp in *.
    - move => ->. econstructor; [done..|]. rewrite Hp. by case_bool_decide.
  }
  iMod "HE".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first done.
  iFrame.
Qed.

Lemma wp_cast_int_ptr_prov_none Φ v a l it E :
  val_to_Z v it = Some a →
  min_alloc_start ≤ a →
  a ≤ max_alloc_end_zero →
  val_to_byte_prov v = None →
  l = (ProvAlloc None, a) →
  (|={E}⧗=> l ↦ [] -∗ Φ (val_of_loc l)) -∗
  WP UnOp (CastOp PtrOp) (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hs He Hprov Hl) "HΦ".
  iApply wp_unop.
  iIntros (σ) "Hctx". iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iSplit; [iPureIntro; eexists _; by econstructor |].
  iMod "HE" as "_". iApply (physical_step_wand with "HΦ"); iIntros "HΦ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iIntros (v' Hv'). iMod "HE". iModIntro. iFrame.
  inversion Hv'; simplify_eq.
  case_bool_decide.
  { rewrite Hprov. iApply ("HΦ" with "[]"). iApply heap_pointsto_prov_none_nil; done. }
  exfalso. match goal with H : ¬ (valid_ptr _ _) |- _ => apply H end.
  rewrite Hprov. split; right; done.
Qed.

Lemma wp_cast_int_null Φ v E it:
  val_to_Z v it = Some 0 →
  (|={E}⧗=> Φ (val_of_loc NULL_loc)) -∗
  WP UnOp (CastOp PtrOp) (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - inversion 1; simplify_eq => //. case_bool_decide; last done. exfalso.
    revert select (valid_ptr _ _) => /valid_ptr_in_allocation_range []/=.
    rewrite /min_alloc_start //.
  - move => ->. econstructor => //. case_bool_decide; last done. exfalso.
    revert select (valid_ptr _ _) => /valid_ptr_in_allocation_range []/=.
    rewrite /min_alloc_start //.
Qed.

Lemma wp_cast_int_bool Φ v n E it:
  val_to_Z v it = Some n →
  (|={E}⧗=> Φ (val_of_bool (bool_decide (n ≠ 0)))) -∗
  WP UnOp (CastOp BoolOp) (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ". iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - inversion 1; simplify_eq.
    revert select (cast_to_bool _ _ _ = _) => /=.
    rewrite Hv. by move => /= [<-].
  - move => ->. econstructor => //=. by rewrite Hv.
Qed.

Lemma wp_erase_prov Φ v ly E :
  v `has_layout_val` ly →
  (|={E}⧗=> Φ (erase_prov v)) -∗
  WP UnOp EraseProv (UntypedOp ly) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ". iApply (wp_unop_det_pure (erase_prov v)).
  { iIntros (? vt). split.
    - by inversion 1.
    - intros ->. econstructor; [done | | done].
      rewrite /erase_prov /has_layout_val length_fmap //. }
  eauto.
Qed.

Lemma wp_copy_alloc_id Φ it a l v1 v2 E :
  val_to_Z v1 it = Some a →
  val_to_loc v2 = Some l →
  (|={E}⧗=> Φ (val_of_loc (l.1, a))) -∗
  WP CopyAllocId (IntOp it) (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Ha Hl) "HΦ".
  iApply wp_lift_expr_step => //.
  iIntros (σ1) "Hctx". iModIntro.
  iSplit; first by eauto 8 using CopyAllocIdS.
  iIntros (???? Hstep ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame.
  iApply wp_value. iApply ("HΦ").
Qed.

Definition int_arithop_result (it : int_type) n1 n2 op : option Z :=
  match op with
  | AddOp => Some (n1 + n2)
  | SubOp => Some (n1 - n2)
  | MulOp => Some (n1 * n2)
  | UncheckedAddOp => Some (n1 + n2)
  | UncheckedSubOp => Some (n1 - n2)
  | UncheckedMulOp => Some (n1 * n2)
  | AndOp => Some (Z.land n1 n2)
  | OrOp  => Some (Z.lor n1 n2)
  | XorOp => Some (Z.lxor n1 n2)
  | ShlOp => Some (n1 ≪ n2)
  | ShrOp => Some (n1 ≫ n2)
  | DivOp => Some (n1 `quot` n2)
  | ModOp => Some (n1 `rem` n2)
  | _     => None (* Relational operators. *)
  end.

Definition int_arithop_sidecond (it : int_type) (n1 n2 n : Z) op : Prop :=
  match op with
  | AddOp => True
  | SubOp => True
  | MulOp => True
  | UncheckedAddOp => n ∈ it
  | UncheckedSubOp => n ∈ it
  | UncheckedMulOp => n ∈ it
  | AndOp => True
  | OrOp  => True
  | XorOp => True
  (* TODO check semantics of shifting operators *)
  | ShlOp => 0 ≤ n2 < bits_per_int it ∧ 0 ≤ n1
  | ShrOp => 0 ≤ n2 < bits_per_int it ∧ 0 ≤ n1 (* Result of shifting negative numbers is implementation defined. *)
  | DivOp => n2 ≠ 0
  | ModOp => n2 ≠ 0
  | _     => True (* Relational operators. *)
  end.

Lemma wp_int_arithop Φ op v1 v2 n1 n2 nr it E :
  val_to_Z v1 it = Some n1 →
  val_to_Z v2 it = Some n2 →
  int_arithop_result it n1 n2 op = Some nr →
  int_arithop_sidecond it n1 n2 nr op →
  (∀ v, ⌜val_of_Z (wrap_to_it nr it) it None = Some v⌝ -∗ |={E}⧗=> Φ v) -∗
  WP BinOp op (IntOp it) (IntOp it) (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hn1 Hn2 Hop Hsc) "HΦ".
  assert (wrap_to_it nr it ∈ it) as [v Hv]%(val_of_Z_is_Some None).
  { apply wrap_to_it_in_range. }
  move: (Hv) => /val_of_Z_in_range ?.
  iApply (wp_binop_det_pure v with "[HΦ]"). 2: by iApply "HΦ".
  move => ??. split.
  + destruct op => //.
    all: inversion 1; simplify_eq/=.
    all: try case_bool_decide => //.
    all: simplify_eq/= => //.
    all: try rewrite ->wrap_to_it_id in Hv; simplify_eq; done.
  + move => ->. destruct op.
    1-25: (apply: ArithOpII; [|done|done|];
        first (simpl; try done; try case_bool_decide; naive_solver)).
    all: try done.
Qed.

Lemma wp_check_int_arithop Φ op v1 v2 n1 n2 b it E :
  val_to_Z v1 it = Some n1 →
  val_to_Z v2 it = Some n2 →
  check_arith_bin_op op it n1 n2 = Some b →
  (|={E}⧗=> Φ (val_of_bool b)) -∗
  WP CheckBinOp op (IntOp it) (IntOp it) (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hn1 Hn2 Hop) "HΦ".
  iApply (wp_check_binop_det_pure b with "HΦ").
  intros b'. split.
  - inversion 1; simplify_eq/=. done.
  - intros ->. econstructor; done.
Qed.

Lemma wp_check_int_unop Φ op v n b it E:
  val_to_Z v it = Some n →
  check_arith_un_op op it n = Some b →
  (|={E}⧗=> Φ (val_of_bool b)) -∗
  WP CheckUnOp op (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hn Hop) "HΦ".
  iApply (wp_check_unop_det_pure b with "HΦ").
  intros b'. split.
  - inversion 1; simplify_eq/=. done.
  - intros ->. econstructor; done.
Qed.

Lemma wp_ptr_relop Φ op v1 v2 v l1 l2 b rit E :
  val_to_loc v1 = Some l1 →
  val_to_loc v2 = Some l2 →
  val_of_Z (bool_to_Z b) rit None = Some v →
  match op with
  | EqOp rit => Some (bool_decide (l1.2 = l2.2), rit)
  | NeOp rit => Some (bool_decide (l1.2 ≠ l2.2), rit)
  | LtOp rit => Some (bool_decide (l1.2 < l2.2), rit)
  | GtOp rit => Some (bool_decide (l1.2 > l2.2), rit)
  | LeOp rit => Some (bool_decide (l1.2 <= l2.2), rit)
  | GeOp rit => Some (bool_decide (l1.2 >= l2.2), rit)
  | _ => None
  end = Some (b, rit) →
  (|={E}⧗=> Φ v) -∗
  WP BinOp op PtrOp PtrOp (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hv1 Hv2 Hv Hop) "HΦ".
  iApply wp_binop. iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  destruct l1, l2; simplify_eq/=. iSplit. {
    iPureIntro. destruct op; simplify_eq/=; eexists _.
    all: apply: RelOpPP => //; repeat case_bool_decide; naive_solver.
  }
  iMod "HE" as "_". iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iIntros (v' Hstep). iMod "HE". iModIntro. iFrame.
  inversion Hstep; simplify_eq => //.
Qed.

Lemma wp_ptr_offset Φ vl l E it o ly vo:
  val_to_loc vl = Some l →
  val_to_Z vo it = Some o →
  ly_size ly * o ∈ ISize →
  loc_in_bounds (l offset{ly}ₗ o) 0 0 -∗
  loc_in_bounds l 0 0 -∗
  (|={E}⧗=> Φ (val_of_loc (l offset{ly}ₗ o))) -∗
  WP Val vl at_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo ?) "Hl Hl' HΦ".
  iApply wp_binop_det. iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iDestruct (loc_in_bounds_to_heap_loc_in_bounds' with "Hl Hσ") as %?.
  iDestruct (loc_in_bounds_to_heap_loc_in_bounds' with "Hl' Hσ") as %?.
  iSplit. {
    iPureIntro. split.
    - inversion 1. by simplify_eq.
    - move => ->. by apply PtrOffsetOpIP.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_ptr_neg_offset Φ vl l E it o ly vo:
  val_to_loc vl = Some l →
  val_to_Z vo it = Some o →
  ly_size ly * -o ∈ ISize →
  loc_in_bounds (l offset{ly}ₗ -o) 0 0 -∗
  loc_in_bounds l 0 0 -∗
  (|={E}⧗=> Φ (val_of_loc (l offset{ly}ₗ -o))) -∗
  WP Val vl at_neg_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo ?) "Hl Hl' HΦ".
  iApply wp_binop_det. iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iDestruct (loc_in_bounds_to_heap_loc_in_bounds' with "Hl Hσ") as %?.
  iDestruct (loc_in_bounds_to_heap_loc_in_bounds' with "Hl' Hσ") as %?.
  iSplit. {
    iPureIntro. split.
    - inversion 1. by simplify_eq.
    - move => ->. by apply PtrNegOffsetOpIP.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_ptr_wrapping_neg_offset Φ vl l E it o ly vo:
  val_to_loc vl = Some l →
  val_to_Z vo it = Some o →
  (|={E}⧗=> Φ (val_of_loc (l wrapping_offset{ly}ₗ -o))) -∗
  WP Val vl at_wrapping_neg_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo) "HΦ".
  iApply wp_binop_det. iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iSplit. {
    iPureIntro. split.
    - inversion 1. by simplify_eq.
    - move => ->. by apply PtrWrappingNegOffsetOpIP.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.
Lemma wp_ptr_wrapping_offset Φ vl l E it o ly vo:
  val_to_loc vl = Some l →
  val_to_Z vo it = Some o →
  (|={E}⧗=> Φ (val_of_loc (l wrapping_offset{ly}ₗ o))) -∗
  WP Val vl at_wrapping_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo) "HΦ".
  iApply wp_binop_det. iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iSplit. {
    iPureIntro. split.
    - inversion 1. by simplify_eq.
    - move => ->. by apply PtrWrappingOffsetOpIP.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_ptr_diff Φ vl1 l1 vl2 l2 ly vo:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  val_of_Z ((l1.2 - l2.2) `div` ly.(ly_size)) ISize None = Some vo →
  l1.1 = l2.1 →
  0 < ly.(ly_size) →
  loc_in_bounds l1 0 0 -∗
  loc_in_bounds l2 0 0 -∗
  (alloc_alive_loc l1 ∧ |={⊤}⧗=> Φ vo) -∗
  WP Val vl1 sub_ptr{ly , PtrOp, PtrOp} Val vl2 {{ Φ }}.
Proof.
  iIntros (Hvl1 Hvl2 Hvo ??) "Hl1 Hl2 HΦ".
  iApply wp_binop_det. iIntros (σ) "Hσ".
  destruct (decide (valid_ptr l1 σ.(st_heap))). 2: {
    iDestruct "HΦ" as "[Ha _]".
    by iMod (alloc_alive_loc_to_valid_ptr with "Hl1 Ha Hσ") as %?.
  }
  destruct (decide (valid_ptr l2 σ.(st_heap))). 2: {
    iDestruct "HΦ" as "[Ha _]".
    iMod (alloc_alive_loc_to_valid_ptr with "Hl2 [Ha] Hσ") as %?; [|done].
    by iApply alloc_alive_loc_mono.
  }
  iDestruct "HΦ" as "[_ HΦ]".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iSplit. {
    iPureIntro. split.
    - inversion 1; by simplify_eq.
    - move => ->. by apply: PtrDiffOpPP.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_get_member `{!LayoutAlg} Φ vl l sls sl n E:
  val_to_loc vl = Some l →
  use_struct_layout_alg sls = Some sl →
  is_Some (index_of sl.(sl_members) n) →
  loc_in_bounds l 0 (ly_size sl) -∗
  (|={E}⧗=> Φ (val_of_loc (l at{sl}ₗ n))) -∗
  WP Val vl at{sls} n @ E {{ Φ }}.
Proof.
  iIntros (Hvl Halg [i Hi]) "#Hl HΦ".
  rewrite /GetMember/GetMemberLoc/GetMember'/offset_of /=.
  rewrite /use_struct_layout_alg' Halg /= Hi /=.
  have [|v Hv]:= (val_of_Z_is_Some None ISize (offset_of_idx sl.(sl_members) i)). {
    rewrite int_elem_of_it_iff.
    split; first by rewrite /min_int /int_half_modulus/=; lia.
    by apply offset_of_bound. }
  rewrite Hv /=. move: Hv => /val_to_of_Z Hv.
  iApply wp_ptr_offset; [done| done | .. ].
  { have ? := offset_of_idx_le_size sl i.
    replace (ly_size U8) with 1%nat by done. rewrite Z.mul_1_l.
    have Hs : ly_size sl < max_int ISize + 1 by apply sl_size.
    have ? := MinInt_le_0 ISize.
    split; first lia.
    rewrite MaxInt_eq. lia. }
  { have ? := offset_of_idx_le_size sl i. rewrite offset_loc_sz1 //.
    iApply (loc_in_bounds_offset with "Hl"); simpl; [done| destruct l => /=; lia  | destruct l => /=; lia ]. }
  { iApply loc_in_bounds_shorten_suf; last done. lia. }
  by rewrite offset_loc_sz1.
Qed.
Lemma wp_get_member_union `{!LayoutAlg} Φ vl l ul uls n E:
  use_union_layout_alg uls = Some ul →
  val_to_loc vl = Some l →
 (* Technically, we only need vl ≠ NULL_bytes here, but we use
  the loc_in_bounds precondition for uniformity with wp_get_member *)
  loc_in_bounds l 0 (ly_size ul) -∗
  Φ (val_of_loc (l at_union{ul}ₗ n)) -∗
  WP Val vl at_union{uls} n @ E {{ Φ }}.
Proof.
  iIntros (Halg [|[??]]%val_of_to_loc) "Hlib HΦ"; subst.
  2: {
    iDestruct (loc_in_bounds_is_alloc with "Hlib") as %[[?[=]] | (? & ? & ?)].
    rewrite /GetMemberUnion/GetMemberUnionLoc. by iApply @wp_value.
  }
  rewrite /GetMemberUnion/GetMemberUnionLoc. by iApply @wp_value.
Qed.

(* TODO: lemmas for accessing discriminant/data of enum *)

Lemma wp_offset_of `{!LayoutAlg} Φ sls sl m i E:
  use_struct_layout_alg sls = Some sl →
  offset_of sl.(sl_members) m = Some i →
  (∀ v, ⌜val_of_Z i ISize None = Some v⌝ -∗ Φ v) -∗
  WP OffsetOf sls m @ E {{ Φ }}.
Proof.
  rewrite /OffsetOf. iIntros (Halg Ho) "HΦ".
  rewrite /use_struct_layout_alg' Halg /=.
  have [|? Hs]:= (val_of_Z_is_Some None ISize i). {
    rewrite int_elem_of_it_iff.
    split; first by rewrite /min_int /int_half_modulus /=; lia.
    move: Ho => /fmap_Some[?[?->]].
    by apply offset_of_bound.
  }
  rewrite Ho /= Hs /=. iApply wp_value.
  by iApply "HΦ".
Qed.

Lemma wp_offset_of_union Φ uls m E:
  Φ (i2v 0 ISize) -∗ WP OffsetOfUnion uls m @ E {{ Φ }}.
Proof. by iApply @wp_value. Qed.

Lemma wp_if_int Φ it v e1 e2 n E:
  val_to_Z v it = Some n →
  (|={E}⧗=> if bool_decide (n ≠ 0) then WP e1 @ E {{ Φ }} else WP e2 @ E {{ Φ }}) -∗
  WP IfE (IntOp it) (Val v) e1 e2 @ E {{ Φ }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?". iModIntro.
  iSplit. { iPureIntro. repeat eexists. apply IfES. rewrite /= Hn //. }
  iIntros (? ? σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame. by case_bool_decide.
Qed.

Lemma wp_if_bool Φ v e1 e2 b E:
  val_to_bool v = Some b →
  (|={E}⧗=> if b then WP e1 @ E {{ Φ }} else WP e2 @ E {{ Φ }}) -∗
  WP IfE BoolOp (Val v) e1 e2 @ E {{ Φ }}.
Proof.
  iIntros (Hb) "HΦ". iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?". iModIntro.
  iSplit. { iPureIntro. repeat eexists. apply IfES. rewrite /= Hb //. }
  iIntros (? ? σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame. by destruct b.
Qed.

Lemma wp_skip Φ v E:
  (|={E}⧗=> Φ v) -∗ WP SkipE (Val v) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?". iModIntro. iSplit; first by eauto 8 using lang.SkipES.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame. iApply wp_value. iApply "HΦ".
Qed.

Lemma wp_concat E Φ vs:
  (|={E}⧗=> Φ (mjoin vs)) -∗ WP Concat (Val <$> vs) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?".
  iModIntro. iSplit; first by eauto 8 using ConcatS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame. iApply wp_value.
  iApply "HΦ".
Qed.

Lemma wps_concat_bind_ind vs E Φ es:
  foldr (λ e f, (λ vl, WP e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP (Concat (Val <$> (vs ++ vl))) @ E {{ Φ }}) es [] -∗
  WP Concat ((Val <$> vs) ++ es) @ E {{ Φ }}.
Proof.
  rewrite -{2}(app_nil_r vs).
  move: {2 3}[] => vl2.
  elim: es vs vl2 => /=.
  - iIntros (vs vl2) "He". by rewrite !app_nil_r.
  - iIntros (e el IH vs vl2) "Hf".
    rewrite /wp/wp_expr_wp.
    have -> : (coerce_rtexpr (Concat ((Val <$> vs ++ vl2) ++ e :: el)))%E = (fill [ExprCtx (ConcatCtx (vs ++ vl2) (to_rtexpr <$> el))] (to_rtexpr e)). {
        by rewrite /coerce_rtexpr/= fmap_app fmap_cons -!list_fmap_compose.
    }
    iApply wp_bind. iApply (wp_wand with "Hf").
    iIntros (v) "Hf" => /=.
    have -> : Expr (RTConcat ((Expr <$> (RTVal <$> vs ++ vl2)) ++ of_val v :: (to_rtexpr <$> el)))
             = Concat ((Val <$> vs ++ (vl2 ++ [v])) ++ el). 2: by iApply IH.
    by rewrite /coerce_rtexpr /= !fmap_app /= (cons_middle (of_val v)) !app_assoc -!list_fmap_compose.
Qed.

Lemma wp_concat_bind E Φ es:
  foldr (λ e f, (λ vl, WP e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP (Concat (Val <$> vl)) @ E {{ Φ }}) es [] -∗
  WP Concat es @ E {{ Φ }}.
Proof. by iApply (wps_concat_bind_ind []). Qed.

Lemma wp_struct_init'' `{!LayoutAlg} E Φ sl fs:
  foldr (λ '(n, ly) f, (λ vl,
     WP (default (Val (replicate (ly_size ly) MPoison)) (n' ← n; (list_to_map fs : gmap _ _) !! n'))
        @ E {{ v, f (vl ++ [v]) }}))
    (λ vl, |={E}⧗=> Φ (mjoin vl)) sl.(sl_members) [] -∗
  WP StructInit' sl fs @ E {{ Φ }}.
Proof.
  iIntros "He".
  iApply wp_concat_bind.
  move: {2 4}[] => vs.
  iInduction (sl_members sl) as [|[o?]?] "IH" forall (vs) => /=.
  { iApply wp_concat. done. }
  iApply (wp_wand with "He"). iIntros (v') "Hfold". by iApply "IH".
Qed.
Lemma wp_struct_init' `{!LayoutAlg} E Φ sls sl fs:
  use_struct_layout_alg sls = Some sl →
  foldr (λ '(n, ly) f, (λ vl,
     WP (default (Val (replicate (ly_size ly) MPoison)) (n' ← n; (list_to_map fs : gmap _ _) !! n'))
        @ E {{ v, f (vl ++ [v]) }}))
    (λ vl, |={E}⧗=> Φ (mjoin vl)) sl.(sl_members) [] -∗
  WP StructInit sls fs @ E {{ Φ }}.
Proof.
  intros Halg. rewrite /StructInit /use_struct_layout_alg' Halg/=.
  apply wp_struct_init''.
Qed.

(* This lemma is much more useful as it also includes the layout algorithm handling and abstracts from padding *)
Lemma wp_struct_init `{!LayoutAlg} E (Φ : val → iProp Σ) (sls : struct_layout_spec) (sl : struct_layout) (fs : list (string * expr)):
  use_struct_layout_alg sls = Some sl →
  foldr (λ '(n, st) f, (λ vl : list val,
     ∀ ly, ⌜syn_type_has_layout st ly⌝ -∗
     WP (default (Val (replicate (ly_size ly) MPoison)) ((list_to_map fs : gmap _ _) !! n)) @ E {{ v, f (vl ++ [v]) }}))
    (λ vl : list val, |={E}⧗=> Φ (mjoin (pad_struct sl.(sl_members) vl (λ ly, (replicate (ly_size ly) MPoison))))) sls.(sls_fields) [] -∗
  WP StructInit sls fs @ E {{ Φ }}.
Proof.
  intros Halg. iIntros "HT".
  iApply wp_struct_init'; first done.
  apply struct_layout_spec_has_layout_alt_1 in Halg as (fields & Hf & Halg).
  specialize (struct_layout_alg_has_fields _ _ _ _ Halg) as Heq.
  clear Halg. move: Hf Heq.
  rewrite /sl_has_members.
  generalize (sl_members sl).
  generalize (sls_fields sls).
  clear sls sl.
  intros field_specs mems Hfields ->.
  set (previous_mems := [] : field_list).
  assert ([] = pad_struct previous_mems [] (λ ly : layout, replicate (ly_size ly) ☠%V)) as Heqinit by done.
  rewrite {4}Heqinit.
  fold val.
  assert (mems = previous_mems ++ mems) as Heqmem by done.
  rewrite {1}Heqmem.
  clear Heqmem Heqinit.
  assert (length (field_names previous_mems) = length ([] : list val)) as Heq by done.
  move: Heq.
  generalize ([] : list val) at 1 3 5 as vs => vs.
  generalize (previous_mems) => previous_mems'.
  clear previous_mems. rename previous_mems' into previous_mems.
  intros Heq.
  iInduction mems as [ | [mem ly] mems] "IH" forall (vs previous_mems field_specs Hfields Heq); simpl in *.
  { apply Forall2_nil_inv_r in Hfields as ->. simpl. rewrite right_id. done. }
  destruct mem as [ mem | ].
  - simpl. apply Forall2_cons_inv_r in Hfields as ([? st] & field_specs' & [Halgst ->] & Hfields & ->).
    simpl.
    iPoseProof ("HT" with "[//]") as "HT".
    iApply (wp_wand with "HT").
    iIntros (v0) "HT". iPoseProof ("IH" $! (vs ++ [v0]) (previous_mems ++ [(Some s, ly)]) with "[] [] [HT]") as "HT".
    { done. }
    { rewrite /field_names. rewrite omap_app !length_app/=. rewrite Heq//. }
    { rewrite -app_assoc. simpl. done. }
    simpl.
    rewrite pad_struct_snoc_Some; done.
  - simpl. iApply wp_value.
    iPoseProof ("IH" $! (vs) (previous_mems ++ [(None, ly)]) field_specs with "[] [] [HT]") as "HT".
    { done. }
    { rewrite /field_names omap_app !length_app/=. rewrite Nat.add_0_r. done. }
    { simpl. rewrite -app_assoc. done. }
    simpl. rewrite pad_struct_snoc_None; done.
Qed.

(* A slightly more usable version defined via a fixpoint *)
Fixpoint struct_init_components `{!LayoutAlg} E (fields : list (var_name * syn_type)) (fs : list (string * expr)) (Φ : list val → iProp Σ) : iProp Σ :=
  match fields with
  | [] => Φ []
  | (n, st) :: fields' =>
      ∀ ly, ⌜syn_type_has_layout st ly⌝ -∗
        WP (default (Val (replicate (ly_size ly) MPoison)) ((list_to_map fs : gmap _ _) !! n)) @ E {{ v, struct_init_components E fields' fs (λ vs, Φ (v :: vs)) }}
  end.
Instance struct_init_components_proper `{!LayoutAlg} E fields fs :
  Proper (((=) ==> (≡)) ==> (≡)) (struct_init_components E fields fs).
Proof.
  intros a b Heq.
  induction fields as [ | [ n st] fields IH] in a, b, Heq|-*; simpl.
  { by iApply Heq. }
  do 3 f_equiv.
  apply wp_proper. intros ?. apply IH.
  intros ? ? ->. apply Heq. done.
Qed.
Lemma wp_struct_init2 `{!LayoutAlg} E (Φ : val → iProp Σ) (sls : struct_layout_spec) (sl : struct_layout) (fs : list (string * expr)) :
  use_struct_layout_alg sls = Some sl →
  struct_init_components E sls.(sls_fields) fs (λ vl : list val, |={E}⧗=> Φ (mjoin (M:=list)(pad_struct sl.(sl_members) vl (λ ly, (replicate (ly_size ly) MPoison))))) -∗
  WP StructInit sls fs @ E {{ Φ }}.
Proof.
  iIntros (Halg) "Hinit".
  iApply wp_struct_init; first done.
  apply use_struct_layout_alg_inv in Halg as (mems & Halg & Hfields).
  opose proof* struct_layout_alg_has_fields as Hmems; first apply Halg.
  move: Hfields Hmems. clear Halg.
  generalize (sls_fields sls) as fields => fields.
  rewrite /sl_has_members.
  generalize (sl_members sl) as all_mems => all_mems.
  move => Hfields ?. clear sls. subst mems.

  (* hack because rewrite doesn't work *)
  iAssert (∀ vi Φ,
    struct_init_components E fields fs (λ vl : list val, Φ (vi ++ vl)) -∗
    foldr (λ '(n, st) (f : list val → iPropI Σ) (vl : list val), ∀ ly : layout, ⌜syn_type_has_layout st ly⌝ -∗ WP default (Val $ replicate (ly_size ly) ☠%V) (list_to_map (M:=gmap _ _) fs !! n) @ E {{ v, f (vl ++ [v]) }}) (λ vl : list val, Φ vl) fields vi)%I as "Ha".
  {
    iIntros (vi Ψ) "Ha". clear Hfields.
    iInduction fields as [ | [n st] fields] "IH" forall (vi); simpl.
    { rewrite app_nil_r. done. }
    iIntros (ly) "%Hst". iPoseProof ("Ha" $! ly with "[//]") as "Ha".
    iApply (wp_wand with "Ha").
    iIntros (v) "Hinit".
    iApply "IH".
    iClear "IH".
    iStopProof.
    rewrite struct_init_components_proper; first eauto.
    intros ?? ->. by rewrite -app_assoc. }
  by iApply "Ha".
Qed.

Lemma wp_enum_init `{!LayoutAlg} E Φ (els : enum_layout_spec) el variant rsty e :
  use_enum_layout_alg els = Some el →
  WP e @ E {{ v,
    |={E}⧗=> Φ (mjoin $ pad_struct el.(sl_members) [(i2v (default 0 $ (list_to_map els.(els_tag_int) : gmap _ _) !! variant) els.(els_tag_it)); (v ++ replicate (ly_size (use_union_layout_alg' (uls_of_els els)) - ly_size (use_layout_alg' (default UnitSynType ((list_to_map els.(els_variants) : gmap _ _) !! variant)))) ☠%V)] (λ ly, (replicate (ly_size ly) MPoison))) }} -∗
  WP EnumInit els variant rsty e @ E {{ Φ }}.
Proof.
  iIntros (Halg ) "HT".
  rewrite /EnumInit.
  cbn.
  iApply wp_struct_init.
  { by apply use_enum_layout_alg_inv'. }
  simpl. iIntros (ly' Hit).
  apply syn_type_has_layout_int_inv in Hit as ->.
  rewrite lookup_insert_eq/=.
  iApply wp_value.
  iIntros (ly'' Hunion).
  apply (syn_type_has_layout_union_inv) in Hunion as (variant_lys & ul & -> & Hul & Hvariants).
  rewrite lookup_insert_ne//. rewrite lookup_insert_eq/=.
  iApply wp_concat_bind. simpl.
  iApply (wp_wand with "HT").
  iIntros (v) "HP".
  iApply wp_value. iApply (wp_concat _ _ [v; replicate _ _]).
  iApply physical_step_intro. iNext.
  simpl. rewrite app_nil_r. done.
Qed.

(** Focussing initialized struct components *)
Local Lemma pad_struct_focus' {A} (els : list A) fields (make_uninit : layout → A) (Φ : nat → A → iProp Σ) (i0 : nat) :
  length els = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x ∈ pad_struct fields els make_uninit, Φ (i + i0)%nat x) -∗
  (* get just the named fields *)
  ([∗ list] i ↦ x ∈ els, ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! (i)%nat = Some (n, ly)⌝ ∗ Φ (j + i0)%nat x) ∗
  (* and separately the ownership of the unnamed fields *)
  ([∗ list] i ↦ x ∈ pad_struct fields (replicate (length els) None) Some,
    from_option (λ ly, Φ (i + i0)%nat (make_uninit ly)) True x).
Proof.
  iIntros (Hlen Hnd) "Ha".
  iInduction fields as [ | [n ly] fields] "IH" forall (els Hlen i0 Hnd); simpl.
  { simpl in Hlen. destruct els; last done. simpl. iSplitR; first done. done. }
  destruct n as [ n | ]; simpl.
  - simpl in Hlen. destruct els as [ | el els]; first done; simpl in *.
    iDestruct "Ha" as "(Ha & Hb)".
    iPoseProof ("IH" $! els with "[] [] [Hb]") as "(Hb & Hpad)".
    { iPureIntro. lia. }
    { inversion Hnd. done. }
    { setoid_rewrite <-Nat.add_succ_r. iApply "Hb". }
    iSplitL "Ha Hb".
    { (* show the split *)
      iSplitL "Ha".
      { iExists 0%nat, _, _. iSplitR; first done. iSplitR; done. }
      iApply (big_sepL_impl with "Hb"). iModIntro. iIntros (k x Hlook).
      iIntros "(%j & % & % & %Hlook1 & %Hlook2 & Ha)".
      iExists (S j), _, _. simpl. rewrite Nat.add_succ_r. iSplitR; first done. iSplitR; done. }
    iSplitR; first done. iApply (big_sepL_wand with "Hpad").
    iApply big_sepL_intro. iModIntro. iIntros (???).
    destruct x; simpl; try rewrite Nat.add_succ_r; eauto.
  - simpl in *.
    iDestruct "Ha" as "(Ha & Hb)".
    iPoseProof ("IH" with "[//] [//] [Hb]") as "(Hb & Hpad)".
    { setoid_rewrite <-Nat.add_succ_r. done. }
    iSplitL "Hb".
    { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
      iModIntro. iIntros (k x Hlook) "(%j & % & % & ? & ? & ?)".
      iExists (S j). rewrite Nat.add_succ_r. eauto with iFrame. }
    iFrame. iApply (big_sepL_wand with "Hpad").
    iApply big_sepL_intro. iModIntro. iIntros (???).
    destruct x; simpl; try rewrite Nat.add_succ_r; eauto.
Qed.
Local Lemma pad_struct_unfocus' {A} (els : list A) fields (make_uninit : layout → A) (Φ : nat → A → iProp Σ) (i0 : nat) :
  length els = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x ∈ els, ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! (i)%nat = Some (n, ly)⌝ ∗ Φ (j + i0)%nat x) -∗
  ([∗ list] i ↦ x ∈ pad_struct fields (replicate (length els) None) Some,
    from_option (λ ly, Φ (i + i0)%nat (make_uninit ly)) True x) -∗
  ([∗ list] i ↦ x ∈ pad_struct fields els make_uninit, Φ (i + i0)%nat x).
Proof.
  iIntros (Hlen Hnd) "Ha Hpad".
  iInduction fields as [ | [n ly] fields] "IH" forall (els Hlen i0 Hnd); simpl.
  { eauto. }
  destruct n as [ n | ]; simpl.
  - simpl in Hlen. destruct els as [ | el els]; first done; simpl in *.
    iDestruct "Hpad" as "(_ & Hpad)".
    iDestruct "Ha" as "((%j & % & % & %Hf & %Heq & Ha) & Hb)".
    apply NoDup_cons in Hnd as (Hnel & Hnd).
    (* now we have these elements back *)
    injection Heq as <- <-.

    (* uses duplicate-freedom *)
    assert (j = 0%nat) as ->.
    { destruct j; first done. simpl in *.
      apply list_elem_of_lookup_2 in Hf.
      contradict Hnel. rewrite /field_names.
      apply list_elem_of_omap. eexists _. split; done. }
    simpl in *. iFrame.
    iEval (setoid_rewrite <-Nat.add_succ_r).
    iApply ("IH" $! els with "[] [] [Hb]").
    { iPureIntro. lia. }
    { done. }
    { iApply (big_sepL_impl with "Hb"). iModIntro. iIntros (k x Hlook).
      iIntros "(%j' & % & % & %Hlook1 & %Hlook2 & Ha)".
      destruct j'.
      { (* contrasdictory due to no-dup *)
        simpl in Hlook1. injection Hlook1 as <- <-.
        apply list_elem_of_lookup_2 in Hlook2.
        contradict Hnel. eapply elem_of_named_fields_field_names. done. }
      iExists j'. rewrite Nat.add_succ_r.
      eauto with iFrame. }
    { iApply (big_sepL_wand with "Hpad").
      iApply big_sepL_intro. iModIntro. iIntros (???).
      destruct x; simpl; try rewrite Nat.add_succ_r; eauto. }
  - iDestruct "Hpad" as "(Hpad1 & Hpad)". iFrame.
    iEval (setoid_rewrite <-Nat.add_succ_r).
    iApply ("IH" $! els with "[] [] [Ha]"); first done.
    { done. }
    { iApply (big_sepL_wand with "Ha"). iApply big_sepL_intro.
      iModIntro. iIntros (k x Hlook) "(%j & %ly' & %n & %Hlook1 & %Hlook2 & Ha)".
      destruct j as [ | j]; first done.
      iExists j. simpl. rewrite -Nat.add_succ_r. eauto with iFrame. }
    { iApply (big_sepL_wand with "Hpad").
      iApply big_sepL_intro. iModIntro. iIntros (???).
      destruct x; simpl; try rewrite Nat.add_succ_r; eauto. }
Qed.

Lemma pad_struct_focus {A} (els : list A) fields (make_uninit : layout → A) (Φ : nat → A → iProp Σ) :
  length els = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x ∈ pad_struct fields els make_uninit, Φ i x) -∗
  ([∗ list] i ↦ x ∈ els, ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! i = Some (n, ly)⌝ ∗ Φ j x) ∗
  ([∗ list] i ↦ x ∈ pad_struct fields (replicate (length els) None) Some,
    from_option (λ ly, Φ i (make_uninit ly)) True x).
Proof.
  iIntros (??) "Ha".
  iPoseProof (pad_struct_focus' els fields make_uninit Φ 0 with "[Ha]") as "Ha".
  { done. }
  { done. }
  { setoid_rewrite Nat.add_0_r. done. }
  iDestruct "Ha" as "(Ha & Hb)".
  iEval (setoid_rewrite Nat.add_0_r) in "Ha". iFrame.
  iApply (big_sepL_wand with "Hb").
  iApply big_sepL_intro. iModIntro. iIntros (???).
  destruct x; simpl; try rewrite Nat.add_0_r; eauto.
Qed.
Lemma pad_struct_unfocus {A} (els : list A) fields (make_uninit : layout → A) (Φ : nat → A → iProp Σ) :
  length els = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x ∈ els, ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! i = Some (n, ly)⌝ ∗ Φ j x) -∗
  ([∗ list] i ↦ x ∈ pad_struct fields (replicate (length els) None) Some,
    from_option (λ ly, Φ i (make_uninit ly)) True x) -∗
  ([∗ list] i ↦ x ∈ pad_struct fields els make_uninit, Φ i x).
Proof.
  iIntros (??) "Ha Hpad".
  iPoseProof (pad_struct_unfocus' els fields make_uninit Φ 0 with "[Ha] [Hpad]") as "Ha".
  { done. }
  { done. }
  { setoid_rewrite Nat.add_0_r. done. }
  { iApply (big_sepL_wand with "Hpad").
    iApply big_sepL_intro. iModIntro. iIntros (???).
    destruct x; simpl; try rewrite Nat.add_0_r; eauto. }
  setoid_rewrite Nat.add_0_r. done.
Qed.
Lemma pad_struct_focus_no_uninit {A} (els : list A) fields (make_uninit : layout → A) (Φ : nat → A → iProp Σ) :
  length els = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x ∈ pad_struct fields els make_uninit, Φ i x) -∗
  ([∗ list] i ↦ x ∈ els, ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! i = Some (n, ly)⌝ ∗ Φ j x) ∗
  (∀ els',
    ⌜length els' = length els⌝ -∗
    ([∗ list] i ↦ x ∈ els', ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! i = Some (n, ly)⌝ ∗ Φ j x) -∗
    ([∗ list] i ↦ x ∈ pad_struct fields els' make_uninit, Φ i x)).
Proof.
  iIntros (??) "Ha".
  iPoseProof (pad_struct_focus els fields make_uninit Φ with "Ha") as "($ & Hpad)".
  { done. }
  { done. }
  iIntros (els' Hlen) "Ha".
  rewrite -Hlen.
  iApply (pad_struct_unfocus els' fields make_uninit Φ with "Ha Hpad").
  { rewrite Hlen. done. }
  done.
Qed.

Lemma wp_call_bind_ind vs E Φ vf el:
  foldr (λ e f, (λ vl, WP e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP Call (Val vf) (Val <$> (vs ++ vl)) @ E {{ Φ }}) el [] -∗
  WP (Call (Val vf) ((Val <$> vs) ++ el)) @ E {{ Φ}}.
Proof.
  rewrite -{2}(app_nil_r vs).
  move: {2 3}[] => vl2.
  elim: el vs vl2 => /=.
  - iIntros (vs vl2) "He". by rewrite !app_nil_r.
  - iIntros (e el IH vs vl2) "Hf".
    rewrite /wp/wp_expr_wp.
    have -> : (coerce_rtexpr (Call (Val vf) ((Val <$> vs ++ vl2) ++ e :: el)))%E = (fill [ExprCtx (CallRCtx vf (vs ++ vl2) (to_rtexpr <$> el))] (to_rtexpr e)). {
        by rewrite /coerce_rtexpr/= fmap_app fmap_cons -!list_fmap_compose.
    }
    iApply wp_bind. iApply (wp_wand with "Hf").
    iIntros (v) "Hf" => /=.
    have -> : Expr (RTCall vf ((Expr <$> (RTVal <$> vs ++ vl2)) ++ of_val v :: (to_rtexpr <$> el)))
             = Call vf ((Val <$> vs ++ (vl2 ++ [v])) ++ el). 2: by iApply IH.
    by rewrite /coerce_rtexpr /= !fmap_app /= (cons_middle (of_val v)) !app_assoc -!list_fmap_compose.
Qed.

Lemma wp_call_bind E Φ el ef:
  WP ef @ E {{ vf, foldr (λ e f, (λ vl, WP e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP Call (Val vf) (Val <$> vl) @ E {{ Φ }}) el [] }} -∗
  WP (Call ef el) @ E {{ Φ }}.
Proof.
  iIntros "HWP".
  rewrite /wp/wp_expr_wp.
  have -> : coerce_rtexpr (Call ef el) = fill [ExprCtx $ CallLCtx (coerce_rtexpr <$> el)] (coerce_rtexpr ef) by [].
  iApply wp_bind.
  iApply (wp_wand with "HWP"). iIntros (vf) "HWP".
  by iApply (wp_call_bind_ind []).
Qed.

Lemma wp_alloc E Φ (v_size v_align : val) (n_size n_align : nat) :
  val_to_Z v_size USize = Some (Z.of_nat n_size) →
  val_to_Z v_align USize = Some (Z.of_nat n_align) →
  n_size > 0 →
  (|={E}⧗=> ∀ l, l ↦ (replicate n_size MPoison) -∗ freeable l n_size 1 HeapAlloc -∗ ⌜l `has_layout_loc` Layout n_size n_align⌝ -∗ Φ (val_of_loc l)) -∗
  WP (Alloc (Val v_size) (Val v_align)) @ E {{ Φ }}.
Proof.
  iIntros (Hsz Hal Hnz) "Hwp".
  iApply wp_lift_expr_step; first done.
  iIntros (hs) "((%&Hhctx&Hactx)&Hfctx)/=".
  iModIntro.
  iSplit; first by eauto 10 using AllocFailS.
  iIntros (??[??]? Hstep _). inv_expr_step; last first. {
    (* Alloc failure case. *)
    iApply physical_step_intro.
    iModIntro. iSplit; first done. rewrite /state_ctx. iFrame. iSplit; first done.
    iApply wp_alloc_failed.
  }
  iMod (heap_alloc_new_block_upd with "[$Hhctx $Hactx]") as "(Hctx & Hlv & Hlf)" => //.
  rewrite length_replicate.
  iApply (physical_step_wand with "Hwp"). iIntros "Hwp".
  iDestruct ("Hwp" with "Hlv Hlf [//]") as "Hpost".
  iSplit => //.
  iFrame "Hctx Hfctx". iApply wp_value. iApply "Hpost".
Qed.
End expr_lifting.

(*** Lifting of statements *)
Definition stmt_wp_def `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) (s : stmt) : iProp Σ :=
  (∀ Φ rf, ⌜Q = rf.(rf_fn).(f_code)⌝ -∗ (∀ v, Ψ v -∗ WP to_rtstmt rf (Return v) {{ Φ }}) -∗
    WP to_rtstmt rf s @ E {{ Φ }}).
Definition stmt_wp_aux `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) : seal (@stmt_wp_def Σ _ E Q Ψ). by eexists. Qed.
Definition stmt_wp `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) :
  stmt → iProp Σ := (stmt_wp_aux E Q Ψ).(unseal).
Definition stmt_wp_eq `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) : stmt_wp E Q Ψ = @stmt_wp_def Σ _ E Q Ψ := (stmt_wp_aux E Q Ψ).(seal_eq).

Notation "'WPs' s @ E {{ Q , Ψ } }" := (stmt_wp E Q Ψ s%E)
  (at level 20, s, Q, Ψ at level 200, format "'[' 'WPs'  s  '/' '[       ' @  E  {{  Q ,  Ψ  } } ']' ']'" ) : bi_scope.

Notation "'WPs' s {{ Q , Ψ } }" := (stmt_wp ⊤ Q Ψ s%E)
  (at level 20, s, Q, Ψ at level 200, format "'[' 'WPs'  s  '/' '[   ' {{  Q ,  Ψ  } } ']' ']'") : bi_scope.

Section stmt_lifting.
Context `{!refinedcG Σ}.

Lemma stmt_wp_unfold s E Q Ψ  :
  WPs s @ E {{ Q, Ψ }} ⊣⊢ stmt_wp_def E Q Ψ s.
Proof. by rewrite stmt_wp_eq. Qed.

Lemma fupd_wps s E Q Ψ :
  (|={E}=> WPs s @ E {{ Q, Ψ }}) ⊢ WPs s @ E{{ Q, Ψ }}.
Proof.
  rewrite stmt_wp_unfold. iIntros "Hs" (? rf HQ) "HΨ".
  iApply fupd_wp. by iApply "Hs".
Qed.

Lemma wps_fupd s E Q Ψ :
  WPs s @ E {{ Q, (λ v, |={E}=> Ψ v)}} ⊢ WPs s @ E {{ Q, Ψ }}.
Proof.
  rewrite !stmt_wp_unfold. iIntros "Hs" (? rf HQ) "HΨ".
  iApply wp_fupd. iApply "Hs"; first done.
  iIntros (v) "Hv".
  iApply fupd_wp. iMod (fupd_mask_mono with "Hv") as "Hv"; first done.
  iModIntro. iApply (wp_wand with "(HΨ Hv)"). eauto.
Qed.

Global Instance elim_modal_bupd_wps p s Q Ψ P E :
    ElimModal True p false (|==> P) P (WPs s @ E {{ Q, Ψ }}) (WPs s @ E {{ Q, Ψ }}).
Proof. by rewrite /ElimModal intuitionistically_if_elim (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wps. Qed.

Global Instance elim_modal_fupd_wps p s Q Ψ P E :
    ElimModal True p false (|={E}=> P) P (WPs s @ E {{ Q, Ψ }}) (WPs s @ E {{ Q, Ψ }}).
Proof. by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r fupd_wps. Qed.

Lemma wps_wand s E Q Φ Ψ:
  WPs s @ E {{ Q , Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WPs s @ E {{ Q , Ψ }}.
Proof.
  rewrite !stmt_wp_unfold. iIntros "HΦ H" (???) "HΨ".
  iApply "HΦ"; [ done | ..]. iIntros (v) "Hv".
  iApply "HΨ". iApply "H". iApply "Hv".
Qed.

Lemma wp_call vf vl f fn Φ:
  val_to_loc vf = Some f →
  Forall2 has_layout_val vl (f_args fn).*2 →
  fntbl_entry f fn -∗ (|={⊤}⧗=> ∀ lsa lsv, ⌜Forall2 has_layout_loc lsa (f_args fn).*2⌝ -∗
    ([∗ list] l; v ∈ lsa; vl, l↦v) -∗ ([∗ list] l; v ∈ lsv; fn.(f_local_vars), l↦|v.2|) -∗ ∃ Ψ',
          WPs Goto fn.(f_init) {{ (subst_stmt (zip (fn.(f_args).*1 ++ fn.(f_local_vars).*1)
                            (val_of_loc <$> (lsa ++ lsv)))) <$> fn.(f_code), Ψ' }} ∗
          (∀ v, Ψ' v -∗
                  ([∗ list] l; v ∈ lsa; fn.(f_args), l↦|v.2|) ∗
                  ([∗ list] l; v ∈ lsv; fn.(f_local_vars), l↦|v.2|) ∗
                  (|={⊤}⧗=> Φ v))
   ) -∗
   WP (Call (Val vf) (Val <$> vl)) {{ Φ }}.
Proof.
  move => Hf Hly. move: (Hly) => /Forall2_length. rewrite length_fmap => Hlen_vs.
  iIntros "Hf HWP". iApply wp_lift_expr_step; first done.
  iIntros (σ1) "((%&Hhctx&Hbctx)&Hfctx)".
  iDestruct (fntbl_entry_lookup with "Hfctx Hf") as %[a [? Hfn]]; subst. iModIntro.
  iSplit; first by eauto 10 using CallFailS.
  iIntros (??[??]? Hstep _). inv_expr_step; last first. {
    (* Alloc failure case. *)
    iApply physical_step_intro. iNext.
    iSplit; first done. rewrite /state_ctx. iFrame. iSplit; first done.
    iApply wp_alloc_failed.
  }
  iMod (heap_alloc_new_blocks_upd with "[$Hhctx $Hbctx]") as "[Hctx Hlv]" => //.
  rewrite big_sepL2_sep. iDestruct "Hlv" as "[Hlv Hfree_v]".
  iMod (heap_alloc_new_blocks_upd with "Hctx") as "[Hctx Hla]" => //.
  rewrite big_sepL2_sep. iDestruct "Hla" as "[Hla Hfree_a]".

  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplit => //.

  iDestruct ("HWP" $! lsa lsv with "[//] Hla [Hlv]") as (Ψ') "(HQinit & HΨ')". {
    rewrite big_sepL2_fmap_r. iApply (big_sepL2_mono with "Hlv") => ??? ?? /=.
    iIntros "?". iExists _. iFrame. iPureIntro. split; first by apply length_replicate.
    apply: Forall2_lookup_lr. 2: done. 1: done. rewrite list_lookup_fmap. apply fmap_Some. naive_solver.
  }
  iFrame. rewrite stmt_wp_eq. iApply "HQinit" => //.

  (** prove Return *)
  iIntros (v) "Hv". iDestruct ("HΨ'" with "Hv") as "(Ha & Hv & Hs)".
  iApply wp_lift_stmt_step => //.
  iIntros (σ3) "(Hctx&?)".
  iMod (heap_free_blocks_upd (zip lsa (f_args fn).*2 ++ zip lsv (f_local_vars fn).*2) with "[Ha Hfree_a Hv Hfree_v] Hctx") as (σ2 Hfree) "Hctx". {
    rewrite big_sepL_app !big_sepL_sep !big_sepL2_alt.
    iDestruct "Ha" as "[% Ha]". iDestruct "Hv" as "[% Hv]".
    iDestruct "Hfree_a" as "[% Hfree_a]". iDestruct "Hfree_v" as "[% Hfree_v]".
    rewrite !zip_fmap_r !big_sepL_fmap/=. iFrame.
    setoid_rewrite length_replicate. iFrame.
    iApply (big_sepL_impl' with "Hfree_a").
    { rewrite !length_zip_with !min_l ?length_fmap //; lia. }
    iIntros (??? [?[v0[?[??]]]]%lookup_zip_with_Some [?[ly0[?[??]]]]%lookup_zip_with_Some) "!> H2"; simplify_eq/=.
    have -> : v0 `has_layout_val` ly0.2; last done.
    eapply Forall2_lookup_lr; [done..|].
    rewrite list_lookup_fmap fmap_Some. naive_solver.
  }
  iModIntro.
  iSplit; first by eauto 8 using ReturnS.
  iIntros (os ts3 σ2' ? Hst ?). inv_stmt_step.
  iApply (physical_step_wand with "Hs"). iIntros "Hs".
  iSplitR => //.
  have ->: (σ2 = hs) by apply: free_blocks_inj.
  iFrame. iApply wp_value. iApply "Hs".
Qed.

Lemma wps_return Q Ψ v:
  Ψ v -∗ WPs (Return (Val v)) {{ Q , Ψ }}.
Proof. rewrite stmt_wp_unfold. iIntros "Hb" (? rf ?) "HΨ". by iApply "HΨ". Qed.

Lemma wps_goto Q Ψ b s:
  Q !! b = Some s →
  (|={⊤}⧗=> WPs s {{ Q, Ψ }}) -∗ WPs Goto b {{ Q , Ψ }}.
Proof.
  iIntros (Hs) "HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iApply wp_lift_stmt_step. iIntros (?) "Hσ !>".
  iSplit; first by eauto 10 using GotoS.
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplit; first done. iFrame. by iApply "HWP".
Qed.

Lemma wps_free Q Ψ s l v_size v_align (n_size n_align : nat) :
  val_to_Z v_size USize = Some (Z.of_nat n_size) →
  val_to_Z v_align USize = Some (Z.of_nat n_align) →
  n_size > 0 →
  l ↦|Layout n_size n_align| -∗
  freeable l n_size 1 HeapAlloc -∗
  (|={⊤}⧗=> WPs s {{ Q, Ψ }}) -∗
  WPs (Free (Val v_size) (Val v_align) (val_of_loc l) s) {{ Q, Ψ }}.
Proof.
  iIntros (???) "Hl Hf HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iPoseProof (heap_pointsto_layout_has_layout with "Hl") as "%".
  iApply wp_lift_stmt_step. iIntros (σ) "(Hhctx&Hfctx)".
  iMod (heap_free_block_upd with "Hl Hf Hhctx") as (σ') "(%Hf & Hhctx)".
  iModIntro. iSplit; first by eauto 10 using FreeS, val_to_of_loc.
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplitR; first done.
  revert select (val_to_loc _ = Some _) => /val_of_to_loc[/(inj _ _ _)Heq|[??]//]. subst.
  erewrite (free_block_inj σ.(st_heap) _ (Layout n_size n_align) HeapAlloc hs' σ'); [ | done..].
  iFrame. by iApply "HWP".
Qed.

Lemma wps_skip Q Ψ s:
  (|={⊤}⧗=> WPs s {{ Q, Ψ }}) -∗ WPs SkipS s {{ Q , Ψ }}.
Proof.
  iIntros "HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iApply wp_lift_stmt_step. iIntros (?) "Hσ".
  iModIntro.
  iSplit; first by eauto 10 using SkipSS.
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplit; first done. iFrame.
  by iApply "HWP".
Qed.

Lemma wps_exprs Q Ψ s v:
  (|={⊤}⧗=> WPs s {{ Q, Ψ }}) -∗ WPs ExprS (Val v) s {{ Q , Ψ }}.
Proof.
  iIntros "HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iApply wp_lift_stmt_step. iIntros (?) "Hσ".
  iModIntro.
  iSplit; first by eauto 10 using ExprSS.
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplit; first done. iFrame.
  by iApply "HWP".
Qed.

Lemma wps_assign Q Ψ vl ot vr s l o:
  let E := if o is ScOrd then ∅ else ⊤ in
  o = ScOrd ∨ o = Na1Ord →
  val_to_loc vl = Some l →
  (|={⊤,E}=> ⌜vr `has_layout_val` ot_layout ot⌝ ∗ l↦|ot_layout ot| ∗ |={E}⧗=> (l↦vr ={E,⊤}=∗ WPs s {{Q, Ψ}}))
    -∗ WPs (Assign o ot (Val vl) (Val vr) s) {{ Q , Ψ }}.
Proof.
  iIntros (E Ho Hvl) "HWP". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step_fupd. iIntros ([h1 ?]) "((%&Hhctx&Hfctx)&?) /=". iMod "HWP" as (Hly) "[Hl HWP]".
  iApply (fupd_mask_weaken ∅); first set_solver. iIntros "HE".
  iDestruct "Hl" as (v' Hlyv' ?) "Hl".
  iDestruct (heap_pointsto_is_alloc with "Hl") as %Haid.
  unfold E. case: Ho => ->.
  - iModIntro.
    iDestruct (heap_pointsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl") as %? => //.
    iSplit; first by eauto 12 using AssignS.
    iIntros (? e2 σ2 efs Hstep ?). inv_stmt_step. unfold end_val.
    iApply (physical_step_wand with "HWP"). iIntros "HWP".
    iMod (heap_write with "Hhctx Hl") as "[$ Hl]" => //; first congruence.
    iMod ("HWP" with "Hl") as "HWP".
    iModIntro => /=. iSplit; first done. iFrame. iSplit; first done. by iApply "HWP".
  - iMod (heap_write_na _ _ _ vr with "Hhctx Hl") as (?) "[Hhctx Hc]" => //; first by congruence.
    iModIntro. iSplit; first by eauto 12 using AssignS.
    iIntros (? e2 σ2 efs Hst ?). inv_stmt_step.
    have ? : (v' = v'0) by [apply: heap_at_inj_val]; subst v'0.
    iFrame => /=. iMod "HE" as "_".
    iApply (physical_step_wand with "HWP"). iIntros "HWP".
    iApply fupd_mask_intro_subseteq; first set_solver.
    iSplit; first done.
    iFrame. iSplit; first done.

    (* second step *)
    iApply wp_lift_stmt_step.
    iIntros ([h2 ?]) "((%&Hhctx&Hfctx)&?)" => /=.
    iMod ("Hc" with "Hhctx") as (?) "[Hhctx Hmt]".
    iModIntro. iSplit; first by eauto 12 using AssignS. unfold end_stmt.
    iIntros (? e2 σ2 efs Hst ?). inv_stmt_step.

    have ? : (v' = v'0) by [apply: heap_lookup_loc_inj_val]; subst v'0.
    iApply physical_step_fupd.
    iApply physical_step_intro. iNext.
    iFrame => /=. iMod ("HWP" with "Hmt") as "HWP".
    iModIntro. iSplit; first done. iSplit; first done. by iApply "HWP".
Qed.

Lemma wps_switch Q Ψ v n ss def m it:
  val_to_Z v it = Some n →
  (∀ i, m !! n = Some i → is_Some (ss !! i)) →
  (|={⊤}⧗=> WPs default def (i ← m !! n; ss !! i) {{ Q, Ψ }}) -∗ WPs (Switch it (Val v) m ss def) {{ Q , Ψ }}.
Proof.
  iIntros (Hv Hm) "HWP". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step. iIntros (?) "Hσ".
  iModIntro. iSplit; first by eauto 8 using SwitchS.
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplit; first done.
  iFrame "Hσ". by iApply "HWP".
Qed.

(** a version of wps_switch which is directed by ss instead of n *)
Lemma wps_switch' Q Ψ v n ss def m it:
  val_to_Z v it = Some n →
  map_Forall (λ _ i, is_Some (ss !! i)) m →
  (|={⊤}⧗=> [∧ list] i↦s∈ss, ⌜m !! n = Some i⌝ -∗ WPs s {{ Q, Ψ }}) ∧
  (|={⊤}⧗=> ⌜m !! n = None⌝ -∗ WPs def {{ Q, Ψ }}) -∗
  WPs (Switch it (Val v) m ss def) {{ Q , Ψ }}.
Proof.
  iIntros (Hn Hm) "Hs". iApply wps_switch; eauto.
  destruct (m !! n) as [i|] eqn:Hi => /=.
  - iDestruct "Hs" as "[Hs _]".
    destruct (ss !! i) as [s|] eqn:? => /=. 2: by move: (Hm _ _ Hi) => [??]; simplify_eq.
    iApply (physical_step_wand with "Hs"). iIntros "Hs".
    by iApply (big_andL_lookup with "Hs").
  - iDestruct "Hs" as "[_ Hs]".
    iApply (physical_step_wand with "Hs"). iIntros "Hs".
    by iApply "Hs".
Qed.

Lemma wps_if Q Ψ it join v s1 s2 n:
  val_to_Z v it = Some n →
  (|={⊤}⧗=> if bool_decide (n ≠ 0) then WPs s1 {{ Q, Ψ }} else WPs s2 {{ Q, Ψ }}) -∗
  WPs (if{IntOp it, join}: (Val v) then s1 else s2) {{ Q , Ψ }}.
Proof.
  iIntros (Hn) "Hs". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step. iIntros (?) "Hσ". iModIntro.
  iSplit. { iPureIntro. repeat eexists. apply IfSS. rewrite /= Hn //. }
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "Hs"). iIntros "Hs".
  iSplit; first done.
  iFrame "Hσ". case_bool_decide; by iApply "Hs".
Qed.

Lemma wps_if_bool Q Ψ v s1 s2 b join:
  val_to_bool v = Some b →
  (|={⊤}⧗=> if b then WPs s1 {{ Q, Ψ }} else WPs s2 {{ Q, Ψ }}) -∗
  WPs (if{BoolOp, join}: (Val v) then s1 else s2) {{ Q , Ψ }}.
Proof.
  iIntros (Hb) "Hs". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step. iIntros (?) "Hσ". iModIntro.
  iSplit. { iPureIntro. repeat eexists. apply IfSS. rewrite /= Hb //. }
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "Hs"). iIntros "Hs".
  iSplit; first done.
  iFrame "Hσ". destruct b; by iApply "Hs".
Qed.

Lemma wps_assert_bool Q Ψ v s b:
  val_to_bool v = Some b →
  b = true →
  (|={⊤}⧗=> WPs s {{ Q, Ψ }}) -∗
  WPs (assert{BoolOp}: Val v; s) {{ Q , Ψ }}.
Proof.
  iIntros (Hv Hb) "Hs". rewrite /notation.Assert.
  iApply wps_if_bool => //. by rewrite Hb.
Qed.

Lemma wps_assert_int Q Ψ it v s n:
  val_to_Z v it = Some n →
  n ≠ 0 →
  (|={⊤}⧗=> WPs s {{ Q, Ψ }}) -∗
  WPs (assert{IntOp it}: Val v; s) {{ Q , Ψ }}.
Proof.
  iIntros (Hv Hn) "Hs". rewrite /notation.Assert.
  iApply wps_if => //. by case_decide.
Qed.

Definition wps_block (P : iProp Σ) (b : label) (Q : gmap label stmt) (Ψ : val → iProp Σ) : iProp Σ :=
  (□ (P -∗ WPs Goto b {{ Q, Ψ }})).

(* NOTE: does not offer a physical step since we have to use it up to strip the later from the Löb induction *)
Lemma wps_block_rec Ps Q Ψ :
  ([∗ map] b ↦ P ∈ Ps, ∃ s, ⌜Q !! b = Some s⌝ ∗ □(([∗ map] b ↦ P ∈ Ps, wps_block P b Q Ψ) -∗ P -∗ £ (num_laters_per_step 1) -∗ WPs s {{ Q, Ψ }})) -∗
  [∗ map] b ↦ P ∈ Ps, wps_block P b Q Ψ.
Proof.
  iIntros "#HQ". iLöb as "IH".
  iApply (big_sepM_impl with "HQ").
  iIntros "!#" (b P HPs).
  iDestruct 1 as (s HQ) "#Hs".
  iIntros "!# HP".
  iApply wps_goto; first by apply: lookup_weaken.
  iApply physical_step_intro_lc.
  iIntros "Hcred". iModIntro.
  iNext.
  iApply ("Hs" with "IH HP Hcred").
Qed.

End stmt_lifting.
