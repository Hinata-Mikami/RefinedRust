From Equations Require Import Equations.
From iris.proofmode Require Import proofmode.
From radium.program_logic Require Export weakestpre.
From radium.program_logic Require Import ectx_lifting.
From radium Require Export lang ghost_state notation.
From radium Require Import tactics.
Export logical_step.
Set Default Proof Using "Type".
Import uPred.

Class refinedcG Σ := RefinedCG {
  refinedcG_invG :: invGS Σ;
  refinedcG_gen_heapG :: heapG Σ;
  refinedcG_threadG :: threadG Σ;
  refinedcG_trGS :: trGS Σ;
  (* Fix a global layout algorithm here *)
  ALG :: LayoutAlg;
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

  Lemma logical_step_intro_later E P :
    ▷ P -∗ logical_step E P.
  Proof.
    iIntros "HP". unfold logical_step.
    iApply (step_update_lb_step_very_strong E _ True 0).
    iSplit.
    - iMod tr_persistent_zero as "$".
      iMod (fupd_mask_subseteq); last done.
      set_solver.
    - iSplitL; first last.
      { iApply step_update_intro; done. }
      iModIntro. simpl. iModIntro. iNext.
      iModIntro. iIntros "_".
      done.
  Qed.

  Lemma logical_step_intro_maybe F P n (b : bool) :
    (if b then tr n else True) -∗
    ((if b then £(num_laters_per_step n) ∗ tr n else True) ={F}=∗ P) -∗
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

  Lemma physical_step_logical_step E P Q :
    (logical_step E Q) -∗
    (|={E}⧗=> (Q -∗ P)) -∗
    |={E}⧗=> P.
  Proof.
    iApply physical_step_step_upd.
  Qed.
End physical_step.

Global Instance into_val_val π v : IntoVal (to_rtexpr π (Val v)) v.
Proof. done. Qed.
Global Instance into_val_val' v : IntoVal (RTVal v) v.
Proof. done. Qed.

Local Hint Extern 0 (reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Unfold heap_at : core.


Local Ltac solve_atomic :=
  match goal with
  | |- Atomic _ (to_rtexpr _ ?e) =>
    apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; simplify_eq;
      match goal with
      | H : to_rtexpr _ _ = Expr _ _ |- _ =>
          apply (to_rtexpr_inj' _ _ _ e) in H
      end;
      simplify_eq;
      inv_expr_step; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [[]|[]|[]] **; naive_solver]
  end.

Global Instance cas_atomic π s ot (v1 v2 v3 : val) : Atomic s (to_rtexpr π (CAS ot v1 v2 v3)).
Proof. solve_atomic. Qed.
Global Instance skipe_atomic π s (v : val) : Atomic s (to_rtexpr π (SkipE v)).
Proof. solve_atomic. Qed.
Global Instance deref_atomic π s (l : loc) ly : Atomic s (to_rtexpr π (Deref ScOrd ly l)).
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
    ((∃ π e', e = to_rtexpr π e' ∧ step_rel = expr_step e' π) ∨
     (∃ π rf s, e = to_rtstmt π rf s ∧ step_rel = stmt_step s π rf)) →
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, step_rel σ1 os e2 σ2 tsl⌝ ∗
         (∀ os e2 σ2 tsl, ⌜step_rel σ1 os e2 σ2 tsl⌝ -∗
          ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
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
    move: (Hstep) => /runtime_step_preserves_heap_invariant?.
    Arguments to_rtstmt : simpl never.
    destruct He as [(π & e' & [??])|(? & ? & s & [??])]; inversion Hstep; subst.
    all: try by [destruct e'; discriminate].
    all: try by simplify_eq.
    all: try match goal with | H : to_rtexpr _ ?e = to_rtstmt _ _ _ |- _ => destruct e; discriminate end.
    all: try match goal with | H : to_rtexpr _ _ = to_rtexpr _ _ |- _ => apply to_rtexpr_inj_strong_2 in H as [-> ->]; last done end.
    all: try match goal with | H : to_rtstmt _ _ _ = to_rtstmt _ _ _ |- _ => apply to_rtstmt_inj in H as (-> & -> & ->) end.
    all: iSpecialize ("HWP" with "[//] [%]"); first naive_solver.
    all: iApply (physical_step_wand with "HWP"); iIntros "HWP".
    all: iMod "HWP" as (->) "[$ HWP]".
    all: iFrame.
    all: by iModIntro => /=.
  Qed.
  Lemma wp_lift_expr_step_fupd E π (e : expr) Φ:
    to_val (to_rtexpr π e) = None →
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, expr_step e π σ1 os e2 σ2 tsl⌝ ∗
        (∀ os e2 σ2 tsl, ⌜expr_step e π σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={∅}⧗=> |={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtexpr π e @ E {{ Φ }}.
  Proof. iIntros (?) "HWP". iApply (wp_c_lift_step_fupd) => //. naive_solver. Qed.
  Lemma wp_lift_stmt_step_fupd E π s rf Φ:
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, stmt_step s π rf σ1 os e2 σ2 tsl⌝ ∗
         (∀ os e2 σ2 tsl, ⌜stmt_step s π rf σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={∅}⧗=> |={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtstmt π rf s @ E {{ Φ }}.
  Proof. iIntros "HWP". iApply (wp_c_lift_step_fupd) =>//. naive_solver. Qed.

  (** Not mask-changing + physical step*)
  Lemma wp_c_lift_step E e step_rel Φ:
    ((∃ π e', e = to_rtexpr π e' ∧ step_rel = expr_step e' π) ∨
     (∃ π rf s, e = to_rtstmt π rf s ∧ step_rel = stmt_step s π rf)) →
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
  Lemma wp_lift_expr_step E π (e : expr) Φ:
    to_val (to_rtexpr π e) = None →
    (∀ (σ1 : state), state_ctx σ1 ={E}=∗
       ⌜∃ os e2 σ2 tsl, expr_step e π σ1 os e2 σ2 tsl⌝ ∗
        (∀ os e2 σ2 tsl, ⌜expr_step e π σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={E}⧗=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtexpr π e @ E {{ Φ }}.
  Proof. iIntros (?) "HWP". iApply (wp_c_lift_step) => //. naive_solver. Qed.
  Lemma wp_lift_stmt_step E π s rf Φ:
    (∀ (σ1 : state), state_ctx σ1 ={E}=∗
       ⌜∃ os e2 σ2 tsl, stmt_step s π rf σ1 os e2 σ2 tsl⌝ ∗
         (∀ os e2 σ2 tsl, ⌜stmt_step s π rf σ1 os e2 σ2 tsl⌝ -∗ ⌜heap_state_invariant σ2.(st_heap)⌝ -∗
          |={E}⧗=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtstmt π rf s @ E {{ Φ }}.
  Proof. iIntros "HWP". iApply (wp_c_lift_step) =>//. naive_solver. Qed.

  Lemma wp_alloc_failed E Φ:
    ⊢ WP AllocFailed @ E {{ Φ }}.
  Proof.
    iLöb as "IH".
    iApply wp_lift_pure_det_base_step_no_fork'; [done|by eauto using AllocFailedStep| | by iIntros "!> _"].
    move => ????? . inversion 1; simplify_eq => //.
    match goal with | H: to_rtexpr _ ?e = AllocFailed |- _ => destruct e; discriminate end.
  Qed.
End lifting.

(** Stmt WP *)
Definition stmt_wp_def `{!refinedcG Σ} (E : coPset) (π : thread_id) (Q : gmap label stmt) (Ψ : val → iProp Σ) (s : stmt) : iProp Σ :=
  (∀ Φ rf, ⌜Q = rf.(f_code)⌝ -∗ (∀ v, Ψ v -∗ WP to_rtstmt π rf (Return v) {{ Φ }}) -∗
    WP to_rtstmt π rf s @ E {{ Φ }}).
Definition stmt_wp_aux `{!refinedcG Σ} (E : coPset) (π : thread_id) (Q : gmap label stmt) (Ψ : val → iProp Σ) : seal (@stmt_wp_def Σ _ E π Q Ψ). Proof. by eexists. Qed.
Definition stmt_wp `{!refinedcG Σ} (E : coPset) (π : thread_id) (Q : gmap label stmt) (Ψ : val → iProp Σ) :
  stmt → iProp Σ := (stmt_wp_aux E π Q Ψ).(unseal).
Definition stmt_wp_eq `{!refinedcG Σ} (E : coPset) (π : thread_id) (Q : gmap label stmt) (Ψ : val → iProp Σ) : stmt_wp E π Q Ψ = @stmt_wp_def Σ _ E π Q Ψ := (stmt_wp_aux E π Q Ψ).(seal_eq).

Notation "'WPs{' π '}' s @ E {{ Q , Ψ } }" := (stmt_wp E π Q Ψ s%E)
  (at level 0, s, Q, Ψ at level 200, format "'[' 'WPs{' π '}' s  '/' '[       ' @  E  {{  Q ,  Ψ  } } ']' ']'" ) : bi_scope.

Notation "'WPs{' π '}' s {{ Q , Ψ } }" := (stmt_wp ⊤ π Q Ψ s%E)
  (at level 0, s, Q, Ψ at level 200, format "'[' 'WPs{' π '}'  s  '/' '[   ' {{  Q ,  Ψ  } } ']' ']'") : bi_scope.

Section stmt_wp.
Context `{!refinedcG Σ}.

Global Instance wps_proper E π Q :
  Proper (pointwise_relation _ (≡) ==> eq ==> (≡)) (stmt_wp E π Q).
Proof.
  intros ? ? Ha ?? <-.
  rewrite !stmt_wp_eq.
  solve_proper.
Qed.

Lemma stmt_wp_unfold s E π Q Ψ  :
  WPs{ π } s @ E {{ Q, Ψ }} ⊣⊢ stmt_wp_def E π Q Ψ s.
Proof. by rewrite stmt_wp_eq. Qed.

Lemma fupd_wps s E π Q Ψ :
  (|={E}=> WPs{π} s @ E {{ Q, Ψ }}) ⊢ WPs{π} s @ E{{ Q, Ψ }}.
Proof.
  rewrite stmt_wp_unfold. iIntros "Hs" (? rf HQ) "HΨ".
  iApply fupd_wp. by iApply "Hs".
Qed.

Lemma wps_fupd s E π Q Ψ :
  WPs{π} s @ E {{ Q, (λ v, |={E}=> Ψ v)}} ⊢ WPs{π} s @ E {{ Q, Ψ }}.
Proof.
  rewrite !stmt_wp_unfold. iIntros "Hs" (? rf HQ) "HΨ".
  iApply wp_fupd. iApply "Hs"; first done.
  iIntros (v) "Hv".
  iApply fupd_wp. iMod (fupd_mask_mono with "Hv") as "Hv"; first done.
  iModIntro. iApply (wp_wand with "(HΨ Hv)"). eauto.
Qed.

Global Instance elim_modal_bupd_wps π p s Q Ψ P E :
    ElimModal True p false (|==> P) P (WPs{π} s @ E {{ Q, Ψ }}) (WPs{π} s @ E {{ Q, Ψ }}).
Proof. by rewrite /ElimModal intuitionistically_if_elim (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wps. Qed.

Global Instance elim_modal_fupd_wps π p s Q Ψ P E :
    ElimModal True p false (|={E}=> P) P (WPs{π} s @ E {{ Q, Ψ }}) (WPs{π} s @ E {{ Q, Ψ }}).
Proof. by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r fupd_wps. Qed.

Lemma wps_wand s E π Q Φ Ψ:
  WPs{π} s @ E {{ Q , Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WPs{π} s @ E {{ Q , Ψ }}.
Proof.
  rewrite !stmt_wp_unfold. iIntros "HΦ H" (???) "HΨ".
  iApply "HΦ"; [ done | ..]. iIntros (v) "Hv".
  iApply "HΨ". iApply "H". iApply "Hv".
Qed.
End stmt_wp.

(** Expr WP *)
Definition expr_wp_def `{!refinedcG Σ} (E : coPset) (π : thread_id) (Φ : val → iProp Σ) (e : expr) : iProp Σ :=
  WP to_rtexpr π e @ E {{ Φ }}.
Definition expr_wp_aux `{!refinedcG Σ} (E : coPset) (π : thread_id) (Ψ : val → iProp Σ) : seal (@expr_wp_def Σ _ E π Ψ). Proof. by eexists. Qed.
Definition expr_wp `{!refinedcG Σ} (E : coPset) (π : thread_id) (Ψ : val → iProp Σ) :
  expr → iProp Σ := (expr_wp_aux E π Ψ).(unseal).
Definition expr_wp_eq `{!refinedcG Σ} (E : coPset) (π : thread_id) (Ψ : val → iProp Σ) : expr_wp E π Ψ = @expr_wp_def Σ _ E π Ψ := (expr_wp_aux E π Ψ).(seal_eq).

Notation "'WPe{' π '}' e @ E {{ Ψ } }" := (expr_wp E π Ψ e%E)
  (at level 0, e, Ψ at level 200, format "'[' 'WPe{' π '}' e  '/' '[       ' @  E  {{  Ψ  } } ']' ']'" ) : bi_scope.

Notation "'WPe{' π '}' e {{ Ψ } }" := (expr_wp ⊤ π Ψ e%E)
  (at level 0, e, Ψ at level 200, format "'[' 'WPe{' π '}'  e  '/' '[   ' {{  Ψ  } } ']' ']'") : bi_scope.

Section expr_wp.
Context `{!refinedcG Σ}.

Global Instance wpe_proper E π :
  Proper (pointwise_relation _ (≡) ==> eq ==> (≡)) (expr_wp E π).
Proof.
  intros ? ? Ha ?? <-.
  rewrite !expr_wp_eq.
  apply wp_proper. done.
Qed.

Lemma wpe_value π e v Φ  :
  IntoVal (to_rtexpr π e) v →
  Φ v -∗ WPe{π} e {{ Φ }}.
Proof.
  rewrite expr_wp_eq.
  iIntros (?) "Hv".
  by iApply wp_value.
Qed.

Lemma expr_wp_unfold e E π Ψ  :
  WPe{ π } e @ E {{ Ψ }} ⊣⊢ expr_wp_def E π Ψ e.
Proof. by rewrite expr_wp_eq. Qed.

Lemma fupd_wpe e E π Ψ :
  (|={E}=> WPe{π} e @ E {{ Ψ }}) ⊢ WPe{π} e @ E{{ Ψ }}.
Proof.
  rewrite expr_wp_unfold/expr_wp_def.
  iIntros "Ha". by iApply fupd_wp.
Qed.

Lemma wpe_fupd e E π Ψ :
  WPe{π} e @ E {{ λ v, |={E}=> Ψ v }} ⊢ WPe{π} e @ E {{ Ψ }}.
Proof.
  rewrite !expr_wp_unfold.
  iApply wp_fupd.
Qed.

Global Instance elim_modal_bupd_wpe π p e Ψ P E :
    ElimModal True p false (|==> P) P (WPe{π} e @ E {{ Ψ }}) (WPe{π} e @ E {{ Ψ }}).
Proof. by rewrite /ElimModal intuitionistically_if_elim (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wpe. Qed.

Global Instance elim_modal_fupd_wpe π p e Ψ P E :
    ElimModal True p false (|={E}=> P) P (WPe{π} e @ E {{ Ψ }}) (WPe{π} e @ E {{ Ψ }}).
Proof. by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r fupd_wpe. Qed.

Lemma wpe_wand e E π Φ Ψ:
  WPe{π} e @ E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WPe{π} e @ E {{ Ψ }}.
Proof.
  rewrite !expr_wp_unfold. iIntros "HΦ H".
  by iApply (wp_wand with "HΦ").
Qed.

Lemma wpe_logical_step (e : expr) π E1 E2 P Φ :
  TCEq (to_val (to_rtexpr π e)) None → E1 ⊆ E2 →
  logical_step E1 P -∗
  WPe{π} e @ E2 {{ λ v, P -∗ Φ v }} -∗
  WPe{π} e @ E2 {{ Φ }}.
Proof.
  rewrite !expr_wp_unfold.
  eapply wp_logical_step.
Qed.
Lemma wpe_maybe_logical_step π e E1 E2 P b Φ :
  TCEq (to_val (to_rtexpr π e)) None →
  E1 ⊆ E2 →
  maybe_logical_step b E1 P -∗
  WPe{π} e @ E2 {{ λ v, P -∗ Φ v }} -∗ WPe{π} e @ E2 {{ λ v, Φ v }}.
Proof.
  rewrite !expr_wp_eq.
  iIntros (??) "Hstep".
  iApply wp_maybe_logical_step; done.
Qed.


Global Instance frame_wpe π p e E R Φ Ψ :
  (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Ψ v)) →
  Frame p R (WPe{π} e @ E {{ Φ }}) (WPe{π} e @ E {{ Ψ }}) | 2.
Proof.
  rewrite !expr_wp_eq. apply _.
Qed.

Global Instance is_except_0_wp π e E Φ : IsExcept0 (WPe{π} e @ E {{ Φ }}).
Proof. rewrite expr_wp_eq. apply _. Qed.

Global Instance elim_modal_bupd_wp p π e E P Φ :
  ElimModal True p false (|==> P) P (WPe{π} e @ E {{ Φ }}) (WPe{π} e @ E {{ Φ }}).
Proof.
  rewrite !expr_wp_eq. apply _.
Qed.
End expr_wp.

(*** Lifting of expressions *)

Section expr_lifting.
Context `{!refinedcG Σ}.

Lemma wp_var π i x st l Φ :
  current_frame π i -∗
  x is_live{(π, i), st} l -∗
  (|={⊤}⧗=> ∀ v, ⌜val_of_loc l = Some v⌝ -∗ current_frame π i -∗ x is_live{(π, i), st} l -∗ Φ v) -∗
  WPe{π} Var x {{ Φ }}.
Proof.
  iIntros "Hframe Hlive HWP".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step; first done.
  iIntros (σ1) "(Hhctx & Hfctx & Htctx)".
  iPoseProof (state_lookup_var with "Htctx Hframe Hlive") as "(%ts & %cf & %ly & %Hsynty & % & % & % & %)".
  iModIntro.
  assert (val_of_loc l = Some (l2v l)).
  { by apply val_of_loc_Some_l2v. }
  iSplit; first by eauto 8 using VarS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  unfold thread_get_frame, state_get_thread in *.
  simplify_eq.
  iApply (physical_step_wand with "HWP").
  iIntros "HWP". iSplitR; first done.
  iFrame. iApply wp_value.
  iApply ("HWP" with "[] Hframe Hlive").
  done.
Qed.

Lemma wp_binop v1 v2 Φ op π E ot1 ot2:
  (∀ σ, state_ctx σ ={E, ∅}=∗
    ⌜∃ v', eval_bin_op op ot1 ot2 σ v1 v2 v'⌝ ∗
     |={∅}⧗=> (∀ v', ⌜eval_bin_op op ot1 ot2 σ v1 v2 v'⌝ -∗ |={∅, E}=> state_ctx σ ∗ Φ v')) -∗
  WPe{π} BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite expr_wp_unfold.
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

Lemma wp_binop_det v' v1 v2 Φ op π E ot1 ot2:
  (∀ σ, state_ctx σ ={E, ∅}=∗ ⌜∀ v, eval_bin_op op ot1 ot2 σ v1 v2 v ↔ v = v'⌝ ∗ |={∅}⧗=> (|={∅, E}=> state_ctx σ ∗ Φ v')) -∗
    WPe{π} BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_binop. iIntros (σ) "Hctx".
  iMod ("H" with "Hctx") as (Hv) "HΦ". iModIntro.
  iSplit.
  { iExists v'. by rewrite Hv. }
  iApply (physical_step_wand with "HΦ").
  by iIntros "Ha" (v ->%Hv).
Qed.

Lemma wp_binop_det_pure v' v1 v2 Φ op π E ot1 ot2:
  (∀ σ v, eval_bin_op op ot1 ot2 σ v1 v2 v ↔ v = v') →
  (|={E}⧗=> Φ v') -∗
  WPe{π} BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hop) "HΦ". iApply (wp_binop_det v').
  iIntros (σ) "Hσ". iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iSplit; [done|].
  iMod "He".
  iApply (physical_step_wand with "HΦ").
  iIntros "$". iApply fupd_mask_intro_subseteq; first set_solver. done.
Qed.

Lemma wp_check_binop v1 v2 Φ op π E ot1 ot2:
  (⌜∃ b, check_bin_op op ot1 ot2 v1 v2 b⌝ ∗
    |={E}⧗=> (∀ b, ⌜check_bin_op op ot1 ot2 v1 v2 b⌝ -∗ Φ (val_of_bool b))) -∗
  WPe{π} CheckBinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros "((%b & %Hcheck) & HΦ)".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step_fupd; auto.
  iIntros (σ1) "Hctx".
  iMod (fupd_mask_subseteq ∅) as "Hcl"; first set_solver.
  iModIntro.
  iSplit; first by eauto 8 using CheckBinOpS.
  clear Hcheck.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iMod "Hcl" as "_".
  iApply (physical_step_wand with "HΦ").
  iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iPoseProof ("HΦ" with "[//]") as "HΦ".
  iSplit => //. iFrame. by iApply wp_value.
Qed.

Lemma wp_check_binop_det_pure b' v1 v2 Φ op π E ot1 ot2:
  (∀ b, check_bin_op op ot1 ot2 v1 v2 b ↔ b = b') →
  (|={E}⧗=> Φ (val_of_bool b')) -∗
  WPe{π} CheckBinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (H) "H".
  iApply wp_check_binop.
  iSplitR. { iPureIntro. exists b'. by apply H. }
  iApply (physical_step_wand with "H").
  by iIntros "?" (b <-%H).
Qed.

Lemma wp_unop v1 Φ op π E ot:
  (∀ σ, state_ctx σ ={E, ∅}=∗
    ⌜∃ v', eval_un_op op ot σ v1 v'⌝ ∗
    |={∅}⧗=> (∀ v', ⌜eval_un_op op ot σ v1 v'⌝ ={∅, E}=∗ state_ctx σ ∗ Φ v')) -∗
   WPe{π} UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step_fupd; auto.
  iIntros (σ1) "Hctx".
  iMod ("HΦ" with "Hctx") as ([v' Heval]) "HΦ". iModIntro.
  iSplit; first by eauto 8 using UnOpS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iMod ("HΦ" with "[//]") as "[$ HΦ]".
  iModIntro. iSplit => //. by iApply wp_value.
Qed.

Lemma wp_unop_det v' v1 Φ op π E ot:
  (∀ σ, state_ctx σ ={E, ∅}=∗ ⌜∀ v, eval_un_op op ot σ v1 v ↔ v = v'⌝ ∗ |={∅}⧗=> (|={∅, E}=> state_ctx σ ∗ Φ v')) -∗
  WPe{π} UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_unop. iIntros (σ) "Hctx".
  iMod ("H" with "Hctx") as (Hv) "HΦ". iModIntro.
  iSplit.
  { iExists v'. by rewrite Hv. }
  iApply (physical_step_wand with "HΦ").
  by iIntros "?" (v ->%Hv).
Qed.

Lemma wp_unop_det_pure v' v1 Φ op π E ot:
  (∀ σ v, eval_un_op op ot σ v1 v ↔ v = v') →
  (|={E}⧗=> Φ v') -∗
  WPe{π} UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros (Hop) "HΦ". iApply (wp_unop_det v').
  iIntros (σ) "Hσ". iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iSplit; [done|].
  iMod "He" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_check_unop v1 Φ op π E ot:
  (⌜∃ b', check_un_op op ot v1 b'⌝ ∗
    |={E}⧗=> (∀ b', ⌜check_un_op op ot v1 b'⌝ -∗ Φ (val_of_bool b'))) -∗
   WPe{π} CheckUnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros "((%b' & %Hb') & HΦ)".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "Hctx".
  iModIntro.
  iSplit; first by eauto 8 using CheckUnOpS.
  clear Hb'. iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame. iApply wp_value.
  by iApply "HΦ".
Qed.

Lemma wp_check_unop_det_pure b' v1 Φ op π E ot:
  (∀ b, check_un_op op ot v1 b ↔ b = b') →
  (|={E}⧗=> (Φ (val_of_bool b'))) -∗
  WPe{π} CheckUnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros (H) "H".
  iApply wp_check_unop.
  iSplitR. { iPureIntro. exists b'. by apply H. }
  iApply (physical_step_wand with "H"). iIntros "H".
  by iIntros (b <-%H).
Qed.

Lemma wp_deref v Φ vl l ot q π E o:
  o = ScOrd ∨ o = Na1Ord →
  (∀ st, decode_op_val vl PtrOp st = Some $ OVPtr l) →
  l `has_layout_loc` ot_layout ot →
  (∀ st, ∃ ov, decode_op_val v ot st = Some ov) →
  l↦{q}v -∗ (|={E}⧗=> (∀ st ov, ⌜decode_op_val v ot st = Some ov⌝ -∗ l ↦{q} v -∗ Φ (encode_op_val ov))) -∗
  WPe{π} !{ot, o} (Val vl) @ E {{ Φ }}.
Proof.
  iIntros (Ho Hl Hll Hdecv) "Hmt HΦ".
  have Hlv : v `has_layout_val` ot_layout ot.
  { destruct (Hdecv inhabitant) as (ov & Hdec). by eapply decode_op_val_has_layout. }
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step; auto.
  iIntros ([[h ub] fn]) "((%&Hhctx&Hactx)&Hfctx)/=".
  iDestruct (heap_pointsto_is_alloc with "Hmt") as %Haid.
  destruct o; try by destruct Ho.
  - iModIntro. iDestruct (heap_pointsto_lookup_q (λ st, ∃ n, st = RSt n) with "Hhctx Hmt") as %Hat. { naive_solver. }
    iSplit; first by destruct (Hdecv {| hs_heap := h; hs_allocs := ub |}) as (? & ?); eauto 11 using DerefS.
    iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
    rename select (decode_op_val vl PtrOp _ = Some (OVPtr _)) into Hdecl.
    rewrite Hl in Hdecl. simplify_eq/=.
    iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
    iSplit => //. unfold end_st, end_expr.
    have Heq : (v = v') by apply: heap_at_inj_val. subst v'.
    rewrite /heap_fmap/=. erewrite heap_upd_heap_at_id => //.
    iFrame. iSplit; first done. iApply wp_value.
    by iApply ("HΦ" with "[] Hmt").
  - iMod (heap_read_na with "Hhctx Hmt") as "(% & Hσ & Hσclose)" => //. iModIntro.
    iSplit; first by destruct (Hdecv {| hs_heap := h; hs_allocs := ub |}) as (? & ?); eauto 11 using DerefS.
    iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
    rename select (decode_op_val vl PtrOp _ = Some (OVPtr _)) into Hdecl.
    rewrite Hl in Hdecl. simplify_eq/=.
    iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
    iSplit => //. unfold end_st, end_expr.
    have ? : (v = v') by apply: heap_at_inj_val. subst v'.
    iFrame => /=. iSplit; first done.
    iApply (wp_lift_expr_step _ _ (Deref Na2Ord ot (Val vl))); auto.
    iIntros ([[h2 ub2] fn2]) "((%&Hhctx&Hactx)&Hfctx)/=".
    iMod ("Hσclose" with "Hhctx") as (?) "(Hσ & Hv)".
    iModIntro; iSplit; first by destruct (Hdecv {| hs_heap := h2; hs_allocs := ub2 |}) as (? & ?); eauto 11 using DerefS.
    iIntros (? e2 σ2 efs Hst ?).
    iApply physical_step_intro.
    inv_expr_step.
    rename select (decode_op_val vl PtrOp _ = Some (OVPtr _)) into Hdecl.
    rewrite Hl in Hdecl. simplify_eq/=.
    iSplit => //.
    have ? : (v = v') by apply: (heap_at_inj_val _ _ h2). subst.
    iFrame. iSplit; first done.
    iApply wp_value. by iApply ("HΦ" with "[] Hv").
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

Lemma wp_cas_fail vl1 vl2 vd vo ve z1 z2 Φ l1 l2 ot q π E:
  (∀ st, decode_op_val vl1 PtrOp st = Some $ OVPtr l1) →
  (∀ st, decode_op_val vl2 PtrOp st = Some $ OVPtr l2) →
  l1 `has_layout_loc` ot_layout ot →
  l2 `has_layout_loc` ot_layout ot →
  val_to_Z_ot vo ot = Some z1 →
  val_to_Z_ot ve ot = Some z2 →
  length vd = (ot_layout ot).(ly_size) →
  ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
  z1 ≠ z2 →
  l1↦{q}vo -∗ l2↦ve -∗
  (|={E}⧗=> (l1 ↦{q} vo -∗ l2↦vo -∗ Φ (val_of_bool false))) -∗
   WPe{π} CAS ot (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Hneq) "Hl1 Hl2 HΦ".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "((%&Hhctx&?)&Hfctx)".
  iDestruct (heap_pointsto_is_alloc with "Hl1") as %Haid1.
  iDestruct (heap_pointsto_is_alloc with "Hl2") as %Haid2.
  move: (Hvo) (Hve) => /val_to_Z_ot_length ? /val_to_Z_ot_length ?.
  iDestruct (heap_pointsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl1") as %? => //. { naive_solver. }
  iDestruct (heap_pointsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl2") as %? => //.
  iModIntro. iSplit; first by eauto 15 using CasFailS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  - rename select (decode_op_val vl1 _ _ = Some _) into Hdec1.
    rename select (decode_op_val vl2 _ _ = Some _) into Hdec2.
    rewrite Hl1 in Hdec1. rewrite Hl2 in Hdec2. simplify_eq/=.
    have ? : (vo = vo0) by apply: heap_lookup_loc_inj_val.
    have ? : (ve = ve0) by apply: heap_lookup_loc_inj_val. simplify_eq.
    have ? : (length ve0 = length vo0) by congruence.
    iApply physical_step_fupd.
    iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
    iMod (heap_write with "Hhctx Hl2") as "[$ Hl2]" => //. iModIntro.
    iFrame. iSplit => //. iSplit; first done.
    iApply wp_value. by iApply ("HΦ" with "[$] [$]").
  - rename select (decode_op_val vl1 _ _ = Some _) into Hdec1.
    rename select (decode_op_val vl2 _ _ = Some _) into Hdec2.
    rewrite Hl1 in Hdec1. rewrite Hl2 in Hdec2. simplify_eq/=.
    have ? : (vo = vo0) by apply: heap_lookup_loc_inj_val.
    have ? : (ve = ve0) by apply: heap_lookup_loc_inj_val. simplify_eq.
Qed.

Lemma wp_cas_suc vl1 vl2 vd vo ve z1 z2 Φ l1 l2 ot π E q:
  (∀ st, decode_op_val vl1 PtrOp st = Some $ OVPtr l1) →
  (∀ st, decode_op_val vl2 PtrOp st = Some $ OVPtr l2) →
  l1 `has_layout_loc` ot_layout ot →
  l2 `has_layout_loc` ot_layout ot →
  val_to_Z_ot vo ot = Some z1 →
  val_to_Z_ot ve ot = Some z2 →
  length vd = (ot_layout ot).(ly_size) →
  ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
  z1 = z2 →
  l1↦vo -∗ l2↦{q}ve -∗
  (|={E}⧗=> (l1 ↦ vd -∗ l2↦{q}ve -∗ Φ (val_of_bool true))) -∗
  WPe{π} CAS ot (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Hneq) "Hl1 Hl2 HΦ".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "((%&Hhctx&?)&Hfctx)".
  iDestruct (heap_pointsto_is_alloc with "Hl1") as %Haid1.
  iDestruct (heap_pointsto_is_alloc with "Hl2") as %Haid2.
  move: (Hvo) (Hve) => /val_to_Z_ot_length ? /val_to_Z_ot_length ?.
  iDestruct (heap_pointsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl1") as %? => //.
  iDestruct (heap_pointsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl2") as %? => //. { naive_solver. }
  iModIntro. iSplit; first by eauto 15 using CasSucS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  - rename select (decode_op_val vl1 _ _ = Some _) into Hdec1.
    rename select (decode_op_val vl2 _ _ = Some _) into Hdec2.
    rewrite Hl1 in Hdec1. rewrite Hl2 in Hdec2. simplify_eq/=.
    have ? : (ve = ve0) by apply: heap_lookup_loc_inj_val.
    have ? : (vo = vo0) by apply: heap_lookup_loc_inj_val. simplify_eq.
  - rename select (decode_op_val vl1 _ _ = Some _) into Hdec1.
    rename select (decode_op_val vl2 _ _ = Some _) into Hdec2.
    rewrite Hl1 in Hdec1. rewrite Hl2 in Hdec2. simplify_eq/=.
    have ? : (ve = ve0) by apply: heap_lookup_loc_inj_val.
    have ? : (vo = vo0) by apply: heap_lookup_loc_inj_val. simplify_eq.
    have ? : (length vo0 = length vd) by congruence.
    iApply physical_step_fupd.
    iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
    iMod (heap_write with "Hhctx Hl1") as "[$ Hmt]" => //. iModIntro.
    iFrame. iSplit => //. iSplit; first done.
    iApply wp_value. by iApply ("HΦ" with "[$] [$]").
Qed.

Lemma wp_neg_int Φ v v' n π E it:
  val_to_Z v it = Some n →
  val_of_Z (wrap_to_it (-n) it) it = Some v' →
  (|={E}⧗=> Φ (v')) -∗ WPe{π} UnOp NegOp (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply (wp_unop_det_pure v'); [|done].
  move => ??. split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_int Φ v v' i i' π E its itt:
  val_to_Z v its = Some i →
  wrap_to_it i itt = i' →
  val_of_Z i' itt = Some v' →
  (|={E}⧗=> Φ (v')) -∗ WPe{π} UnOp (CastOp (IntOp itt)) (IntOp its) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv ? Hv') "HΦ".
  iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_loc Φ v l π E:
  (∀ st, decode_op_val v PtrOp st = Some $ OVPtr l) →
  (|={E}⧗=> Φ v) -∗ WPe{π} UnOp (CastOp PtrOp) PtrOp (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_ptr_ref Φ v l π E:
  (∀ st, decode_op_val v RefOp st = Some $ OVPtr l) →
  (|={E}⧗=> Φ (encode_op_val (OVPtr l))) -∗
  WPe{π} UnOp (CastOp RefOp) PtrOp (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - inversion 1; simplify_eq/=.
    rename select (decode_op_val _ RefOp _ = Some _) into Hdec.
    rewrite Hv in Hdec. by simplify_eq/=.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_bool_int Φ b v v' π E it:
  val_to_bool v = Some b →
  val_of_Z (bool_to_Z b) it = Some v' →
  (|={E}⧗=> Φ v') -∗
  WPe{π} UnOp (CastOp (IntOp it)) (BoolOp) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hb) "HΦ". iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_ptr_int Φ v v' l π E it:
  (∀ st, decode_op_val v PtrOp st = Some $ OVPtr l) →
  val_of_Z l.(loc_a) it = Some v' →
  (|={E}⧗=> Φ (v')) -∗
  WPe{π} UnOp (CastOp (IntOp it)) PtrOp (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply (wp_unop_det v').
  iIntros (σ) "Hctx".
  iMod (fupd_mask_subseteq ∅) as "Hcl"; first set_solver.
  iModIntro.
  iSplit. {
    iPureIntro. split.
    - inversion 1; simplify_eq/=.
      rename select (decode_op_val _ _ _ = Some _) into Hdec.
      rewrite Hv in Hdec. by simplify_eq/=.
    - move => ->. by econstructor.
  }
  iMod "Hcl" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_cast_null_int Φ v π E it:
  val_of_Z 0 it = Some v →
  (|={E}⧗=> Φ v) -∗
  WPe{π} UnOp (CastOp (IntOp it)) PtrOp (Val NULL) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_cast_ptr_int.
  { intros.
    simp decode_op_val.
    rewrite (val_to_of_loc NULL_loc); first done.
    apply val_of_loc_Some. simpl.
    rewrite int_elem_of_it_iff. done. }
  { done. }
  done.
Qed.

Lemma wp_cast_int_ptr_prov_none Φ v a l it π E :
  val_to_Z v it = Some a →
  min_alloc_start ≤ a →
  a ≤ max_alloc_end_zero →
  l = Loc ProvNone a →
  (|={E}⧗=> ∀ v, ⌜val_of_loc l = Some v⌝ -∗ l ↦ [] -∗ Φ v) -∗
  WPe{π} UnOp (CastOp PtrOp) (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hs He Hl) "HΦ".
  iApply wp_unop.
  iIntros (σ) "Hctx". iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iSplit.
  { iPureIntro; eexists _. econstructor; [done.. | ].
    subst. apply val_of_loc_Some. simpl.
    rewrite int_elem_of_it_iff. split; last done.
    change (0 ≤ a). unfold min_alloc_start in Hs. lia. }
  iMod "HE" as "_". iApply (physical_step_wand with "HΦ"); iIntros "HΦ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iIntros (v' Hv'). iMod "HE" as "_". iModIntro. iFrame.
  inversion Hv'; simplify_eq.
  iApply ("HΦ" with "[//] []").
  iApply heap_pointsto_prov_none_nil; done.
Qed.

Lemma wp_cast_int_null_ptr Φ v it π E :
  val_to_Z v it = Some 0 →
  (|={E}⧗=> Φ NULL) -∗
  WPe{π} UnOp (CastOp PtrOp) (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop.
  iIntros (σ) "Hctx". iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iSplit.
  { iPureIntro; eexists NULL. econstructor; [done.. | ].
    apply val_of_loc_Some. simpl.
    rewrite int_elem_of_it_iff. done. }
  iMod "HE" as "_". iApply (physical_step_wand with "HΦ"); iIntros "HΦ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iIntros (v' Hv'). iMod "HE" as "_". iModIntro.
  inversion Hv'; simplify_eq.
  assert (val_of_loc NULL_loc = Some NULL) as Hnull.
  { apply val_of_loc_Some. simpl. rewrite int_elem_of_it_iff. done. }
  change (val_of_loc (Loc ProvNone 0) = Some NULL) in Hnull.
  injection (eq_trans (eq_sym H2) Hnull) as ->. iFrame.
Qed.

Lemma wp_cast_int_bool Φ v n E π it:
  val_to_Z v it = Some n →
  (|={E}⧗=> Φ (val_of_bool (bool_decide (n ≠ 0)))) -∗
  WPe{π} UnOp (CastOp BoolOp) (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ". iApply wp_unop_det_pure; [|done].
  move => ??. split.
  - inversion 1; simplify_eq.
    revert select (cast_to_bool _ _ _ = _) => /=.
    rewrite Hv. by move => /= [<-].
  - move => ->. econstructor => //=. by rewrite Hv.
Qed.

Lemma wp_copy_alloc_id Φ it a l v1 v2 π E :
  val_to_Z v1 it = Some a →
  (∀ st, decode_op_val v2 PtrOp st = Some $ OVPtr l) →
  a ∈ USize →
  (|={E}⧗=> ∀ v, ⌜val_of_loc (Loc l.(loc_p) a) = Some v⌝ -∗ Φ v) -∗
  WPe{π} CopyAllocId (IntOp it) (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Ha Hl ?) "HΦ".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step => //.
  iIntros (σ1) "Hctx". iModIntro.
  iSplit.
  { iPureIntro; eexists _, _, _, _. eapply CopyAllocIdS; [done.. | ].
    by apply val_of_loc_Some. }
  iIntros (???? Hstep ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame.
  iApply wp_value. iApply ("HΦ").
  rename select (decode_op_val _ _ _ = Some _) into Hdec.
  rewrite Hl in Hdec. simplify_eq.
  done.
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
  | ShlOp => 0 ≤ n2
  | ShrOp => 0 ≤ n2
  | DivOp => n2 ≠ 0
  | ModOp => n2 ≠ 0
  | _     => True (* Relational operators. *)
  end.

Lemma wp_int_arithop Φ op v1 v2 n1 n2 nr it π E :
  val_to_Z v1 it = Some n1 →
  val_to_Z v2 it = Some n2 →
  int_arithop_result it n1 n2 op = Some nr →
  int_arithop_sidecond it n1 n2 nr op →
  (∀ v, ⌜val_of_Z (wrap_to_it nr it) it = Some v⌝ -∗ |={E}⧗=> Φ v) -∗
  WPe{π} BinOp op (IntOp it) (IntOp it) (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hn1 Hn2 Hop Hsc) "HΦ".
  assert (wrap_to_it nr it ∈ it) as [v Hv]%(val_of_Z_is_Some).
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

Lemma wp_check_int_arithop Φ op v1 v2 n1 n2 b it π E :
  val_to_Z v1 it = Some n1 →
  val_to_Z v2 it = Some n2 →
  check_arith_bin_op op it n1 n2 = Some b →
  (|={E}⧗=> Φ (val_of_bool b)) -∗
  WPe{π} CheckBinOp op (IntOp it) (IntOp it) (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hn1 Hn2 Hop) "HΦ".
  iApply (wp_check_binop_det_pure b with "HΦ").
  intros b'. split.
  - inversion 1; simplify_eq/=. done.
  - intros ->. econstructor; done.
Qed.

Lemma wp_check_int_unop Φ op v n b it π E:
  val_to_Z v it = Some n →
  check_arith_un_op op it n = Some b →
  (|={E}⧗=> Φ (val_of_bool b)) -∗
  WPe{π} CheckUnOp op (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hn Hop) "HΦ".
  iApply (wp_check_unop_det_pure b with "HΦ").
  intros b'. split.
  - inversion 1; simplify_eq/=. done.
  - intros ->. econstructor; done.
Qed.

Lemma wp_ptr_relop Φ op v1 v2 v l1 l2 b rit π E :
  (∀ st, decode_op_val v1 PtrOp st = Some $ OVPtr l1) →
  (∀ st, decode_op_val v2 PtrOp st = Some $ OVPtr l2) →
  val_of_Z (bool_to_Z b) rit = Some v →
  match op with
  | EqOp rit => Some (bool_decide (l1.(loc_a) = l2.(loc_a)), rit)
  | NeOp rit => Some (bool_decide (l1.(loc_a) ≠ l2.(loc_a)), rit)
  | LtOp rit => Some (bool_decide (l1.(loc_a) < l2.(loc_a)), rit)
  | GtOp rit => Some (bool_decide (l1.(loc_a) > l2.(loc_a)), rit)
  | LeOp rit => Some (bool_decide (l1.(loc_a) <= l2.(loc_a)), rit)
  | GeOp rit => Some (bool_decide (l1.(loc_a) >= l2.(loc_a)), rit)
  | _ => None
  end = Some (b, rit) →
  (|={E}⧗=> Φ v) -∗
  WPe{π} BinOp op PtrOp PtrOp (Val v1) (Val v2) @ E {{ Φ }}.
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
  iIntros (v' Hstep). iMod "HE" as "_". iModIntro. iFrame.
  inversion Hstep; simplify_eq => //.
  rename select (decode_op_val v1 _ _ = Some _) into Hdec1.
  rename select (decode_op_val v2 _ _ = Some _) into Hdec2.
  rewrite Hv1 in Hdec1. rewrite Hv2 in Hdec2.
  simplify_eq/=. done.
Qed.

Lemma loc_in_bounds_enum_tag el variant variant_ly l :
  enum_variant_lookup el.(el_variants) variant = Some variant_ly →
  loc_in_bounds l 0 (ly_size el) -∗
  loc_in_bounds l 0 (ly_size (it_layout el.(el_tag_it))).
Proof.
  intros Hvariant.
  pose proof (enum_variant_layout_bounds _ _ _ Hvariant) as (Htag_data & Hvariant_bound).
  iIntros "Hlb". iApply (loc_in_bounds_shorten_suf with "Hlb").
  simpl. change (ly_size el) with (el_size el). lia.
Qed.

Lemma loc_in_bounds_enum_tag_padding el variant variant_ly l :
  enum_variant_lookup el.(el_variants) variant = Some variant_ly →
  loc_in_bounds l 0 (ly_size el) -∗
  loc_in_bounds (l +ₗ ly_size (it_layout el.(el_tag_it))) 0
    (ly_size (enum_tag_padding_ly el)).
Proof.
  intros Hvariant.
  pose proof (enum_variant_layout_bounds _ _ _ Hvariant) as (Htag_data & Hvariant_bound).
  iIntros "Hlb".
  iApply (loc_in_bounds_offset with "Hlb").
  - done.
  - simpl. lia.
  - simpl. rewrite /enum_tag_padding_ly /=.
    change (ly_size {| ly_size := el_data_offset el - ly_size (el_tag_it el); ly_align_log := 0 |}) with
      (el_data_offset el - ly_size (el_tag_it el))%nat.
    change (ly_size el) with (el_size el).
    destruct l => /=; lia.
Qed.

Lemma loc_in_bounds_enum_payload el variant variant_ly l :
  enum_variant_lookup el.(el_variants) variant = Some variant_ly →
  loc_in_bounds l 0 (ly_size el) -∗
  loc_in_bounds (l +ₗ el.(el_data_offset)) 0 (ly_size variant_ly).
Proof.
  intros Hvariant.
  pose proof (enum_variant_layout_bounds _ _ _ Hvariant) as (_ & Hvariant_bound).
  iIntros "Hlb".
  iApply (loc_in_bounds_offset with "Hlb").
  - done.
  - simpl. lia.
  - simpl. change (ly_size el) with (el_size el). lia.
Qed.

Lemma loc_in_bounds_enum_tail_padding el variant variant_ly l :
  enum_variant_lookup el.(el_variants) variant = Some variant_ly →
  loc_in_bounds l 0 (ly_size el) -∗
  loc_in_bounds (l +ₗ el.(el_data_offset) +ₗ ly_size variant_ly) 0
    (ly_size (enum_tail_padding_ly el variant_ly)).
Proof.
  intros Hvariant.
  pose proof (enum_variant_layout_bounds _ _ _ Hvariant) as (_ & Hvariant_bound).
  iIntros "Hlb".
  rewrite shift_loc_assoc_nat.
  iApply (loc_in_bounds_offset with "Hlb").
  - done.
  - simpl. lia.
  - simpl. rewrite /enum_tail_padding_ly /=.
    change (ly_size {| ly_size := el_size el - el_data_offset el - ly_size variant_ly; ly_align_log := 0 |}) with
      (el_size el - el_data_offset el - ly_size variant_ly)%nat.
    change (ly_size el) with (el_size el).
    replace (el_size el - el_data_offset el - ly_size variant_ly)%nat with
      (el_size el - (el_data_offset el + ly_size variant_ly))%nat by lia.
    rewrite Nat2Z.inj_sub; lia.
Qed.

Lemma wp_ptr_offset Φ vl l π E it o ly vo:
  (∀ st, decode_op_val vl PtrOp st = Some $ OVPtr l) →
  val_to_Z vo it = Some o →
  ly_size ly * o ∈ ISize →
  loc_in_bounds (l offset{ly}ₗ o) 0 0 -∗
  loc_in_bounds l 0 0 -∗
  (|={E}⧗=> ∀ v, ⌜val_of_loc (l offset{ly}ₗ o) = Some v⌝ -∗ Φ v) -∗
  WPe{π} Val vl at_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo ?) "Hl Hl' HΦ".
  iApply (wp_binop_det (l2v (l offset{ly}ₗ o))). iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iDestruct "Hσ" as "(Hhctx & ?)".
  iDestruct (loc_in_bounds_to_heap_loc_in_bounds' with "Hl Hhctx") as %?.
  iDestruct (loc_in_bounds_to_heap_loc_in_bounds' with "Hl' Hhctx") as %?.
  iDestruct (loc_in_bounds_in_range_usize with "Hl") as %?.
  iSplit. {
    iPureIntro. split.
    - inversion 1. simplify_eq.
      rename select (decode_op_val _ _ _ = Some _) into Hdec.
      rewrite Hvl in Hdec. simplify_eq/=.
      erewrite l2v_correct; done.
    - move => ->. eapply PtrOffsetOpIP; try done.
      by apply val_of_loc_Some_l2v. }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
  iApply "HΦ". iPureIntro.
  by apply val_of_loc_Some_l2v.
Qed.

Lemma wp_enum_data `{!LayoutAlg} π E Φ (els : enum_layout_spec) el variant variant_ly l :
  use_enum_layout_alg els = Some el →
  enum_variant_lookup el.(el_variants) variant = Some variant_ly →
  loc_in_bounds l 0 el.(el_size) -∗
  (|={E}⧗=> ∀ v, ⌜val_to_loc v = Some (GetEnumDataLocSt l els)⌝ -∗ Φ v) -∗
  WPe{π} EnumData els variant (Val (l2v l)) @ E {{ Φ }}.
Proof.
  iIntros (Halg Hvariant) "#Hlb HΦ".
  iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Haddr".
  rewrite /EnumData /use_enum_layout_alg' Halg /=.
  iApply (wp_ptr_offset _ (l2v l) l _ _ ISize (Z.of_nat el.(el_data_offset)) U8 _).
  { intros. apply val_to_loc_decode. by apply val_to_loc_Some_l2v. }
  { destruct (val_of_Z_is_Some ISize (Z.of_nat el.(el_data_offset))) as (vo & Hvo).
    { rewrite int_elem_of_it_iff. split; first by rewrite /min_int /int_half_modulus /=; lia.
      pose proof (enum_variant_lookup_in_bounds el variant variant_ly Hvariant).
      pose proof (el_size_bounded el). lia. }
    rewrite Hvo /=. by apply val_to_of_Z. }
  { simpl. rewrite Z.mul_1_l. rewrite int_elem_of_it_iff. split; first by rewrite /min_int /int_half_modulus /=; lia.
    pose proof (enum_variant_lookup_in_bounds el variant variant_ly Hvariant).
    pose proof (el_size_bounded el). lia. }
  { rewrite offset_loc_sz1 //.
    iPoseProof (loc_in_bounds_enum_payload with "Hlb") as "Hpayload_lb"; first done.
    iApply loc_in_bounds_shorten_suf; last iExact "Hpayload_lb". lia. }
  { iApply loc_in_bounds_shorten_suf; last done. lia. }
  iApply (physical_step_wand with "HΦ").
  iIntros "HΦ" (v Hv).
  iApply "HΦ". iPureIntro.
  rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=.
  rewrite offset_loc_sz1 in Hv; last done.
  by apply val_to_of_loc.
Qed.

Lemma wp_ptr_neg_offset Φ vl l π E it o ly vo:
  (∀ st, decode_op_val vl PtrOp st = Some $ OVPtr l) →
  val_to_Z vo it = Some o →
  ly_size ly * -o ∈ ISize →
  loc_in_bounds (l offset{ly}ₗ -o) 0 0 -∗
  loc_in_bounds l 0 0 -∗
  (|={E}⧗=> ∀ v, ⌜val_of_loc (l offset{ly}ₗ -o) = Some v⌝ -∗ Φ v) -∗
  WPe{π} Val vl at_neg_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo ?) "Hl Hl' HΦ".
  iApply (wp_binop_det ((l offset{ly}ₗ -o))). iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iDestruct "Hσ" as "(Hhctx & ?)".
  iDestruct (loc_in_bounds_to_heap_loc_in_bounds' with "Hl Hhctx") as %?.
  iDestruct (loc_in_bounds_to_heap_loc_in_bounds' with "Hl' Hhctx") as %?.
  iDestruct (loc_in_bounds_in_range_usize with "Hl") as %?.
  iSplit. {
    iPureIntro. split.
    - inversion 1. simplify_eq.
      rename select (decode_op_val _ _ _ = Some _) into Hdec.
      rewrite Hvl in Hdec. simplify_eq/=.
      erewrite l2v_correct; done.
    - move => ->. eapply PtrNegOffsetOpIP; try done.
      by apply val_of_loc_Some_l2v.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
  iApply "HΦ". iPureIntro.
  by apply val_of_loc_Some_l2v.
Qed.

Lemma wp_ptr_wrapping_neg_offset Φ vl l π E it o ly vo:
  (∀ st, decode_op_val vl PtrOp st = Some $ OVPtr l) →
  val_to_Z vo it = Some o →
  (|={E}⧗=> ∀ v, ⌜val_of_loc (l wrapping_offset{ly}ₗ -o) = Some v⌝ -∗ Φ v) -∗
  WPe{π} Val vl at_wrapping_neg_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo) "HΦ".
  iApply wp_binop_det. iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  assert (val_of_loc (l wrapping_offset{ly}ₗ -o) = Some (l2v (l wrapping_offset{ly}ₗ -o))) as Hv.
  { apply val_of_loc_Some_l2v. apply wrapping_shift_loc_in_range. }
  iSplit. {
    iPureIntro. split.
    - inversion 1. simplify_eq.
      rename select (decode_op_val _ _ _ = Some _) into Hdec.
      rewrite Hvl in Hdec. simplify_eq/=.
      erewrite l2v_correct; done.
    - move => ->. eapply PtrWrappingNegOffsetOpIP; try done.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
  iApply "HΦ". iPureIntro.
  apply val_of_loc_Some_l2v.
  apply wrapping_shift_loc_in_range.
Qed.
Lemma wp_ptr_wrapping_offset Φ vl l π E it o ly vo:
  (∀ st, decode_op_val vl PtrOp st = Some $ OVPtr l) →
  val_to_Z vo it = Some o →
  (|={E}⧗=> ∀ v, ⌜val_of_loc (l wrapping_offset{ly}ₗ o) = Some v⌝ -∗ Φ v) -∗
  WPe{π} Val vl at_wrapping_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo) "HΦ".
  iApply wp_binop_det. iIntros (σ) "Hσ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  assert (val_of_loc (l wrapping_offset{ly}ₗ o) = Some (l2v (l wrapping_offset{ly}ₗ o))) as Hv.
  { apply val_of_loc_Some_l2v. apply wrapping_shift_loc_in_range. }
  iSplit. {
    iPureIntro. split.
    - inversion 1. simplify_eq.
      rename select (decode_op_val _ _ _ = Some _) into Hdec.
      rewrite Hvl in Hdec. simplify_eq/=.
      erewrite l2v_correct; done.
    - move => ->. by eapply PtrWrappingOffsetOpIP.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
  iApply "HΦ". iPureIntro.
  apply val_of_loc_Some_l2v.
  apply wrapping_shift_loc_in_range.
Qed.

Lemma wp_ptr_diff π Φ vl1 l1 vl2 l2 ly vo:
  (∀ st, decode_op_val vl1 PtrOp st = Some $ OVPtr l1) →
  (∀ st, decode_op_val vl2 PtrOp st = Some $ OVPtr l2) →
  val_of_Z ((l1.(loc_a) - l2.(loc_a)) `div` ly.(ly_size)) ISize = Some vo →
  l1.(loc_p) = l2.(loc_p) →
  0 < ly.(ly_size) →
  loc_in_bounds l1 0 0 -∗
  loc_in_bounds l2 0 0 -∗
  (alloc_alive_loc l1 ∧ |={⊤}⧗=> Φ vo) -∗
  WPe{π} Val vl1 sub_ptr{ly , PtrOp, PtrOp} Val vl2 {{ Φ }}.
Proof.
  iIntros (Hvl1 Hvl2 Hvo ??) "Hl1 Hl2 HΦ".
  iApply wp_binop_det. iIntros (σ) "Hσ".
  destruct (decide (valid_ptr l1 σ.(st_heap))). 2: {
    iDestruct "HΦ" as "[Ha _]".
    iDestruct "Hσ" as "(Hhctx & _)".
    by iMod (alloc_alive_loc_to_valid_ptr with "Hl1 Ha Hhctx") as %?.
  }
  destruct (decide (valid_ptr l2 σ.(st_heap))). 2: {
    iDestruct "HΦ" as "[Ha _]".
    iDestruct "Hσ" as "(Hhctx & _)".
    iMod (alloc_alive_loc_to_valid_ptr with "Hl2 [Ha] Hhctx") as %?; [|done].
    by iApply alloc_alive_loc_mono.
  }
  iDestruct "HΦ" as "[_ HΦ]".
  iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
  iSplit. {
    iPureIntro. split.
    - inversion 1; simplify_eq.
      rename select (decode_op_val vl1 _ _ = Some _) into Hdec1.
      rename select (decode_op_val vl2 _ _ = Some _) into Hdec2.
      rewrite Hvl1 in Hdec1. rewrite Hvl2 in Hdec2.
      simplify_eq/=. done.
    - move => ->. by apply: PtrDiffOpPP.
  }
  iMod "HE" as "_".
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
Qed.

Lemma wp_get_member `{!LayoutAlg} Φ vl l sls sl n π E:
  (∀ st, decode_op_val vl PtrOp st = Some $ OVPtr l) →
  use_struct_layout_alg sls = Some sl →
  is_Some (index_of sl.(sl_members) n) →
  loc_in_bounds l 0 (ly_size sl) -∗
  (|={E}⧗=> ∀ v, ⌜val_of_loc (l at{sl}ₗ n) = Some v⌝ -∗ Φ v) -∗
  WPe{π} Val vl at{sls} n @ E {{ Φ }}.
Proof.
  iIntros (Hvl Halg [i Hi]) "#Hl HΦ".
  rewrite /GetMember/GetMemberLoc/offset_of /=.
  rewrite /use_struct_layout_alg' Halg /= Hi /=.
  have [|v Hv]:= (val_of_Z_is_Some ISize (offset_of_idx sl.(sl_members) i)). {
    rewrite int_elem_of_it_iff.
    split; first by rewrite /min_int /int_half_modulus/=; lia.
    by apply offset_of_bound. }
  rewrite Hv /=. move: Hv => /val_to_of_Z Hv.
  iApply wp_ptr_offset; [| done | .. ].
  { done. }
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
Lemma wp_get_member_union `{!LayoutAlg} Φ vl l ul uls n π E:
  use_union_layout_alg uls = Some ul →
  val_to_loc vl = Some l →
  (∀ v, ⌜val_of_loc (l at_union{ul}ₗ n) = Some v⌝ -∗ Φ v) -∗
  WPe{π} Val vl at_union{uls} n @ E {{ Φ }}.
Proof.
  iIntros (Halg ?%val_of_to_loc) "HΦ"; subst.
  rewrite expr_wp_unfold.
  rewrite /GetMemberUnion/GetMemberUnionLoc. iApply @wp_value.
  iApply "HΦ". done.
Qed.

(* TODO: lemmas for accessing discriminant/data of enum *)

Lemma wp_offset_of `{!LayoutAlg} Φ sls sl m i π E:
  use_struct_layout_alg sls = Some sl →
  offset_of sl.(sl_members) m = Some i →
  (∀ v, ⌜val_of_Z i ISize = Some v⌝ -∗ Φ v) -∗
  WPe{π} OffsetOf sls m @ E {{ Φ }}.
Proof.
  rewrite /OffsetOf. iIntros (Halg Ho) "HΦ".
  rewrite /use_struct_layout_alg' Halg /=.
  have [|? Hs]:= (val_of_Z_is_Some ISize i). {
    rewrite int_elem_of_it_iff.
    split; first by rewrite /min_int /int_half_modulus /=; lia.
    move: Ho => /fmap_Some[?[?->]].
    by apply offset_of_bound.
  }
  rewrite Ho /= Hs /=.
  rewrite expr_wp_unfold.
  iApply wp_value.
  by iApply "HΦ".
Qed.

Lemma wp_offset_of_union Φ uls m π E:
  Φ (i2v 0 ISize) -∗ WPe{π} OffsetOfUnion uls m @ E {{ Φ }}.
Proof. rewrite expr_wp_unfold. by iApply wp_value. Qed.

Lemma wp_if_int Φ it v e1 e2 n π E:
  val_to_Z v it = Some n →
  (|={E}⧗=> if bool_decide (n ≠ 0) then WPe{π} e1 @ E {{ Φ }} else WPe{π} e2 @ E {{ Φ }}) -∗
  WPe{π} IfE (IntOp it) (Val v) e1 e2 @ E {{ Φ }}.
Proof.
  iIntros (Hn) "HΦ".
  iEval (rewrite expr_wp_unfold).
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?". iModIntro.
  iSplit. { iPureIntro. repeat eexists. apply IfES. rewrite /= Hn //. }
  iIntros (? ? σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame.
  case_bool_decide; by rewrite expr_wp_unfold.
Qed.

Lemma wp_if_bool Φ v e1 e2 b π E:
  val_to_bool v = Some b →
  (|={E}⧗=> if b then WPe{π} e1 @ E {{ Φ }} else WPe{π} e2 @ E {{ Φ }}) -∗
  WPe{π} IfE BoolOp (Val v) e1 e2 @ E {{ Φ }}.
Proof.
  iIntros (Hb) "HΦ".
  iEval (rewrite expr_wp_unfold).
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?". iModIntro.
  iSplit. { iPureIntro. repeat eexists. apply IfES. rewrite /= Hb //. }
  iIntros (? ? σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame.
  destruct b; by rewrite expr_wp_unfold.
Qed.

Lemma wp_skip Φ v π E:
  (|={E}⧗=> Φ v) -∗ WPe{π} SkipE (Val v) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?". iModIntro. iSplit; first by eauto 8 using lang.SkipES.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame. iApply wp_value. iApply "HΦ".
Qed.

Lemma wp_concat π E Φ vs:
  (|={E}⧗=> Φ (mjoin vs)) -∗ WPe{π} Concat (Val <$> vs) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  rewrite expr_wp_unfold.
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?".
  iModIntro. iSplit; first by eauto 8 using ConcatS.
  iIntros (? e2 σ2 efs Hst ?). inv_expr_step.
  iApply (physical_step_wand with "HΦ"). iIntros "HΦ".
  iSplit => //. iFrame. iApply wp_value.
  iApply "HΦ".
Qed.

Lemma wps_concat_bind_ind vs π E Φ es:
  foldr (λ e f, (λ vl, WPe{π} e @ E {{ λ v, f (vl ++ [v]) }}))
        (λ vl, WPe{π} (Concat (Val <$> (vs ++ vl))) @ E {{ Φ }}) es [] -∗
  WPe{π} Concat ((Val <$> vs) ++ es) @ E {{ Φ }}.
Proof.
  rewrite -{2}(app_nil_r vs).
  move: {2 3}[] => vl2.
  elim: es vs vl2 => /=.
  - iIntros (vs vl2) "He". by rewrite !app_nil_r.
  - iIntros (e el IH vs vl2) "Hf".
    rewrite !expr_wp_unfold. unfold expr_wp_def.
    have -> : (to_rtexpr π (Concat ((Val <$> vs ++ vl2) ++ e :: el)))%E = (fill [ExprCtx (ConcatCtx (vs ++ vl2) (to_rtexpr π <$> el)) π] (to_rtexpr π e)). {
        by rewrite /= fmap_app fmap_cons -!list_fmap_compose.
    }
    iApply wp_bind. iApply (wp_wand with "Hf").
    iIntros (v) "Hf" => /=.
    have -> : Expr π (RTConcat (((RTVal <$> vs ++ vl2)) ++ of_val v :: (to_rtexpr π <$> el)))
             = to_rtexpr π $ Concat ((Val <$> vs ++ (vl2 ++ [v])) ++ el).
    { by rewrite /= !fmap_app /= (cons_middle (of_val v)) !app_assoc -!list_fmap_compose. }
    iPoseProof (IH with "Hf") as "IH". by rewrite expr_wp_unfold.
Qed.

Lemma wp_concat_bind π E Φ es:
  foldr (λ e f, (λ vl, WPe{π} e @ E {{ λ v, f (vl ++ [v]) }}))
        (λ vl, WPe{π} (Concat (Val <$> vl)) @ E {{ Φ }}) es [] -∗
  WPe{π} Concat es @ E {{ Φ }}.
Proof. by iApply (wps_concat_bind_ind []). Qed.

Lemma wp_struct_init' `{!LayoutAlg} π E Φ sls sl fs:
  use_struct_layout_alg sls = Some sl →
  foldr (λ '(n, ly) f, (λ vl,
     WPe{π} (default (Val (replicate (ly_size ly) MPoison)) (n' ← n; (list_to_map fs : gmap _ _) !! n'))
        @ E {{ λ v, f (vl ++ [v]) }}))
    (λ vl, |={E}⧗=> Φ (mjoin vl)) sl.(sl_members) [] -∗
  WPe{π} StructInit sls fs @ E {{ Φ }}.
Proof.
  intros Halg. rewrite /StructInit /use_struct_layout_alg' Halg/=.
  iIntros "He".
  iApply wp_concat_bind.
  move: {2 4}[] => vs.
  iInduction (sl_members sl) as [|[o?]?] "IH" forall (vs) => /=.
  { iApply wp_concat. done. }
  iApply (wpe_wand with "He"). iIntros (v') "Hfold". by iApply "IH".
Qed.

(* This lemma is much more useful as it also includes the layout algorithm handling and abstracts from padding *)
Lemma wp_struct_init `{!LayoutAlg} π E (Φ : val → iProp Σ) (sls : struct_layout_spec) (sl : struct_layout) (fs : list (string * expr)):
  use_struct_layout_alg sls = Some sl →
  foldr (λ '(n, st) f, (λ vl : list val,
     ∀ ly, ⌜syn_type_has_layout st ly⌝ -∗
     WPe{π} (default (Val (replicate (ly_size ly) MPoison)) ((list_to_map fs : gmap _ _) !! n)) @ E {{ λ v, f (vl ++ [v]) }}))
    (λ vl : list val, |={E}⧗=> Φ (mjoin (pad_struct sl.(sl_members) vl (λ ly, (replicate (ly_size ly) MPoison))))) sls.(sls_fields) [] -∗
  WPe{π} StructInit sls fs @ E {{ Φ }}.
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
    iApply (wpe_wand with "HT").
    iIntros (v0) "HT". iPoseProof ("IH" $! (vs ++ [v0]) (previous_mems ++ [(Some s, ly)]) with "[] [] [HT]") as "HT".
    { done. }
    { rewrite /field_names. rewrite omap_app !length_app/=. rewrite Heq//. }
    { rewrite -app_assoc. simpl. done. }
    simpl.
    rewrite pad_struct_snoc_Some; done.
  - simpl. rewrite expr_wp_unfold. iApply wp_value.
    iPoseProof ("IH" $! (vs) (previous_mems ++ [(None, ly)]) field_specs with "[] [] [HT]") as "HT".
    { done. }
    { rewrite /field_names omap_app !length_app/=. rewrite Nat.add_0_r. done. }
    { simpl. rewrite -app_assoc. done. }
    simpl. rewrite pad_struct_snoc_None; done.
Qed.

(* A slightly more usable version defined via a fixpoint *)
Fixpoint struct_init_components `{!LayoutAlg} π E (fields : list (var_name * syn_type)) (fs : list (string * expr)) (Φ : list val → iProp Σ) : iProp Σ :=
  match fields with
  | [] => Φ []
  | (n, st) :: fields' =>
      ∀ ly, ⌜syn_type_has_layout st ly⌝ -∗
        WPe{π} (default (Val (replicate (ly_size ly) MPoison)) ((list_to_map fs : gmap _ _) !! n)) @ E {{ λ v, struct_init_components π E fields' fs (λ vs, Φ (v :: vs)) }}
  end.
Instance struct_init_components_proper `{!LayoutAlg} π E fields fs :
  Proper (((=) ==> (≡)) ==> (≡)) (struct_init_components π E fields fs).
Proof.
  intros a b Heq.
  induction fields as [ | [ n st] fields IH] in a, b, Heq|-*; simpl.
  { by iApply Heq. }
  do 3 f_equiv.
  rewrite !expr_wp_unfold.
  apply wp_proper. intros ?. apply IH.
  intros ? ? ->. apply Heq. done.
Qed.
Lemma wp_struct_init2 `{!LayoutAlg} π E (Φ : val → iProp Σ) (sls : struct_layout_spec) (sl : struct_layout) (fs : list (string * expr)) :
  use_struct_layout_alg sls = Some sl →
  struct_init_components π E sls.(sls_fields) fs (λ vl : list val, |={E}⧗=> Φ (mjoin (M:=list)(pad_struct sl.(sl_members) vl (λ ly, (replicate (ly_size ly) MPoison))))) -∗
  WPe{π} StructInit sls fs @ E {{ Φ }}.
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
    struct_init_components π E fields fs (λ vl : list val, Φ (vi ++ vl)) -∗
    foldr (λ '(n, st) (f : list val → iPropI Σ) (vl : list val), ∀ ly : layout, ⌜syn_type_has_layout st ly⌝ -∗ WPe{π} default (Val $ replicate (ly_size ly) ☠%V) (list_to_map (M:=gmap _ _) fs !! n) @ E {{ λ v, f (vl ++ [v]) }}) (λ vl : list val, Φ vl) fields vi)%I as "Ha".
  {
    iIntros (vi Ψ) "Ha". clear Hfields.
    iInduction fields as [ | [n st] fields] "IH" forall (vi); simpl.
    { rewrite app_nil_r. done. }
    iIntros (ly) "%Hst". iPoseProof ("Ha" $! ly with "[//]") as "Ha".
    iApply (wpe_wand with "Ha").
    iIntros (v) "Hinit".
    iApply "IH".
    iClear "IH".
    iStopProof.
    rewrite struct_init_components_proper; first eauto.
    intros ?? ->. by rewrite -app_assoc. }
  by iApply "Ha".
Qed.

Lemma encode_OVEnum_unfold_init el variant tag ly payload :
  enum_variant_lookup el.(el_variants) variant = Some ly →
  length (encode_op_val payload) = ly_size ly →
  encode_op_val (OVEnum el variant tag payload) =
    mjoin [i2v tag el.(el_tag_it);
           replicate (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it))) MPoison;
           encode_op_val payload;
           replicate (el.(el_size) - el.(el_data_offset) - ly_size ly) MPoison].
Proof.
  intros Hly Hpayload_len.
  destruct ly as [ly_sz ly_align].
  change (ly_size {| ly_size := ly_sz; ly_align_log := ly_align |}) with ly_sz in *.
  pose proof (el_tag_before_data el) as Htag_before.
  pose proof (enum_variant_lookup_in_bounds el variant {| ly_size := ly_sz; ly_align_log := ly_align |} Hly) as Hdata_bound.
  change (ly_size {| ly_size := ly_sz; ly_align_log := ly_align |}) with ly_sz in *.
  simpl.
  rewrite /overwrite_val /mjoin /= !app_nil_r.
  rewrite !(i2v_length tag el.(el_tag_it)) /it_layout /ly_size in Htag_before *.
  rewrite (take_app_ge (i2v tag el.(el_tag_it))
    (drop (bytes_per_int el.(el_tag_it)) (replicate el.(el_size) MPoison))
    el.(el_data_offset)).
  2: { rewrite i2v_length. lia. }
  rewrite i2v_length.
  rewrite take_drop_replicate; last lia.
  rewrite (drop_app_ge (i2v tag el.(el_tag_it))
    (drop (bytes_per_int el.(el_tag_it)) (replicate el.(el_size) MPoison))
    (el.(el_data_offset) + length (encode_op_val payload))).
  2: { rewrite i2v_length. lia. }
  rewrite i2v_length.
  rewrite drop_drop drop_replicate Hpayload_len.
  replace (el_size el - (bytes_per_int (el_tag_it el) +
    (el_data_offset el + ly_sz - bytes_per_int (el_tag_it el)))) with
    (el_size el - el_data_offset el - ly_sz) by lia.
  rewrite -!app_assoc.
  f_equiv. f_equiv. f_equiv. f_equiv. lia.
Qed.

Lemma wp_enum_init `{!LayoutAlg} π E Φ (els : enum_layout_spec) el variant rsty e tag st :
  use_enum_layout_alg els = Some el →
  (list_to_map els.(els_tag_int) : gmap _ _) !! variant = Some tag →
  (list_to_map els.(els_variants) : gmap _ _) !! variant = Some st →
  WPe{π} e @ E {{ λ v,
    |={E}=>
    ∃ payload, ⌜∀ hst, decode_op_val v (use_op_alg' st) hst = Some payload⌝ ∗
    (|={E}⧗=> (
      Φ (i2v tag els.(els_tag_it) ++ replicate (el.(el_data_offset) - ly_size (it_layout els.(els_tag_it))) MPoison ++ v ++ replicate (el.(el_size) - el.(el_data_offset) - length v) MPoison))) }} -∗
  WPe{π} EnumInit els variant rsty e @ E {{ Φ }}.
Proof.
  Local Arguments encode_op_val : simpl never.
  iIntros (Halg Htag Hst) "HT".
  pose proof Halg as Huse_alg.
  apply use_enum_layout_alg_inv in Halg as (variant_lys & Halg & Hf).
  pose proof (enum_layout_alg_has_variants _ _ _ _ _ Halg) as Hel.
  destruct Hel as (Hel_tag_it & ->).
  subst.
  rewrite /EnumInit.
  rewrite /use_enum_layout_alg' Huse_alg /=.
  apply elem_of_list_to_map_2 in Hst.
  apply list_elem_of_lookup_1 in Hst as (i & Hst).
  opose proof* Forall2_lookup_l as Ha; [apply Hf | apply Hst | ].
  destruct Ha as ([??] & Hvariant & [<- Hst_el]).
  erewrite enum_variant_lookup_is_Some; first last.
  { by eapply list_elem_of_lookup_2. }
  simpl.
  rewrite Htag /=.
  simpl.
  iApply wp_concat_bind. simpl.
  iEval (rewrite expr_wp_unfold).
  iApply wp_value.
  iEval (rewrite expr_wp_unfold).
  iApply wp_value.
  iApply (wpe_wand with "HT").
  iIntros (v) "HP".
  iDestruct "HP" as ">(%payload & %Hv & HP)".
  rewrite expr_wp_unfold.
  iApply wp_value.

  opose proof* (decode_op_val_has_layout v) as Hvlen.
  { apply (Hv inhabitant). }
  rewrite Hvlen.
  apply syn_type_has_layout_op_alg in Hst_el as (ot & Hot & <-).
  move: Hv Hvlen. rewrite /use_op_alg' Hot/=.
  intros Hv Hvlen.
  iApply (wp_concat _ _ _ [i2v tag els.(els_tag_it);
                            replicate (el.(el_data_offset) - ly_size (it_layout els.(els_tag_it))) MPoison;
                            v;
                            replicate (el.(el_size) - el.(el_data_offset) - ly_size (ot_layout ot)) MPoison]).
  simpl. rewrite !app_nil_r -Hel_tag_it.
  iApply (physical_step_wand with "HP").
  eauto.
Qed.

Lemma wp_alloc π E Φ (v_size v_align : val) (n_size n_align : nat) :
  val_to_Z v_size USize = Some (Z.of_nat n_size) →
  val_to_Z v_align USize = Some (Z.of_nat n_align) →
  n_size > 0 →
  (|={E}⧗=> ∀ l v,
    l ↦ (replicate n_size MPoison) -∗
    freeable l n_size 1 HeapAlloc -∗
    ⌜l `has_layout_loc` Layout n_size n_align⌝ -∗
    ⌜val_of_loc l = Some v⌝ -∗
    Φ v) -∗
  WPe{π} (Alloc (Val v_size) (Val v_align)) @ E {{ Φ }}.
Proof.
  iIntros (Hsz Hal Hnz) "Hwp".
  rewrite expr_wp_unfold.
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
  iFrame "Hctx Hfctx". iApply wp_value. by iApply "Hpost".
Qed.

Lemma to_rtexpr_vals π (vs : list val) :
  to_rtexpr π <$> (Val <$> vs) = RTVal <$> vs.
Proof. by rewrite -list_fmap_compose. Qed.

Lemma wps_call_bind_ind vs π E Q Ψ vf el o ret_ot destination normal unwind:
  foldr (λ e f, (λ vl, WPe{π} e @ E {{ λ v, f (vl ++ [v]) }}))
        (λ vl, WPs{π} Call (Val vf) (Val <$> (vs ++ vl)) o ret_ot destination normal unwind
          @ E {{ Q, Ψ }}) el [] -∗
  WPs{π} (Call (Val vf) ((Val <$> vs) ++ el) o ret_ot destination normal unwind)
    @ E {{ Q, Ψ }}.
Proof.
  rewrite -{2}(app_nil_r vs).
  move: {2 3}[] => vl2.
  elim: el vs vl2 => /=.
  - iIntros (vs vl2) "He". by rewrite !app_nil_r.
  - iIntros (e el IH vs vl2) "Hf".
    rewrite stmt_wp_unfold. iIntros (Φ rf HQ) "HΨ".
    have ->: (to_rtstmt π rf (Call (Val vf) ((Val <$> vs ++ vl2) ++ e :: el)
        o ret_ot destination normal unwind)%E =
      fill [StmtCtx (CallRCtx vf (vs ++ vl2) (to_rtexpr π <$> el)
        o ret_ot destination normal unwind) π rf] (to_rtexpr π e)).
    { by rewrite /to_rtstmt /= fmap_app fmap_cons -!list_fmap_compose. }
    iApply wp_bind.
    rewrite expr_wp_unfold.
    iApply (wp_wand with "Hf").
    iIntros (v) "Hf" => /=.
    have -> : Stmt π rf (RTCall (RTVal vf) (((RTVal <$> vs ++ vl2)) ++ of_val v :: (to_rtexpr π <$> el))
        o ret_ot destination normal unwind) =
      to_rtstmt π rf (Call vf ((Val <$> vs ++ (vl2 ++ [v])) ++ el)
        o ret_ot destination normal unwind).
    { rewrite /to_rtstmt /= !fmap_app /= !to_rtexpr_vals.
      by rewrite (cons_middle (of_val v)) !app_assoc. }
    iPoseProof (IH with "Hf") as "IH".
    iEval (rewrite stmt_wp_unfold) in "IH".
    by iApply ("IH" $! Φ rf with "[] HΨ").
Qed.

Lemma wps_call_bind π E Q Ψ el ef o ret_ot destination normal unwind:
  WPe{π} ef @ E {{ λ vf, foldr (λ e f, (λ vl, WPe{π} e @ E {{ λ v, f (vl ++ [v]) }}))
        (λ vl, WPs{π} Call (Val vf) (Val <$> vl) o ret_ot destination normal unwind
          @ E {{ Q, Ψ }}) el [] }} -∗
  WPs{π} (Call ef el o ret_ot destination normal unwind) @ E {{ Q, Ψ }}.
Proof.
  iIntros "HWP".
  rewrite stmt_wp_unfold. iIntros (Φ rf HQ) "HΨ".
  have -> : to_rtstmt π rf (Call ef el o ret_ot destination normal unwind) =
    fill [StmtCtx (CallLCtx (to_rtexpr π <$> el) o ret_ot destination normal unwind) π rf]
      (to_rtexpr π ef) by [].
  iApply wp_bind.
  rewrite expr_wp_unfold.
  iApply (wp_wand with "HWP"). iIntros (vf) "HWP".
  iPoseProof (wps_call_bind_ind [] with "HWP") as "Ha".
  iEval (rewrite stmt_wp_unfold) in "Ha".
  by iApply ("Ha" $! Φ rf with "[] HΨ").
Qed.

Lemma wps_call π i (sta : list syn_type) vf vl f fn Q Ψ o ret_ot destination normal unwind:
  val_to_loc vf = Some f →
  Forall2 has_layout_val vl (f_args fn).*2 →
  Forall2 syn_type_has_layout sta fn.(f_args).*2 →
  fntbl_entry f fn -∗
  current_frame π i -∗
  (|={⊤}⧗=> ∀ lsa,
    (* ownership of arguments *)
    ⌜Forall2 has_layout_loc lsa (f_args fn).*2⌝ -∗
    ([∗ list] l; v ∈ lsa; vl, l↦v) -∗
    (* locals *)
    ([∗ list] xl; synty ∈ zip ((f_args fn).*1) lsa; sta, xl.1 is_live{(π, (S i)), synty} xl.2) -∗
    (* new stack frame *)
    current_frame π (S i) -∗
    allocated_locals (π, S i) (fn.(f_args).*1) -∗
    (* pick a postcondition *)
    ∃ Ψ',
      WPs{π} Goto fn.(f_init) {{ fn.(f_code), Ψ' }} ∗
      (* using the postcondition, recover the local variables *)
      (∀ v, Ψ' v -∗
        ∃ locals,
        current_frame π (S i) ∗
        allocated_locals (π, S i) locals ∗
        (* ownership of remaining locals *)
        ([∗ list] x ∈ locals,
          ∃ ly l st, ⌜syn_type_has_layout st ly⌝ ∗ x is_live{(π, S i), st} l ∗ l ↦|ly|) ∗
        (|={⊤}⧗=> current_frame π i -∗
          WPs{π} AssignSE o ret_ot destination (Val v) normal {{ Q, Ψ }}))
    ) -∗
    WPs{π} (Call (Val vf) (Val <$> vl) o ret_ot destination normal unwind) {{ Q, Ψ }}.
Proof.
  move => Hf Hly Hsta. move: (Hly) => /Forall2_length. rewrite length_fmap => Hlen_vs.
  iIntros "Hf Hframe HWP".
  rewrite stmt_wp_unfold. iIntros (Φ caller HQ) "Hret".
  iApply wp_lift_stmt_step.
  iIntros (σ1) "((%&Hhctx&Hbctx)&Hfctx & Htctx)".
  iDestruct (fntbl_entry_lookup with "Hfctx Hf") as %[a [? Hfn]]; subst. iModIntro.
  iSplit; first by eauto 10 using CallFailS.
  iIntros (??[??]? Hstep _). inv_stmt_step; last first. {
    (* Alloc failure case. *)
    iApply physical_step_intro. iNext.
    iSplit; first done. rewrite /state_ctx. iFrame. iSplit; first done.
    iApply wp_alloc_failed.
  }
  rename select (Forall2 has_layout_val vl _) into Hlyv.
  (* alloc blocks for args *)
  iMod (heap_alloc_new_blocks_upd with "[$Hhctx $Hbctx]") as "[Hctx Hla]" => //.
  rewrite big_sepL2_sep. iDestruct "Hla" as "[Hla Hfree_a]".
  (* push new frame *)
  iMod (thread_push_frame_empty with "Htctx Hframe") as "(Hlocals & Hframe & Htctx)"; [done.. | ].
  (* allocate vars for args *)
  iMod (thread_frame_allocate_vars _ _ _ _ _ _ lsa with "Htctx Hframe [Hfree_a] Hlocals") as "(Hframe & Hlocals & Hxs & Htcxtx)".
  { done. }
  { apply Forall_forall. intros. apply not_elem_of_nil. }
  { apply f_args_nodup. }
  { rewrite lookup_insert_eq//. }
  { unfold thread_get_frame, thread_push_frame. simpl. done. }
  { by eapply alloc_new_blocks_start_in_usize. }
  { done. }
  { rewrite insert_insert decide_True; last done.
    unfold thread_update_frame, thread_push_frame. simpl. done. }
  { done. }
  { iPoseProof (big_sepL2_to_zip with "Hfree_a") as "Ha".
    iApply big_sepL2_from_zip. { rewrite length_fmap. lia. }
    iApply (big_sepL2_elim_r vl).
    iApply big_sepL2_from_zip. { rewrite length_zip length_fmap. lia. }
    iPoseProof (big_sepL_extend_r (f_args fn).*2 with "Ha") as "Ha".
    { rewrite length_zip length_fmap. lia. }
    iPoseProof (big_sepL2_to_zip with "Ha") as "Ha".
    rewrite zip_assoc_l. rewrite (zip_flip vl _) zip_fmap_r zip_assoc_r !big_sepL_fmap.
    iApply (big_sepL_impl with "Ha").
    iModIntro. iIntros (? [[] ?] Hlook). simpl.
    apply lookup_zip_Some in Hlook as (Hlook1 & Hlook3).
    apply lookup_zip_Some in Hlook1 as (Hlook1 & Hlook2).
    opose proof (Forall2_lookup_lr _ _ _ _ _ _ Hlyv _ _) as Ha; [done.. | ].
    rewrite /use_layout_alg' Ha/=. eauto. }

  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplit => //.

  iEval (rewrite right_id) in "Hlocals".
  iDestruct ("HWP" $! lsa with "[//] Hla Hxs Hframe Hlocals") as (Ψ') "(HQinit & HΨ')".
  iFrame.
  have -> : CallFrame π caller o ret_ot destination normal unwind
      (to_rtstmt π fn (Goto fn.(f_init))) =
    fill [CallFrameCtx π caller o ret_ot destination normal unwind]
      (to_rtstmt π fn (Goto fn.(f_init))) by done.
  iApply wp_bind.
  rewrite stmt_wp_eq. iApply "HQinit" => //.

  (** prove Return *)
  iIntros (v) "Hv". iDestruct ("HΨ'" with "Hv") as "(%rem_locals & Hframe & Hlocals & Hxs & Hs)".
  iApply wp_lift_stmt_step => //.
  iIntros (σ3) "((% & Hctx) & ? & Htctx)".

  specialize (Forall2_length _ _ _ Hsta) as Hlen_sta.
  rewrite length_fmap in Hlen_sta.


  rewrite big_sepL_exists. iDestruct "Hxs" as "(%lys & Hxs)".
  iPoseProof (big_sepL2_length with "Hxs") as "%Hlen1".
  iPoseProof (big_sepL2_exists_r with "Hxs") as "(%ls & %Hls & Hxs)".
  iPoseProof (big_sepL2_exists_r with "Hxs") as "(%sts & %Hsts & Hxs)".
  rewrite length_zip Hls Nat.min_idempotent in Hsts.
  iPoseProof (big_sepL2_sep with "Hxs") as "(Hsts & Hxs)".
  iPoseProof (big_sepL2_sep with "Hxs") as "(Hxs & Hls)".
  iPoseProof (big_sepL2_elim_l with "Hsts") as "Hsts".
  iPoseProof (big_sepL2_elim_l with "Hls") as "Hls".

  iAssert ([∗ list] st; ly ∈ sts; lys, ⌜syn_type_has_layout st ly⌝)%I with "[Hsts]" as "Hsts".
  { rewrite zip_assoc_l big_sepL_fmap.
    iApply big_sepL2_from_zip. { lia. }
    iApply big_sepL2_elim_l.
    rewrite zip_assoc_r.
    rewrite (zip_flip lys ls) zip_fmap_l.
    rewrite zip_assoc_l (zip_flip lys sts) zip_fmap_r.
    rewrite !big_sepL_fmap.
    iApply big_sepL2_from_zip; first last.
    { iApply (big_sepL_impl with "Hsts").
      iModIntro. iIntros (? [? []] ?); simpl. done. }
    rewrite length_zip. lia. }
  iPoseProof (big_sepL2_Forall2 with "Hsts") as "%Hsts'".
  iClear "Hsts".

  iAssert ([∗ list] l ∈ zip ls lys, l.1 ↦|l.2|)%I with "[Hls]" as "Hxs2".
  { rewrite (zip_flip lys ls) zip_fmap_l big_sepL_fmap.
    iApply big_sepL2_elim_r. iApply big_sepL2_from_zip; first last.
    { iApply (big_sepL_impl with "Hls").
      iModIntro. iIntros (? ([] & ?) ?); simpl; eauto. }
    rewrite !length_zip. lia. }

  iAssert ([∗ list] x;lsynty ∈ rem_locals; zip ls sts, x is_live{ (π, S i), lsynty.2} lsynty.1)%I with "[Hxs]" as "Hxs1".
  { iPoseProof (big_sepL2_to_zip with "Hxs") as "Hxs1".
    rewrite (zip_flip lys ls) zip_fmap_l zip_fmap_r.
    rewrite (zip_assoc_l ls lys sts).
    rewrite (zip_flip lys sts) ?zip_fmap_l ?zip_fmap_r.
    rewrite (zip_assoc_r ls sts lys) zip_fmap_r.
    rewrite (zip_assoc_r rem_locals _ lys).
    iApply big_sepL2_from_zip. { rewrite length_zip. lia. }
    iApply big_sepL2_elim_r.
    iApply big_sepL2_from_zip; first last.
    { rewrite !big_sepL_fmap. iApply (big_sepL_impl with "Hxs1").
      iModIntro. iIntros (? ([? []] & []) ?). simpl. eauto. }
      rewrite !length_zip. lia. }

  (* these are all the remaining stack-allocatd variables *)
  iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as "(%ts' & %cf & % & % & %Hlocals & %)".
  apply call_frame_has_locals_nodup in Hlocals.
  iPoseProof (state_lookup_vars with "Htctx Hframe Hxs1 Hlocals") as "(% & % & % & % & %Hperm)".
  { done. }
  { lia. }
  unfold thread_get_frame in *. simplify_eq.

  (* remove locals *)
  iMod (thread_frame_deallocate_vars _ _ _ _ _ rem_locals _ _ _ sts ls with "Htctx Hframe Hlocals Hxs1") as "(Hframe & Hlocals & Hfree_a & Htctx)"; [done | done | done | done | | | ].
  { lia. }
  { lia. }

  (* deallocate args *)
  iMod (heap_free_blocks_upd (zip ls lys) with "[Hxs2 Hfree_a] [$Hctx //]") as (σ2 Hfree) "Hctx".
  { rewrite !big_sepL_sep. iFrame.
    iPoseProof (big_sepL2_to_zip  with "Hfree_a") as "Ha".
    iApply (big_sepL2_elim_r sts).
    iApply big_sepL2_from_zip. { rewrite length_zip. lia. }
    iPoseProof (big_sepL_extend_r lys with "Ha") as "Ha".
    { rewrite length_zip. lia. }
    iPoseProof (big_sepL2_to_zip with "Ha") as "Ha".
    rewrite zip_assoc_l. rewrite (zip_flip sts _) zip_fmap_r zip_assoc_r !big_sepL_fmap.
    iApply (big_sepL_impl with "Ha").
    iModIntro. iIntros (? [[] ?] Hlook). simpl.
    apply lookup_zip_Some in Hlook as (Hlook1 & Hlook3).
    apply lookup_zip_Some in Hlook1 as (Hlook1 & Hlook2).
    opose proof (Forall2_lookup_lr _ _ _ _ _ _ Hsts' _ _) as Ha; [done.. | ].
    rewrite /use_layout_alg' Ha/=. eauto. }
  eapply free_blocks_perm in Hfree; last done; first last.
  { symmetry. done. }

  (* pop frame *)
  iMod (thread_pop_frame_empty with "Htctx Hframe Hlocals") as "(Hframe & Htctx)".
  { rewrite lookup_insert_eq. done. }
  { rewrite insert_insert decide_True; last done.
    unfold thread_pop_frame, thread_update_frame; simpl. done. }
  { by rewrite list_difference_diag. }
  iModIntro.
  iSplit; first by eauto 10 using ReturnS.
  iIntros (os ts3 σ2' ? Hst ?). inv_stmt_step.
  unfold state_get_thread, thread_get_frame in *. simplify_eq.

  iApply (physical_step_wand with "Hs"). iIntros "Hs".
  iSplitR => //.
  have ->: (σ2 = hs) by apply: free_blocks_inj.
  iFrame. iApply wp_value.
  iApply wp_lift_pure_det_base_step_no_fork'.
  - done.
  - by eauto using CallFrameReturnStep.
  - move => ?????. inversion 1; simplify_eq => //.
    match goal with H : to_rtexpr _ ?e = CallFrame _ _ _ _ _ _ _ _ |- _ =>
      destruct e; discriminate H
    end.
  - iNext. iIntros "_".
    iDestruct ("Hs" with "Hframe") as "Hs".
    iEval (rewrite stmt_wp_unfold) in "Hs".
    by iApply ("Hs" $! Φ caller with "[] Hret").
Qed.
End expr_lifting.

(*** Lifting of statements *)
Section stmt_lifting.
Context `{!refinedcG Σ}.

Lemma wps_return π Q Ψ v:
  Ψ v -∗ WPs{π} (Return (Val v)) {{ Q , Ψ }}.
Proof. rewrite stmt_wp_unfold. iIntros "Hb" (? rf ?) "HΨ". by iApply "HΨ". Qed.

Lemma wps_goto π Q Ψ b s:
  Q !! b = Some s →
  (|={⊤}⧗=> WPs{π} s {{ Q, Ψ }}) -∗ WPs{π} Goto b {{ Q , Ψ }}.
Proof.
  iIntros (Hs) "HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iApply wp_lift_stmt_step. iIntros (?) "Hσ !>".
  iSplit; first by eauto 10 using GotoS.
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplit; first done. iFrame. by iApply "HWP".
Qed.

Lemma wps_free π Q Ψ s l v_size v_align vl (n_size n_align : nat) :
  val_to_Z v_size USize = Some (Z.of_nat n_size) →
  val_to_Z v_align USize = Some (Z.of_nat n_align) →
  (∀ st, decode_op_val vl PtrOp st = Some (OVPtr l)) →
  n_size > 0 →
  l ↦|Layout n_size n_align| -∗
  freeable l n_size 1 HeapAlloc -∗
  (|={⊤}⧗=> WPs{π} s {{ Q, Ψ }}) -∗
  WPs{π} (Free (Val v_size) (Val v_align) vl s) {{ Q, Ψ }}.
Proof.
  iIntros (?? Hl ?) "Hl Hf HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iPoseProof (heap_pointsto_layout_has_layout with "Hl") as "%".
  iApply wp_lift_stmt_step. iIntros (σ) "(Hhctx&Hfctx)".
  iMod (heap_free_block_upd with "Hl Hf Hhctx") as (σ') "(%Hf & Hhctx)".
  iModIntro. iSplit; first by eauto 10 using FreeS, val_to_of_loc.
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplitR; first done.
  rename select (decode_op_val _ _ _ = Some _) into Hdec.
  rewrite Hl in Hdec.
  simplify_eq/=.
  erewrite (free_block_inj σ.(st_heap) _ (Layout n_size n_align) HeapAlloc hs' σ'); [ | done.. ].
  iFrame. by iApply "HWP".
Qed.

Lemma wps_skip π Q Ψ s:
  (|={⊤}⧗=> WPs{π} s {{ Q, Ψ }}) -∗ WPs{π} SkipS s {{ Q , Ψ }}.
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

Lemma wps_exprs π Q Ψ s v:
  (|={⊤}⧗=> WPs{π} s {{ Q, Ψ }}) -∗ WPs{π} ExprS (Val v) s {{ Q , Ψ }}.
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

Lemma wps_assign π Q Ψ vl ot vr s l o:
  let E := if o is ScOrd then ∅ else ⊤ in
  o = ScOrd ∨ o = Na1Ord →
  (∀ st, decode_op_val vl PtrOp st = Some (OVPtr l)) →
  op_type_wf ot →
  (|={⊤,E}=> ⌜∀ st, ∃ ov, decode_op_val vr ot st = Some ov⌝ ∗ l↦|ot_layout ot| ∗
    |={E}⧗=> (∀ st ov, ⌜decode_op_val vr ot st = Some ov⌝ -∗
      l↦(encode_op_val ov) ={E,⊤}=∗ WPs{π} s {{Q, Ψ}})) -∗
  WPs{π} (Assign o ot (Val vl) (Val vr) s) {{ Q , Ψ }}.
Proof.
  iIntros (E Ho Hvl Hwf) "HWP". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step_fupd. iIntros ([[h1 ub] fn]) "((%&Hhctx&Hfctx)&?) /=". iMod "HWP" as (Hdecvr) "[Hl HWP]".
  have Hly : vr `has_layout_val` ot_layout ot.
  { destruct (Hdecvr inhabitant) as (ov & Hdec). by eapply decode_op_val_has_layout. }
  iApply (fupd_mask_weaken ∅); first set_solver. iIntros "HE".
  iDestruct "Hl" as (v' Hlyv' ?) "Hl".
  iDestruct (heap_pointsto_is_alloc with "Hl") as %Haid.
  unfold E. case: Ho => ->.
  - iModIntro.
    iDestruct (heap_pointsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl") as %? => //.
    iSplit; first by destruct (Hdecvr {| hs_heap := h1; hs_allocs := ub |}) as (? & ?); eauto 12 using AssignS.
    iIntros (? e2 σ2 efs Hstep ?). inv_stmt_step. unfold end_val.
    rename select (decode_op_val vl PtrOp _ = Some _) into Hdec.
    rewrite Hvl in Hdec. simplify_eq/=.
    iApply (physical_step_wand with "HWP"). iIntros "HWP".
    have Hlen : length v' = length (encode_op_val ov).
    { rewrite Hlyv'. symmetry. eapply encode_op_val_length; first done.
      by eapply decode_op_val_has_type. }
    iMod (heap_write with "Hhctx Hl") as "[$ Hl]" => //.
    iMod ("HWP" with "[] Hl") as "HWP"; first done.
    iModIntro => /=. iSplit; first done. iFrame. iSplit; first done. by iApply "HWP".
  - destruct (Hdecvr {| hs_heap := h1; hs_allocs := ub |}) as (ov & Hdecvr1).
    have Hlen : length v' = length (encode_op_val ov).
    { rewrite Hlyv'. symmetry. eapply encode_op_val_length; first done.
      by eapply decode_op_val_has_type. }
    iMod (heap_write_na _ _ _ (encode_op_val ov) with "Hhctx Hl") as (?) "[Hhctx Hc]" => //.
    iModIntro. iSplit; first by eauto 12 using AssignS.
    iIntros (? e2 σ2 efs Hst ?). inv_stmt_step.
    rename select (decode_op_val vl PtrOp _ = Some _) into Hdec.
    rewrite Hvl in Hdec. simplify_eq/=.
    have ? : (v' = v'0) by [apply: heap_at_inj_val]; subst v'0.
    iFrame => /=. iMod "HE" as "_".
    iApply (physical_step_wand with "HWP"). iIntros "HWP".
    iApply fupd_mask_intro_subseteq; first set_solver.
    iSplit; first done.
    iFrame. iSplit; first done.

    (* second step *)
    iApply wp_lift_stmt_step.
    iIntros ([[h2 ub2] fn2]) "((%&Hhctx&Hfctx)&?)" => /=.
    iMod ("Hc" with "Hhctx") as (?) "[Hhctx Hmt]".
    iModIntro. iSplit; first by destruct (Hdecvr {| hs_heap := h2; hs_allocs := ub2 |}) as (? & ?); eauto 12 using AssignS. unfold end_stmt.
    iIntros (? e2 σ2 efs Hst ?). inv_stmt_step.
    rename select (decode_op_val vl PtrOp _ = Some _) into Hdec.
    rewrite Hvl in Hdec. simplify_eq/=.

    rename select (decode_op_val vr ot _ = Some _) into Hdecvr2.
    have Hstable := decode_op_val_stable vr ot
      {| hs_heap := h1; hs_allocs := ub |} {| hs_heap := h2; hs_allocs := ub2 |}.
    rewrite Hdecvr1 Hdecvr2 in Hstable. simplify_eq/=.

    have ? : (v' = v'0) by [apply: heap_lookup_loc_inj_val]; subst v'0.
    iApply physical_step_fupd.
    iApply physical_step_intro. iNext.
    iFrame => /=. iMod ("HWP" with "[] Hmt") as "HWP"; first done.
    iModIntro. iSplit; first done. iSplit; first done. by iApply "HWP".
Qed.

Lemma wps_switch π Q Ψ v n ss def m it:
  val_to_Z v it = Some n →
  (∀ i, m !! n = Some i → is_Some (ss !! i)) →
  (|={⊤}⧗=> WPs{π} default def (i ← m !! n; ss !! i) {{ Q, Ψ }}) -∗
  WPs{π} (Switch it (Val v) m ss def) {{ Q , Ψ }}.
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
Lemma wps_switch' π Q Ψ v n ss def m it:
  val_to_Z v it = Some n →
  map_Forall (λ _ i, is_Some (ss !! i)) m →
  (|={⊤}⧗=> [∧ list] i↦s∈ss, ⌜m !! n = Some i⌝ -∗ WPs{π} s {{ Q, Ψ }}) ∧
  (|={⊤}⧗=> ⌜m !! n = None⌝ -∗ WPs{π} def {{ Q, Ψ }}) -∗
  WPs{π} (Switch it (Val v) m ss def) {{ Q , Ψ }}.
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

Lemma wps_if π Q Ψ it v s1 s2 n:
  val_to_Z v it = Some n →
  (|={⊤}⧗=> if bool_decide (n ≠ 0) then WPs{π} s1 {{ Q, Ψ }} else WPs{π} s2 {{ Q, Ψ }}) -∗
  WPs{π} (if{IntOp it}: (Val v) then s1 else s2) {{ Q , Ψ }}.
Proof.
  iIntros (Hn) "Hs". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step. iIntros (?) "Hσ". iModIntro.
  iSplit. { iPureIntro. repeat eexists. apply IfSS. rewrite /= Hn //. }
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "Hs"). iIntros "Hs".
  iSplit; first done.
  iFrame "Hσ". case_bool_decide; by iApply "Hs".
Qed.

Lemma wps_if_bool π Q Ψ v s1 s2 b :
  val_to_bool v = Some b →
  (|={⊤}⧗=> if b then WPs{π} s1 {{ Q, Ψ }} else WPs{π} s2 {{ Q, Ψ }}) -∗
  WPs{π} (if{BoolOp}: (Val v) then s1 else s2) {{ Q , Ψ }}.
Proof.
  iIntros (Hb) "Hs". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step. iIntros (?) "Hσ". iModIntro.
  iSplit. { iPureIntro. repeat eexists. apply IfSS. rewrite /= Hb //. }
  iIntros (???? Hstep ?). inv_stmt_step.
  iApply (physical_step_wand with "Hs"). iIntros "Hs".
  iSplit; first done.
  iFrame "Hσ". destruct b; by iApply "Hs".
Qed.

Lemma wps_assert_bool π Q Ψ v s b:
  val_to_bool v = Some b →
  b = true →
  (|={⊤}⧗=> WPs{π} s {{ Q, Ψ }}) -∗
  WPs{π} (assert{BoolOp}: Val v; s) {{ Q , Ψ }}.
Proof.
  iIntros (Hv Hb) "Hs". rewrite /notation.Assert.
  iApply wps_if_bool => //. by rewrite Hb.
Qed.

Lemma wps_assert_int π Q Ψ it v s n:
  val_to_Z v it = Some n →
  n ≠ 0 →
  (|={⊤}⧗=> WPs{π} s {{ Q, Ψ }}) -∗
  WPs{π} (assert{IntOp it}: Val v; s) {{ Q , Ψ }}.
Proof.
  iIntros (Hv Hn) "Hs". rewrite /notation.Assert.
  iApply wps_if => //. by case_decide.
Qed.

Definition wps_block (P : iProp Σ) (b : label) (π : thread_id) (Q : gmap label stmt) (Ψ : val → iProp Σ) : iProp Σ :=
  (□ (P -∗ WPs{π} Goto b {{ Q, Ψ }})).

(* NOTE: does not offer a physical step since we have to use it up to strip the later from the Löb induction *)
Lemma wps_block_rec Ps π Q Ψ :
  ([∗ map] b ↦ P ∈ Ps, ∃ s, ⌜Q !! b = Some s⌝ ∗ □(([∗ map] b ↦ P ∈ Ps, wps_block P b π Q Ψ) -∗ P -∗ £ (num_laters_per_step 1) -∗ WPs{π} s {{ Q, Ψ }})) -∗
  [∗ map] b ↦ P ∈ Ps, wps_block P b π Q Ψ.
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

Lemma wps_local_live π st x s ly S i Q Ψ :
  syn_type_has_layout st ly →
  x ∉ S →
  current_frame π i -∗
  allocated_locals (π, i) S -∗
  (|={⊤}⧗=> ∀ l,
    x is_live{ (π, i), st} l -∗
    current_frame π i -∗
    allocated_locals (π, i) (x :: S) -∗
    l ↦ (replicate (ly_size ly) MPoison) -∗
    ⌜l `has_layout_loc` ly⌝ -∗
    WPs{π} s {{ Q, Ψ }}) -∗
  WPs{π} (local_live{st} x; s) {{ Q, Ψ }}.
Proof.
  iIntros (Hst Hnel) "Hframe Hlocals HWP".
  rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step.
  iIntros ([h1 f1 t1]) "((%&Hhctx&Hactx)&? & Htctx) /=".
  iModIntro.
  iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as "(%ts & %cf & %Hthread & %Hframe & %Hlocals & %)".
  assert (cf.(cf_locals) !! x = None).
  { destruct (cf_locals cf !! x) eqn:Heq; last done.
    exfalso. apply Hnel. rewrite -Hlocals.
    rewrite list_elem_of_fmap. eexists.
    split; last apply elem_of_map_to_list; last done.
    done. }
  iSplit; first by eauto 10 using LocalLiveFailS.
  iIntros (??[??]? Hstep _). inv_stmt_step; last first. {
    (* Alloc failure case. *)
    iApply physical_step_intro.
    iModIntro. iSplit; first done. rewrite /state_ctx. iFrame. iSplit; first done.
    iApply wp_alloc_failed.
  }
  unfold state_get_thread, thread_get_frame in *.
  simpl in *. simplify_eq.
  iMod (heap_alloc_new_block_upd with "[$Hhctx $Hactx]") as "(Hctx & Hlv & Hlf)" => //.
  rewrite length_replicate.
  unfold state_ctx; simpl.
  iApply physical_step_fupd.
  iApply (physical_step_wand with "HWP"); iIntros "HWP". iSplitR; first done.
  iMod (thread_frame_allocate_var with "Htctx Hframe Hlf Hlocals") as "(Hframe & Hlocals & Hlive & $)"; [ | done | done | done | | done | done | ].
  { unfold use_layout_alg'. rewrite Hst. apply Hst. }
  { by eapply alloc_new_block_start_in_usize. }
  iFrame.
  rewrite /use_layout_alg' Hst/=.
  iApply ("HWP" with "Hlive Hframe Hlocals Hlv [] [//] [$]").
  iPureIntro.
  rename select (l `has_layout_loc` _) into Hst'.
  move: Hst'. rewrite /use_layout_alg' Hst//.
Qed.

Lemma wps_local_dead_nop x s π i S Q Ψ :
  x ∉ S →
  current_frame π i -∗
  allocated_locals (π, i) S -∗
  (|={⊤}⧗=> current_frame π i -∗ allocated_locals (π, i) S -∗ WPs{π} s {{ Q, Ψ }}) -∗
  WPs{π} (LocalDead x s) {{ Q, Ψ }}.
Proof.
  iIntros (Hnel) "Hframe Hlocals HWP".
  rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step.
  iIntros ([h1 f1 t1]) "((%&Hhctx&Hactx)&? & Htctx) /=".
  iModIntro.
  iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as "(%ts & %cf & %Hthread & %Hframe & %Hlocals & %)".
  assert (cf.(cf_locals) !! x = None).
  { destruct (cf_locals cf !! x) eqn:Heq; last done.
    exfalso. apply Hnel. rewrite -Hlocals.
    rewrite list_elem_of_fmap. eexists.
    split; last apply elem_of_map_to_list; last done.
    done. }
  iSplit; first by eauto 10 using LocalDeadNopS.
  iIntros (??[??]? Hstep _). inv_stmt_step.
  all: unfold state_get_thread, thread_get_frame, call_frame_has_locals in *; simpl in *; simplify_eq.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  iSplitR; first done. iFrame. iSplitR; first done.
  iApply ("HWP" with "Hframe Hlocals [//]"); done.
Qed.

Lemma wps_local_dead π i x synty ly l S s Q Ψ :
  syn_type_has_layout synty ly →
  current_frame π i -∗
  allocated_locals (π, i) S -∗
  x is_live{(π, i), synty} l -∗
  l ↦|ly| -∗
  (|={⊤}⧗=> current_frame π i -∗ allocated_locals (π, i) (list_difference S [ x ]) -∗ WPs{π} s {{ Q, Ψ }}) -∗
  WPs{π} (LocalDead x s) {{ Q, Ψ }}.
Proof.
  iIntros (Hly) "Hframe Hlocals Hx Hl HWP".
  rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step.
  iIntros ([h1 f1 t1]) "(Hhctx&? & Htctx) /=".
  iPoseProof (live_local_is_allocated with "Htctx Hlocals Hx") as "%Hel".
  iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as "(%ts & %cf & %Hthread & %Hframe & %Hlocals & %)".
  iPoseProof (state_lookup_var with "Htctx Hframe Hx") as "(% & % & % & %Hly' & % & % & % & %)".
  simplify_eq.
  specialize (syn_type_has_layout_inj _ _ _ Hly Hly') as <-.
  unfold call_frame_has_locals in Hlocals.

  iMod (thread_frame_deallocate_var with "Htctx Hframe Hlocals Hx") as "(Hframe & Hlocals & Hf & Htctx)"; [done.. | ].
  iPoseProof (heap_pointsto_layout_has_layout with "Hl") as "%".
  iMod (heap_free_block_upd with "Hl [Hf] Hhctx") as (σ') "(%Hf & Hhctx)".
  { rewrite /use_layout_alg' Hly'. done. }

  iModIntro. iSplitR; first by eauto 10 using LocalDeadDeallocS, val_to_of_loc.
  iIntros (???? Hstep ?). inv_stmt_step.
  all: unfold state_get_thread, thread_get_frame in *; simpl in *; simplify_eq.
  iApply physical_step_fupd.
  iApply (physical_step_wand with "HWP"). iIntros "HWP".
  erewrite (free_block_inj h1 _ ly StackAlloc hs' σ'); [ | done..].
  simpl. iFrame.
  iSplitR; first done.
  iApply ("HWP" with "Hframe Hlocals [//]"); done.
Qed.
End stmt_lifting.

Section lemmas.
Context `{!refinedcG Σ}.
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

Local Lemma pad_struct_focus_big_sepL2' {A} (els1 els2 : list A) fields (make_uninit : layout → A) (Φ : nat → A → A → iProp Σ) (i0 : nat) :
  length els2 = length (named_fields fields) →
  length els1 = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x; y ∈ pad_struct fields els1 make_uninit; pad_struct fields els2 make_uninit, Φ (i + i0)%nat x y) -∗
  (* get just the named fields *)
  ([∗ list] i ↦ x; y ∈ els1; els2,
    ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! (i)%nat = Some (n, ly)⌝ ∗ Φ (j + i0)%nat x y) ∗
  (* and separately the ownership of the unnamed fields *)
  ([∗ list] i ↦ x ∈ pad_struct fields (replicate (length els1) None) Some,
    from_option (λ ly, Φ (i + i0)%nat (make_uninit ly) (make_uninit ly)) True x).
Proof.
  iIntros (Hlen1 Hlen2 Hnd) "Ha".
  iInduction fields as [ | [n ly] fields] "IH" forall (els1 els2 Hlen1 Hlen2 i0 Hnd); simpl.
  { simpl in Hlen1, Hlen2. destruct els1, els2; try done. simpl. iSplitR; first done. done. }
  destruct n as [ n | ]; simpl.
  - simpl in Hlen1, Hlen2.
    destruct els1 as [ | el1 els1]; first done; simpl in *.
    destruct els2 as [ | el2 els2]; first done; simpl in *.
    iDestruct "Ha" as "(Ha & Hb)".
    iPoseProof ("IH" $! els1 els2 with "[] [] [] [Hb]") as "(Hb & Hpad)".
    { iPureIntro. lia. }
    { iPureIntro. lia. }
    { inversion Hnd. done. }
    { setoid_rewrite <-Nat.add_succ_r. iApply "Hb". }
    iSplitL "Ha Hb".
    { (* show the split *)
      iSplitL "Ha".
      { iExists 0%nat, _, _. iSplitR; first done. iSplitR; done. }
      iApply (big_sepL2_impl with "Hb"). iModIntro. iIntros (k x1 x2 Hlook1 Hlook2).
      iIntros "(%j & % & % & %Hlook1' & %Hlook2' & Ha)".
      iExists (S j), _, _. simpl. rewrite Nat.add_succ_r. do 2 iR. done. }
    iR. iApply (big_sepL_wand with "Hpad").
    iApply big_sepL_intro. iModIntro. iIntros (???).
    destruct x; simpl; try rewrite Nat.add_succ_r; eauto.
  - simpl in *.
    iDestruct "Ha" as "(Ha & Hb)".
    iPoseProof ("IH" with "[] [] [//] [Hb]") as "(Hb & Hpad)".
    { rewrite -Hlen1//. }
    { rewrite -Hlen2//. }
    { setoid_rewrite <-Nat.add_succ_r. done. }
    iSplitL "Hb".
    { iApply (big_sepL2_wand with "Hb"). iApply big_sepL2_intro.
      { lia. }
      iModIntro. iIntros (k x1 x2 Hlook1 Hlook2) "(%j & % & % & ? & ? & ?)".
      iExists (S j). rewrite Nat.add_succ_r. eauto with iFrame. }
    iFrame. iApply (big_sepL_wand with "Hpad").
    iApply big_sepL_intro. iModIntro. iIntros (???).
    destruct x; simpl; try rewrite Nat.add_succ_r; eauto.
Qed.
Local Lemma pad_struct_unfocus_big_sepL2' {A} (els1 els2 : list A) fields (make_uninit : layout → A) (Φ : nat → A → A → iProp Σ) (i0 : nat) :
  length els1 = length (named_fields fields) →
  length els2 = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x; y ∈ els1; els2,
    ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! (i)%nat = Some (n, ly)⌝ ∗ Φ (j + i0)%nat x y) -∗
  ([∗ list] i ↦ x ∈ pad_struct fields (replicate (length els1) None) Some,
    from_option (λ ly, Φ (i + i0)%nat (make_uninit ly) (make_uninit ly)) True x) -∗
  ([∗ list] i ↦ x; y ∈ pad_struct fields els1 make_uninit; pad_struct fields els2 make_uninit, Φ (i + i0)%nat x y).
Proof.
  iIntros (Hlen1 Hlen2 Hnd) "Ha Hpad".
  iInduction fields as [ | [n ly] fields] "IH" forall (els1 els2 Hlen1 Hlen2 i0 Hnd); simpl.
  { eauto. }
  destruct n as [ n | ]; simpl.
  - simpl in Hlen1, Hlen2.
    destruct els1 as [ | el1 els1]; first done; simpl in *.
    destruct els2 as [ | el2 els2]; first done; simpl in *.
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
    iApply ("IH" $! els1 els2 with "[] [] [] [Hb]").
    { iPureIntro. lia. }
    { iPureIntro. lia. }
    { done. }
    { iApply (big_sepL2_impl with "Hb"). iModIntro. iIntros (k x1 x2 Hlook1 Hlook2).
      iIntros "(%j' & % & % & %Hlook1' & %Hlook2' & Ha)".
      destruct j'.
      { (* contrasdictory due to no-dup *)
        simpl in Hlook1'. injection Hlook1' as <- <-.
        apply list_elem_of_lookup_2 in Hlook2'.
        contradict Hnel. eapply elem_of_named_fields_field_names. done. }
      iExists j'. rewrite Nat.add_succ_r.
      eauto with iFrame. }
    { iApply (big_sepL_wand with "Hpad").
      iApply big_sepL_intro. iModIntro. iIntros (???).
      destruct x; simpl; try rewrite Nat.add_succ_r; eauto. }
  - iDestruct "Hpad" as "(Hpad1 & Hpad)". iFrame.
    iEval (setoid_rewrite <-Nat.add_succ_r).
    iApply ("IH" $! els1 els2 with "[] [] [] [Ha]"); first done.
    { done. }
    { done. }
    { iApply (big_sepL2_wand with "Ha"). iApply big_sepL2_intro. { lia. }
      iModIntro. iIntros (k x1 x2 Hlook1 Hlook2) "(%j & %ly' & %n & %Hlook1' & %Hlook2' & Ha)".
      destruct j as [ | j]; first done.
      iExists j. simpl. rewrite -Nat.add_succ_r. eauto with iFrame. }
    { iApply (big_sepL_wand with "Hpad").
      iApply big_sepL_intro. iModIntro. iIntros (???).
      destruct x; simpl; try rewrite Nat.add_succ_r; eauto. }
Qed.

Lemma pad_struct_focus_big_sepL2 {A} (els1 els2 : list A) fields (make_uninit : layout → A) (Φ : nat → A → A → iProp Σ) :
  length els1 = length (named_fields fields) →
  length els2 = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x; y ∈ pad_struct fields els1 make_uninit; pad_struct fields els2 make_uninit, Φ i x y) -∗
  ([∗ list] i ↦ x; y ∈ els1; els2,
    ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! i = Some (n, ly)⌝ ∗ Φ j x y) ∗
  ([∗ list] i ↦ x ∈ pad_struct fields (replicate (length els1) None) Some,
    from_option (λ ly, Φ i (make_uninit ly) (make_uninit ly)) True x).
Proof.
  iIntros (???) "Ha".
  iPoseProof (pad_struct_focus_big_sepL2' els1 els2 fields make_uninit Φ 0 with "[Ha]") as "Ha".
  { done. }
  { done. }
  { done. }
  { setoid_rewrite Nat.add_0_r. done. }
  iDestruct "Ha" as "(Ha & Hb)".
  iEval (setoid_rewrite Nat.add_0_r) in "Ha". iFrame.
  iApply (big_sepL_wand with "Hb").
  iApply big_sepL_intro. iModIntro. iIntros (???).
  destruct x; simpl; try rewrite Nat.add_0_r; eauto.
Qed.
Lemma pad_struct_unfocus_big_sepL2 {A} (els1 els2 : list A) fields (make_uninit : layout → A) (Φ : nat → A → A → iProp Σ) :
  length els1 = length (named_fields fields) →
  length els2 = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x; y ∈ els1; els2, ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! i = Some (n, ly)⌝ ∗ Φ j x y) -∗
  ([∗ list] i ↦ x ∈ pad_struct fields (replicate (length els1) None) Some,
    from_option (λ ly, Φ i (make_uninit ly) (make_uninit ly)) True x) -∗
  ([∗ list] i ↦ x; y ∈ pad_struct fields els1 make_uninit; pad_struct fields els2 make_uninit, Φ i x y).
Proof.
  iIntros (???) "Ha Hpad".
  iPoseProof (pad_struct_unfocus_big_sepL2' els1 els2 fields make_uninit Φ 0 with "[Ha] [Hpad]") as "Ha".
  { done. }
  { done. }
  { done. }
  { setoid_rewrite Nat.add_0_r. done. }
  { iApply (big_sepL_wand with "Hpad").
    iApply big_sepL_intro. iModIntro. iIntros (???).
    destruct x; simpl; try rewrite Nat.add_0_r; eauto. }
  setoid_rewrite Nat.add_0_r. done.
Qed.
Lemma pad_struct_focus_big_sepL2_no_uninit {A} (els1 els2 : list A) fields (make_uninit : layout → A) (Φ : nat → A → A → iProp Σ) :
  length els1 = length (named_fields fields) →
  length els2 = length (named_fields fields) →
  NoDup (field_names fields) →
  ([∗ list] i ↦ x; y ∈ pad_struct fields els1 make_uninit; pad_struct fields els2 make_uninit, Φ i x y) -∗
  ([∗ list] i ↦ x; y ∈ els1; els2, ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! i = Some (n, ly)⌝ ∗ Φ j x y) ∗
  (∀ els1' els2',
    ⌜length els1' = length els1⌝ -∗
    ⌜length els2' = length els2⌝ -∗
    ([∗ list] i ↦ x; y ∈ els1'; els2', ∃ j ly n, ⌜fields !! j = Some (Some n, ly)⌝ ∗ ⌜named_fields fields !! i = Some (n, ly)⌝ ∗ Φ j x y) -∗
    ([∗ list] i ↦ x; y ∈ pad_struct fields els1' make_uninit; pad_struct fields els2' make_uninit, Φ i x y)).
Proof.
  iIntros (???) "Ha".
  iPoseProof (pad_struct_focus_big_sepL2 els1 els2 fields make_uninit Φ with "Ha") as "($ & Hpad)".
  { done. }
  { done. }
  { done. }
  iIntros (els1' els2' Hlen1 Hlen2) "Ha".
  rewrite -Hlen1.
  iApply (pad_struct_unfocus_big_sepL2 els1' els2' fields make_uninit Φ with "Ha Hpad").
  { rewrite Hlen1. done. }
  { rewrite Hlen2. done. }
  done.
Qed.
End lemmas.
