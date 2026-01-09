(** From the CPP'26 paper "Building Blocks for Step-Indexed Program Logics",
    by Thomas Somers, Jonas Kastberg Hinrichsen, Lennard Gäher, and Robbert Krebbers. 
    
    Upstream: https://gitlab.mpi-sws.org/tlsomers/iris-contrib/-/tree/8a482f0a60295cb016c5a39b2ec5f602b74e3514
*)
From iris.prelude Require Import options.
From iris.base_logic.lib Require Import iprop own later_credits.
From iris.proofmode Require Import base environments classes classes_make
                                   modality_instances ltac_tactics.
From caesium.physical_step Require Export tr_view.
Import uPred.


(** The ghost state for time-receipts  *)
Class trGpreS (Σ : gFunctors) := TrGpreS {
  #[local] trGpreS_inG :: inG Σ tr_viewUR;
}.

Class trGS (Σ : gFunctors) := TrGS {
  #[local] trGS_inG :: inG Σ tr_viewUR;
  trGS_name : gname;
}.
Global Hint Mode trGS - : typeclass_instances.

Definition trΣ := #[GFunctor tr_viewUR].
Global Instance subG_trΣ {Σ} : subG trΣ Σ → trGpreS Σ.
Proof. solve_inG. Qed.


(** The user-facing non-persistent time-receipts, denoting ownership of [n] non-persistent time-receipts.
    Each non-persistent time-receipt can be used to generate a later credit per step, and can be composed
    more modularly than `steps_lb`.
*)
Local Definition tr_def `{!trGS Σ} (n : nat) : iProp Σ := own trGS_name (◯⧗V n).
Local Definition tr_aux : seal ( @tr_def). Proof. by eexists. Qed.
Definition tr := tr_aux.(unseal).
Local Definition tr_unseal :
  @tr = @tr_def := tr_aux.(seal_eq).
Global Arguments tr {Σ _} n.

Notation "'⧗'  n" := (tr n) (at level 1).

(** The user-facing persistent time receipt resource, denoting ownership of [n] persistent time-receipts.
    Persistent time-receipts are similar to the prior `steps_lb` from heaplang. *)
Local Definition tr_persistent_def `{!trGS Σ} (n : nat) : iProp Σ := own trGS_name (◯⧖V n).
Local Definition tr_persistent_aux : seal ( @tr_persistent_def). Proof. by eexists. Qed.
Definition tr_persistent := tr_persistent_aux.(unseal).
Local Definition tr_persistent_unseal :
  @tr_persistent = @tr_persistent_def := tr_persistent_aux.(seal_eq).
Global Arguments tr_persistent {Σ _} n.

Notation "'⧖'  n" := (tr_persistent n) (at level 1).

(** The internal authoritative part of the time-receipt state,
  tracking how many time-receipts are remaining for the given step.
  This should not be used directly. *)
Local Definition tr_supply_base_def `{!trGS Σ} (m : nat) : iProp Σ := own trGS_name (●⧗V m).
Local Definition tr_supply_base_aux : seal ( @tr_supply_base_def). Proof. by eexists. Qed.
Definition tr_supply_base := tr_supply_base_aux.(unseal).
Local Definition tr_supply_base_unseal :
  @tr_supply_base = @tr_supply_base_def := tr_supply_base_aux.(seal_eq).
Global Arguments tr_supply_base {Σ _} m.

(** The derived 2-argument supply presented in the paper. This supply consists of
  a base supply, an additive time receipt, and a persistent time receipt.
  The first argument is half that in the paper, as multiplication by 2 is easier
  than division in Rocq.  *)
Local Definition tr_supply_def `{!trGS Σ} (n₁ n₂ : nat) : iProp Σ :=
  tr_supply_base (n₁ + n₁) ∗ ⧗ n₂ ∗ ⧖ n₁.
Local Definition tr_supply_aux : seal ( @tr_supply_def). Proof. by eexists. Qed.
Definition tr_supply := tr_supply_aux.(unseal).
Local Definition tr_supply_unseal :
  @tr_supply = @tr_supply_def := tr_supply_aux.(seal_eq).
Global Arguments tr_supply {Σ _} n₁ n₂.


Local Ltac unseal := rewrite
  ?tr_unseal /tr_def
  ?tr_persistent_unseal /tr_persistent_def
  ?tr_supply_base_unseal /tr_supply_base_def.

Local Ltac unseal_supply := rewrite
  ?tr_supply_unseal /tr_supply_def.

Section time_receipt_theory.
  Context `{trGS Σ}.

  Global Instance tr_timeless n : Timeless (⧗ n).
  Proof. unseal. apply _. Qed.
  Global Instance tr_0_persistent : Persistent (⧗ 0).
  Proof. unseal. apply _. Qed.
  Global Instance tr_persistent_timeless n : Timeless (⧖ n).
  Proof. unseal. apply _. Qed.
  Global Instance tr_persistent_persistent n : Persistent (⧖ n).
  Proof. unseal. apply _. Qed.

  (** Later credit rules *)
  Lemma tr_split n₁ n₂ :
    ⧗ (n₁ + n₂) ⊣⊢ ⧗ n₁ ∗ ⧗ n₂.
  Proof.
    unseal. rewrite -own_op //=.
  Qed.

  Lemma tr_persistent_split n₁ n₂ :
    ⧖ (n₁ `max` n₂) ⊣⊢ ⧖ n₁ ∗ ⧖ n₂.
  Proof.
    unseal. rewrite -own_op //=.
  Qed.

  Lemma tr_zero : ⊢ |==> ⧗ 0.
  Proof.
    unseal. iApply own_unit.
  Qed.

  Lemma tr_persistent_zero : ⊢ |==> ⧖ 0.
  Proof.
    unseal. iApply own_unit.
  Qed.

  Lemma tr_weaken {n'} n :
    n ≤ n' → ⧗ n' -∗ ⧗ n.
  Proof.
    intros [k ->]%Nat.le_sum. rewrite tr_split. iIntros "[$ _]".
  Qed.

  Lemma tr_persistent_weaken {n'} n :
    n ≤ n' → ⧖ n' -∗ ⧖ n.
  Proof.
    intros. unseal.
    iApply own_mono. by apply tr_view_tr_persistent_mono.
  Qed.

  Lemma tr_succ n :
    ⧗ (S n) ⊣⊢ ⧗ 1 ∗ ⧗ n.
  Proof. rewrite -tr_split //=. Qed.

  Lemma tr_persistent_incr n₁ n₂ :
    ⧖ n₁ -∗ ⧗ n₂ ==∗ ⧖ (n₁ + n₂).
  Proof.
    iIntros "Htr Hptr". unseal.
    iMod (own_update_2 with "Htr Hptr") as "$"; [|done].
    apply tr_view_tr_persistent_increase.
  Qed.

  Lemma tr_persist n :
    ⧗ n ==∗ ⧗ n ∗ ⧖ n.
  Proof.
    iIntros "H⧗". unseal.
    iMod(own_update with "H⧗") as "[$ $]"; [|done].
    apply tr_view_tr_persist.
  Qed.

  Lemma tr_supply_base_both_bound n₁ n₂ m :
    tr_supply_base m -∗ ⧗ n₁ -∗ ⧖ n₂ -∗ ⌜n₁ + n₂ ≤ m⌝.
  Proof.
    unseal.
    iIntros "H1 H2 H3". iCombine "H1 H2 H3" gives %[_ Hop].
    by apply tr_view_both_valid in Hop.
  Qed.

  Lemma tr_supply_base_tr_bound n m :
    tr_supply_base m -∗ ⧗ n -∗ ⌜n ≤ m⌝.
  Proof.
    unseal.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hop.
    apply tr_view_tr_valid in Hop.
    iPureIntro; lia.
  Qed.

  Lemma tr_supply_base_tr_persistent_bound n m :
    tr_supply_base m -∗ ⧖ n -∗ ⌜n ≤ m⌝.
  Proof.
    unseal.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hop.
    by apply tr_view_tr_persistent_valid in Hop.
  Qed.

  Lemma tr_supply_base_increase n₂ m n₁ :
    tr_supply_base m -∗ ⧖ n₁ ==∗ tr_supply_base (m + n₂ + n₂) ∗ ⧖ (n₁ + n₂) ∗ ⧗ n₂.
  Proof.
    unseal. iIntros "H1 H2".
    iMod (own_update_2 with "H1 H2") as "($ & $ & $)"; [apply tr_view_auth_incr|done].
  Qed.

  (** Make sure that the rule for [+] is used before [S], otherwise Coq's
  unification applies the [S] hint too eagerly. See Iris issue #470. *)
  Global Instance from_sep_tr_add n₁ n₂ :
    FromSep (⧗ (n₁ + n₂)) (⧗ n₁) (⧗ n₂) | 0.
  Proof.
    by rewrite /FromSep tr_split.
  Qed.
  Global Instance from_sep_tr_S n :
    FromSep (⧗ (S n)) (⧗ 1) (⧗ n) | 1.
  Proof.
    by rewrite /FromSep (tr_succ n).
  Qed.

  Global Instance combine_sep_tr_add n₁ n₂ :
    CombineSepAs (⧗ n₁) (⧗ n₂) (⧗ (n₁ + n₂)) | 1.
  Proof.
    by rewrite /CombineSepAs tr_split.
  Qed.

  Global Instance combine_sep_tr_persistent_max n₁ n₂ :
    CombineSepAs (⧖ n₁) (⧖ n₂) (⧖ (n₁ `max` n₂)) | 1.
  Proof.
    by rewrite /CombineSepAs tr_persistent_split.
  Qed.

  Global Instance combine_sep_tr_S_l n :
    CombineSepAs (⧗ n) (⧗ 1) (⧗ (S n)) | 0.
  Proof.
    by rewrite /CombineSepAs comm (tr_succ n).
  Qed.

  Global Instance into_sep_tr_add n₁ n₂ :
    IntoSep (⧗ (n₁ + n₂)) (⧗ n₁) (⧗ n₂) | 0.
  Proof.
    by rewrite /IntoSep tr_split.
  Qed.
  Global Instance into_sep_tr_S n :
    IntoSep (⧗ (S n)) (⧗ 1) (⧗ n) | 1.
  Proof.
    by rewrite /IntoSep (tr_succ n).
  Qed.

  (** Derived lemmas for the tr_supply with 3 parameters. *)

  Lemma tr_supply_valid n₁ n₂ m :
    tr_supply n₁ n₂ -∗ ⧖ m -∗ ⌜n₂ + m ≤ n₁ + n₁⌝.
  Proof.
    unseal_supply.
    iIntros "(?&?&Htrp1) Htrp2".
    iCombine "Htrp1 Htrp2" as "?".
    iDestruct (tr_supply_base_both_bound with "[$] [$] [$]") as "%Hle".
    iPureIntro; lia.
  Qed.

  Lemma tr_supply_snapshot n₁ n₂ :
    tr_supply n₁ n₂ -∗ tr_supply n₁ n₂ ∗ ⧖ n₁.
  Proof.
    unseal_supply.
    iIntros "($&$&#?)".
    iFrame "#".
  Qed.

  (* A derived lemma that relates both n₂ to n₂ and n₂ + m to 2*n₁. *)
  Lemma tr_supply_valid_strong n₁ n₂ m :
    tr_supply n₁ n₂ -∗ ⧖ m -∗ ⌜n₂ + m `max` n₁ ≤ n₁ + n₁⌝.
  Proof.
    iIntros "Hsup H⧖".
    iDestruct (tr_supply_snapshot with "[$]") as "[Hsup H⧖']".
    iCombine "H⧖ H⧖'" as "H".
    iApply (tr_supply_valid with "[$] [$]").
  Qed.

  (** The following lemmas are split up to make it easy to apply the correct
     direction in the Iris proof mode. *)
  Lemma tr_supply_tr_1 n₁ n₂ m :
    tr_supply n₁ n₂ -∗ ⧗ m -∗ tr_supply n₁ (n₂ + m).
  Proof.
    unseal_supply.
    iIntros "($&H₁&$) H₂".
    iApply tr_split. iFrame.
  Qed.
  Lemma tr_supply_tr_2 n₁ n₂ m :
    tr_supply n₁ (n₂ + m) -∗ tr_supply n₁ n₂ ∗ ⧗ m.
  Proof. unseal_supply. iIntros "($&[$$]&$)". Qed.

  Lemma tr_supply_incr n₁ n₂ m :
    tr_supply n₁ n₂ ==∗ tr_supply (n₁ + m) (n₂ + m).
  Proof.
    unseal_supply. iIntros "(?&?&?)".
    replace (n₁ + m + (n₁ + m)) with (n₁ + n₁ + m + m) by lia.
    iMod (tr_supply_base_increase m with "[$] [$]") as "($&$&?)".
    iApply tr_split. by iFrame.
  Qed.
End time_receipt_theory.

Local Lemma tr_supply_base_alloc `{!trGpreS Σ} n :
  ⊢ |==> ∃ _ : trGS Σ, tr_supply_base (n + n) ∗ ⧗ n.
Proof.
  unseal.
  iMod (own_alloc (●⧗V (n + n) ⋅ ◯⧗V n)) as (γTR) "[H● H◯]";
    first (by apply tr_view_tr_valid).
  pose (C := TrGS _ _ γTR).
  iModIntro. iExists C. iFrame.
Qed.

Lemma tr_supply_alloc `{!trGpreS Σ} n :
  ⊢ |==> ∃ _ : trGS Σ, tr_supply n n.
Proof.
  unseal_supply.
  iMod (tr_supply_base_alloc n) as  (?) "[$ H]".
  by iApply (tr_persist).
Qed.

