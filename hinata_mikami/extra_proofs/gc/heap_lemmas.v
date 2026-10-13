From caesium Require Import lang notation.
From refinedrust Require Import typing.
From iris.base_logic.lib Require Import ghost_map.
From hinata_mikami.extra_proofs.gc Require Import gc_defs.

Section heap_lemmas.

Context `{RRGS : !refinedrustGS Σ}.

Lemma simplify_goal_big_sepL_app {A}
    (xs1 xs2 : list A)
    (Φ : nat → A → iProp Σ) T :
  ([∗ list] i ↦ x ∈ xs1, Φ i x) ∗
  ([∗ list] i ↦ x ∈ xs2,
      Φ (length xs1 + i)%nat x) ∗ T
  ⊢
  simplify_goal
    ([∗ list] i ↦ x ∈ xs1 ++ xs2, Φ i x) T.
Proof.
  rewrite /simplify_goal.
  rewrite big_sepL_app.
  iIntros "($ & $ & $)".
Qed.

Definition simplify_goal_big_sepL_app_inst :=
  [instance @simplify_goal_big_sepL_app with 10%N].

Global Existing Instance simplify_goal_big_sepL_app_inst.

Lemma prove_with_subtype_big_sepL_acc {A}
    E L step pm
    (xs : list A)
    (Φ : nat → A → iProp Σ)
    (i : nat) (x : A) T :
  (Φ i x -∗
     [∗ list] k ↦ y ∈ xs, Φ k y) -∗
  prove_with_subtype E L step pm
    (Φ i x) T -∗
  prove_with_subtype E L step pm
    ([∗ list] k ↦ y ∈ xs, Φ k y) T.
Proof.
  iIntros "Hclose Hsub".

  rewrite /prove_with_subtype.
  iEval (rewrite /prove_with_subtype) in "Hsub".

  iIntros (F ???) "#CTX #HE HL".

  iMod ("Hsub" with "[//] [//] [//] CTX HE HL")
    as "(%L' & %κs & %R & Hstep & HL & HT)".

  iModIntro.
  iExists L', κs, R.
  iFrame "HL HT".

  iApply (maybe_logical_step_wand with "[Hclose] Hstep").

  destruct pm.
  - iIntros "(Hi & HR)".
    iFrame "HR".
    iApply "Hclose".
    iExact "Hi".

  - iIntros "(Hi & HR)".
    iFrame "HR".

    iIntros "Hdead".
    iMod ("Hi" with "Hdead") as "Hi".
    iModIntro.

    iApply "Hclose".
    iExact "Hi".
Qed.

Lemma NoDup_snoc_local {A}
    (xs : list A) (x : A) :
  NoDup xs ->
  x ∉ xs ->
  NoDup (xs ++ [x]).
Proof.
  intros Hnd.
  revert x.

  induction Hnd as
      [| a xs Ha Hnd IH];
    intros x Hfresh.

  - simpl.
    constructor.
    + set_solver.
    + constructor.

  - simpl.
    constructor.
    + intro Hin.
      apply elem_of_app in Hin.
      destruct Hin as [Hin | Hin].
      * exact (Ha Hin).
      * simpl in Hin.
        apply list_elem_of_singleton in Hin.
        subst x.
        apply Hfresh.
        apply elem_of_cons.
        left.
        reflexivity.

    + apply IH.
      intro Hin.
      apply Hfresh.
      right.
      exact Hin.
Qed.

Lemma freeable_full_ne
    (l1 l2 : loc)
    (n1 n2 : nat)
    (k1 k2 : alloc_kind) :
  freeable l1 n1 1 k1 -∗
  freeable l2 n2 1 k2 -∗
  ⌜l1 ≠ l2⌝.
Proof.
  rewrite !freeable_eq.

  iIntros "H1 H2".

  iDestruct "H1" as
    (id1)
    "(%Hp1 & #Hmeta1 & Halive1)".

  iDestruct "H2" as
    (id2)
    "(%Hp2 & #Hmeta2 & Halive2)".

  rewrite !alloc_alive_eq.

  iDestruct
    (ghost_map_elem_ne with "Halive1 Halive2")
    as %Hid_ne.

  iPureIntro.
  intro Heq.
  subst l2.

  apply Hid_ne.
  congruence.
Qed.

Lemma freeable_nz_full_ne
    (l1 l2 : loc)
    (n : nat)
    (k1 k2 : alloc_kind) :
  (0 < n)%nat ->
  freeable_nz l1 n 1 k1 -∗
  freeable_nz l2 n 1 k2 -∗
  ⌜l1 ≠ l2⌝.
Proof.
  intros Hn.
  iIntros "H1 H2".

  iPoseProof
    (freeable_nz_to_freeable
       l1 n 1 k1 Hn
       with "H1")
    as "H1f".

  iPoseProof
    (freeable_nz_to_freeable
       l2 n 1 k2 Hn
       with "H2")
    as "H2f".

  iApply
    (freeable_full_ne
       with "H1f H2f").
Qed.

Global Instance freeable_full_ne_gives
    (l1 l2 : loc)
    (n1 n2 : nat)
    (k1 k2 : alloc_kind) :
  CombineSepGives
    (freeable l1 n1 1 k1)
    (freeable l2 n2 1 k2)
    ⌜l1 ≠ l2⌝.
Proof.
  rewrite /CombineSepGives.
  iIntros "[H1 H2]".
  iDestruct
    (freeable_full_ne with "H1 H2")
    as %Hne.
  eauto.
Qed.

Definition aligned_nodes
    (vals : list Z)
    (locs nexts : list loc)
    (marks : list bool)
    (Φ :
      nat → Z → loc → loc → bool → iProp Σ)
    : iProp Σ :=
  [∗ list] k ↦ v ∈ vals,
    ∃ (l n : loc) (m : bool),
      ⌜locs !! k = Some l⌝ ∗
      ⌜nexts !! k = Some n⌝ ∗
      ⌜marks !! k = Some m⌝ ∗
      Φ k v l n m.

Definition sweep_nodes_inv
    (cut : nat)
    (vals : list Z)
    (locs nexts : list loc)
    (orig_marks : list bool)
    (Φ :
      nat → Z → loc → loc → bool → iProp Σ)
    : iProp Σ :=
  aligned_nodes
    (keep_marked_suffix cut vals orig_marks)
    (keep_marked_suffix cut locs orig_marks)
    (keep_marked_suffix cut nexts orig_marks)
    (sweep_marks cut orig_marks)
    Φ.

Lemma sweep_nodes_inv_init
    vals locs nexts marks Φ :
  length vals = length marks →
  length locs = length marks →
  length nexts = length marks →
  aligned_nodes vals locs nexts marks Φ -∗
  sweep_nodes_inv
    (length marks)
    vals locs nexts marks Φ.

Proof.
Admitted.

Lemma sweep_nodes_inv_step
    (cut : nat)
    vals locs nexts marks Φ :
  0 < cut →
  cut ≤ length marks →
  length vals = length marks →
  length locs = length marks →
  length nexts = length marks →

  sweep_nodes_inv
    cut vals locs nexts marks Φ
  -∗

  ∃ (v : Z) (l n : loc) (m : bool),

    ⌜vals !! (cut - 1) = Some v⌝ ∗
    ⌜locs !! (cut - 1) = Some l⌝ ∗
    ⌜nexts !! (cut - 1) = Some n⌝ ∗
    ⌜marks !! (cut - 1) = Some m⌝ ∗

    Φ (cut - 1) v l n m ∗

    match m with
    | true =>
        Φ (cut - 1) v l n false -∗
        sweep_nodes_inv
          (cut - 1)
          vals locs nexts marks Φ
    | false =>
        sweep_nodes_inv
          (cut - 1)
          vals locs nexts marks Φ
    end.

Proof.
Admitted.

Lemma sweep_nodes_inv_done
    vals locs nexts marks Φ :
  length vals = length marks →
  length locs = length marks →
  length nexts = length marks →

  sweep_nodes_inv
    0 vals locs nexts marks Φ
  -∗

  aligned_nodes
    (keep_marked vals marks)
    (keep_marked locs marks)
    (keep_marked nexts marks)
    (replicate
      (length (keep_marked locs marks))
      false)
    Φ.

Proof.
Admitted.


Lemma keep_marked_length_same_mask {A B}
    (xs : list A)
    (ys : list B)
    (marks : list bool) :
  length xs = length ys →
  length (keep_marked xs marks) =
  length (keep_marked ys marks).

Proof.
Admitted.


Lemma keep_marked_NoDup {A}
    (xs : list A)
    (marks : list bool) :
  NoDup xs →
  NoDup (keep_marked xs marks).

Proof.
Admitted.



Lemma keep_marked_Forall {A}
    (P : A → Prop)
    (xs : list A)
    (marks : list bool) :
  Forall P xs →
  Forall P (keep_marked xs marks).

Proof.
Admitted.


Lemma marks_closed_keep_marked_next_valid
    (locs nexts : list loc)
    (marks : list bool) :
  length locs = length nexts →
  marks_closed locs nexts marks →
  Forall
    (λ n,
      n = NULL_loc ∨
      n ∈ keep_marked locs marks)
    (keep_marked nexts marks).

Proof.
Admitted.


End heap_lemmas.