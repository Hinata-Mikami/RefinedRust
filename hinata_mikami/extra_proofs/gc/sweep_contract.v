From radium Require Import lang notation.
From refinedrust Require Import typing.
From hinata_mikami.extra_proofs.gc Require Import gc_defs heap_lemmas.

(** Address-based statements remain meaningful when Vec deletion changes indices.
    All occurrences of [marks] below refer to the snapshot BEFORE sweep. *)
Definition reachable_loc (locs nexts : list loc) (l : loc) : Prop :=
  ∃ i, locs !! i = Some l ∧ reachable locs nexts i.

Definition marking_exact (locs nexts : list loc) (marks : list bool) : Prop :=
  ∀ i, marks !! i = Some true ↔ reachable locs nexts i.

Definition keep_unmarked {A} (xs : list A) (marks : list bool) : list A :=
  keep_marked xs (negb <$> marks).

(** These are candidate Drop arguments, not certificates of physical deallocation.
    The implementation scans the initial Vec from right to left. *)
Definition sweep_drop_targets (locs : list loc) (marks : list bool) : list loc :=
  reverse (keep_unmarked locs marks).

Definition sweep_kept_exact (locs : list loc) (marks : list bool)
    (remaining : list loc) : Prop :=
  ∀ i l, locs !! i = Some l →
    (l ∈ remaining ↔ marks !! i = Some true).

Definition sweep_reachable_exact (locs nexts remaining : list loc) : Prop :=
  ∀ l, l ∈ remaining ↔ reachable_loc locs nexts l.

Definition sweep_reachability_preserved
    (locs nexts remaining remaining_nexts : list loc) : Prop :=
  ∀ l, reachable_loc remaining remaining_nexts l ↔ reachable_loc locs nexts l.

Lemma elem_of_keep_unmarked {A} (x : A) xs marks :
  x ∈ keep_unmarked xs marks ↔
  ∃ i, xs !! i = Some x ∧ marks !! i = Some false.
Proof.
  rewrite /keep_unmarked elem_of_keep_marked.
  split.
  - intros (i & Hi & Hm).
    apply list_lookup_fmap_Some in Hm as (m & Hm & Hneg).
    destruct m; simpl in Hneg; try discriminate. eauto.
  - intros (i & Hi & Hm). exists i. split; first done.
    rewrite list_lookup_fmap Hm. done.
Qed.

Lemma sweep_kept_exact_filter locs marks :
  NoDup locs → sweep_kept_exact locs marks (keep_marked locs marks).
Proof.
  intros Hnd i l Hi. rewrite elem_of_keep_marked.
  split.
  - intros (j & Hj & Hmarked).
    have Heq : j = i by (eapply NoDup_lookup; eassumption).
    by subst j.
  - intros Hmarked. eauto.
Qed.

Lemma sweep_reachable_exact_filter locs nexts marks :
  marking_exact locs nexts marks →
  sweep_reachable_exact locs nexts (keep_marked locs marks).
Proof.
  intros Hexact l. rewrite elem_of_keep_marked.
  split.
  - intros (i & Hi & Hprop). exists i. split; first done. by apply Hexact.
  - intros (i & Hi & Hprop). exists i. split; first done. by apply Hexact.
Qed.

Lemma sweep_partition (locs : list loc) marks :
  length locs = length marks →
  ∀ l, l ∈ locs ↔ l ∈ keep_marked locs marks ∨ l ∈ keep_unmarked locs marks.
Proof.
  intros Hlen l. rewrite elem_of_keep_marked elem_of_keep_unmarked.
  split.
  - intros (i & Hi)%list_elem_of_lookup_1.
    have Hbound : (i < length marks)%nat.
    { rewrite -Hlen. eapply lookup_lt_Some. exact Hi. }
    destruct (lookup_lt_is_Some_2 marks i Hbound) as [m Hm].
    destruct m; [left | right]; eauto.
  - intros [(i & Hi & _) | (i & Hi & _)]; eapply list_elem_of_lookup_2; eauto.
Qed.

Lemma sweep_partition_disjoint (locs : list loc) marks :
  NoDup locs →
  ∀ l, l ∈ keep_marked locs marks → l ∉ keep_unmarked locs marks.
Proof.
  intros Hnd l Hlive Hdead.
  apply elem_of_keep_marked in Hlive as (i & Hi & Hmi).
  apply elem_of_keep_unmarked in Hdead as (j & Hj & Hmj).
  have Heq : i = j by (eapply NoDup_lookup; eassumption).
  subst j. congruence.
Qed.

Lemma sweep_drop_targets_exact locs marks l :
  l ∈ sweep_drop_targets locs marks ↔
  ∃ i, locs !! i = Some l ∧ marks !! i = Some false.
Proof. rewrite /sweep_drop_targets elem_of_reverse elem_of_keep_unmarked. done. Qed.

Lemma sweep_drop_targets_nodup locs marks :
  NoDup locs → NoDup (sweep_drop_targets locs marks).
Proof.
  intros Hnd. rewrite /sweep_drop_targets reverse_Permutation.
  apply keep_marked_NoDup. exact Hnd.
Qed.

Lemma sweep_drop_targets_unreachable locs nexts marks l :
  length locs = length marks → NoDup locs →
  marking_exact locs nexts marks →
  (l ∈ sweep_drop_targets locs marks ↔
    l ∈ locs ∧ ¬ reachable_loc locs nexts l).
Proof.
  intros Hlen Hnd Hexact. rewrite sweep_drop_targets_exact.
  split.
  - intros (i & Hi & Hfalse). split.
    + eapply list_elem_of_lookup_2; eauto.
    + intros (j & Hj & Hreach).
      have Heq : i = j by (eapply NoDup_lookup; eassumption).
      subst j. apply Hexact in Hreach. congruence.
  - intros (Hmem & Hnot).
    apply list_elem_of_lookup_1 in Hmem as (i & Hi).
    have Hbound : (i < length marks)%nat.
    { rewrite -Hlen. eapply lookup_lt_Some. exact Hi. }
    destruct (lookup_lt_is_Some_2 marks i Hbound) as [m Hm].
    destruct m; last eauto.
    exfalso. apply Hnot. exists i. split; first done. by apply Hexact.
Qed.

(** Filtering several lists with the same mask keeps their fields aligned. *)
Lemma keep_marked_lookup_pair {A B} (xs : list A) (ys : list B) marks j x y :
  keep_marked xs marks !! j = Some x →
  keep_marked ys marks !! j = Some y →
  ∃ i, xs !! i = Some x ∧ ys !! i = Some y ∧ marks !! i = Some true.
Proof.
  revert ys marks j.
  induction xs as [|a xs IH]; intros [|b ys] [|m marks] j Hx Hy;
    simpl in Hx, Hy; try discriminate.
  destruct m.
  - destruct j as [|j]; simpl in Hx, Hy.
    + exists 0%nat. by simplify_eq.
    + destruct (IH ys marks j Hx Hy) as (i & Hi & Hj & Hm).
      exists (S i). done.
  - destruct (IH ys marks j Hx Hy) as (i & Hi & Hj & Hm).
    exists (S i). done.
Qed.

Lemma keep_marked_lookup_pair_intro {A B}
    (xs : list A) (ys : list B) marks i x y :
  xs !! i = Some x → ys !! i = Some y → marks !! i = Some true →
  ∃ j, keep_marked xs marks !! j = Some x ∧
       keep_marked ys marks !! j = Some y.
Proof.
  revert xs ys marks.
  induction i as [|i IH]; intros [|a xs] [|b ys] [|m marks] Hx Hy Hm;
    simpl in Hx, Hy, Hm; try discriminate.
  - simplify_eq. exists 0%nat. done.
  - destruct (IH xs ys marks Hx Hy Hm) as (j & Hjx & Hjy).
    destruct m; [exists (S j) | exists j]; done.
Qed.

Lemma sweep_unprocessed_marks_unchanged cut marks :
  (cut ≤ length marks)%nat →
  take cut (sweep_marks cut marks) = take cut marks.
Proof.
  intros Hcut. rewrite /sweep_marks take_app length_take_le; last done.
  rewrite Nat.sub_diag take_0 app_nil_r take_take Nat.min_id. done.
Qed.

Lemma sweep_reset_all_unmarked (locs : list loc) marks :
  all_unmarked (replicate (length (keep_marked locs marks)) false).
Proof. apply Forall_replicate. done. Qed.

Lemma keep_marked_lookup_origin {A} (xs : list A) marks j x :
  keep_marked xs marks !! j = Some x →
  ∃ i, xs !! i = Some x ∧ marks !! i = Some true.
Proof.
  intros Hlookup. apply elem_of_keep_marked.
  eapply list_elem_of_lookup_2. exact Hlookup.
Qed.

Lemma keep_marked_root (locs : list loc) marks root :
  locs !! 0%nat = Some root → marks !! 0%nat = Some true →
  keep_marked locs marks !! 0%nat = Some root.
Proof.
  destruct locs as [|l locs], marks as [|m marks]; simpl;
    intros Hloc Hmark; try discriminate. by simplify_eq.
Qed.

(** Forward direction: every path from a retained root is retained.  The
    induction transports indices; it never assumes that deletion preserves them. *)
Lemma reachable_filter_forward locs nexts marks :
  NoDup locs → length nexts = length locs → length marks = length locs →
  marks !! 0%nat = Some true → marks_closed locs nexts marks →
  ∀ i, reachable locs nexts i →
    ∃ j l, locs !! i = Some l ∧
      keep_marked locs marks !! j = Some l ∧
      reachable (keep_marked locs marks) (keep_marked nexts marks) j ∧
      marks !! i = Some true.
Proof.
  intros Hnd Hnext_len Hmark_len Hroot Hclosed i Hreach.
  unfold reachable in Hreach |- *.
  induction Hreach as [|i q n Hreach IH Hnext Hnonnull Hloc].
  - have Hbound : (0 < length locs)%nat.
    { rewrite -Hmark_len. eapply lookup_lt_Some. exact Hroot. }
    destruct (lookup_lt_is_Some_2 locs 0 Hbound) as [root Hloc].
    exists 0%nat, root. split; first done.
    split; first by eapply keep_marked_root.
    split; [constructor | done].
  - destruct IH as (j & l & Hli & Hlj & Hreachj & Hmi).
    have Hmq : marks !! q = Some true.
    { eapply Hclosed; eassumption. }
    destruct (keep_marked_lookup_pair_intro locs nexts marks i l n
      Hli Hnext Hmi) as (j' & Hlj' & Hnj').
    have Hndf : NoDup (keep_marked locs marks) by (apply keep_marked_NoDup; done).
    have Heq : j' = j by (eapply NoDup_lookup; eassumption).
    subst j'.
    have Hmem : n ∈ keep_marked locs marks.
    { apply elem_of_keep_marked. eauto. }
    apply list_elem_of_lookup_1 in Hmem as (k & Hnk).
    exists k, n. split; first done. split; first done. split; last done.
    eapply reachable_from_step; eassumption.
Qed.

(** Backward direction: filtering cannot create a new path. *)
Lemma reachable_filter_backward locs nexts marks :
  NoDup locs → length nexts = length locs → length marks = length locs →
  marks !! 0%nat = Some true →
  ∀ j, reachable (keep_marked locs marks) (keep_marked nexts marks) j →
    ∃ i l, locs !! i = Some l ∧
      keep_marked locs marks !! j = Some l ∧ reachable locs nexts i.
Proof.
  intros Hnd Hnext_len Hmark_len Hroot j Hreach.
  unfold reachable in Hreach |- *.
  induction Hreach as [|j q n Hreach IH Hnext Hnonnull Hloc].
  - have Hbound : (0 < length locs)%nat.
    { rewrite -Hmark_len. eapply lookup_lt_Some. exact Hroot. }
    destruct (lookup_lt_is_Some_2 locs 0 Hbound) as [root Hloc].
    exists 0%nat, root. split; first done.
    split; [by eapply keep_marked_root | constructor].
  - destruct IH as (i & l & Hli & Hlj & Hreachi).
    destruct (keep_marked_lookup_pair locs nexts marks j l n Hlj Hnext)
      as (i' & Hli' & Hni' & Hmarked).
    have Heq : i' = i by (eapply NoDup_lookup; eassumption).
    subst i'.
    destruct (keep_marked_lookup_origin locs marks q n Hloc) as (k & Hnk & Hmk).
    exists k, n. split; first done. split; first done.
    eapply reachable_from_step; eassumption.
Qed.

Theorem sweep_preserves_reachability locs nexts marks :
  NoDup locs → length nexts = length locs → length marks = length locs →
  marks !! 0%nat = Some true → marks_closed locs nexts marks →
  sweep_reachability_preserved locs nexts
    (keep_marked locs marks) (keep_marked nexts marks).
Proof.
  intros Hnd Hnext_len Hmark_len Hroot Hclosed l. split.
  - intros (j & Hloc & Hreach).
    destruct (reachable_filter_backward locs nexts marks Hnd Hnext_len
      Hmark_len Hroot j Hreach) as (i & l' & Hi & Hj & Hri).
    simplify_eq. exists i. done.
  - intros (i & Hloc & Hreach).
    destruct (reachable_filter_forward locs nexts marks Hnd Hnext_len
      Hmark_len Hroot Hclosed i Hreach) as (j & l' & Hi & Hj & Hrj & Hmi).
    simplify_eq. exists j. done.
Qed.

(** A single readable summary, in addition to the existing ownership postcondition.
    Exact reachability is conditional: [marks_closed] alone permits over-marking. *)
Definition sweep_post (locs nexts : list loc) (marks : list bool)
    (remaining remaining_nexts : list loc) : Prop :=
  sweep_kept_exact locs marks remaining ∧
  (marking_exact locs nexts marks →
    sweep_reachable_exact locs nexts remaining) ∧
  (marks !! 0%nat = Some true →
    sweep_reachability_preserved locs nexts remaining remaining_nexts).

Theorem sweep_post_filter locs nexts marks :
  NoDup locs → length nexts = length locs → length marks = length locs →
  marks_closed locs nexts marks →
  sweep_post locs nexts marks (keep_marked locs marks) (keep_marked nexts marks).
Proof.
  intros Hnd Hnext_len Hmark_len Hclosed. split.
  - by apply sweep_kept_exact_filter.
  - split.
    + by apply sweep_reachable_exact_filter.
    + intros Hroot. eapply sweep_preserves_reachability; eassumption.
Qed.

(** Contract-level composition with mark; this does not claim to verify collect. *)
Theorem mark_sweep_exact locs nexts marks_before marks_after :
  NoDup locs → all_unmarked marks_before →
  mark_from_rel locs nexts marks_before 0%nat marks_after →
  sweep_reachable_exact locs nexts (keep_marked locs marks_after).
Proof.
  intros Hnd Hunmarked Hmark. apply sweep_reachable_exact_filter.
  unfold marking_exact. intros i. eapply mark_from_rel_exact_root; eassumption.
Qed.

Lemma mark_from_rel_length locs nexts before after start :
  mark_from_rel locs nexts before start after → length after = length before.
Proof.
  intros Hrel. induction Hrel as
    [marks i Hmarked
    |marks i l Hfalse Hnext Hnull
    |marks new i j l Hfalse Hnext Hnonnull Hloc Hrel IH].
  - done.
  - apply length_insert.
  - rewrite IH length_insert. done.
Qed.

Theorem mark_sweep_reachability_preserved locs nexts before after :
  NoDup locs → length nexts = length locs → length before = length locs →
  all_unmarked before → mark_from_rel locs nexts before 0%nat after →
  sweep_reachability_preserved locs nexts
    (keep_marked locs after) (keep_marked nexts after).
Proof.
  intros Hnd Hnext_len Hmark_len Hunmarked Hmark.
  have Hafter_len : length after = length locs.
  { rewrite (mark_from_rel_length _ _ _ _ _ Hmark). done. }
  have Hroot : after !! 0%nat = Some true.
  { eapply mark_from_rel_marks_start. exact Hmark. }
  have Hclosed : marks_closed locs nexts after.
  { eapply mark_from_rel_final_closed_unmarked; eassumption. }
  eapply sweep_preserves_reachability; eassumption.
Qed.

(** Retained records keep their original value and next pointer, despite reindexing. *)
Definition sweep_fields_preserved (vals : list Z) (locs nexts : list loc)
    (marks : list bool) : Prop :=
  ∀ j l v n,
    keep_marked locs marks !! j = Some l →
    keep_marked vals marks !! j = Some v →
    keep_marked nexts marks !! j = Some n →
    ∃ i, locs !! i = Some l ∧ vals !! i = Some v ∧
      nexts !! i = Some n ∧ marks !! i = Some true.

Lemma sweep_fields_preserved_filter vals locs nexts marks :
  NoDup locs → sweep_fields_preserved vals locs nexts marks.
Proof.
  intros Hnd j l v n Hloc Hval Hnext.
  destruct (keep_marked_lookup_pair _ _ _ _ _ _ Hloc Hval)
    as (i & Hli & Hvi & Hmi).
  destruct (keep_marked_lookup_pair _ _ _ _ _ _ Hloc Hnext)
    as (k & Hlk & Hnk & Hmk).
  have Heq : k = i by (eapply NoDup_lookup; eassumption).
  subst k. exists i. done.
Qed.

(** A non-vacuous reset example: sweep does NOT preserve the physical mark bit. *)
Example sweep_resets_mark_example : sweep_marks 0 [true] = [false].
Proof. reflexivity. Qed.
