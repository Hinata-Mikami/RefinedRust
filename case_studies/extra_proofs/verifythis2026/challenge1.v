From refinedrust Require Import typing.

Definition ListSorted := Sorted.
Definition revsorted (l : list Z) :=
  ListSorted _  (Z.ge) l.


Definition count_ge (l : list Z) (k : Z) : nat :=
  length (filter (fun x => k <=? x) l).
(* h is the h-index of l *)
Definition hindex (l : list Z) (h : Z) : Prop :=
  (* feasibility: at least h entries are >= h *)
  h <= count_ge l h
  /\
  (* maximality: no larger k is feasible *)
  (forall k, h < k -> count_ge l k < k).

Global Typeclasses Opaque hindex.

Definition increment_at (l : list Z) (i : nat) : list Z :=
  <[i := l !!! i + 1]> l.

Definition citation_update (before after : list Z) (i : nat) : Prop :=
  exists j, (j < length before)%nat /\
    before !!! j = before !!! i /\ after = increment_at before j.

Definition add_at (l : list Z) (i : nat) (k : Z) : list Z :=
  <[i := l !!! i + k]> l.

Definition citation_update_k
    (before after : list Z) (i : nat) (k : Z) : Prop :=
  Permutation after (add_at before i k).

(* All pairs are ordered except those whose right endpoint is the moving item. *)
Definition revsorted_except_at (l : list Z) (moving : nat) : Prop :=
  forall i j, (i < j < length l)%nat -> j <> moving -> l !!! j <= l !!! i.

Definition swap_at (l : list Z) (i j : nat) : list Z :=
  <[i := l !!! j]> (<[j := l !!! i]> l).

Definition revsorted_prefix (l : list Z) (n : nat) : Prop :=
  forall i j, (i < j < length l)%nat -> (i < n)%nat -> l !!! j <= l !!! i.

Lemma swap_at_length l i j :
  length (swap_at l i j) = length l.
Proof.
  unfold swap_at. rewrite !length_insert. reflexivity.
Qed.

Lemma swap_at_lookup_left l i j :
  (i < length l)%nat -> swap_at l i j !!! i = l !!! j.
Proof.
  intros Hi. unfold swap_at.
  apply list_lookup_total_insert_eq.
  rewrite length_insert. exact Hi.
Qed.

Lemma swap_at_lookup_right l i j :
  (j < length l)%nat -> i <> j -> swap_at l i j !!! j = l !!! i.
Proof.
  intros Hj Hij. unfold swap_at.
  rewrite list_lookup_total_insert_ne; last exact Hij.
  apply list_lookup_total_insert_eq. exact Hj.
Qed.

Lemma swap_at_lookup_other l i j k :
  k <> i -> k <> j -> swap_at l i j !!! k = l !!! k.
Proof.
  intros Hki Hkj. unfold swap_at.
  rewrite !list_lookup_total_insert_ne; congruence.
Qed.

Lemma add_at_length l i k :
  length (add_at l i k) = length l.
Proof. unfold add_at. apply length_insert. Qed.

Lemma add_at_lookup_eq l i k :
  (i < length l)%nat -> add_at l i k !!! i = l !!! i + k.
Proof. intros Hi. unfold add_at. apply list_lookup_total_insert_eq. exact Hi. Qed.

Lemma add_at_lookup_ne l i j k :
  j <> i -> add_at l i k !!! j = l !!! j.
Proof. intros Hji. unfold add_at. apply list_lookup_total_insert_ne. congruence. Qed.

Lemma swap_head_Permutation (x : Z) l j :
  (j < length l)%nat -> Permutation (x :: l) (l !!! j :: <[j := x]> l).
Proof.
  induction j as [|j IH] in l |- *;
    destruct l as [|y l]; simpl; try lia.
  - intros _. apply perm_swap.
  - intros Hj.
    etrans; first apply perm_swap.
    etrans; first (apply perm_skip; apply IH; lia).
    apply perm_swap.
Qed.

Lemma swap_at_Permutation l i j :
  (i < length l)%nat -> (j < length l)%nat -> i <> j ->
  Permutation l (swap_at l i j).
Proof.
  induction l as [|x l IH] in i, j |- *; first (simpl; lia).
  destruct i as [|i], j as [|j]; simpl; try lia.
  - intros _ Hj _. unfold swap_at. simpl.
    apply swap_head_Permutation. lia.
  - intros Hi _ _. unfold swap_at. simpl.
    apply swap_head_Permutation. lia.
  - intros Hi Hj Hij. apply perm_skip. apply IH; lia.
Qed.

Lemma revsorted_of_lookup_mono l :
  (forall i j, (i < j < length l)%nat -> l !!! j <= l !!! i) ->
  revsorted l.
Proof.
  unfold revsorted, ListSorted.
  induction l as [|x l IH]; first constructor.
  intros Hmono. apply Sorted_cons.
  - apply IH. intros i j Hij.
    change ((x :: l) !!! S j <= (x :: l) !!! S i).
    apply Hmono. simpl. lia.
  - destruct l as [|y l]; first constructor.
    apply HdRel_cons.
    opose proof (Hmono 0%nat 1%nat _) as Hxy.
    { simpl. lia. }
    simpl in Hxy. lia.
Qed.

Lemma revsorted_prefix_complete l n :
  revsorted_prefix l n -> (length l <= n)%nat -> revsorted l.
Proof.
  intros Hprefix Hlen. apply revsorted_of_lookup_mono.
  intros i j Hij. apply Hprefix; lia.
Qed.

Lemma revsorted_prefix_swap_at l i j :
  revsorted_prefix l i ->
  (i < j < length l)%nat ->
  revsorted_prefix (swap_at l i j) i.
Proof.
  intros Hprefix Hij p q Hpq Hp.
  rewrite swap_at_length in Hpq.
  opose proof (swap_at_lookup_other l i j p _ _) as Hp_lookup.
  { lia. }
  { lia. }
  rewrite Hp_lookup.
  destruct (decide (q = i)) as [->|Hqi].
  - opose proof (swap_at_lookup_left l i j _) as Hlookup.
    { lia. }
    rewrite Hlookup. apply Hprefix; lia.
  - destruct (decide (q = j)) as [->|Hqj].
    + opose proof (swap_at_lookup_right l i j _ _) as Hlookup.
      { lia. }
      { lia. }
      rewrite Hlookup. apply Hprefix; lia.
    + rewrite swap_at_lookup_other; last lia; last lia.
      apply Hprefix; lia.
Qed.

Lemma scanned_max_swap_at l i j :
  (i < j < length l)%nat ->
  (forall k, (i <= k < j)%nat -> l !!! k <= l !!! i) ->
  l !!! i < l !!! j ->
  forall k, (i <= k < S j)%nat ->
    swap_at l i j !!! k <= swap_at l i j !!! i.
Proof.
  intros Hij Hmax Hlt k Hk.
  opose proof (swap_at_lookup_left l i j _) as Hleft.
  { lia. }
  rewrite Hleft.
  destruct (decide (k = i)) as [->|Hki].
  - lia.
  - destruct (decide (k = j)) as [->|Hkj].
    + opose proof (swap_at_lookup_right l i j _ _) as Hright.
      { lia. }
      { lia. }
      rewrite Hright. lia.
    + rewrite (swap_at_lookup_other l i j k Hki Hkj).
      opose proof (Hmax k _) as Hold.
      { lia. }
      lia.
Qed.

Lemma scanned_max_keep (l : list Z) i j :
  (forall k, (i <= k < j)%nat -> l !!! k <= l !!! i) ->
  ~ l !!! i < l !!! j ->
  forall k, (i <= k < S j)%nat -> l !!! k <= l !!! i.
Proof.
  intros Hmax Hnot k Hk.
  destruct (decide (k = j)) as [->|Hkj]; first lia.
  apply Hmax. lia.
Qed.

Lemma revsorted_prefix_extend l i :
  revsorted_prefix l i ->
  (forall k, (i <= k < length l)%nat -> l !!! k <= l !!! i) ->
  revsorted_prefix l (S i).
Proof.
  intros Hprefix Hmax p q Hpq Hp.
  destruct (decide (p = i)) as [->|Hpi].
  - apply Hmax. lia.
  - apply Hprefix; lia.
Qed.

Lemma count_ge_Permutation l1 l2 k :
  Permutation l1 l2 -> count_ge l1 k = count_ge l2 k.
Proof.
  intros Hperm. unfold count_ge.
  apply Permutation_length, filter_Permutation, Hperm.
Qed.

Lemma hindex_Permutation l1 l2 h :
  Permutation l1 l2 -> hindex l1 h -> hindex l2 h.
Proof.
  intros Hperm [Hfeasible Hmaximal]. split.
  - rewrite <- (count_ge_Permutation l1 l2 h Hperm). exact Hfeasible.
  - intros k Hhk.
    rewrite <- (count_ge_Permutation l1 l2 k Hperm).
    apply Hmaximal. exact Hhk.
Qed.

Lemma lookup_total_is_Some (l : list Z) i :
  (i < length l)%nat -> l !! i = Some (l !!! i).
Proof.
  intros Hi.
  destruct (lookup_lt_is_Some_2 l i) as [x Hx]; first done.
  rewrite (list_lookup_total_correct l i x Hx).
  exact Hx.
Qed.

Lemma revsorted_increment_first l i :
  revsorted l ->
  (i < length l)%nat ->
  (forall j, (j < i)%nat -> l !!! j > l !!! i) ->
  revsorted (increment_at l i).
Proof.
  unfold revsorted, ListSorted, increment_at.
  induction i as [|i IH] in l |- *; destruct l as [|x l]; simpl; try lia.
  - intros Hsorted _ _.
    apply Sorted_cons.
    + exact (proj1 (Sorted_inv Hsorted)).
    + destruct l as [|y l]; first constructor.
      apply HdRel_cons.
      pose proof (HdRel_inv (proj2 (Sorted_inv Hsorted))).
      lia.
  - intros Hsorted Hi Hfirst.
    apply Sorted_cons.
    + apply IH; first exact (proj1 (Sorted_inv Hsorted)); first lia.
      intros j Hj.
      change ((x :: l) !!! S j > (x :: l) !!! S i).
      apply Hfirst; lia.
    + destruct i as [|i].
      * destruct l as [|y l]; first constructor.
        apply HdRel_cons.
        pose proof (Hfirst 0%nat ltac:(lia)).
        simpl in H.
        change (x >= y + 1).
        lia.
      * destruct l as [|y l]; first constructor.
        apply HdRel_cons.
        exact (HdRel_inv (proj2 (Sorted_inv Hsorted))).
Qed.

Lemma count_ge_cons x l k :
  count_ge (x :: l) k =
    if k <=? x then S (count_ge l k) else count_ge l k.
Proof.
  unfold count_ge; rewrite filter_cons.
  destruct (k <=? x); reflexivity.
Qed.

Lemma count_ge_increment_at l i k :
  (i < length l)%nat ->
  count_ge (increment_at l i) k =
    if decide (k = l !!! i + 1) then S (count_ge l k) else count_ge l k.
Proof.
  unfold increment_at.
  induction i as [|i IH] in l |- *; destruct l as [|x l]; simpl; try lia.
  - intros _.
    unfold count_ge; repeat rewrite filter_cons.
    repeat case_decide; simpl; try reflexivity; try lia.
    all: destruct (k <=? x) eqn:Hkx;
      destruct (k <=? x + 1) eqn:Hkx1;
      simpl in *; try reflexivity;
      try (apply Z.leb_le in Hkx); try (apply Z.leb_gt in Hkx);
      try (apply Z.leb_le in Hkx1); try (apply Z.leb_gt in Hkx1); lia.
  - intros Hi.
    change (count_ge (x :: <[i := l !!! i + 1]> l) k =
      if decide (k = l !!! i + 1) then S (count_ge (x :: l) k)
      else count_ge (x :: l) k).
    repeat rewrite count_ge_cons.
    specialize (IH l ltac:(lia)).
    rewrite IH.
    destruct (k <=? x); destruct (decide (k = l !!! i + 1)); reflexivity.
Qed.

Lemma revsorted_lookup_mono l i j :
  revsorted l -> (i <= j)%nat -> (j < length l)%nat -> l !!! j <= l !!! i.
Proof.
  unfold revsorted, ListSorted.
  induction i as [|i IH] in l, j |- *; destruct l as [|x l]; simpl; try lia.
  - intros Hsorted _ Hj.
    destruct j as [|j]; first reflexivity.
    pose proof (@Sorted_extends Z Z.ge
      (fun a b c Hab Hbc => ltac:(lia)) x l Hsorted) as Hall.
    destruct (lookup_lt_is_Some_2 l j) as [y Hy]; first lia.
    change (l !!! j <= x).
    rewrite (list_lookup_total_correct l j y Hy).
    pose proof (Forall_lookup_1 _ _ j y Hall Hy).
    lia.
  - intros Hsorted Hij Hj.
    destruct j as [|j]; first lia.
    change (l !!! j <= l !!! i).
    apply IH; try lia.
    exact (proj1 (Sorted_inv Hsorted)).
Qed.

Lemma count_ge_prefix l k n :
  (n <= length l)%nat ->
  (forall i, (i < n)%nat -> k <= l !!! i) ->
  (n <= count_ge l k)%nat.
Proof.
  induction n as [|n IH] in l |- *; first lia.
  destruct l as [|x l]; simpl; first lia.
  intros Hlen Hall.
  unfold count_ge; rewrite filter_cons.
  assert (Hzero : (0 < S n)%nat) by lia.
  pose proof (Hall 0%nat Hzero) as Hhead.
  simpl in Hhead.
  case_decide as Hdec; simpl.
  - change (S n <= S (count_ge l k))%nat.
    specialize (IH l ltac:(lia)).
    enough (n <= count_ge l k)%nat by lia.
    apply IH.
    intros i Hi.
    change (k <= (x :: l) !!! S i).
    apply Hall; lia.
  - exfalso; apply Hdec.
    destruct (k <=? x) eqn:Hkx; simpl; first done.
    apply Z.leb_gt in Hkx; lia.
Qed.

Lemma count_ge_suffix l k n :
  (n <= length l)%nat ->
  (forall i, (n <= i < length l)%nat -> l !!! i < k) ->
  (count_ge l k <= n)%nat.
Proof.
  induction n as [|n IH] in l |- *.
  - intros _ Hall.
    unfold count_ge.
    induction l as [|x l IHl]; simpl; first lia.
    rewrite filter_cons.
    assert (Hzero : (0 <= 0 < S (length l))%nat) by lia.
    pose proof (Hall 0%nat Hzero) as Hhead.
    simpl in Hhead.
    case_decide as Hdec; simpl.
    + exfalso.
      destruct (k <=? x) eqn:Hkx; simpl in Hdec; last contradiction.
      apply Z.leb_le in Hkx; lia.
    + change (count_ge l k <= 0)%nat.
      apply IHl.
      intros i Hi.
      change ((x :: l) !!! S i < k).
      apply Hall; simpl; lia.
  - destruct l as [|x l]; simpl; first lia.
    intros Hlen Hall.
    unfold count_ge; rewrite filter_cons; case_decide; simpl.
    + change (S (count_ge l k) <= S n)%nat.
      enough (count_ge l k <= n)%nat by lia.
      apply IH; first lia.
      intros i Hi.
      change ((x :: l) !!! S i < k).
      apply Hall; simpl; lia.
    + change (count_ge l k <= S n)%nat.
      enough (count_ge l k <= n)%nat by lia.
      apply IH; first lia.
      intros i Hi.
      change ((x :: l) !!! S i < k).
      apply Hall; simpl; lia.
Qed.

Lemma revsorted_hindex_boundary l h :
  revsorted l -> hindex l h -> 0 <= h -> h < length l ->
  l !!! Z.to_nat h <= h.
Proof.
  intros Hsorted [_ Hmax] Hh Hlen.
  destruct (decide (l !!! Z.to_nat h <= h)); first done.
  pose proof (count_ge_prefix l (Z.succ h) (S (Z.to_nat h)) ltac:(lia)) as Hprefix.
  specialize (Hprefix ltac:(
    intros j Hj;
    pose proof (revsorted_lookup_mono l j (Z.to_nat h) Hsorted ltac:(lia) ltac:(lia));
    lia)).
  pose proof (Hmax (Z.succ h) ltac:(lia)).
  lia.
Qed.

Lemma revsorted_add_at_except l i k :
  revsorted l -> (i < length l)%nat -> 0 <= k ->
  revsorted_except_at (add_at l i k) i.
Proof.
  intros Hsorted Hi Hk p q Hpq Hqi.
  rewrite add_at_length in Hpq.
  rewrite (add_at_lookup_ne l i q k Hqi).
  destruct (decide (p = i)) as [-> | Hpi].
  - rewrite (add_at_lookup_eq l i k Hi).
    opose proof (revsorted_lookup_mono l i q Hsorted _ _) as Hmono.
    { lia. }
    { lia. }
    lia.
  - rewrite (add_at_lookup_ne l i p k Hpi).
    apply revsorted_lookup_mono; assumption || lia.
Qed.

Lemma revsorted_except_swap_left (l : list Z) j :
  revsorted_except_at l j ->
  (0 < j < length l)%nat ->
  l !!! (j - 1)%nat < l !!! j ->
  revsorted_except_at (swap_at l (j - 1)%nat j) (j - 1)%nat.
Proof.
  intros Halmost Hj Hlt p q Hpq Hq.
  rewrite swap_at_length in Hpq.
  assert (Hleft : (j - 1 < length l)%nat) by lia.
  assert (Hjlen : (j < length l)%nat) by lia.
  assert (Hneq : (j - 1)%nat <> j) by lia.
  destruct (decide (p = (j - 1)%nat)) as [-> | Hp_left].
  - rewrite (swap_at_lookup_left l (j - 1)%nat j Hleft).
    destruct (decide (q = j)) as [-> | Hqj].
    + rewrite (swap_at_lookup_right l (j - 1)%nat j Hjlen Hneq). lia.
    + rewrite (swap_at_lookup_other l (j - 1)%nat j q Hq Hqj).
      apply (Halmost j q); lia.
  - destruct (decide (p = j)) as [-> | Hpj].
    + rewrite (swap_at_lookup_right l (j - 1)%nat j Hjlen Hneq).
      assert (Hqj : q <> j) by lia.
      rewrite (swap_at_lookup_other l (j - 1)%nat j q Hq Hqj).
      apply (Halmost (j - 1)%nat q); lia.
    + destruct (decide (q = j)) as [-> | Hqj].
      * rewrite (swap_at_lookup_right l (j - 1)%nat j Hjlen Hneq).
        rewrite (swap_at_lookup_other l (j - 1)%nat j p Hp_left Hpj).
        apply (Halmost p (j - 1)%nat); lia.
      * rewrite (swap_at_lookup_other l (j - 1)%nat j p Hp_left Hpj).
        rewrite (swap_at_lookup_other l (j - 1)%nat j q Hq Hqj).
        apply (Halmost p q); lia.
Qed.

Lemma revsorted_except_complete (l : list Z) j :
  revsorted_except_at l j ->
  (j = 0%nat \/ l !!! j <= l !!! (j - 1)%nat) ->
  revsorted l.
Proof.
  intros Halmost Hstop. apply revsorted_of_lookup_mono.
  intros p q Hpq.
  destruct (decide (q = j)) as [-> | Hqj]; last (apply Halmost; done).
  destruct Hstop as [-> | Hstop]; first lia.
  destruct (decide (p = (j - 1)%nat)) as [-> | Hp]; first exact Hstop.
  opose proof (Halmost p (j - 1)%nat _ _) as Hprefix.
  { lia. }
  { lia. }
  lia.
Qed.

Lemma count_ge_length l threshold :
  (count_ge l threshold <= length l)%nat.
Proof.
  induction l as [|x l IH]; first reflexivity.
  rewrite count_ge_cons. destruct (threshold <=? x); simpl; lia.
Qed.

Lemma count_ge_threshold_mono l lower upper :
  lower <= upper ->
  (count_ge l upper <= count_ge l lower)%nat.
Proof.
  intros Hthreshold. induction l as [|x l IH]; first reflexivity.
  rewrite !count_ge_cons.
  destruct (upper <=? x) eqn:Hupper;
    destruct (lower <=? x) eqn:Hlower; simpl.
  - lia.
  - apply Z.leb_le in Hupper. apply Z.leb_gt in Hlower. lia.
  - lia.
  - exact IH.
Qed.

Lemma count_ge_add_at l i delta threshold :
  (i < length l)%nat -> 0 <= delta ->
  count_ge (add_at l i delta) threshold =
    if decide (l !!! i < threshold <= l !!! i + delta)
    then S (count_ge l threshold)
    else count_ge l threshold.
Proof.
  unfold add_at.
  induction i as [|i IH] in l |- *; destruct l as [|x l]; simpl; try lia.
  - intros _ Hdelta.
    change (count_ge ((x + delta) :: l) threshold =
      if decide (x < threshold <= x + delta)
      then S (count_ge (x :: l) threshold)
      else count_ge (x :: l) threshold).
    rewrite !count_ge_cons.
    destruct (threshold <=? x) eqn:Hold;
      destruct (threshold <=? x + delta) eqn:Hnew;
      case_decide as Hcross; simpl; try reflexivity;
      try (apply Z.leb_le in Hold); try (apply Z.leb_gt in Hold);
      try (apply Z.leb_le in Hnew); try (apply Z.leb_gt in Hnew); lia.
  - intros Hi Hdelta.
    change (count_ge (x :: <[i:=l !!! i + delta]> l) threshold =
      if decide (l !!! i < threshold <= l !!! i + delta)
      then S (count_ge (x :: l) threshold)
      else count_ge (x :: l) threshold).
    rewrite !count_ge_cons.
    opose proof (IH l _ Hdelta) as Hcount. { lia. }
    rewrite Hcount.
    destruct (threshold <=? x);
      destruct (decide (l !!! i < threshold <= l !!! i + delta)); reflexivity.
Qed.

Lemma hindex_update_k_succ before after h i delta :
  hindex before h ->
  citation_update_k before after i delta ->
  revsorted after ->
  (i < length before)%nat ->
  0 <= delta ->
  0 <= h ->
  h < length after ->
  h < after !!! Z.to_nat h ->
  hindex after (Z.succ h).
Proof.
  intros [Hfeasible Hmaximal] Hupdate Hsorted Hi Hdelta Hh Hhlen Hboundary.
  split.
  - opose proof (count_ge_prefix after (Z.succ h) (S (Z.to_nat h)) _ _)
      as Hprefix.
    { lia. }
    { intros j Hj.
      opose proof (revsorted_lookup_mono after j (Z.to_nat h) Hsorted _ _)
        as Hmono.
      { lia. }
      { lia. }
      lia. }
    lia.
  - intros threshold Hthreshold.
    unfold citation_update_k in Hupdate.
    opose proof (count_ge_Permutation after (add_at before i delta)
      threshold Hupdate) as Hperm.
    opose proof (count_ge_add_at before i delta threshold Hi Hdelta)
      as Hadd.
    rewrite Hperm. rewrite Hadd.
    case_decide as Hcross.
    + opose proof (count_ge_threshold_mono before (Z.succ h) threshold _)
        as Hmono. { lia. }
      opose proof (Hmaximal (Z.succ h) _) as Hnext. { lia. }
      lia.
    + opose proof (Hmaximal threshold _) as Hbound. { lia. }
      lia.
Qed.

Lemma hindex_update_k_same before after h i delta :
  hindex before h ->
  citation_update_k before after i delta ->
  revsorted after ->
  (i < length before)%nat ->
  0 <= delta ->
  0 <= h ->
  ~ (h < length after /\ h < after !!! Z.to_nat h) ->
  hindex after h.
Proof.
  intros [Hfeasible Hmaximal] Hupdate Hsorted Hi Hdelta Hh Hboundary.
  unfold citation_update_k in Hupdate.
  split.
  - opose proof (count_ge_Permutation after (add_at before i delta)
      h Hupdate) as Hperm.
    opose proof (count_ge_add_at before i delta h Hi Hdelta) as Hadd.
    rewrite Hperm. rewrite Hadd.
    case_decide; lia.
  - intros threshold Hthreshold.
    destruct (decide (threshold = Z.succ h)) as [-> | Hneq].
    + destruct (decide (h < length after)) as [Hhlen | Hhlen].
      * assert (Hvalue : after !!! Z.to_nat h <= h).
        { destruct (decide (h < after !!! Z.to_nat h)) as [Hvalue | Hvalue];
            last lia.
          exfalso. apply Hboundary. split; assumption. }
        opose proof (count_ge_suffix after (Z.succ h) (Z.to_nat h) _ _)
          as Hsuffix.
        { lia. }
        { intros j Hj.
          opose proof (revsorted_lookup_mono after (Z.to_nat h) j
            Hsorted _ _) as Hmono.
          { lia. }
          { lia. }
          lia. }
        lia.
      * opose proof (count_ge_length after (Z.succ h)) as Hlength.
        lia.
    + opose proof (count_ge_Permutation after (add_at before i delta)
        threshold Hupdate) as Hperm.
      opose proof (count_ge_add_at before i delta threshold Hi Hdelta)
        as Hadd.
      rewrite Hperm. rewrite Hadd.
      case_decide as Hcross.
      * opose proof (count_ge_threshold_mono before (Z.succ h) threshold _)
          as Hmono. { lia. }
        opose proof (Hmaximal (Z.succ h) _) as Hnext. { lia. }
        lia.
      * opose proof (Hmaximal threshold _) as Hbound. { lia. }
        lia.
Qed.
