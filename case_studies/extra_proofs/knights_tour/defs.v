From refinedrust Require Import typing shims.

(* !start spec(knights_tour.knights_tour) *)
Definition in_bounds (sz : nat) (p : Z * Z) :=
  name_hint "HlowerX" (0 ≤ p.1) ∧ name_hint "HupperX" (p.1 < sz) ∧ name_hint "HlowerY" (0 ≤ p.2) ∧ name_hint "HupperY" (p.2 < sz).

Lemma in_bounds_nonneg_l sz p0 p1 :
  in_bounds sz (p0, p1) -> 0 ≤ p0. 
Proof.
  unfold in_bounds, name_hint. cbn. lia.
Qed.

Lemma in_bounds_nonneg_r sz p0 p1 :
  in_bounds sz (p0, p1) -> 0 ≤ p1. 
Proof.
  unfold in_bounds, name_hint. cbn. lia.
Qed.

Definition pos := (Z * Z)%type.

Definition board_at (board : list (list Z)) (p : pos) : Z :=
  let (x, y) := p in
  (board !!! (Z.to_nat x)) !!! (Z.to_nat y).

Definition kmove (p q : pos) :=
  let '(x1,y1) := p in
  let '(x2,y2) := q in
  (Z.abs (x1 - x2) = 2 ∧ Z.abs (y1 - y2) = 1) ∨ 
  (Z.abs (x1 - x2) = 1 ∧ Z.abs (y1 - y2) = 2).

Definition extend_kpath (board : (nat * list (list Z))) (p : pos) (candidates : list _) :=
  ∀ (z : RT_xt (place_rfnRT (tuple2_rt Z _))), z ∈ candidates → in_bounds board.1 (z.:1) ∧ board_at board.2 (z.:1) = 0 ∧ kmove p (z.:1).

Lemma extend_kpath_trivial (board : (nat * list (list Z))) (p : pos) : extend_kpath board p [].
Proof.
  unfold extend_kpath. intros z. solve_goal.
Qed.

Lemma extend_kpath_singleton (board : (nat * list (list Z))) (p : pos) (size : Z) (x : RT_xt (place_rfnRT (tuple2_rt _ _))) :
  in_bounds board.1 x.:1     ->
  board_at  board.2 x.:1 = 0 ->
  kmove     p       x.:1     ->
  extend_kpath board p [x].
Proof.
  intros H1 H2 H3 z Hinsngltn.
  apply list_elem_of_singleton in Hinsngltn.
  inversion Hinsngltn; subst. done.
Qed.

Lemma extend_kpath_app (board : (nat * list (list Z))) (p: pos) (xs ys : list _) :
  extend_kpath board p xs ->
  extend_kpath board p ys ->
  extend_kpath board p (xs ++ ys).
Proof.
  intros H1 H2 z Hincands.
  apply elem_of_app in Hincands as [Hin | Hin].
  - apply H1 in Hin. done.
  - apply H2. exact Hin.
Qed.

Lemma kpath_extension_in_bounds (board : (nat * list (list Z))) (p q: pos) (xs : list _) (deg : Z) :
  -[deg; q] ∈ xs          ->
  extend_kpath board p xs ->
  in_bounds board.1 q.
Proof.
  intros Hinxs Hext. unfold extend_kpath in Hext. specialize Hext with -[deg; q]. solve_goal.
Qed.

Lemma kpath_extension_is0 (board : (nat * list (list Z))) (p q: pos) (xs : list _) (deg : Z) :
  -[deg; q] ∈ xs          ->
  extend_kpath board p xs ->
  board_at     board.2 q = 0.
Proof.
  intros Hinxs Hext. unfold extend_kpath in Hext. specialize Hext with -[deg; q]. solve_goal.
Qed.

Lemma kpath_extension_kmove (board : (nat * list (list Z))) (p q: pos) (xs : list _) (deg : Z) :
  -[deg; q] ∈ xs          ->
  extend_kpath board p xs ->
  kmove p q.
Proof.
  intros Hinxs Hext. unfold extend_kpath in Hext. specialize Hext with -[deg; q]. solve_goal.
Qed.

Fixpoint kpath (board : nat * (list (list Z))) (s t : pos) (len : nat) :=
  match len with
  | 0%nat => s = t ∧ in_bounds board.1 s ∧ board_at board.2 s = 1
  | S len' => 
      ∃ u : pos,
        kmove u t            ∧
        kpath board s u len' ∧
        in_bounds board.1 t  ∧ 
        board_at board.2 t = len' + 2
  end.

Arguments kpath : simpl never.

Lemma on_kpath_in_bounds board s t len :
  kpath board s t len -> in_bounds board.1 t.
Proof.
  destruct len as [|len']; first solve_goal.
  intros (_ & _ & _ & Hib & _). exact Hib.
Qed.

Lemma kpath_transfer board1 board2 s t n :
  (∀ p, in_bounds board1.1 p -> 1 ≤ board_at board1.2 p -> board_at board2.2 p = board_at board1.2 p) ->
  board1.1 = board2.1  ->
  in_bounds board1.1 t   ->
  kpath board1 s t n ->
  kpath board2 s t n.
Proof.
  revert s t.
  induction n as [|n IH]; intros s t Hagree Hsz Hbounds Hk.
  - destruct Hk as [-> [Hbounds_t H1]].
    split; first done.
    rewrite <- H1.
    split. { rewrite <-Hsz. done. }
    apply Hagree; last lia. done.
  - destruct Hk as [u [Hmv [Hpath [Hbounds_t Hcoord]]]].
    exists u. split; first done. split.
    + specialize IH with s u. apply IH; try done.
      apply (on_kpath_in_bounds board1 s u n). done.
    + specialize Hagree with t. rewrite Hagree; try solve_goal.
    split; last done. rewrite <-Hsz. done.
Qed.

Lemma kpath_extend (s u t : pos) (board board2 : nat *list (list Z)) (len : nat) :
  (∀ (i j : nat), if decide ((Z.of_nat i, Z.of_nat j) = t) then
    board_at board2.2 (Z.of_nat i, Z.of_nat j) = S (S len) else
    board_at board2.2 (Z.of_nat i, Z.of_nat j) = board_at board.2 (Z.of_nat i, Z.of_nat j)
  ) ->
  board.1 = board2.1       ->
  in_bounds board2.1 t     ->
  board_at board.2  t = 0  ->
  kmove    u       t       ->
  kpath    board   s u len ->
  kpath    board2  s t (S len).
Proof.
  intros Htransfer Heqsz Htib Hboardt0 Hkmov Hpath_old.
  exists u. split; try done. split.
  - apply (kpath_transfer board board2 s u len); try done.
    + intros [p0 p1] Hib Hpgeq1.
      specialize Htransfer with (Z.to_nat p0) (Z.to_nat p1).
      rewrite Z2Nat.id in Htransfer; last apply (in_bounds_nonneg_l board.1 p0 p1); try done.
      rewrite Z2Nat.id in Htransfer; last apply (in_bounds_nonneg_r board.1 p0 p1); try done.
      case_decide; last exact Htransfer.
      rewrite H in Hpgeq1. lia.
    + by apply (on_kpath_in_bounds board s u len).
  - split; first done.
    destruct t as [t0 t1].
    specialize Htransfer with (Z.to_nat t0) (Z.to_nat t1). 
    rewrite! Z2Nat.id in Htransfer.
    + rewrite decide_True in Htransfer; last done. lia.
    + apply (in_bounds_nonneg_r board.1 t0 t1).
      rewrite Heqsz; done.
    + apply (in_bounds_nonneg_l board.1 t0 t1).
      rewrite Heqsz; done.
Qed.

(* !end spec *)
