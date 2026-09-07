From caesium Require Import lang notation.
From refinedrust Require Import typing.



(*
  locs, nexts で表されるヒープにおいて， 
  index i のノードから mark_from を実行（再帰呼び出し）したときに
  marks が実行後に marks_new になる
*)
Inductive mark_from_rel
    (locs nexts : list loc) :
    list bool -> nat -> list bool -> Prop :=

(* marked ならなにもしない *)
| mark_from_rel_marked
    (marks : list bool) (i : nat) :
    marks !! i = Some true ->
    mark_from_rel locs nexts marks i marks

(* false で，next が null なら自分だけmark *)
| mark_from_rel_null
    (marks : list bool) (i : nat) (l : loc) :
    marks !! i = Some false ->
    nexts !! i = Some l ->
    loc_a l = 0 ->
    mark_from_rel
      locs nexts
      marks i
      (<[i := true]> marks)

(* false で，next も存在するとき再帰 *)
| mark_from_rel_next
    (marks marks_new : list bool)
    (i j : nat) (l : loc) :
    marks !! i = Some false ->
    nexts !! i = Some l ->
    loc_a l <> 0 ->
    locs !! j = Some l ->
    mark_from_rel
      locs nexts
      (<[i := true]> marks)
      j
      marks_new ->
    mark_from_rel
      locs nexts
      marks
      i
      marks_new.





(* start 番目から引数番目まで到達可能かを表す命題 *)
(*
  reachable_from : 
    locs  : アドレスリスト
    nexts : 各アドレスの next アドレスリスト
    start : 開始インデックス
*)
Inductive reachable_from
    (locs nexts : list loc)
    (start : nat) : nat -> Prop :=

  (* start -> start *)
  | reachable_from_refl :
      reachable_from locs nexts start start

  (* start -> i は到達可能と仮定 *)
  (* 
    next[i] == l ∧ l == locs[j] 
    => start -> j は到達可能
  *)
  | reachable_from_step
      (i j : nat) (l : loc) :
      reachable_from locs nexts start i ->
      nexts !! i = Some l ->
      loc_a l <> 0 ->
      locs !! j = Some l ->
      reachable_from locs nexts start j.


(* locs[i]が到達可能か *)
Definition reachable
    (locs nexts : list loc)
    (i : nat) : Prop :=
  reachable_from locs nexts 0%nat i.


(* 全ノードが未マーク *)
Definition all_unmarked (marks : list bool) : Prop :=
  Forall (fun m => m = false) marks.


(*
  reachable_from の推移性

  a から b に到達可能で、
  b から c に到達可能なら、
  a から c にも到達可能
*)
Lemma reachable_from_trans
    (locs nexts : list loc)
    (a b c : nat) :
  reachable_from locs nexts a b ->
  reachable_from locs nexts b c ->
  reachable_from locs nexts a c.
Proof.
  intros Hab Hbc.
  induction Hbc.
  - exact Hab.
  - eapply reachable_from_step; eauto.
Qed.


(*
  mark_from_rel の soundness。

  mark_from 実行後に k 番目が true なら、

  1. k 番目は実行前から true だった
     または
  2. start から k 番目へ到達可能

  のどちらか。
*)
Lemma mark_from_rel_sound
    (locs nexts : list loc)
    (marks marks_new : list bool)
    (start : nat) :
  mark_from_rel locs nexts marks start marks_new ->
  forall k,
    marks_new !! k = Some true ->
    marks !! k = Some true \/
    reachable_from locs nexts start k.
Proof.
  intros Hrel.

  induction Hrel as
      [marks i Hmarked
      | marks i l Hfalse Hnext Hnull
      | marks marks_new i j l
          Hfalse Hnext Hnonnull Hloc
          Hrel IH];
    intros k Hk.

  (* すでに marked だった場合 *)
  - left.
    exact Hk.

  (* false かつ next が null の場合
     i だけ true に更新される *)
  - destruct (decide (k = i)) as [Heq | Hneq].

    (* k = i なら start (= i) 自身なので reachable *)
    + subst k.
      right.
      constructor.

    (* k <> i なら更新の影響を受けない。
       従って、実行前から k は true だった。 *)
    + left.
      rewrite list_lookup_insert_ne in Hk.
      * exact Hk.
      * congruence.

  (* false かつ next が存在し、j へ再帰した場合 *)
  - specialize (IH k Hk).

    destruct IH as [Hold | Hreach].

    (* 再帰開始時点
         <[i := true]> marks
       で k がすでに true だった場合 *)
    + destruct (decide (k = i)) as [Heq | Hneq].

      (* k = i なら start 自身 *)
      * subst k.
        right.
        constructor.

      (* k <> i なら、i の更新とは無関係なので
         元の marks でも k は true *)
      * left.
        rewrite list_lookup_insert_ne in Hold.
        -- exact Hold.
        -- congruence.

    (* j から k が reachable なら、
       i -> j と j -> k をつなぐ *)
    + right.

      eapply reachable_from_trans.

      (* i から j へ1ステップで到達可能 *)
      * eapply reachable_from_step
          with (i := i) (j := j) (l := l).
        -- constructor.
        -- exact Hnext.
        -- exact Hnonnull.
        -- exact Hloc.

      (* j から k は IH で分かっている *)
      * exact Hreach.
Qed.


(*
  初期状態が all_unmarked なら、
  「実行前から true」はあり得ない。

  したがって、実行後に true なら必ず reachable。
*)
Lemma mark_from_rel_sound_unmarked
    (locs nexts : list loc)
    (marks marks_new : list bool)
    (start : nat) :
  all_unmarked marks ->
  mark_from_rel locs nexts marks start marks_new ->
  forall k,
    marks_new !! k = Some true ->
    reachable_from locs nexts start k.
Proof.
  intros Hunmarked Hrel k Hk.

  destruct
    (mark_from_rel_sound
      locs nexts marks marks_new start
      Hrel k Hk)
    as [Hold | Hreach].

  (* marks[k] = true だが、
     all_unmarked より marks[k] = false のはずなので矛盾 *)
  - unfold all_unmarked in Hunmarked.

    pose proof
      ((proj1
          (Forall_lookup
            (fun m : bool => m = false)
            marks)
          Hunmarked)
        k true Hold)
      as Hfalse.

    discriminate Hfalse.

  - exact Hreach.
Qed.


(*
  GC の root = 0 に特化した形。

  Heap::mark の最終仕様で使いやすい形。
*)
Corollary mark_from_rel_sound_root
    (locs nexts : list loc)
    (marks marks_new : list bool) :
  all_unmarked marks ->
  mark_from_rel
    locs nexts
    marks 0%nat marks_new ->
  forall k,
    marks_new !! k = Some true ->
    reachable locs nexts k.
Proof.
  intros Hunmarked Hrel k Hk.

  unfold reachable.

  eapply mark_from_rel_sound_unmarked.
  - exact Hunmarked.
  - exact Hrel.
  - exact Hk.
Qed.

(*
  一度 true だった mark は、
  mark_from_rel の実行後も true のまま。
*)
Lemma mark_from_rel_preserves_true
    (locs nexts : list loc)
    (marks marks_new : list bool)
    (start : nat) :
  mark_from_rel locs nexts marks start marks_new ->
  forall k,
    marks !! k = Some true ->
    marks_new !! k = Some true.
Proof.
  intros Hrel.

  induction Hrel as
      [marks i Hmarked
      | marks i l Hfalse Hnext Hnull
      | marks marks_new i j l
          Hfalse Hnext Hnonnull Hloc
          Hrec IH];
    intros k Hk.

  (* marked: 状態は変化しない *)
  - exact Hk.

  (* null: i だけ true にする *)
  - destruct (decide (k = i)) as [Heq | Hneq].

    + subst k.
      pose proof
        (lookup_lt_Some _ _ _ Hfalse)
        as Hi.
      rewrite list_lookup_insert_eq.
      * done.
      * exact Hi.

    + rewrite list_lookup_insert_ne.
      * exact Hk.
      * congruence.

  (* next:
     まず i を true にし、
     その状態から再帰する *)
  - apply IH.

    destruct (decide (k = i)) as [Heq | Hneq].

    + subst k.
      pose proof
        (lookup_lt_Some _ _ _ Hfalse)
        as Hi.
      rewrite list_lookup_insert_eq.
      * done.
      * exact Hi.

    + rewrite list_lookup_insert_ne.
      * exact Hk.
      * congruence.
Qed.


(*
  mark_from_rel が完了すれば、
  start 自身は必ず true になっている。
*)
Lemma mark_from_rel_marks_start
    (locs nexts : list loc)
    (marks marks_new : list bool)
    (start : nat) :
  mark_from_rel locs nexts marks start marks_new ->
  marks_new !! start = Some true.
Proof.
  intros Hrel.

  destruct Hrel as
      [marks i Hmarked
      | marks i l Hfalse Hnext Hnull
      | marks marks_new i j l
          Hfalse Hnext Hnonnull Hloc Hrec].

  (* 最初から true *)
  - exact Hmarked.

  (* 自分を true に更新 *)
  - pose proof
      (lookup_lt_Some _ _ _ Hfalse)
      as Hi.

    rewrite list_lookup_insert_eq.
    + done.
    + exact Hi.

  (* 自分を true にしてから再帰。
     再帰後も true は保存される。 *)
  - eapply mark_from_rel_preserves_true.
    + exact Hrec.
    + pose proof
        (lookup_lt_Some _ _ _ Hfalse)
        as Hi.

      rewrite list_lookup_insert_eq.
      * done.
      * exact Hi.
Qed.

Lemma nodup_locs_lookup_unique
    (locs : list loc)
    (i j : nat)
    (l : loc) :
  NoDup locs ->
  locs !! i = Some l ->
  locs !! j = Some l ->
  i = j.
Proof.
  intros Hnd Hi Hj.
  eapply NoDup_lookup; eauto.
Qed.


(*
  marked なノードから next を辿った先は marked である。
  ただし cur は「現在処理中」なので例外としてよい。
*)
Definition marks_closed_except
    (locs nexts : list loc)
    (marks : list bool)
    (cur : nat) : Prop :=
  forall p q l,
    marks !! p = Some true ->
    nexts !! p = Some l ->
    loc_a l <> 0 ->
    locs !! q = Some l ->
    q <> cur ->
    marks !! q = Some true.


(*
  最終的には例外なしで successor に閉じている。
*)
Definition marks_closed
    (locs nexts : list loc)
    (marks : list bool) : Prop :=
  forall p q l,
    marks !! p = Some true ->
    nexts !! p = Some l ->
    loc_a l <> 0 ->
    locs !! q = Some l ->
    marks !! q = Some true.


Lemma all_unmarked_closed_except
    (locs nexts : list loc)
    (marks : list bool)
    (cur : nat) :
  all_unmarked marks ->
  marks_closed_except locs nexts marks cur.
Proof.
  intros Hunmarked.
  unfold marks_closed_except.

  intros p q l Hp _ _ _ _.

  unfold all_unmarked in Hunmarked.

  pose proof
    ((proj1
        (Forall_lookup
          (fun m : bool => m = false)
          marks)
        Hunmarked)
      p true Hp)
    as Hfalse.

  discriminate Hfalse.
Qed.

Lemma mark_from_rel_final_closed
    (locs nexts : list loc)
    (marks marks_new : list bool)
    (start : nat) :
  NoDup locs ->
  marks_closed_except locs nexts marks start ->
  mark_from_rel locs nexts marks start marks_new ->
  marks_closed locs nexts marks_new.
Proof.
  intros Hnodup Hclosed Hrel.

  revert Hclosed.

  induction Hrel as
      [marks i Hmarked
      | marks i l0 Hfalse Hnext Hnull
      | marks marks_new i j l0
          Hfalse Hnext Hnonnull Hloc
          Hrec IH];
    intros Hclosed.

  (* -------------------------------------------------- *)
  (* 既に marked                                        *)
  (* -------------------------------------------------- *)
  - unfold marks_closed.
    unfold marks_closed_except in Hclosed.

    intros p q l Hp Hnext_p Hnonnull_p Hloc_q.

    destruct (decide (q = i)) as [Heq | Hneq].

    + subst q.
      exact Hmarked.

    + eapply Hclosed; eauto.

  (* -------------------------------------------------- *)
  (* null                                                *)
  (* -------------------------------------------------- *)
  - unfold marks_closed.
    unfold marks_closed_except in Hclosed.

    intros p q l Hp Hnext_p Hnonnull_p Hloc_q.

    destruct (decide (p = i)) as [Heq_p | Hneq_p].

    (* 新しく marked にした i からは、
       null なので non-null successor は存在しない *)
    + subst p.

      assert (l = l0) as -> by congruence.

      exfalso.
      apply Hnonnull_p.
      exact Hnull.

    (* p は以前から marked *)
    + assert (Hp_old :
        marks !! p = Some true).
      {
        rewrite list_lookup_insert_ne in Hp.
        - exact Hp.
        - congruence.
      }

      destruct (decide (q = i)) as [Heq_q | Hneq_q].

      (* successor が今回 mark した i なら OK *)
      * subst q.

        pose proof
          (lookup_lt_Some _ _ _ Hfalse)
          as Hi.

        rewrite list_lookup_insert_eq.
        -- done.
        -- exact Hi.

      (* それ以外は以前の closed_except から得る *)
      * assert (Hq_old :
          marks !! q = Some true).
        {
          eapply Hclosed; eauto.
        }

        rewrite list_lookup_insert_ne.
        -- exact Hq_old.
        -- congruence.

  (* -------------------------------------------------- *)
  (* next                                                *)
  (* -------------------------------------------------- *)
  - apply IH.

    unfold marks_closed_except.
    unfold marks_closed_except in Hclosed.

    intros p q l Hp Hnext_p Hnonnull_p Hloc_q Hq_not_j.

    destruct (decide (p = i)) as [Heq_p | Hneq_p].

    (* p = i の場合。
       i の successor は j で一意なので、
       q <> j と矛盾する。 *)
    + subst p.

      assert (l = l0) as -> by congruence.

      assert (Hjq : j = q).
      {
        eapply nodup_locs_lookup_unique.
        - exact Hnodup.
        - exact Hloc.
        - exact Hloc_q.
      }

      exfalso.
      apply Hq_not_j.
      symmetry.
      exact Hjq.

    (* p は i 以外。
       以前から marked だった。 *)
    + assert (Hp_old :
        marks !! p = Some true).
      {
        rewrite list_lookup_insert_ne in Hp.
        - exact Hp.
        - congruence.
      }

      destruct (decide (q = i)) as [Heq_q | Hneq_q].

      (* q = i なら、今回 i を true にしたので OK *)
      * subst q.

        pose proof
          (lookup_lt_Some _ _ _ Hfalse)
          as Hi.

        rewrite list_lookup_insert_eq.
        -- done.
        -- exact Hi.

      (* q != i なら、以前の closed_except を使える *)
      * assert (Hq_old :
          marks !! q = Some true).
        {
          eapply Hclosed; eauto.
        }

        rewrite list_lookup_insert_ne.
        -- exact Hq_old.
        -- congruence.
Qed.


Lemma mark_from_rel_final_closed_unmarked
    (locs nexts : list loc)
    (marks marks_new : list bool)
    (start : nat) :
  NoDup locs ->
  all_unmarked marks ->
  mark_from_rel locs nexts marks start marks_new ->
  marks_closed locs nexts marks_new.
Proof.
  intros Hnodup Hunmarked Hrel.

  eapply mark_from_rel_final_closed.
  - exact Hnodup.
  - apply all_unmarked_closed_except.
    exact Hunmarked.
  - exact Hrel.
Qed.


(*
  completeness:

  start から reachable なノードは、
  mark_from 完了後には必ず true。
*)
Lemma mark_from_rel_complete
    (locs nexts : list loc)
    (marks marks_new : list bool)
    (start : nat) :
  NoDup locs ->
  all_unmarked marks ->
  mark_from_rel locs nexts marks start marks_new ->
  forall k,
    reachable_from locs nexts start k ->
    marks_new !! k = Some true.
Proof.
  intros Hnodup Hunmarked Hrel.

  pose proof
    (mark_from_rel_marks_start
      locs nexts marks marks_new start
      Hrel)
    as Hstart.

  pose proof
    (mark_from_rel_final_closed_unmarked
      locs nexts marks marks_new start
      Hnodup Hunmarked Hrel)
    as Hclosed.

  intros k Hreachable.

  induction Hreachable.

  (* start 自身 *)
  - exact Hstart.

  (* i が marked なら、
     successor j も closed 性より marked *)
  - eapply Hclosed.
    + exact IHHreachable.
    + exact H.
    + exact H0.
    + exact H1.
Qed.

Corollary mark_from_rel_complete_root
    (locs nexts : list loc)
    (marks marks_new : list bool) :
  NoDup locs ->
  all_unmarked marks ->
  mark_from_rel
    locs nexts marks 0%nat marks_new ->
  forall k,
    reachable locs nexts k ->
    marks_new !! k = Some true.
Proof.
  intros Hnodup Hunmarked Hrel k Hreach.

  unfold reachable in Hreach.

  eapply mark_from_rel_complete.
  - exact Hnodup.
  - exact Hunmarked.
  - exact Hrel.
  - exact Hreach.
Qed.


Theorem mark_from_rel_exact_root
    (locs nexts : list loc)
    (marks marks_new : list bool) :
  NoDup locs ->
  all_unmarked marks ->
  mark_from_rel
    locs nexts marks 0%nat marks_new ->
  forall k,
    marks_new !! k = Some true <->
    reachable locs nexts k.
Proof.
  intros Hnodup Hunmarked Hrel k.
  split.

  (* marked -> reachable *)
  - intro Hmarked.
    eapply mark_from_rel_sound_root.
    + exact Hunmarked.
    + exact Hrel.
    + exact Hmarked.

  (* reachable -> marked *)
  - intro Hreachable.
    eapply mark_from_rel_complete_root.
    + exact Hnodup.
    + exact Hunmarked.
    + exact Hrel.
    + exact Hreachable.
Qed.
