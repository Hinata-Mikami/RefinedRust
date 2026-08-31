From caesium Require Import lang notation.
From refinedrust Require Import typing.


(* start 番目から i 番目へ next を0回以上辿って到達できる *)
Inductive reachable_from
    (locs nexts : list loc)
    (start : nat) : nat -> Prop :=

| reachable_from_refl :
    reachable_from locs nexts start start

| reachable_from_step
    (i j : nat) (l : loc) :
    reachable_from locs nexts start i ->
    nexts !! i = Some l ->
    l <> NULL_loc ->
    locs !! j = Some l ->
    reachable_from locs nexts start j.


(* GC の root は0番目 *)
Definition reachable
    (locs nexts : list loc)
    (i : nat) : Prop :=
  reachable_from locs nexts 0%nat i.


(* 全ノードが未マーク *)
Definition all_unmarked (marks : list bool) : Prop :=
  Forall (fun m => m = false) marks.


(*
  mark_from を1回実行したときに
  marks が marks_new にどう変化するかを表す関係
*)
Inductive mark_from_rel
    (locs nexts : list loc) :
    list bool -> nat -> list bool -> Prop :=
| mark_from_rel_marked
    (marks : list bool) (i : nat) :
    marks !! i = Some true ->
    mark_from_rel locs nexts marks i marks

| mark_from_rel_null
    (marks : list bool) (i : nat) (l : loc) :
    marks !! i = Some false ->
    nexts !! i = Some l ->
    loc_a l = 0 ->
    mark_from_rel
      locs nexts
      marks i
      (<[i := true]> marks)

| mark_from_rel_next
    (marks marks_new : list bool)
    (i j : nat) (l : loc) :
    marks !! i = Some false ->
    nexts !! i = Some l ->
    l <> NULL_loc ->
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