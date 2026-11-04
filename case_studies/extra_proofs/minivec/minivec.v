From radium Require Import lang notation.
From refinedrust Require Import typing.

Lemma list_lookup_insert_Some' {A} (l : list A) i x j y :
  <[i:=x]>l !! j = Some y ↔
    (i = j → x = y ∧ (j < length l)%nat) ∧ (i ≠ j → l !! j = Some y).
Proof. rewrite list_lookup_insert_Some. destruct (decide (i = j)); naive_solver. Qed.

Lemma list_eq_singleton {A} (l : list A) x:
  l = [x] ↔ (length l ≤ 1)%nat ∧ l !! 0%nat = Some x.
Proof.
  split.
  - move => ->. naive_solver.
  - move => [??]. destruct l as [|? [|]]; naive_solver lia.
Qed.

Global Instance simpl_lookup_total_insert_eq {A} `{!Inhabited A} (l : list A) i j x x' `{!CanSolve (i = j)} `{!CanSolve (j < length l)%nat}:
  SimplBothRel (=) (<[i := x']> l !!! j) (x) (x = x').
Proof.
  unfold SimplBothRel, CanSolve in *; subst.
  rewrite list_lookup_total_insert_eq; naive_solver.
Qed.

#[universes(polymorphic)]
Definition extract_val {rt : RT} (r : place_rfn rt) := if r is #r then Some r else None.

Section project_vec_els.
  Context {rt : RT}.
  Set Universe Polymorphism.

  Global Instance is_xrfn_minivec_nested_fmap (xr : list (RT_xt rt)) :
    IsXrfn (<#> <$#@{rt}> xr).
  Proof.
    constructor. exists xr. rewrite -list_fmap_compose.
    apply list_fmap_ext. intros. done.
  Qed.

  Global Instance is_xrfn_minivec_nested_fmap_lookup_total
      (xr : list (RT_xt rt)) i `{!CanSolve (i < length xr)%nat} :
    IsXrfn ((<#> <$#@{rt}> xr) !!! i).
  Proof.
    unfold CanSolve in *.
    destruct (lookup_lt_is_Some_2 xr i ltac:(lia)) as (x & Hx).
    constructor. exists x.
    erewrite list_lookup_total_correct; last by rewrite !list_lookup_fmap Hx.
    done.
  Qed.

  Definition project_vec_els (len : nat) (els : list (place_rfn (option (place_rfn rt))))
    : list (place_rfn rt) :=
    (λ x, default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)) <$> (take len els).

  Lemma project_vec_els_length len els :
    length (project_vec_els len els) = (len `min` length els)%nat.
  Proof. by rewrite /project_vec_els length_fmap length_take. Qed.

  Lemma project_vec_els_insert_lt (len : nat) (i : nat) x els:
    (i < len)%nat →
    project_vec_els len (<[i:=x]> els) =
       <[i:=default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)]>
         (project_vec_els len els).
  Proof.
    rewrite {1}/project_vec_els => ?. by rewrite take_insert_lt // list_fmap_insert.
  Qed.
  Lemma project_vec_els_insert_ge (len : nat) (i : nat) x els:
    (len ≤ i)%nat →
    project_vec_els len (<[i:=x]> els) = project_vec_els len els.
  Proof. rewrite {1}/project_vec_els => ?. by rewrite take_insert_ge. Qed.

  Lemma project_vec_els_lookup_mono (len : nat) (i : nat) els len' els':
    (i < len `min` len')%nat →
    els !! i = els' !! i →
    project_vec_els len els !! i = project_vec_els len' els' !! i.
  Proof.
    move => ? Hels. rewrite /project_vec_els !list_lookup_fmap. f_equal.
    rewrite !lookup_take_lt //; lia.
  Qed.

  Lemma project_vec_els_take len els len':
    take len' (project_vec_els len els) = project_vec_els (len' `min` len) els.
  Proof. rewrite /project_vec_els. by rewrite !fmap_take take_take. Qed.
  Lemma project_vec_els_take_r len els :
    project_vec_els len els = project_vec_els len (take len els).
  Proof. rewrite /project_vec_els. f_equal. rewrite take_take. f_equal. lia. Qed.
  Lemma project_vec_els_drop len els len':
    drop len' (project_vec_els len els) = project_vec_els (len - len') (drop len' els).
  Proof. rewrite /project_vec_els. by rewrite -!fmap_drop skipn_firstn_comm. Qed.

  Lemma project_vec_els_lookup (len i : nat) els x :
    (i < len)%nat →
    els !! i = Some (#(Some x)) →
    project_vec_els len els !! i = Some x.
  Proof.
    intros Hi Hlook. rewrite /project_vec_els.
    simpl.
    rewrite list_lookup_fmap.
    rewrite lookup_take_lt; last lia.
    rewrite Hlook. done.
  Qed.

  Lemma project_vec_els_length' xs x2 len :
    <#> <$#@{rt}> xs = project_vec_els len x2 → length xs ≤ min len (length x2).
  Proof.
    intros Ha.
    assert (length (<#> <$#> xs) = length (project_vec_els len x2)) as Hlen.
    { rewrite Ha. done. }
    rewrite length_map project_vec_els_length in Hlen.
    rewrite length_map in Hlen.
    lia.
  Qed.
  Global Instance is_xrfn_minivec_vec_hint
      (els : list (place_rfn (option (place_rfn rt))))
      (xr : list (RT_xt rt)) len cap:
    TCDone (∀ i : nat, (0 ≤ i < len)%nat →
      els !! i = Some (#(Some ((PlaceIn ∘ RT_xrt rt <$> xr) !!! i)))) →
    TCDone (∀ i : nat, (len ≤ i < cap)%nat → els !! i = Some (#None)) →
    TCDone (length els = cap) →
    TCDone ((PlaceIn ∘ RT_xrt rt <$> xr) = project_vec_els len els) →
    IsXrfn els.
  Proof.
    unfold TCDone. intros Hlook1 Hlook2 Hlen Hx.
    constructor. apply is_xrfn_list_iff, Forall_forall.
    intros x (i & Hlook)%list_elem_of_lookup_1.
    have Hiels : (i < length els)%nat by apply lookup_lt_Some in Hlook.
    destruct (decide (i < len)) as [Hi | Hi].
    - opose proof (Hlook1 i _) as Hlook'; first lia.
      rewrite Hlook in Hlook'. simplify_eq.
      have Hixr : (i < length ((PlaceIn ∘ RT_xrt rt) <$> xr))%nat.
      { rewrite Hx project_vec_els_length. lia. }
      rewrite length_fmap in Hixr.
      destruct (lookup_lt_is_Some_2 xr i Hixr) as (xri & Hxri).
      erewrite list_lookup_total_correct; last by rewrite list_lookup_fmap Hxri.
      apply is_xrfn_proof.
    - opose proof (Hlook2 i _) as Hlook'; first lia.
      rewrite Hlook in Hlook'. simplify_eq. apply is_xrfn_proof.
  Qed.
End project_vec_els.

Global Typeclasses Opaque project_vec_els.
Global Opaque project_vec_els.

Global Hint Rewrite @project_vec_els_length : lithium_rewrite.
Global Hint Rewrite @list_fmap_compose : lithium_rewrite.
