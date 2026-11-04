From refinedrust Require Import typing.

#[universes(polymorphic)]
Definition extract_val {rt : RT} (r : place_rfn rt) := if r is #r then Some r else None.

Section project_vec_els.
  Context {rt : RT}.
  Set Universe Polymorphism.

  Definition project_vec_els (len : nat) (els : list (place_rfn (option (place_rfn rt))))
    : list (place_rfn rt) :=
    (λ x, default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)) <$> (take len els).

  Lemma project_vec_els_lookup_Some len i els x :
    project_vec_els len els !! i = Some x →
    ∃ x', els !! i = Some x' ∧ x = default (👻 inhabitant) (extract_val x' ≫= id) ∧ (i < len)%nat. 
  Proof.
    rewrite /project_vec_els.
    rewrite list_lookup_fmap_Some.
    intros (x' & Heq & Hlook).
    apply lookup_take_Some in Hlook as (Hlook & ?).
    eauto.
  Qed.

  Lemma project_vec_els_length len els :
    length (project_vec_els len els) = (len `min` length els)%nat.
  Proof. by rewrite /project_vec_els length_fmap length_take. Qed.


  Global Instance is_xrfn_vec_hint
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
