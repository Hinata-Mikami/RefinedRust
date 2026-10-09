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

Section vec_shareable.
  Context `{!typeGS Σ} {rt : RT}.

  Global Program Instance shareable_minivec_vec
      (π : thread_id) (κ : lft) (ty : type rt)
      (inner : plist (RT_rt ∘ place_rfnRT) [prodRT locRT natRT; ZRT])
      (xs : list (place_rfn rt)) :
    Shareable π κ (ty_lfts ty) xs
      (∃ (cap : nat) (l : loc) (len : nat)
          (els : list (place_rfn (option (place_rfn rt)))),
        ⌜inner = -[#(l, cap); #(Z.of_nat len)]⌝ ∗
        guarded true (l ◁ₗ[π, Owned] #els @ ◁ array_t cap (maybe_uninit ty)) ∗
        ⌜xs = project_vec_els len els⌝ ∗
        ⌜∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))⌝ ∗
        ⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝ ∗
        ⌜length els = cap⌝ ∗ ⌜len = length xs⌝ ∗ ⌜len ≤ cap⌝ ∗
        ⌜if decide (size_of_st (ty_syn_type ty MetaNone) = 0%nat)
          then cap = Z.to_nat (MaxInt USize)
          else size_of_array_in_bytes (ty_syn_type ty MetaNone) cap ≤ MaxInt ISize⌝ ∗
        True)%I := {|
      shareable_prop :=
        (∃ (cap : nat) (l : loc) (len : nat)
            (els : list (place_rfn (option (place_rfn rt)))),
          ⌜inner = -[#(l, cap); #(Z.of_nat len)]⌝ ∗
          guarded false (l ◁ₗ[π, Shared κ] #els @ ◁ array_t cap (maybe_uninit ty)) ∗
          ⌜xs = project_vec_els len els⌝ ∗
          ⌜∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))⌝ ∗
          ⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝ ∗
          ⌜length els = cap⌝ ∗ ⌜len = length xs⌝ ∗ ⌜len ≤ cap⌝ ∗
          ⌜if decide (size_of_st (ty_syn_type ty MetaNone) = 0%nat)
            then cap = Z.to_nat (MaxInt USize)
            else size_of_array_in_bytes (ty_syn_type ty MetaNone) cap ≤ MaxInt ISize⌝ ∗
          True)%I
    |}.
  Next Obligation.
    intros π κ ty inner xs Hxsxr F G q HF.
    iIntros "#CTX Hna Htok1 Htok2 Hb Hcont".
    iPoseProof "CTX" as "#(LFT & LLCTX)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as "(%cap & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%l & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%len & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%els & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first done.
    iMod (bor_persistent with "LFT Heq Htok1") as "(>%Hinner & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hg & Hrest)"; first done.
    iMod (bor_persistent with "LFT Hrest Htok1") as "(>Hrest & Htok1)"; first done.
    iDestruct "Hrest" as "(%Hxs & %Hinit & %Huninit & %Helslen & %Hlen & %Hcap & %Hsize & _)".
    destruct Hxsxr as (xr & Hxsxr). subst xs.
    have Helsxr : is_xrfn els by apply is_xrfn_proof.
    have Helsplacexr : is_xrfn (#els).
    { destruct Helsxr as (elsxr & ->). eexists elsxr. done. }
    iPoseProof (ltype_own_ofty_share' π F κ (ty_lfts ty) q l
      (array_t cap (maybe_uninit ty)) (#els)
      with "CTX Hna Htok1 Htok2 Hg") as "Hstep".
    { done. }
    { exact Helsplacexr. }
    { repeat rewrite ty_lfts_unfold /=. set_solver. }
    iApply (logical_step_compose with "Hcont").
    iApply (logical_step_wand with "Hstep").
    iModIntro. iIntros "(Hg & Htok1 & Htok2) Hclose".
    iApply "Hclose". iFrame "Htok1 Htok2".
    iExists cap, l, len, els. iFrame "Hg". done.
  Qed.
End vec_shareable.

Global Hint Extern 10 (Shareable _ _ _ _ _) =>
  apply shareable_minivec_vec : typeclass_instances.
