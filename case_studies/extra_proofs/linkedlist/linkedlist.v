From refinedrust Require Import typing.

Section linkedlist.
  Context `{!typeGS Σ} {rt : RT}.

  Definition linkedlist_node π (ty : type rt) sls (locs : list loc) i x : iProp Σ :=
    ∃ l lnext lprev : loc, ⌜locs !! i = Some l⌝ ∗
      ⌜(locs ++ [NULL_loc]) !! S i = Some lnext⌝ ∗
      ⌜(NULL_loc :: locs) !! i = Some lprev⌝ ∗
      guarded true (l ◁ₗ[π, Owned] #( *[#x; #lnext; #lprev]) @
        ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t]) ∗
      freeable_nz l (ly_size (use_struct_layout_alg' sls)) 1 HeapAlloc.

  Definition linkedlist_node_shared π κ (ty : type rt) sls (locs : list loc) prev_ptr i x : iProp Σ :=
    ∃ l lnext lprev : loc, ⌜locs !! i = Some l⌝ ∗
      ⌜(locs ++ [NULL_loc]) !! S i = Some lnext⌝ ∗
      ⌜(prev_ptr :: locs) !! i = Some lprev⌝ ∗
      guarded false (l ◁ₗ[π, Shared κ] #( *[#x; #lnext; #lprev]) @
        ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t]) ∗ True.

  Global Instance linkedlist_nodes_shareable π κ (ty : type rt) sls locs xs (assumptions : Prop) :
    Shareable π κ (ty_lfts ty) xs assumptions
      ([∗ list] i ↦ x ∈ xs, linkedlist_node π ty sls locs i x).
  Proof.
    apply big_sepL_shareable_lookup. intros i x.
    unfold linkedlist_node.
    apply exist_shareable. intros l.
    apply exist_shareable. intros next.
    apply exist_shareable. intros prev.
    assert (Hcanonical : (assumptions ∧ xs !! i = Some x) →
      IsXrfnImplies (rt2 := place_rfnRT (plistRT [rt; locRT; locRT]))
        xs (#( *[#x; #next; #prev]))).
    { intros [_ Hlook]. constructor. intros Houter.
      assert (Hx : IsXrfn x).
      { constructor. apply is_xrfn_list_iff in Houter.
        eapply Forall_lookup_1; eauto. }
      apply is_xrfn_proof. }
    apply _.
  Defined.
End linkedlist.
