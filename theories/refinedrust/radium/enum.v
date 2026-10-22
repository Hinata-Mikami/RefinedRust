From Stdlib.Logic Require Import ProofIrrelevance.
From stdpp Require Import list.
From radium Require Export struct.
Set Default Proof Using "Type".

(** First-class enum layouts.

  We do not model niche optimizations here. An enum consists of a
  discriminant at offset [0] and a shared data region at [el_data_offset].
  Every variant payload starts at this shared data offset and is described by
  its layout. *)

Definition enum_variant_list := list (var_name * layout).

Definition enum_variant_names (variants : enum_variant_list) : list var_name :=
  variants.*1.

Definition enum_variant_layouts (variants : enum_variant_list) : list layout :=
  variants.*2.

Definition enum_variant_index_of (variants : enum_variant_list) (n : var_name) : option nat :=
  fst <$> list_find (λ x, x.1 = n) variants.

Definition enum_variant_lookup (variants : enum_variant_list) (n : var_name) : option layout :=
  (λ x, x.2.2) <$> list_find (λ x, x.1 = n) variants.

Definition enum_variant_wf (data_offset : nat) (variant : var_name * layout) : Prop :=
  let ly := variant.2 in
  layout_wf ly ∧
  data_offset `mod` ly_align ly = 0.

Record enum_layout := {
  el_size : nat;
  el_align_log : nat;

  el_tag_it : int_type;

  el_data_offset : nat;
  el_variants : enum_variant_list;

  el_variants_nodup : bool_decide (NoDup (enum_variant_names el_variants));

  el_size_bounded : el_size < max_int ISize + 1;
  el_layout_wf : layout_wf {| ly_size := el_size; ly_align_log := el_align_log |};
  el_tag_align : ly_align (it_layout el_tag_it) ≤ ly_align {| ly_size := el_size; ly_align_log := el_align_log |};
  el_variant_align :
    Forall (λ variant : var_name * layout,
      ly_align variant.2 ≤ ly_align {| ly_size := el_size; ly_align_log := el_align_log |}) el_variants;

  el_tag_before_data : ly_size (it_layout el_tag_it) ≤ el_data_offset;

  el_variants_wf : Forall (enum_variant_wf el_data_offset) el_variants;
  el_variants_in_bounds :
    Forall (λ variant : var_name * layout, el_data_offset + ly_size variant.2 ≤ el_size) el_variants;
}.

Definition layout_of_enum (el : enum_layout) : layout := {|
  ly_size := el.(el_size);
  ly_align_log := el.(el_align_log);
|}.

Coercion layout_of_enum : enum_layout >-> layout.

Lemma enum_layout_eq el1 el2 :
  el1.(el_size) = el2.(el_size) →
  el1.(el_align_log) = el2.(el_align_log) →
  el1.(el_tag_it) = el2.(el_tag_it) →
  el1.(el_data_offset) = el2.(el_data_offset) →
  el1.(el_variants) = el2.(el_variants) →
  el1 = el2.
Proof. destruct el1, el2 => /= ?????. subst. f_equal; apply proof_irrelevance. Qed.

Lemma enum_variant_names_NoDup el :
  NoDup (enum_variant_names el.(el_variants)).
Proof.
  specialize (el_variants_nodup el). naive_solver.
Qed.

Lemma enum_layout_wf (el : enum_layout) :
  layout_wf el.
Proof.
  change (layout_wf (layout_of_enum el)).
  apply el_layout_wf.
Qed.

Lemma enum_variant_index_of_lookup el n i :
  enum_variant_index_of el.(el_variants) n = Some i ↔
  ∃ sl, el.(el_variants) !! i = Some (n, sl).
Proof.
  rewrite /enum_variant_index_of fmap_Some.
  split.
  - intros ([j [n' sl]] & Ha%list_find_Some & ->).
    simpl in Ha. destruct Ha as (? & -> & _). eauto.
  - intros (sl & Hlook).
    exists (i, (n, sl)). rewrite list_find_Some. split; last done.
    split; first done. split; first done.
    intros j [n' sl'] Hlook' Hlt Heq. simpl in Heq. subst.
    assert (i = j) as ->; last lia.
    eapply (NoDup_lookup (enum_variant_names el.(el_variants)) i j n).
    + apply enum_variant_names_NoDup.
    + rewrite /enum_variant_names list_lookup_fmap Hlook. done.
    + rewrite /enum_variant_names list_lookup_fmap Hlook'. done.
Qed.

Lemma enum_variant_lookup_Some variants n sl :
  enum_variant_lookup variants n = Some sl ↔
  ∃ i, variants !! i = Some (n, sl) ∧
    (∀ j variant, variants !! j = Some variant → (j < i)%nat → variant.1 ≠ n).
Proof.
  rewrite /enum_variant_lookup fmap_Some.
  split.
  - intros ([i [n' sl']] & Ha%list_find_Some & ?); simplify_eq/=.
    destruct Ha as (? & -> & ?). eauto.
  - intros (i & Hlook & Hnotin).
    exists (i, (n, sl)). rewrite list_find_Some. naive_solver.
Qed.

Lemma enum_variant_lookup_is_Some el n sl :
  (n, sl) ∈ el.(el_variants) →
  enum_variant_lookup el.(el_variants) n = Some sl.
Proof.
  intros Hel.
  apply enum_variant_lookup_Some.
  apply list_elem_of_lookup_1 in Hel as [i Hlook].
  exists i. split; first done.
  intros j [n' sl'] Hlook' Hlt Heq. simpl in Heq. subst.
  assert (i = j) as ->; last lia.
  eapply (NoDup_lookup (enum_variant_names el.(el_variants)) i j n).
  - apply enum_variant_names_NoDup.
  - rewrite /enum_variant_names list_lookup_fmap Hlook. done.
  - rewrite /enum_variant_names list_lookup_fmap Hlook'. done.
Qed.

Lemma enum_variant_lookup_in el n sl :
  enum_variant_lookup el.(el_variants) n = Some sl →
  (n, sl) ∈ el.(el_variants).
Proof.
  rewrite enum_variant_lookup_Some.
  intros (i & Hlook & _). by eapply list_elem_of_lookup_2.
Qed.

Lemma enum_variant_lookup_wf el n sl :
  enum_variant_lookup el.(el_variants) n = Some sl →
  layout_wf sl ∧
  el.(el_data_offset) `mod` ly_align sl = 0.
Proof.
  intros Hlook.
  apply enum_variant_lookup_in in Hlook.
  pose proof (proj1 (Forall_forall _ _) (el_variants_wf el) (n, sl) Hlook) as Hwf.
  exact Hwf.
Qed.

Lemma enum_variant_lookup_in_bounds el n sl :
  enum_variant_lookup el.(el_variants) n = Some sl →
  el.(el_data_offset) + ly_size sl ≤ el.(el_size).
Proof.
  intros Hlook.
  apply enum_variant_lookup_in in Hlook.
  pose proof (proj1 (Forall_forall _ _) (el_variants_in_bounds el) (n, sl) Hlook) as Hb.
  exact Hb.
Qed.

Definition enum_tag_padding_ly (el : enum_layout) : layout :=
  Layout (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it))) 0.

Definition enum_tail_padding_ly (el : enum_layout) (variant_ly : layout) : layout :=
  Layout (el.(el_size) - el.(el_data_offset) - ly_size variant_ly) 0.

Lemma enum_variant_layout_bounds el variant variant_ly :
  enum_variant_lookup el.(el_variants) variant = Some variant_ly →
  let tag_size := ly_size (it_layout el.(el_tag_it)) in
  let data_offset := el.(el_data_offset) in
  let variant_size := ly_size variant_ly in
  tag_size ≤ data_offset ∧ data_offset + variant_size ≤ el.(el_size).
Proof.
  intros Hvariant.
  split.
  - apply el_tag_before_data.
  - apply (enum_variant_lookup_in_bounds el variant variant_ly). done.
Qed.

Lemma enum_tag_has_layout_loc (el : enum_layout) l :
  l `has_layout_loc` el →
  l `has_layout_loc` it_layout el.(el_tag_it).
Proof.
  intros Hly.
  eapply has_layout_loc_trans; first exact Hly.
  apply ly_align_log_ly_align_le_iff.
  change (ly_align (it_layout el.(el_tag_it)) ≤ ly_align {| ly_size := el.(el_size); ly_align_log := el.(el_align_log) |})%nat.
  apply Nat2Z.inj_le. apply el_tag_align.
Qed.

Lemma enum_payload_has_layout_loc (el : enum_layout) variant variant_ly l :
  l `has_layout_loc` el →
  enum_variant_lookup el.(el_variants) variant = Some variant_ly →
  (l +ₗ el.(el_data_offset)) `has_layout_loc` variant_ly.
Proof.
  intros Hly Hvariant.
  apply has_layout_loc_shift_loc_nat.
  - eapply has_layout_loc_trans; first exact Hly.
    apply ly_align_log_ly_align_le_iff.
    pose proof (enum_variant_lookup_in _ _ _ Hvariant) as Hin.
    change (ly_align variant_ly ≤ ly_align {| ly_size := el.(el_size); ly_align_log := el.(el_align_log) |})%nat.
    apply Nat2Z.inj_le.
    exact (proj1 (Forall_forall _ _) (el_variant_align el) (variant, variant_ly) Hin).
  - apply enum_variant_lookup_wf in Hvariant as [_ Hmod].
    apply Nat2Z.divide.
    apply Z.mod_divide; last done.
    rewrite /ly_align. lia.
Qed.

Global Hint Resolve enum_layout_wf : core.
