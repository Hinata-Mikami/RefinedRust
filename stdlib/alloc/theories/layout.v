From refinedrust Require Import typing.
From rrstd.ptr.ptr.generated Require Import generated_specs_ptr.
From rrstd.ptr.theories Require Import specs.

Record rust_layout := mk_rust_layout {
  layout_sz : nat;
  layout_alignment : alignment_enum;
}.
Global Instance rust_layout_inh : Inhabited rust_layout.
Proof. exact (populate (mk_rust_layout inhabitant inhabitant)). Qed.

(* TODO: move? *)
Lemma is_power_of_two_log2_pow n :
  is_power_of_two n →
  2^(Nat.log2 n) = n.
Proof.
  intros (m & ->).
  rewrite Nat.log2_pow2; lia.
Qed.
Lemma is_power_of_two_Z_log2_pow z :
  is_power_of_two (Z.to_nat z) →
  2^(Z.log2 z) = z.
Proof.
  intros (m & Heq).
  assert (z = 2^m) as -> by lia.
  rewrite Z.log2_pow2; lia.
Qed.

Canonical Structure rust_layoutRT := directRT rust_layout.

Definition layout_alignment_log2_nat (rly : rust_layout) : nat :=
  alignment_to_align_log2 rly.(layout_alignment).
Definition layout_alignment_nat (rly : rust_layout) : nat :=
  alignment_to_align_nat rly.(layout_alignment).

Definition rust_layout_to_layout (rly : rust_layout) : layout :=
  Layout rly.(layout_sz) (layout_alignment_log2_nat rly).

Global Coercion rust_layout_to_layout : rust_layout >-> layout.

Lemma ly_align_of_rust_layout_align sz (align : Z) :
  is_power_of_two (Z.to_nat align) →
  align ∈ usize →
  (ly_align (rust_layout_to_layout (mk_rust_layout sz (alignment_of_align align)))) = Z.to_nat align.
Proof.
  intros Hpow Hel.
  rewrite /ly_align/=.
  rewrite /layout_alignment_log2_nat/=.

  rewrite /alignment_of_align.
  rewrite alignment_to_from_log2.
  - rewrite -(Znat.Z2Nat.inj_pow 2); [ | lia | apply Z.log2_nonneg].
    rewrite is_power_of_two_Z_log2_pow; last done.
    lia.
  - opose proof (power_of_two_log2_usize_in_bounds align _ _); [ solve_goal | done | ].
    lia.
Qed.
