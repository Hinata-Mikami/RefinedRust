From refinedrust Require Import typing.
From rrstd.ptr.ptr.generated Require Import generated_specs_ptr.

Record rust_layout := mk_rust_layout {
  layout_sz : nat;
  layout_alignment : alignment_enum;
}.
Global Instance rust_layout_inh : Inhabited rust_layout.
Proof. exact (populate (mk_rust_layout inhabitant inhabitant)). Qed.

Canonical Structure rust_layoutRT := directRT rust_layout.

Definition alignment_enum_align_log2 (a : alignment_enum) : nat :=
  match a with
  | alignment_AlignmentEnum__Align1Shl0 => 0
  | alignment_AlignmentEnum__Align1Shl1 => 1
  | alignment_AlignmentEnum__Align1Shl2 => 2
  | alignment_AlignmentEnum__Align1Shl3 => 3
  | alignment_AlignmentEnum__Align1Shl4 => 4
  | alignment_AlignmentEnum__Align1Shl5 => 5
  | alignment_AlignmentEnum__Align1Shl6 => 6
  | alignment_AlignmentEnum__Align1Shl7 => 7
  | alignment_AlignmentEnum__Align1Shl8 => 8
  | alignment_AlignmentEnum__Align1Shl9 => 9
  | alignment_AlignmentEnum__Align1Shl10 => 10
  | alignment_AlignmentEnum__Align1Shl11 => 11
  | alignment_AlignmentEnum__Align1Shl12 => 12
  | alignment_AlignmentEnum__Align1Shl13 => 13
  | alignment_AlignmentEnum__Align1Shl14 => 14
  | alignment_AlignmentEnum__Align1Shl15 => 15
  | alignment_AlignmentEnum__Align1Shl16 => 16
  | alignment_AlignmentEnum__Align1Shl17 => 17
  | alignment_AlignmentEnum__Align1Shl18 => 18
  | alignment_AlignmentEnum__Align1Shl19 => 19
  | alignment_AlignmentEnum__Align1Shl20 => 20
  | alignment_AlignmentEnum__Align1Shl21 => 21
  | alignment_AlignmentEnum__Align1Shl22 => 22
  | alignment_AlignmentEnum__Align1Shl23 => 23
  | alignment_AlignmentEnum__Align1Shl24 => 24
  | alignment_AlignmentEnum__Align1Shl25 => 25
  | alignment_AlignmentEnum__Align1Shl26 => 26
  | alignment_AlignmentEnum__Align1Shl27 => 27
  | alignment_AlignmentEnum__Align1Shl28 => 28
  | alignment_AlignmentEnum__Align1Shl29 => 29
  | alignment_AlignmentEnum__Align1Shl30 => 30
  | alignment_AlignmentEnum__Align1Shl31 => 31
  | alignment_AlignmentEnum__Align1Shl32 => 32
  | alignment_AlignmentEnum__Align1Shl33 => 33
  | alignment_AlignmentEnum__Align1Shl34 => 34
  | alignment_AlignmentEnum__Align1Shl35 => 35
  | alignment_AlignmentEnum__Align1Shl36 => 36
  | alignment_AlignmentEnum__Align1Shl37 => 37
  | alignment_AlignmentEnum__Align1Shl38 => 38
  | alignment_AlignmentEnum__Align1Shl39 => 39
  | alignment_AlignmentEnum__Align1Shl40 => 40
  | alignment_AlignmentEnum__Align1Shl41 => 41
  | alignment_AlignmentEnum__Align1Shl42 => 42
  | alignment_AlignmentEnum__Align1Shl43 => 43
  | alignment_AlignmentEnum__Align1Shl44 => 44
  | alignment_AlignmentEnum__Align1Shl45 => 45
  | alignment_AlignmentEnum__Align1Shl46 => 46
  | alignment_AlignmentEnum__Align1Shl47 => 47
  | alignment_AlignmentEnum__Align1Shl48 => 48
  | alignment_AlignmentEnum__Align1Shl49 => 49
  | alignment_AlignmentEnum__Align1Shl50 => 50
  | alignment_AlignmentEnum__Align1Shl51 => 51
  | alignment_AlignmentEnum__Align1Shl52 => 52
  | alignment_AlignmentEnum__Align1Shl53 => 53
  | alignment_AlignmentEnum__Align1Shl54 => 54
  | alignment_AlignmentEnum__Align1Shl55 => 55
  | alignment_AlignmentEnum__Align1Shl56 => 56
  | alignment_AlignmentEnum__Align1Shl57 => 57
  | alignment_AlignmentEnum__Align1Shl58 => 58
  | alignment_AlignmentEnum__Align1Shl59 => 59
  | alignment_AlignmentEnum__Align1Shl60 => 60
  | alignment_AlignmentEnum__Align1Shl61 => 61
  | alignment_AlignmentEnum__Align1Shl62 => 62
  | alignment_AlignmentEnum__Align1Shl63 => 63
  end
.
Definition alignment_enum_align (a : alignment_enum) : nat :=
  (2^(alignment_enum_align_log2 a))%nat
.

Definition layout_alignment_log2_nat (rly : rust_layout) : nat :=
  alignment_enum_align_log2 rly.(layout_alignment).
Definition layout_alignment_nat (rly : rust_layout) : nat :=
  alignment_enum_align rly.(layout_alignment).

Definition rust_layout_to_layout (rly : rust_layout) : layout :=
  Layout rly.(layout_sz) (layout_alignment_log2_nat rly).

Global Coercion rust_layout_to_layout : rust_layout >-> layout.

