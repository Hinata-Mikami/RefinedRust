From refinedrust Require Import typing.

(** Alignment *)
(* Auto-generated representation of alignment_enum *)
Inductive alignment_enum  :=
  | _Align1Shl0
  | _Align1Shl1
  | _Align1Shl2
  | _Align1Shl3
  | _Align1Shl4
  | _Align1Shl5
  | _Align1Shl6
  | _Align1Shl7
  | _Align1Shl8
  | _Align1Shl9
  | _Align1Shl10
  | _Align1Shl11
  | _Align1Shl12
  | _Align1Shl13
  | _Align1Shl14
  | _Align1Shl15
  | _Align1Shl16
  | _Align1Shl17
  | _Align1Shl18
  | _Align1Shl19
  | _Align1Shl20
  | _Align1Shl21
  | _Align1Shl22
  | _Align1Shl23
  | _Align1Shl24
  | _Align1Shl25
  | _Align1Shl26
  | _Align1Shl27
  | _Align1Shl28
  | _Align1Shl29
  | _Align1Shl30
  | _Align1Shl31
  | _Align1Shl32
  | _Align1Shl33
  | _Align1Shl34
  | _Align1Shl35
  | _Align1Shl36
  | _Align1Shl37
  | _Align1Shl38
  | _Align1Shl39
  | _Align1Shl40
  | _Align1Shl41
  | _Align1Shl42
  | _Align1Shl43
  | _Align1Shl44
  | _Align1Shl45
  | _Align1Shl46
  | _Align1Shl47
  | _Align1Shl48
  | _Align1Shl49
  | _Align1Shl50
  | _Align1Shl51
  | _Align1Shl52
  | _Align1Shl53
  | _Align1Shl54
  | _Align1Shl55
  | _Align1Shl56
  | _Align1Shl57
  | _Align1Shl58
  | _Align1Shl59
  | _Align1Shl60
  | _Align1Shl61
  | _Align1Shl62
  | _Align1Shl63 .

Definition alignment_enumRT  : RT :=
  (directRT (alignment_enum)).
Canonical Structure alignment_enumRT.

#[global] Instance: (Inhabited alignment_enum).
Proof.
  solve_inhabited.
Qed.

Definition alignment_to_align_log2 (a : alignment_enum) : nat :=
  match a with
  | _Align1Shl0 => 0
  | _Align1Shl1 => 1
  | _Align1Shl2 => 2
  | _Align1Shl3 => 3
  | _Align1Shl4 => 4
  | _Align1Shl5 => 5
  | _Align1Shl6 => 6
  | _Align1Shl7 => 7
  | _Align1Shl8 => 8
  | _Align1Shl9 => 9
  | _Align1Shl10 => 10
  | _Align1Shl11 => 11
  | _Align1Shl12 => 12
  | _Align1Shl13 => 13
  | _Align1Shl14 => 14
  | _Align1Shl15 => 15
  | _Align1Shl16 => 16
  | _Align1Shl17 => 17
  | _Align1Shl18 => 18
  | _Align1Shl19 => 19
  | _Align1Shl20 => 20
  | _Align1Shl21 => 21
  | _Align1Shl22 => 22
  | _Align1Shl23 => 23
  | _Align1Shl24 => 24
  | _Align1Shl25 => 25
  | _Align1Shl26 => 26
  | _Align1Shl27 => 27
  | _Align1Shl28 => 28
  | _Align1Shl29 => 29
  | _Align1Shl30 => 30
  | _Align1Shl31 => 31
  | _Align1Shl32 => 32
  | _Align1Shl33 => 33
  | _Align1Shl34 => 34
  | _Align1Shl35 => 35
  | _Align1Shl36 => 36
  | _Align1Shl37 => 37
  | _Align1Shl38 => 38
  | _Align1Shl39 => 39
  | _Align1Shl40 => 40
  | _Align1Shl41 => 41
  | _Align1Shl42 => 42
  | _Align1Shl43 => 43
  | _Align1Shl44 => 44
  | _Align1Shl45 => 45
  | _Align1Shl46 => 46
  | _Align1Shl47 => 47
  | _Align1Shl48 => 48
  | _Align1Shl49 => 49
  | _Align1Shl50 => 50
  | _Align1Shl51 => 51
  | _Align1Shl52 => 52
  | _Align1Shl53 => 53
  | _Align1Shl54 => 54
  | _Align1Shl55 => 55
  | _Align1Shl56 => 56
  | _Align1Shl57 => 57
  | _Align1Shl58 => 58
  | _Align1Shl59 => 59
  | _Align1Shl60 => 60
  | _Align1Shl61 => 61
  | _Align1Shl62 => 62
  | _Align1Shl63 => 63
  end
.
Definition alignment_to_align_nat (a : alignment_enum) : nat :=
  (2^(alignment_to_align_log2 a))%nat
.
Definition alignment_to_align (a : alignment_enum) : Z :=
  (2^(alignment_to_align_log2 a))
.

Definition try_alignment_of_align_log2 (n : nat) : option alignment_enum :=
  match n with
  | 0 => Some _Align1Shl0
  | 1 => Some _Align1Shl1
  | 2 => Some _Align1Shl2
  | 3 => Some _Align1Shl3
  | 4 => Some _Align1Shl4
  | 5 => Some _Align1Shl5
  | 6 => Some _Align1Shl6
  | 7 => Some _Align1Shl7
  | 8 => Some _Align1Shl8
  | 9 => Some _Align1Shl9
  | 10 => Some _Align1Shl10
  | 11 => Some _Align1Shl11
  | 12 => Some _Align1Shl12
  | 13 => Some _Align1Shl13
  | 14 => Some _Align1Shl14
  | 15 => Some _Align1Shl15
  | 16 => Some _Align1Shl16
  | 17 => Some _Align1Shl17
  | 18 => Some _Align1Shl18
  | 19 => Some _Align1Shl19
  | 20 => Some _Align1Shl20
  | 21 => Some _Align1Shl21
  | 22 => Some _Align1Shl22
  | 23 => Some _Align1Shl23
  | 24 => Some _Align1Shl24
  | 25 => Some _Align1Shl25
  | 26 => Some _Align1Shl26
  | 27 => Some _Align1Shl27
  | 28 => Some _Align1Shl28
  | 29 => Some _Align1Shl29
  | 30 => Some _Align1Shl30
  | 31 => Some _Align1Shl31
  | 32 => Some _Align1Shl32
  | 33 => Some _Align1Shl33
  | 34 => Some _Align1Shl34
  | 35 => Some _Align1Shl35
  | 36 => Some _Align1Shl36
  | 37 => Some _Align1Shl37
  | 38 => Some _Align1Shl38
  | 39 => Some _Align1Shl39
  | 40 => Some _Align1Shl40
  | 41 => Some _Align1Shl41
  | 42 => Some _Align1Shl42
  | 43 => Some _Align1Shl43
  | 44 => Some _Align1Shl44
  | 45 => Some _Align1Shl45
  | 46 => Some _Align1Shl46
  | 47 => Some _Align1Shl47
  | 48 => Some _Align1Shl48
  | 49 => Some _Align1Shl49
  | 50 => Some _Align1Shl50
  | 51 => Some _Align1Shl51
  | 52 => Some _Align1Shl52
  | 53 => Some _Align1Shl53
  | 54 => Some _Align1Shl54
  | 55 => Some _Align1Shl55
  | 56 => Some _Align1Shl56
  | 57 => Some _Align1Shl57
  | 58 => Some _Align1Shl58
  | 59 => Some _Align1Shl59
  | 60 => Some _Align1Shl60
  | 61 => Some _Align1Shl61
  | 62 => Some _Align1Shl62
  | 63 => Some _Align1Shl63
  | _ => None
  end%nat
.
Definition alignment_of_align_log2 (n : nat) : alignment_enum :=
  default _Align1Shl0 (try_alignment_of_align_log2 n).
Arguments alignment_of_align_log2 : simpl never.

Definition alignment_of_align (z : Z) : alignment_enum :=
  alignment_of_align_log2 (Z.to_nat (Z.log2 z)).
Arguments alignment_of_align : simpl never.

Lemma power_of_two_log2_usize_in_bounds z :
  z ∈ usize →
  is_power_of_two (Z.to_nat z) →
  0 ≤ Z.log2 z ≤ 63.
Proof.
  intros [Hel1 Hel2].
  intros (m & Heq).
  opose proof (MinInt_unsigned_0 usize _) as Hmin; first done.
  rewrite Hmin in Hel1.
  rewrite MaxInt_eq in Hel2. unfold max_int in Hel2. simpl in Hel2.
  unfold int_modulus, bits_per_int, bytes_per_int, bits_per_byte in Hel2.
  simpl in Hel2.
  assert (z = Z.pow 2 m) as Heq' by lia. clear Heq.
  subst z.
  apply Z.log2_le_pow2 in Hel2; last lia.
  assert (Z.log2 (2 ^ (8%nat * 8) - 1) = 63) as Heq.
  { done. }
  rewrite Heq in Hel2.
  replace 0 with (Z.log2 1) by done.
  replace 63 with (Z.log2 (2^63)).
  split; apply Z.log2_le_mono; first lia.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma try_alignment_from_to_log2 (al : alignment_enum) :
  try_alignment_of_align_log2 (alignment_to_align_log2 al) = Some al.
Proof.
  destruct al; done.
Qed.
Lemma alignment_from_to_log2 (al : alignment_enum) :
  alignment_of_align_log2 (alignment_to_align_log2 al) = al.
Proof.
  rewrite /alignment_of_align_log2.
  rewrite try_alignment_from_to_log2.
  done.
Qed.

Lemma alignment_to_from_log2 (n : nat) :
  0 ≤ n ≤ 63 →
  alignment_to_align_log2 (alignment_of_align_log2 n) = n.
Proof.
  intros Hle.
  do 64 (destruct n as [ | n]; first done).
  lia.
Qed.

Lemma alignment_from_to al :
  alignment_of_align (alignment_to_align al) = al.
Proof.
  unfold alignment_of_align, alignment_to_align.
  rewrite Z.log2_pow2; last lia.
  rewrite Nat2Z.id.
  apply alignment_from_to_log2.
Qed.
Lemma alignment_to_from (z : Z) :
  z ∈ usize →
  is_power_of_two (Z.to_nat z) →
  alignment_to_align (alignment_of_align z) = z.
Proof.
  rewrite /alignment_to_align /alignment_of_align.
  intros Husize Hpower.
  rewrite alignment_to_from_log2.
  - destruct Husize as [Hel1 Hel2].
    opose proof (MinInt_unsigned_0 usize _) as Hmin; first done.
    rewrite Hmin in Hel1.
    rewrite Z2Nat.id; last apply Z.log2_nonneg.
    destruct Hpower as (m & Heq).
    assert (z = 2^m) by lia. subst z. clear Heq.
    rewrite Z.log2_pow2; lia.
  - opose proof (power_of_two_log2_usize_in_bounds z Husize Hpower).
    lia.
Qed.

Lemma alignment_in_bounds al : 
  alignment_to_align al ≤ MaxInt usize.
Proof.
  unfold alignment_to_align. 
  trans (2^63).
  { destruct al; simpl; lia. }
  rewrite MaxInt_eq.
  unfold_common_caesium_defs.
  simpl. lia.
Qed.

(* ptr::copy *)
Definition sublist_lookup' {A} (i n : nat) (l : list A) : list A :=
  take n (drop i l).
Definition ptr_copy_result {A} (off_src : Z) (off_dst : Z) (count : nat) (xs : list A) : list A :=
  (*let wipe_src := list_inserts (Z.to_nat off_src) (replicate count (#None)) xs in*)
  let ins_dst := list_inserts (Z.to_nat off_dst) (sublist_lookup' (Z.to_nat off_src) count xs) xs in
  ins_dst.


(* const_ptr::offset / mut_ptr::offset *)
Inductive trace_offset :=
  | TraceOffset (offset : Z).


(* with_addr *)
Definition with_addr (l : loc) (a : addr) : loc :=
  Loc l.(loc_p) a.
Arguments with_addr : simpl never.
