From Equations Require Export Equations.
From radium Require Import val.
From refinedrust Require Import base util.
From refinedrust Require Import options.

(** ** op_types and mem_casts *)

Definition is_int_ot (ot : op_type) (it : int_type) : Prop :=
  match ot with
    | IntOp it' => it = it'
    | UntypedOp ly => ly = it_layout it
    | _ => False
  end.
Definition is_bool_ot (ot : op_type) : Prop :=
  match ot with | BoolOp => True | UntypedOp ly => ly = it_layout U8 | _ => False end.
Definition is_char_ot (ot : op_type) : Prop :=
  match ot with | CharOp => True | UntypedOp ly => ly = it_layout U32 | _ => False end.
Definition is_ptr_ot (ot : op_type) : Prop :=
  match ot with | PtrOp => True | UntypedOp ly => ly = void* | _ => False end.
Definition is_unit_ot (ot : op_type) : Prop :=
  match ot with | StructOp sl ots => sl = unit_sl ∧ ots = [] | UntypedOp ly => ly = unit_sl | _ => False end.

Lemma is_int_ot_layout it ot:
  is_int_ot ot it → ot_layout ot = it_layout it.
Proof.
  destruct ot => //=; naive_solver.
Qed.
Lemma is_int_ot_size ot it :
  is_int_ot ot it → (ly_size it ≤ MaxInt ISize)%Z.
Proof.
  intros. apply it_size_bounded.
Qed.

Lemma is_bool_ot_layout ot :
  is_bool_ot ot → ot_layout ot = it_layout U8.
Proof. destruct ot => //. Qed.

Lemma is_char_ot_layout ot :
  is_char_ot ot → ot_layout ot = it_layout U32.
Proof. destruct ot => //. Qed.

Lemma is_ptr_ot_layout ot:
  is_ptr_ot ot → ot_layout ot = void*.
Proof. by destruct ot => //= ->. Qed.

Lemma is_unit_ot_layout ot :
  is_unit_ot ot → ot_layout ot = unit_sl.
Proof.
  destruct ot => //=. by intros [-> ->].
Qed.

Lemma mem_cast_UntypedOp v ly st :
  v `has_layout_val` ly →
  mem_cast v (UntypedOp ly) st = v.
Proof.
  intros Hly. rewrite /mem_cast. simp decode_op_val.
  rewrite bool_decide_true; last exact Hly.
  simpl. by rewrite resize_all_alt.
Qed.

Lemma encode_decode_id_int v ov ot it z st :
  is_int_ot ot it →
  val_to_Z v it = Some z →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot Hz Hdec.
  destruct ot as [|it'| | | |ly| ]; simpl in Hot; try done.
  - subst it'. simp decode_op_val in Hdec.
    move: Hdec => /fmap_Some[z' [Hz' ->]].
    rewrite Hz in Hz'. injection Hz' as ->.
    by apply i2v_of_val_to_Z.
  - subst ly. simp decode_op_val in Hdec.
    case_bool_decide; simplify_eq. done.
Qed.

Lemma encode_decode_compat_int v ov ot it z st :
  is_int_ot ot it →
  val_to_Z v it = Some z →
  decode_op_val v ot st = Some ov →
  val_to_Z (encode_op_val ov) it = Some z.
Proof.
  intros Hot Hz Hdec.
  by rewrite (encode_decode_id_int _ _ _ _ _ _ Hot Hz Hdec).
Qed.

Lemma encode_decode_id_bool v ov ot b st :
  is_bool_ot ot →
  val_to_bool v = Some b →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot Hb Hdec.
  destruct ot as [| | | | |ly| ]; simpl in Hot; try done.
  - simp decode_op_val in Hdec.
    move: Hdec => /fmap_Some[b' [Hb' ->]].
    rewrite Hb in Hb'. injection Hb' as ->.
    by apply val_of_to_bool.
  - subst ly. simp decode_op_val in Hdec.
    case_bool_decide; simplify_eq. done.
Qed.

Lemma encode_decode_compat_bool v ov ot b st :
  is_bool_ot ot →
  val_to_bool v = Some b →
  decode_op_val v ot st = Some ov →
  val_to_bool (encode_op_val ov) = Some b.
Proof.
  intros Hot Hb Hdec.
  by rewrite (encode_decode_id_bool _ _ _ _ _ Hot Hb Hdec).
Qed.

Lemma encode_decode_id_char v ov ot z st :
  is_char_ot ot →
  val_to_char v = Some z →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot Hz Hdec.
  destruct ot as [| | | | |ly| ]; simpl in Hot; try done.
  - subst ly. simp decode_op_val in Hdec.
    case_bool_decide; simplify_eq. done.
  - simp decode_op_val in Hdec.
    move: Hdec => /fmap_Some[z' [Hz' ->]].
    rewrite Hz in Hz'. injection Hz' as ->.
    by apply val_of_to_char.
Qed.

Lemma encode_decode_compat_char v ov ot z st :
  is_char_ot ot →
  val_to_char v = Some z →
  decode_op_val v ot st = Some ov →
  val_to_char (encode_op_val ov) = Some z.
Proof.
  intros Hot Hz Hdec.
  by rewrite (encode_decode_id_char _ _ _ _ _ Hot Hz Hdec).
Qed.

Lemma encode_decode_id_loc v ov ot l st :
  is_ptr_ot ot →
  val_to_loc v = Some l →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot Hl Hdec.
  destruct ot as [| | | | |ly| ]; simpl in Hot; try done.
  - simp decode_op_val in Hdec.
    rewrite Hl in Hdec. injection Hdec as <-.
    by apply l2v_correct'.
  - subst ly. simp decode_op_val in Hdec.
    case_bool_decide; simplify_eq. done.
Qed.

Lemma encode_decode_compat_loc v ov ot l st :
  is_ptr_ot ot →
  val_to_loc v = Some l →
  decode_op_val v ot st = Some ov →
  val_to_loc (encode_op_val ov) = Some l.
Proof.
  intros Hot Hl Hdec.
  by rewrite (encode_decode_id_loc _ _ _ _ _ Hot Hl Hdec).
Qed.

Lemma encode_decode_id_unit v ov ot st :
  is_unit_ot ot →
  v = zst_val →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot -> Hdec.
  destruct ot as [| | |sl ots| |ly| ]; simpl in Hot; try done.
  - destruct Hot as [-> ->]. simp decode_op_val in Hdec.
    simpl in Hdec. simplify_eq. done.
  - subst ly. simp decode_op_val in Hdec.
    case_bool_decide; simplify_eq. done.
Qed.

Lemma encode_decode_compat_unit v ov ot st :
  is_unit_ot ot →
  v = zst_val →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = zst_val.
Proof.
  intros Hot Hv Hdec.
  by rewrite (encode_decode_id_unit _ _ _ _ Hot Hv Hdec).
Qed.

Section optypes.
  Context `{refinedcG Σ}.
  Lemma mem_cast_compat_id (P : val → iProp Σ) v ot st :
    (P v ⊢ ⌜mem_cast_id v ot⌝) →
    (P v ⊢ P (mem_cast v ot st)).
  Proof. iIntros (HP) "HP". iDestruct (HP with "HP") as %Hm. rewrite Hm. done. Qed.

  Lemma mem_cast_compat_Untyped (P : val → iProp Σ) v ot st :
    (∀ ly, ot = UntypedOp ly → P v ⊢ ⌜v `has_layout_val` ly⌝) →
    ((if ot is UntypedOp _ then False else True) →
      ⊢ P v -∗ P (mem_cast v ot st)) →
    ⊢ P v -∗ P (mem_cast v ot st).
  Proof.
    move => Hly Hot. destruct ot; try by apply: Hot.
    iIntros "HP". iDestruct (Hly _ eq_refl with "HP") as %Hvly.
    by rewrite mem_cast_UntypedOp.
  Qed.

  Lemma mem_cast_compat_int (P : val → iProp Σ) v ot it:
    is_int_ot ot it →
    (P v ⊢ ⌜∃ z, val_to_Z v it = Some z⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros <-.  etrans; [done|]. iPureIntro => -[??]. by apply: mem_cast_id_int.
    - intros ->. etrans; [done|]. iPureIntro => -[? Hz] st'.
      apply mem_cast_UntypedOp. by apply val_to_Z_length in Hz.
  Qed.

  Lemma mem_cast_compat_bool (P : val → iProp Σ) v ot :
    is_bool_ot ot →
    (P v ⊢ ⌜∃ b, val_to_bool v = Some b⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros _.  etrans; [done|]. iPureIntro => -[??]. by apply: mem_cast_id_bool.
    - intros ->. etrans; [done|]. iPureIntro => -[? Hb] st'.
      apply mem_cast_UntypedOp. by apply val_to_bool_length in Hb.
  Qed.

  Lemma mem_cast_compat_char (P : val → iProp Σ) v ot :
    is_char_ot ot →
    (P v ⊢ ⌜∃ b, val_to_char v = Some b⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros ->. etrans; [done|]. iPureIntro => -[? Hz] st'.
      apply mem_cast_UntypedOp. by apply val_to_char_length in Hz.
    - intros _.  etrans; [done|]. iPureIntro => -[??]. by apply: mem_cast_id_char.
  Qed.

  Lemma mem_cast_compat_loc (P : val → iProp Σ) v ot :
    is_ptr_ot ot →
    (P v ⊢ ⌜∃ l, val_to_loc v = Some l⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros _. etrans; [done|].
      iPureIntro => -[??]. simpl. by eapply mem_cast_id_loc.
    - intros ->. etrans; [done|]. iPureIntro => -[? Hl] st'.
      apply mem_cast_UntypedOp. by apply val_to_loc_length; eexists.
  Qed.

  Lemma mem_cast_compat_unit (P : val → iProp Σ) v ot :
    is_unit_ot ot →
    (P v ⊢ ⌜v = zst_val⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros [-> ->]. etrans; first done. iPureIntro => -> st'.
      by rewrite /mem_cast decode_op_val_equation_4 /=.
    - intros ->. etrans; first done. iPureIntro => -> st'.
      apply mem_cast_UntypedOp. done.
  Qed.
End optypes.

Definition is_memcast_val (v : val) (ot : op_type) (v' : val) : Prop :=
  (v' = v) ∨ ∃ st, v' = mem_cast v ot st.

Lemma is_memcast_val_memcast v ot v' st :
  v `has_layout_val` (ot_layout ot) →
  op_type_wf ot →
  is_memcast_val v ot v' →
  is_memcast_val v ot (mem_cast v' ot st).
Proof.
  intros ?? [-> | [st' ->]].
  - right. eauto.
  - right. exists st'. rewrite mem_cast_idemp; done.
Qed.

Lemma is_memcast_val_untyped_inv v v' ly :
  v `has_layout_val` ly →
  is_memcast_val v (UntypedOp ly) v' → v = v'.
Proof.
  intros Hly [-> | (st & ->)]; first done.
  by rewrite mem_cast_UntypedOp.
Qed.

Lemma has_layout_val_mem_cast v ly ot st :
  v `has_layout_val` ly →
  mem_cast v ot st `has_layout_val` ly.
Proof.
  rewrite /has_layout_val mem_cast_length //.
Qed.

Lemma is_memcast_val_has_layout_val v v' ot ly :
  is_memcast_val v ot v' →
  v `has_layout_val` ly →
  v' `has_layout_val` ly.
Proof.
  intros [-> | (st & ->)] Hb; first done.
  by apply has_layout_val_mem_cast.
Qed.
Lemma is_memcast_val_has_layout_val' v v' ot ly :
  is_memcast_val v ot v' →
  v' `has_layout_val` ly →
  v `has_layout_val` ly.
Proof.
  intros [-> | (st & ->)]; first done.
  rewrite /has_layout_val mem_cast_length//.
Qed.
Lemma is_memcast_val_length v v' ot :
  is_memcast_val v ot v' →
  length v = length v'.
Proof.
  intros [-> | (st & ->)]; first done.
  rewrite mem_cast_length//.
Qed.

Lemma is_memcast_val_untyped_app ly1 ly2 ly3 v1 v2 v1' v2' :
  ly_size ly3 = ly_size ly1 + ly_size ly2 →
  v1 `has_layout_val` ly1 →
  v2 `has_layout_val` ly2 →
  is_memcast_val v1 (UntypedOp ly1) v1' →
  is_memcast_val v2 (UntypedOp ly2) v2' →
  is_memcast_val (v1 ++ v2) (UntypedOp ly3) (v1' ++ v2').
Proof.
  intros Hsz ? ? H1 H2.
  destruct H1 as [->  | (st1 & ->)]; destruct H2 as [-> | (st2 & ->)]; simpl in *;
      try rewrite !mem_cast_UntypedOp; try done.
  all: by left.
Qed.

Definition array_op_merge `{!LayoutAlg} (st : syn_type) (ly : layout) (n1 n2 : nat)
    (ot1 ot2 ot : op_type) : Prop :=
  syn_type_has_layout st ly ∧
  ot1 = UntypedOp (mk_array_layout ly n1) ∧
  ot2 = UntypedOp (mk_array_layout ly n2) ∧
  ot = UntypedOp (mk_array_layout ly (n1 + n2)).

Lemma array_op_merge_untyped `{!LayoutAlg} st n1 n2 ly :
  syn_type_has_layout st ly →
  array_op_merge st ly n1 n2
    (UntypedOp (mk_array_layout ly n1))
    (UntypedOp (mk_array_layout ly n2))
    (UntypedOp (mk_array_layout ly (n1 + n2))).
Proof.
  intros Hst. unfold array_op_merge. naive_solver.
Qed.

Lemma is_memcast_val_array_op_merge `{!LayoutAlg} st ly n1 n2 ot1 ot2 ot v1 v2 v1' v2' :
  array_op_merge st ly n1 n2 ot1 ot2 ot →
  v1 `has_layout_val` mk_array_layout ly n1 →
  v2 `has_layout_val` mk_array_layout ly n2 →
  is_memcast_val v1 ot1 v1' →
  is_memcast_val v2 ot2 v2' →
  is_memcast_val (v1 ++ v2) ot (v1' ++ v2').
Proof.
  intros (_ & -> & -> & ->) H1 H2.
  eapply is_memcast_val_untyped_app; [| try done..].
  rewrite !ly_size_mk_array_layout. lia.
Qed.

Definition array_op_split `{!LayoutAlg} (st : syn_type) (ly : layout) (n1 n2 : nat)
    (ot ot1 ot2 : op_type) : Prop :=
  syn_type_has_layout st ly ∧
  ot = UntypedOp (mk_array_layout ly (n1 + n2)) ∧
  ot1 = UntypedOp (mk_array_layout ly n1) ∧
  ot2 = UntypedOp (mk_array_layout ly n2).

Lemma array_op_split_untyped `{!LayoutAlg} st n1 n2 ly :
  syn_type_has_layout st ly →
  array_op_split st ly n1 n2
    (UntypedOp (mk_array_layout ly (n1 + n2)))
    (UntypedOp (mk_array_layout ly n1))
    (UntypedOp (mk_array_layout ly n2)).
Proof.
  intros Hst. unfold array_op_split. naive_solver.
Qed.

Lemma is_memcast_val_array_op_split `{!LayoutAlg} st ly n1 n2 ot ot1 ot2 v1 v2 v1' v2' :
  array_op_split st ly n1 n2 ot ot1 ot2 →
  length v1 = ly_size (ot_layout ot1) →
  length v2 = ly_size (ot_layout ot2) →
  length v1' = ly_size (ot_layout ot1) →
  is_memcast_val (v1 ++ v2) ot (v1' ++ v2') →
  is_memcast_val v1 ot1 v1' ∧ is_memcast_val v2 ot2 v2'.
Proof.
  intros (_ & -> & -> & ->) Hv1 Hv2 Hv1' Hmc.
  apply is_memcast_val_untyped_inv in Hmc.
  2: { rewrite /has_layout_val length_app.
    rewrite Hv1 Hv2/=.
    rewrite !ly_size_mk_array_layout. lia. }
  rewrite ly_size_mk_array_layout in Hv1, Hv1'.
  apply app_inj_1 in Hmc as [-> ->]; last lia.
  split; left; done.
Qed.

Lemma mem_cast_l2v_id l st :
  l.(loc_a) ∈ USize →
  mem_cast (l2v l) PtrOp st = l2v l.
Proof.
  intros Hl. exact (mem_cast_id_loc _ _ (val_to_loc_Some_l2v _ Hl) st).
Qed.
