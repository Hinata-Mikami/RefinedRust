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
Definition is_fnptr_ot (ot : op_type) : Prop :=
  match ot with | FnPtrOp => True | UntypedOp ly => ly = void* | _ => False end.
Definition is_unit_ot (ot : op_type) : Prop :=
  match ot with | StructOp sl ots => sl = unit_sl ∧ ots = [] | UntypedOp ly => ly = unit_sl | _ => False end.

Definition val_decodes_to_loc (v : val) (l : loc) : Prop :=
  ∀ st, decode_op_val v PtrOp st = Some (OVPtr l).

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

Lemma is_fnptr_ot_layout ot:
  is_fnptr_ot ot → ot_layout ot = void*.
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
  destruct ot as [|it'| | | | |ly| ]; simpl in Hot; try done.
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
  destruct ot as [| | | | | |ly| ]; simpl in Hot; try done.
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
  destruct ot as [| | | | | |ly| ]; simpl in Hot; try done.
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
  destruct ot as [| | | | | |ly| ]; simpl in Hot; try done.
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

Lemma encode_decode_id_fn_loc v ov ot l st :
  is_fnptr_ot ot →
  val_to_loc v = Some l →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot Hl Hdec.
  destruct ot as [| | | | | |ly| ]; simpl in Hot; try done.
  - simp decode_op_val in Hdec.
    rewrite Hl in Hdec. injection Hdec as <-.
    by apply l2v_correct'.
  - subst ly. simp decode_op_val in Hdec.
    case_bool_decide; simplify_eq. done.
Qed.

Lemma encode_decode_compat_fn_loc v ov ot l st :
  is_fnptr_ot ot →
  val_to_loc v = Some l →
  decode_op_val v ot st = Some ov →
  val_to_loc (encode_op_val ov) = Some l.
Proof.
  intros Hot Hl Hdec.
  by rewrite (encode_decode_id_fn_loc _ _ _ _ _ Hot Hl Hdec).
Qed.

Lemma val_to_loc_decodes_to_loc v l :
  val_to_loc v = Some l →
  val_decodes_to_loc v l.
Proof.
  intros Hv st. simp decode_op_val. by rewrite Hv.
Qed.

Lemma l2v_decodes_to_loc l :
  l.(loc_a) ∈ USize →
  val_decodes_to_loc (l2v l) l.
Proof.
  intros Hin. apply val_to_loc_decodes_to_loc.
  by apply val_to_loc_Some_l2v.
Qed.

Lemma val_decodes_to_loc_l2v_inv l l' :
  val_decodes_to_loc (l2v l) l' →
  l = l'.
Proof.
  intros Hdec. specialize (Hdec inhabitant).
  destruct (decide (l.(loc_a) ∈ USize)) as [Hin|Hnin].
  - simp decode_op_val in Hdec.
    rewrite (val_to_loc_Some_l2v _ Hin) in Hdec.
    by injection Hdec as ->.
  - rewrite /l2v /val_of_loc bool_decide_false in Hdec; last done.
    simpl in Hdec. simp decode_op_val in Hdec. simpl in Hdec. done.
Qed.

Lemma val_decodes_to_loc_has_layout v l :
  val_decodes_to_loc v l →
  v `has_layout_val` void*.
Proof.
  intros Hdec. specialize (Hdec inhabitant).
  by eapply decode_op_val_has_layout in Hdec.
Qed.

Lemma val_decodes_to_loc_length v l :
  val_decodes_to_loc v l →
  length v = ly_size void*.
Proof. apply val_decodes_to_loc_has_layout. Qed.

Lemma val_decodes_to_loc_mem_cast v l st :
  l.(loc_a) ∈ USize →
  val_decodes_to_loc v l →
  val_to_loc (mem_cast v PtrOp st) = Some l.
Proof.
  intros Hin Hdec. rewrite /mem_cast. pose proof (Hdec st) as Hdec_st.
  rewrite Hdec_st /=.
  rewrite (val_decodes_to_loc_length _ _ Hdec).
  rewrite resize_all_alt; last by symmetry; apply l2v_has_layout_val.
  apply val_to_of_loc. by apply val_of_loc_Some_l2v.
Qed.

Lemma encode_decode_id_unit v ov ot st :
  is_unit_ot ot →
  v = zst_val →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot -> Hdec.
  destruct ot as [| | | |sl ots| |ly| ]; simpl in Hot; try done.
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
      rewrite /mem_cast /=.
      simp decode_op_val. done.
    - intros ->. etrans; first done. iPureIntro => -> st'.
      apply mem_cast_UntypedOp. done.
  Qed.
End optypes.

(** For now, we show stability of decoding.
  This works because currently decoding doesn't actually depend on the state.
  It is needed to make [value_t] work.
  Eventually, when handling exposed provenance, we likely want to replace that with a notion of monotonicity on state,
  and connect that with separation logic resources.
  *)
Lemma decode_struct_fields_stable sl ots rec1 rec2 fields vs i :
  (∀ v ot Hot, rec1 v ot Hot = rec2 v ot Hot) →
  decode_struct_fields sl ots rec1 fields vs i =
  decode_struct_fields sl ots rec2 fields vs i.
Proof.
  intros Hrec. revert vs i.
  induction fields as [|[[n|] ly] fields IH]; intros [|v vs] i; simpl; try done.
  destruct (lookup_struct_ot ots i) as [[ot Hot]|]; simpl; last done.
  rewrite Hrec. destruct (rec2 v ot _) as [ov|]; simpl; last done.
    by rewrite IH.
Qed.

Lemma decode_struct_fields_stable_lookup sl ots rec1 rec2 fields vs i :
  (∀ j v ot Hot, ots !! j = Some ot → rec1 v ot Hot = rec2 v ot Hot) →
  decode_struct_fields sl ots rec1 fields vs i =
  decode_struct_fields sl ots rec2 fields vs i.
Proof.
  intros Hrec. revert vs i.
  induction fields as [|[[n|] ly] fields IH]; intros [|v vs] i; simpl; try done.
  - destruct (lookup_struct_ot ots i) as [[ot Hot]|]; simpl; last done.
    rewrite (Hrec i v ot _ Hot). destruct (rec2 v ot _) as [ov|]; simpl; last done.
    by rewrite IH.
Qed.

Lemma list_is_list_lookup {A} (P : A → Type) l i x :
  list_is_list A P l →
  l !! i = Some x →
  P x.
Proof.
  intros Hl. induction Hl as [|a Ha l Hl IH] in i |-*; destruct i; simpl; naive_solver.
Qed.

Lemma decode_op_val_stable v ot st st' :
  decode_op_val v ot st = decode_op_val v ot st'.
Proof.
  revert v. induction ot using op_type_recursor; intros v; simp decode_op_val; try done.
  - rewrite (decode_struct_fields_stable_lookup sl ots
      (λ v' ot Hot, decode_op_val v' ot st)
      (λ v' ot Hot, decode_op_val v' ot st')).
    + done.
    + intros j v' ot Hot Hlook.
      pose proof (list_is_list_lookup
        (λ ot0, ∀ v0, decode_op_val v0 ot0 st = decode_op_val v0 ot0 st')
        ots j ot H Hlook) as IH.
      by apply IH.
Qed.

Definition is_same_decoded_val_at (st : gset addr * heap_state) (v1 : val) (ot : op_type) (v2 : val) : Prop :=
  decode_op_val v1 ot st = decode_op_val v2 ot st ∧
  is_Some (decode_op_val v1 ot st).

Definition is_same_decoded_val (v1 : val) (ot : op_type) (v2 : val) : Prop :=
  ∀ st, is_same_decoded_val_at st v1 ot v2.

Lemma is_same_decoded_val_at_sym st v1 ot v2 :
  is_same_decoded_val_at st v1 ot v2 → is_same_decoded_val_at st v2 ot v1.
Proof.
  intros [Heq [ov Hdec]]. split; first by symmetry.
  exists ov. by rewrite -Heq.
Qed.

Lemma is_same_decoded_val_at_stable st st' v1 ot v2 :
  is_same_decoded_val_at st v1 ot v2 →
  is_same_decoded_val_at st' v1 ot v2.
Proof.
  intros [Heq Hsome]. split.
  - rewrite -(decode_op_val_stable v1 ot st st').
    rewrite -(decode_op_val_stable v2 ot st st'). done.
  - destruct Hsome as [ov Hdec]. exists ov.
    by rewrite -(decode_op_val_stable v1 ot st st').
Qed.

Lemma is_same_decoded_val_of_at st v1 ot v2 :
  is_same_decoded_val_at st v1 ot v2 →
  is_same_decoded_val v1 ot v2.
Proof. intros Hsame st'. by eapply is_same_decoded_val_at_stable. Qed.

Lemma is_same_decoded_val_sym v1 ot v2 :
  is_same_decoded_val v1 ot v2 → is_same_decoded_val v2 ot v1.
Proof.
  intros Hsame st. by apply is_same_decoded_val_at_sym.
Qed.

Lemma is_same_decoded_val_at_trans st v1 ot v2 v3 :
  is_same_decoded_val_at st v1 ot v2 →
  is_same_decoded_val_at st v2 ot v3 →
  is_same_decoded_val_at st v1 ot v3.
Proof.
  intros [Heq12 Hsome] [Heq23 _]. split; first by etrans.
  done.
Qed.

Lemma is_same_decoded_val_trans v1 ot v2 v3 :
  is_same_decoded_val v1 ot v2 →
  is_same_decoded_val v2 ot v3 →
  is_same_decoded_val v1 ot v3.
Proof.
  intros H12 H23 st. eapply is_same_decoded_val_at_trans; [apply H12 | apply H23].
Qed.

Lemma is_same_decoded_val_at_decodable_l st v1 ot v2 :
  is_same_decoded_val_at st v1 ot v2 → ∃ ov, decode_op_val v1 ot st = Some ov.
Proof. by intros [_ Hsome]. Qed.

Lemma is_same_decoded_val_at_decodable_r st v1 ot v2 :
  is_same_decoded_val_at st v1 ot v2 → ∃ ov, decode_op_val v2 ot st = Some ov.
Proof.
  intros [Heq [ov Hdec]]. exists ov. by rewrite -Heq.
Qed.

Lemma is_same_decoded_val_decodable_l v1 ot v2 st :
  is_same_decoded_val v1 ot v2 → ∃ ov, decode_op_val v1 ot st = Some ov.
Proof. intros Hsame. by eapply is_same_decoded_val_at_decodable_l. Qed.

Lemma is_same_decoded_val_decodable_r v1 ot v2 st :
  is_same_decoded_val v1 ot v2 → ∃ ov, decode_op_val v2 ot st = Some ov.
Proof. intros Hsame. by eapply is_same_decoded_val_at_decodable_r. Qed.

Lemma is_same_decoded_val_at_has_layout_l st v1 ot v2 :
  is_same_decoded_val_at st v1 ot v2 → v1 `has_layout_val` ot_layout ot.
Proof.
  intros Hsame. destruct (is_same_decoded_val_at_decodable_l _ _ _ _ Hsame) as [ov Hdec].
  by eapply decode_op_val_has_layout.
Qed.

Lemma is_same_decoded_val_at_has_layout_r st v1 ot v2 :
  is_same_decoded_val_at st v1 ot v2 → v2 `has_layout_val` ot_layout ot.
Proof.
  intros Hsame. destruct (is_same_decoded_val_at_decodable_r _ _ _ _ Hsame) as [ov Hdec].
  by eapply decode_op_val_has_layout.
Qed.

Lemma is_same_decoded_val_has_layout_l v1 ot v2 :
  is_same_decoded_val v1 ot v2 → v1 `has_layout_val` ot_layout ot.
Proof.
  intros Hsame. destruct (is_same_decoded_val_decodable_l _ _ _ inhabitant Hsame) as [ov Hdec].
  by eapply decode_op_val_has_layout.
Qed.

Lemma is_same_decoded_val_has_layout_r v1 ot v2 :
  is_same_decoded_val v1 ot v2 → v2 `has_layout_val` ot_layout ot.
Proof.
  intros Hsame. destruct (is_same_decoded_val_decodable_r _ _ _ inhabitant Hsame) as [ov Hdec].
  by eapply decode_op_val_has_layout.
Qed.

Lemma is_same_decoded_val_length v1 ot v2 :
  is_same_decoded_val v1 ot v2 → length v1 = length v2.
Proof.
  intros Hsame.
  pose proof (is_same_decoded_val_has_layout_l _ _ _ Hsame) as Hly1.
  pose proof (is_same_decoded_val_has_layout_r _ _ _ Hsame) as Hly2.
  rewrite /has_layout_val in Hly1, Hly2. lia.
Qed.

Lemma is_same_decoded_val_untyped_inv v1 v2 ly :
  length v1 = ly_size ly →
  length v2 = ly_size ly →
  is_same_decoded_val v1 (UntypedOp ly) v2 → v1 = v2.
Proof.
  intros ?? Hsame.
  destruct (Hsame inhabitant) as [Heq _].
  simp decode_op_val in Heq.
  repeat case_bool_decide; simplify_eq; done.
Qed.

Lemma is_same_decoded_val_at_untyped_inv st v1 v2 ly :
  length v1 = ly_size ly →
  length v2 = ly_size ly →
  is_same_decoded_val_at st v1 (UntypedOp ly) v2 → v1 = v2.
Proof.
  intros ?? [Heq _].
  simp decode_op_val in Heq.
  repeat case_bool_decide; simplify_eq; done.
Qed.

Lemma is_same_decoded_val_refl v ot :
  (∀ st, ∃ ov, decode_op_val v ot st = Some ov) →
  is_same_decoded_val v ot v.
Proof. intros Hdec st. split; first done. apply Hdec. Qed.

Lemma is_same_decoded_val_at_refl st v ot :
  (∃ ov, decode_op_val v ot st = Some ov) →
  is_same_decoded_val_at st v ot v.
Proof. intros Hdec. split; first done. apply Hdec. Qed.

Lemma is_same_decoded_val_at_encode st v ot ov :
  op_type_wf ot →
  decode_op_val v ot st = Some ov →
  is_same_decoded_val_at st v ot (encode_op_val ov).
Proof.
  intros Hwf Hdec. split.
  - rewrite Hdec. symmetry. eapply decode_encode_op_val; [done|].
    by eapply decode_op_val_has_type.
  - eauto.
Qed.

Lemma val_decodes_to_loc_same_decoded v ot v' l st :
  is_ptr_ot ot →
  val_decodes_to_loc v l →
  is_same_decoded_val_at st v ot v' →
  val_decodes_to_loc v' l.
Proof.
  intros Hot Hv Hsame st'.
  destruct ot as [| | | | | |ly| ]; simpl in Hot; try done.
  - destruct Hsame as [Heq _]. specialize (Hv st).
    rewrite Hv in Heq.
    simp decode_op_val in Heq. simp decode_op_val. by symmetry.
  - subst ly.
    pose proof (val_decodes_to_loc_has_layout _ _ Hv) as Hly.
    pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
    rewrite /has_layout_val /= in Hly'.
    pose proof (is_same_decoded_val_at_untyped_inv st v v' void* Hly Hly' Hsame) as ->.
    apply Hv.
Qed.

(*
Lemma is_same_decoded_val_refl_once v ot st ov :
  decode_op_val v ot st = Some ov →
  is_same_decoded_val v ot v.
Proof.
  intros Hdec st'. split; first done.
  exists ov.
  rewrite -(decode_op_val_stable v ot st st'). done.
Qed.
*)

(*
Lemma is_same_decoded_val_encode v ot ov st :
  op_type_wf ot →
  decode_op_val v ot st = Some ov →
  is_same_decoded_val v ot (encode_op_val ov).
Proof.
  intros Hwf Hdec st'. split.
  - rewrite -(decode_op_val_stable v ot st st') Hdec.
    symmetry. eapply decode_encode_op_val; [done|].
    by eapply decode_op_val_has_type.
  - exists ov. by rewrite -(decode_op_val_stable v ot st st').
Qed.
*)

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
