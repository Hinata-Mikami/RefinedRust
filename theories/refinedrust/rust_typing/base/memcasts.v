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
Definition is_ref_ot (ot : op_type) : Prop :=
  match ot with
  | RefOp => True
  | UntypedOp ly => ly = void*
  | _ => False
  end.
Definition is_fnptr_ot (ot : op_type) : Prop :=
  match ot with | FnPtrOp => True | UntypedOp ly => ly = void* | _ => False end.
Definition is_unit_ot (ot : op_type) : Prop :=
  match ot with | StructOp sl ots => sl = unit_sl ∧ ots = [] | UntypedOp ly => ly = unit_sl | _ => False end.
Definition is_never_ot (ot : op_type) : Prop :=
  match ot with | NeverOp => True | UntypedOp ly => ly = zst_layout | _ => False end.

Definition val_decodes_to_loc (v : val) (l : loc) : Prop :=
  ∀ st, decode_op_val v PtrOp st = Some (OVPtr l).
Definition val_decodes_to_ref (v : val) (l : loc) : Prop :=
  ∀ st, decode_op_val v RefOp st = Some (OVPtr l).

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

Lemma is_ref_ot_layout ot:
  is_ref_ot ot → ot_layout ot = void*.
Proof. by destruct ot => //=; naive_solver. Qed.

Lemma ptr_ref_op_layout ot `{Hor : !TCOr (TCDone (ot = PtrOp)) (TCDone (ot = RefOp))} :
  ot_layout ot = void*.
Proof.
  destruct Hor as [Hot | Hot]; unfold TCDone in Hot; by subst ot.
Qed.

Lemma is_ref_ot_wf ot :
  is_ref_ot ot → op_type_wf ot.
Proof.
  destruct ot => //=.
Qed.

Lemma is_fnptr_ot_layout ot:
  is_fnptr_ot ot → ot_layout ot = void*.
Proof. by destruct ot => //= ->. Qed.

Lemma is_unit_ot_layout ot :
  is_unit_ot ot → ot_layout ot = unit_sl.
Proof.
  destruct ot => //=. by intros [-> ->].
Qed.

Lemma is_never_ot_layout ot :
  is_never_ot ot → ot_layout ot = zst_layout.
Proof.
  destruct ot => //=.
Qed.

Lemma encode_decode_id_int v ov ot it z st :
  is_int_ot ot it →
  val_to_Z v it = Some z →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot Hz Hdec.
  destruct ot as [|it'| | | | | |ly| | | ]; simpl in Hot; try done.
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
  destruct ot as [| | | | | | |ly| | | ]; simpl in Hot; try done.
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
  destruct ot as [| | | | | | |ly| | | ]; simpl in Hot; try done.
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
  destruct ot as [| | | | | | |ly| | | ]; simpl in Hot; try done.
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
  destruct ot as [| | | | | | |ly| | | ]; simpl in Hot; try done.
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

Lemma val_to_loc_decodes_to_ref v l :
  val_to_loc v = Some l →
  l.(loc_a) ≠ 0 →
  val_decodes_to_ref v l.
Proof. intros Hv Hnonnull st. by apply val_to_loc_decode_ref. Qed.

Lemma val_decodes_to_ref_to_loc v l :
  val_decodes_to_ref v l →
  val_decodes_to_loc v l.
Proof.
  intros Hdec st. specialize (Hdec st). by apply decode_ref_inv in Hdec as [Hdec _].
Qed.

Lemma val_decodes_to_ref_nonnull v l :
  val_decodes_to_ref v l →
  l.(loc_a) ≠ 0.
Proof.
  intros Hdec. specialize (Hdec inhabitant). by apply decode_ref_inv in Hdec as [_ ?].
Qed.

Lemma val_decodes_to_loc_ptr_ref v l ot
    `{Hor : !TCOr (TCDone (ot = PtrOp)) (TCDone (ot = RefOp))} :
  val_decodes_to_loc v l →
  l.(loc_a) ≠ 0 →
  ∀ st, decode_op_val v ot st = Some (OVPtr l).
Proof.
  intros Hdec Hnonnull.
  destruct Hor as [Hot | Hot]; unfold TCDone in Hot; subst ot.
  - apply Hdec.
  - intros st. by apply decode_ptr_nonnull_ref.
Qed.

Lemma l2v_decodes_to_loc l :
  l.(loc_a) ∈ USize →
  val_decodes_to_loc (l2v l) l.
Proof.
  intros Hin. apply val_to_loc_decodes_to_loc.
  by apply val_to_loc_Some_l2v.
Qed.

Lemma l2v_decodes_to_ref l :
  l.(loc_a) ∈ USize →
  l.(loc_a) ≠ 0 →
  val_decodes_to_ref (l2v l) l.
Proof.
  intros Hin Hnonnull. apply val_to_loc_decodes_to_ref; last done.
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

Lemma val_decodes_to_ref_l2v_inv l l' :
  val_decodes_to_ref (l2v l) l' →
  l = l'.
Proof. intros Hdec. apply val_decodes_to_loc_l2v_inv. by apply val_decodes_to_ref_to_loc. Qed.

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

Lemma val_decodes_to_ref_has_layout v l :
  val_decodes_to_ref v l →
  v `has_layout_val` void*.
Proof. intros Hdec. apply val_decodes_to_loc_has_layout with l. by apply val_decodes_to_ref_to_loc. Qed.

Lemma val_decodes_to_ref_length v l :
  val_decodes_to_ref v l →
  length v = ly_size void*.
Proof. apply val_decodes_to_ref_has_layout. Qed.

Lemma encode_decode_id_unit v ov ot st :
  is_unit_ot ot →
  v = zst_val →
  decode_op_val v ot st = Some ov →
  encode_op_val ov = v.
Proof.
  intros Hot -> Hdec.
  destruct ot as [| | | |sl ots| | |ly| | | ]; simpl in Hot; try done.
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

Definition is_same_decoded_val_at (st : heap_state) (v1 : val) (ot : op_type) (v2 : val) : Prop :=
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
  destruct ot as [| | | | | | |ly| | | ]; simpl in Hot; try done.
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

Lemma val_decodes_to_ref_same_decoded v ot v' l st :
  is_ref_ot ot →
  val_decodes_to_ref v l →
  is_same_decoded_val_at st v ot v' →
  val_decodes_to_ref v' l.
Proof.
  intros Hot Hv Hsame.
  destruct ot as [| | | | | | |ly| | | ]; simpl in Hot; try done.
  - subst ly.
    pose proof (val_decodes_to_ref_has_layout _ _ Hv) as Hly.
    pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
    rewrite /has_layout_val /= in Hly'.
    pose proof (is_same_decoded_val_at_untyped_inv st v v' void* Hly Hly' Hsame) as ->.
    apply Hv.
  - intros st'. destruct Hsame as [Heq _]. specialize (Hv st).
    rewrite Hv in Heq. rewrite -(decode_op_val_stable v' RefOp st st'). by symmetry.
Qed.
