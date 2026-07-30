From Equations Require Import Equations.
From stdpp Require Export strings.
From stdpp Require Import gmap list.
From radium Require Export base layout int_type loc char struct enum val heap.
Set Default Proof Using "Type".


(** ** Converting a value to a boolean (for conditionals). *)

Definition cast_to_bool (ot: op_type) (v: val) (st: heap_state) : option bool :=
  match ot with
  | BoolOp   => val_to_bool v
  | IntOp it => val_to_Z v it ≫= λ n, Some (bool_decide (n ≠ 0))
  | _        => None
  end.

(** ** Structured values for memcasts. *)

Inductive op_val : Set :=
| OVBool (b : bool)
| OVInt (it : int_type) (z : Z)
| OVFnPtr (l : loc)
| OVPtr (l : loc)
| OVStruct (sl : struct_layout) (fields : list op_val)
| OVArray (elements : list op_val)
| OVEnum (el : enum_layout) (variant : var_name) (tag : Z) (payload : op_val)
| OVUntyped (ly : layout) (v : val)
| OVChar (z : Z).

Global Instance op_val_inhabited : Inhabited op_val := populate (OVBool false).

Definition enum_variant_ot_lookup
    (variant_ots : list (var_name * op_type)) (variant : var_name) : option op_type :=
  (λ x, snd (snd x)) <$> list_find (λ x, x.1 = variant) variant_ots.

Definition enum_tag_lookup (tag_int : list (var_name * Z)) (tag : Z) : option var_name :=
  (λ x, fst (snd x)) <$> list_find (λ x, snd x = tag) tag_int.

#[warnings="-register-all"]
Inductive op_val_has_type : op_val → op_type → Prop :=
| OVBool_has_type b : op_val_has_type (OVBool b) BoolOp
| OVInt_has_type it z : z ∈ it → op_val_has_type (OVInt it z) (IntOp it)
| OVFnPtr_has_type l : l.(loc_a) ∈ USize → op_val_has_type (OVFnPtr l) FnPtrOp
| OVPtr_has_type l : l.(loc_a) ∈ USize → op_val_has_type (OVPtr l) PtrOp
| OVStruct_has_type sl fields ots :
    Forall2 op_val_has_type fields ots →
    op_val_has_type (OVStruct sl fields) (StructOp sl ots)
| OVArray_has_type elements ot len :
    Forall (λ element, op_val_has_type element ot) elements →
    length elements = len →
    op_val_has_type (OVArray elements) (ArrayOp ot len)
| OVEnum_has_type el variant tag variant_ots tag_int ot payload :
    enum_tag_lookup tag_int tag = Some variant →
    (*enum_variant_lookup el.(el_variants) variant = Some ly →*)
    enum_variant_ot_lookup variant_ots variant = Some ot →
    op_val_has_type payload ot →
    op_val_has_type (OVEnum el variant tag payload) (EnumOp el variant_ots tag_int)
| OVUntyped_has_type ly v : v `has_layout_val` ly → op_val_has_type (OVUntyped ly v) (UntypedOp ly)
| OVChar_has_type z : is_valid_char z → op_val_has_type (OVChar z) CharOp
| OVRef_has_type l :
    l.(loc_a) ∈ USize →
    l.(loc_a) ≠ 0 →
    op_val_has_type (OVPtr l) RefOp.

Definition overwrite_val (off : nat) (w v : val) : val :=
  take off v ++ w ++ drop (off + length w) v.

Lemma overwrite_val_length off w v :
  (off + length w ≤ length v)%nat →
  length (overwrite_val off w v) = length v.
Proof. rewrite /overwrite_val !length_app length_take length_drop. lia. Qed.

Lemma take_overwrite_val_before off w v n :
  (off ≤ length v)%nat →
  (n ≤ off)%nat →
  take n (overwrite_val off w v) = take n v.
Proof.
  intros Hoff Hn. rewrite /overwrite_val.
  change (take off v ++ w ++ drop (off + length w) v) with
    (take off v ++ (w ++ drop (off + length w) v)).
  rewrite take_app_le; last by rewrite length_take; lia.
  by rewrite take_take Nat.min_l.
Qed.

Lemma take_overwrite_val_0 w v :
  (length w ≤ length v)%nat →
  take (length w) (overwrite_val 0 w v) = w.
Proof.
  intros Hlen. rewrite /overwrite_val take_0 /=.
  by rewrite take_app_length.
Qed.

Lemma take_drop_overwrite_val off w v :
  (off + length w ≤ length v)%nat →
  take (length w) (drop off (overwrite_val off w v)) = w.
Proof.
  intros Hlen. rewrite /overwrite_val.
  rewrite drop_app_length'; last by rewrite length_take_le; lia.
  by rewrite take_app_length.
Qed.

Lemma take_drop_replicate {A} off n m (x : A) :
  (off + n ≤ m)%nat →
  take n (drop off (replicate m x)) = replicate n x.
Proof.
  intros Hbound. rewrite drop_replicate take_replicate.
  f_equal. lia.
Qed.

Lemma overwrite_val_replicate off n m x :
  (off + n ≤ m)%nat →
  overwrite_val off (replicate n x) (replicate m x) = replicate m x.
Proof.
  intros Hbound. rewrite /overwrite_val.
  rewrite length_replicate take_replicate drop_replicate.
  rewrite -!replicate_add. f_equal. lia.
Qed.

Fixpoint encode_op_val (ov : op_val) : val :=
  match ov with
  | OVBool b => val_of_bool b
  | OVInt it z => i2v z it
  | OVFnPtr l => l2v l
  | OVPtr l => l2v l
  | OVStruct sl fields =>
      mjoin $ pad_struct sl.(sl_members) (encode_op_val <$> fields)
        (λ ly, replicate (ly_size ly) MPoison)
  | OVArray elements => mjoin (encode_op_val <$> elements)
  | OVEnum el _ tag payload =>
      overwrite_val el.(el_data_offset)
        (encode_op_val payload) $
      overwrite_val 0 (i2v tag el.(el_tag_it)) $
      replicate el.(el_size) MPoison
  | OVUntyped _ v => v
  | OVChar z => i2v z CharIt
  end.

Fixpoint op_type_size (ot : op_type) : nat :=
  let fix op_type_list_size (ots : list op_type) : nat :=
    match ots with
    | [] => 0%nat
    | ot :: ots => Nat.add (op_type_size ot) (op_type_list_size ots)
    end in
  let fix variant_op_type_list_size (variant_ots : list (var_name * op_type)) : nat :=
    match variant_ots with
    | [] => 0%nat
    | (_, ot) :: variant_ots => Nat.add (op_type_size ot) (variant_op_type_list_size variant_ots)
    end in
  match ot with
  | StructOp _ ots => S (op_type_list_size ots)
  | ArrayOp ot _ => S (op_type_size ot)
  | EnumOp _ variant_ots _ => S (S (variant_op_type_list_size variant_ots))
  | _ => 1%nat
  end.

Definition op_type_size_rel : op_type → op_type → Prop :=
  ltof _ op_type_size.
Global Instance op_type_size_rel_wf : WellFounded op_type_size_rel.
Proof. apply well_founded_ltof. Qed.

Lemma struct_ot_smaller sl ots ot :
  ot ∈ ots → op_type_size_rel ot (StructOp sl ots).
Proof.
  unfold op_type_size_rel, ltof. simpl.
  induction ots as [|ot' ots IH]; simpl; first by intros []%elem_of_nil.
  intros [->|Hin]%elem_of_cons.
  - lia.
  - specialize (IH Hin). simpl in IH. lia.
Qed.

Lemma struct_ot_lookup_smaller sl ots i ot :
  ots !! i = Some ot → op_type_size_rel ot (StructOp sl ots).
Proof. intros Hot. apply struct_ot_smaller. by eapply list_elem_of_lookup_2. Qed.

Lemma array_ot_smaller ot len :
  op_type_size_rel ot (ArrayOp ot len).
Proof. unfold op_type_size_rel, ltof. simpl. lia. Qed.

Lemma enum_variant_ot_smaller el variant_ots tag_int variant ot :
  enum_variant_ot_lookup variant_ots variant = Some ot →
  op_type_size_rel ot (EnumOp el variant_ots tag_int).
Proof.
  rewrite /enum_variant_ot_lookup /op_type_size_rel /ltof fmap_Some.
  intros ([i [variant' ot']] & Hfind%list_find_Some & ?); simplify_eq/=.
  destruct Hfind as (Hlook & _ & _).
  induction variant_ots as [|[variant'' ots''] variant_ots IH] in i, Hlook |-*;
    simpl in Hlook; first done.
  destruct i as [|i]; simpl in Hlook.
  - simplify_eq/=. lia.
  - specialize (IH i Hlook). simpl. lia.
Qed.

Definition lookup_enum_variant_ot
    (variant_ots : list (var_name * op_type)) (variant : var_name) :
    option { ot : op_type & enum_variant_ot_lookup variant_ots variant = Some ot } :=
  match enum_variant_ot_lookup variant_ots variant as oot return
      enum_variant_ot_lookup variant_ots variant = oot →
      option { ot : op_type & enum_variant_ot_lookup variant_ots variant = Some ot }
  with
  | Some ot => λ Hot, Some (@existT op_type
      (λ ot, enum_variant_ot_lookup variant_ots variant = Some ot) ot Hot)
  | None => λ _, None
  end eq_refl.

Lemma enum_variant_ot_lookup_in variant_ots variant ot :
  enum_variant_ot_lookup variant_ots variant = Some ot →
  (variant, ot) ∈ variant_ots.
Proof.
  rewrite /enum_variant_ot_lookup fmap_Some.
  intros ([i [variant' ot']] & Hfind%list_find_Some & ?); simplify_eq/=.
  destruct Hfind as (Hlook & Heq & _). simpl in Heq. subst variant'.
  by eapply list_elem_of_lookup_2.
Qed.

Lemma enum_tag_lookup_in tag_int tag variant :
  enum_tag_lookup tag_int tag = Some variant →
  (variant, tag) ∈ tag_int.
Proof.
  rewrite /enum_tag_lookup fmap_Some.
  intros ([i [variant' tag']] & Hfind%list_find_Some & ?); simplify_eq/=.
  destruct Hfind as (Hlook & Heq & _). simpl in Heq. subst tag'.
  by eapply list_elem_of_lookup_2.
Qed.

Lemma enum_tag_lookup_in_range el variant_ots tag_int tag variant :
  op_type_wf (EnumOp el variant_ots tag_int) →
  enum_tag_lookup tag_int tag = Some variant →
  tag ∈ el.(el_tag_it).
Proof.
  simpl. intros (_ & _ & _ & Hrange & _) Htag.
  eapply (proj1 (Forall_forall _ _) Hrange (variant, tag)); last by eapply enum_tag_lookup_in.
Qed.

Lemma enum_variant_ot_lookup_has_variant el variant_ots tag_int variant ot :
  op_type_wf (EnumOp el variant_ots tag_int) →
  enum_variant_ot_lookup variant_ots variant = Some ot →
  enum_variant_lookup el.(el_variants) variant = Some (ot_layout ot).
Proof.
  simpl. intros (_ & _ & _ & _ & Hvariants) Hot.
  apply Forall_Forall_cb in Hvariants.
  unfold enum_variant_ot_lookup in Hot.
  apply fmap_Some in Hot as ((i & (v & ot')) & Hot & ->).
  apply list_find_Some in Hot.
  destruct Hot as (Ha & ? & _). subst.
  eapply Forall_lookup in Hvariants; last done.
  simpl in Hvariants. destruct Hvariants as (ly & ? & ? & <-).
  done.
Qed.
Lemma enum_variant_payload_wf el variant_ots tag_int variant ot :
  op_type_wf (EnumOp el variant_ots tag_int) →
  enum_variant_ot_lookup variant_ots variant = Some ot →
  op_type_wf ot.
Proof.
  simpl. intros (_ & _ & _ & _ & Hvariants) Hot.
  apply Forall_Forall_cb in Hvariants.
  pose proof (enum_variant_ot_lookup_in _ _ _ Hot) as Hin.
  pose proof (proj1 (Forall_forall _ _) Hvariants _ Hin) as (ly' & Hly' & Hwf & Hlayout).
  done.
Qed.

Definition lookup_struct_ot (ots : list op_type) (i : nat) : option { ot : op_type & ots !! i = Some ot } :=
  match ots !! i as oot return ots !! i = oot → option { ot : op_type & ots !! i = Some ot } with
  | Some ot => λ Hot, Some (@existT _ (λ ot, ots !! i = Some ot) ot Hot)
  | None => λ _, None
  end eq_refl.

Fixpoint decode_struct_fields
    (sl : struct_layout) (ots : list op_type)
    (rec : val → ∀ ot, op_type_size_rel ot (StructOp sl ots) → option op_val)
    (fields : field_list) (vs : list val) (i : nat) {struct fields}
    : option (list op_val) :=
  match fields with
  | [] =>
      match vs with
      | [] => if bool_decide (i = length ots) then Some [] else None
      | _ => None
      end
  | (Some _, _) :: fields' =>
      match vs with
      | v' :: vs' =>
          match lookup_struct_ot ots i with
          | Some (existT ot Hot) =>
              ov ← rec v' ot (struct_ot_lookup_smaller sl ots i ot Hot);
              ovs ← decode_struct_fields sl ots rec fields' vs' (S i);
              Some (ov :: ovs)
          | None => None
          end
      | _ => None
      end
  | (None, _) :: fields' =>
      match vs with
      | _ :: vs' => decode_struct_fields sl ots rec fields' vs' i
      | _ => None
      end
  end.

Equations decode_op_val (v : val) (ot : op_type) (st : (heap_state)) : option op_val by wf ot op_type_size_rel :=
  decode_op_val v BoolOp st := OVBool <$> val_to_bool v;
  decode_op_val v (IntOp it) st := OVInt it <$> val_to_Z v it;
  decode_op_val v FnPtrOp st :=
    (* don't allow integer-pointer casts here *)
    OVFnPtr <$> val_to_loc v;
  decode_op_val v PtrOp st :=
      match val_to_loc v with
      | Some l => Some (OVPtr l)
      | None =>
          v' ← val_to_bytes v;
          a ← val_to_Z v' USize;
          Some (OVPtr (Loc ProvNone a))
      end;
  decode_op_val v (StructOp sl ots) st :=
      if bool_decide (length v = ly_size sl) then
        fields ← decode_struct_fields sl ots (λ v' ot Hot, decode_op_val v' ot st)
          sl.(sl_members) (reshape (ly_size <$> sl.(sl_members).*2) v) 0%nat;
        Some (OVStruct sl fields)
      else None;
  decode_op_val v (ArrayOp ot len) st :=
      if bool_decide (length v = ly_size (mk_array_layout (ot_layout ot) len)) then
        elements ← list_map_option
          (λ v', decode_op_val v' ot st)
          (reshape (replicate len (ly_size (ot_layout ot))) v);
        Some (OVArray elements)
      else None;
  decode_op_val v (EnumOp el variant_ots tag_int) st :=
      if bool_decide (length v = ly_size el) then
        tag ← val_to_Z (take (ly_size (it_layout el.(el_tag_it))) v) el.(el_tag_it);
        variant ← enum_tag_lookup tag_int tag;
        ly ← enum_variant_lookup el.(el_variants) variant;
        ot ← lookup_enum_variant_ot variant_ots variant;
        payload ← decode_op_val (take (ly_size ly) (drop el.(el_data_offset) v))
          (projT1 ot) st;
        Some (OVEnum el variant tag payload)
      else None;
  decode_op_val v (UntypedOp ly) st :=
      if bool_decide (length v = ly_size ly) then Some (OVUntyped ly v) else None;
  decode_op_val v CharOp st := OVChar <$> val_to_char v;
  (* References use raw-pointer decoding, but additionally reject null. *)
  decode_op_val v RefOp st :=
      match (match val_to_loc v with
             | Some l => Some l
             | None =>
                 v' ← val_to_bytes v;
                 a ← val_to_Z v' USize;
                 Some (Loc ProvNone a)
             end) with
      | Some l => if decide (l.(loc_a) ≠ 0) then Some (OVPtr l) else None
      | None => None
      end.
Next Obligation.
  done.
Qed.
Next Obligation.
  intros. apply array_ot_smaller.
Qed.
Next Obligation.
  destruct ot as [ot Hot]. simpl.
  by eapply enum_variant_ot_smaller.
Qed.

Lemma decode_struct_fields_has_type sl ots rec fields vs i ovs :
  (∀ v ot Hot ov, rec v ot Hot = Some ov → op_val_has_type ov ot) →
  decode_struct_fields sl ots rec fields vs i = Some ovs →
  Forall2 op_val_has_type ovs (drop i ots).
Proof.
  intros Hrec.
  induction fields as [|[name ly] fields IH] in vs, i, ovs |-*.
  - simpl. destruct vs as [|??]; first last.
    { intros Hnone. discriminate Hnone. }
    case_bool_decide as Hi; last done.
    intros [= <-]. by rewrite Hi drop_all.
  - destruct name as [n|].
    + destruct vs as [|v' vs']; first (simpl; done).
      simpl. destruct (lookup_struct_ot ots i) as [[ot Hot]|] eqn:Hlookup; last done.
      destruct (rec v' ot _) as [ov|] eqn:Hov; last done.
      destruct (decode_struct_fields sl ots rec fields vs' (S i)) as [ovs'|] eqn:Hfields; last done.
      intros [= <-]. erewrite drop_S; last done.
      constructor; first by eapply Hrec.
      by eapply IH.
    + destruct vs as [|v' vs']; first (simpl; done).
      simpl.
      by eapply IH.
Qed.

Lemma decode_op_val_has_layout v ot st ov :
  decode_op_val v ot st = Some ov →
  v `has_layout_val` ot_layout ot.
Proof.
  revert v st ov.
  induction ot as [ot IH] using (well_founded_induction op_type_size_rel_wf).
  intros v st ov Hdec.
  destruct ot; simp decode_op_val in Hdec.
  - move: Hdec => /fmap_Some[b[Hb Hov]]. by apply val_to_bool_length in Hb.
  - move: Hdec => /fmap_Some[z[Hz Hov]]. by apply val_to_Z_length in Hz.
  - move: Hdec => /fmap_Some[l[Hl Hov]]. by apply val_to_loc_length.
  - destruct (val_to_loc v) as [l|] eqn:Hl.
    + apply val_to_loc_length. eexists. done.
    + apply bind_Some in Hdec as (v' & Hv & Hdec).
      apply bind_Some in Hdec as (a & Ha & Hov).
      apply val_to_Z_length in Ha.
      apply val_to_bytes_length in Hv.
      rewrite /has_layout_val /= -Hv Ha. done.
  - case_bool_decide as Hly; last done.
    rewrite /has_layout_val /=. done.
  - case_bool_decide as Hly; last done.
    by rewrite /has_layout_val /=.
  - case_bool_decide as Hly; last done.
    by rewrite /has_layout_val.
  - case_bool_decide as Hly; last done.
    by rewrite /has_layout_val.
  - move: Hdec => /fmap_Some[z[Hz Hov]]. by apply val_to_char_length in Hz.
  - destruct (val_to_loc v) as [l|] eqn:Hl.
    + case_decide; last done. apply val_to_loc_length. eexists. done.
    + destruct (val_to_bytes v) as [v'|] eqn:Hv; simpl in Hdec; last done.
      destruct (val_to_Z v' USize) as [a|] eqn:Ha; simpl in Hdec; last done.
      case_decide; last done.
      apply val_to_Z_length in Ha. apply val_to_bytes_length in Hv.
      rewrite /has_layout_val /= -Hv Ha. done.
Qed.

Lemma decode_op_val_has_type v ot st ov :
  decode_op_val v ot st = Some ov →
  op_val_has_type ov ot.
Proof.
  revert v st ov.
  induction ot as [ot IH] using (well_founded_induction op_type_size_rel_wf).
  intros v st ov Hdec.
  destruct ot; simp decode_op_val in Hdec.
  - move: Hdec => /fmap_Some[b[Hb Hov]]. simplify_eq. constructor.
  - move: Hdec => /fmap_Some[z[Hz Hov]]. simplify_eq. constructor. by eapply val_to_Z_in_range.
  - move: Hdec => /fmap_Some[l[Hl Hov]]. simplify_eq. constructor.
    by apply val_to_loc_Some_inv in Hl as [_ ?].
  - destruct (val_to_loc v) as [l|] eqn:Hl.
    + injection Hdec as <-. constructor. by apply val_to_loc_Some_inv in Hl as [_ ?].
    + apply bind_Some in Hdec as (v' & Hv & Hdec).
      apply bind_Some in Hdec as (a & Ha & Hov).
      injection Hov as <-. constructor. by eapply val_to_Z_in_range.
  - case_bool_decide; last done.
    apply bind_Some in Hdec as (fields & Hfields & Hov).
    injection Hov as <-. constructor.
    rewrite -(drop_0 ots).
    eapply decode_struct_fields_has_type; last done.
    intros v' ot' Hot ov' Hdec.
    exact (IH ot' Hot v' st ov' Hdec).
  - case_bool_decide; last done.
    apply bind_Some in Hdec as (elements & Helements & Hov).
    injection Hov as <-. constructor.
    + apply list_map_option_alt in Helements.
      eapply Forall2_Forall_impl; first last.
      { exact Helements. }
      intros v' element Hdec.
      exact (IH ot (array_ot_smaller ot len) v' st element Hdec).
    + apply list_map_option_alt in Helements.
      apply Forall2_length in Helements.
      rewrite length_reshape length_replicate in Helements. lia.
  - case_bool_decide; last done.
    apply bind_Some in Hdec as (tag & Htag & Hdec).
    apply bind_Some in Hdec as (variant & Hvariant & Hdec).
    apply bind_Some in Hdec as (sl & Hsl & Hdec).
    apply bind_Some in Hdec as (ots_sig & Hots & Hdec).
    apply bind_Some in Hdec as (payload & Hpayload & Hov).
    injection Hov as <-.
    econstructor; [done| |].
    + exact (projT2 ots_sig).
    + eapply IH; last exact Hpayload.
      simpl. eapply enum_variant_ot_smaller. exact (projT2 ots_sig).
  - case_bool_decide as Hly; last done.
    injection Hdec as <-. constructor. by rewrite /has_layout_val.
  - move: Hdec => /fmap_Some[z[Hz Hov]]. simplify_eq. constructor.
    rewrite /val_to_char in Hz.
    move: Hz => /bind_Some[z'[Hz Hvalid]].
    case_decide; simplify_eq; done.
  - destruct (val_to_loc v) as [l|] eqn:Hl.
    + case_decide as Hnonnull; last done.
      injection Hdec as <-. constructor; last done.
      by apply val_to_loc_Some_inv in Hl as [_ ?].
    + destruct (val_to_bytes v) as [v'|] eqn:Hv; simpl in Hdec; last done.
      destruct (val_to_Z v' USize) as [a|] eqn:Ha; simpl in Hdec; last done.
      case_decide as Hnonnull; last done.
      injection Hdec as <-. constructor; last done. by eapply val_to_Z_in_range.
Qed.

Lemma encode_op_val_length ov ot :
  op_type_wf ot →
  op_val_has_type ov ot →
  length (encode_op_val ov) = ly_size (ot_layout ot).
Proof.
  revert ov.
  induction ot as [ot IH] using (well_founded_induction op_type_size_rel_wf).
  intros ov Hwf Hty.
  destruct Hty; simpl; try done.
  - rewrite i2v_length. done.
  - rewrite l2v_length. done.
  - rewrite l2v_length. done.
  - simpl in Hwf. simpl.
    move: Hwf. rewrite -Forall2_Forall2_cb => Hwf.
    rewrite length_join {2}/ly_size /=.
    apply: sum_list_eq.
    apply Forall2_same_length_lookup_2.
    { rewrite !length_fmap pad_struct_length. done. }
    intros i n1 n2. rewrite list_lookup_fmap.
    intros (venc & Hlook_enc & ->)%fmap_Some Hlook_ly.
    pose proof Hlook_enc as Hlook_enc'.
    apply pad_struct_lookup_Some_1 in Hlook_enc' as (name & ly & Hlook_member & Hor).
    destruct Hor as [[Hsome Hfield]|[[Hnone|Hlen] ->]].
    + destruct name as [name|]; last done.
      apply pad_struct_lookup_Some_Some with (n:=name) (ly:=ly) in Hlook_enc as Hfield'; last done.
      2: { rewrite length_fmap. trans (length ots); first by eapply Forall2_length.
           trans (length (named_fields (sl_members sl))); first by eapply Forall2_length.
           by rewrite named_fields_field_names_length. }
      move: Hfield'. rewrite list_lookup_fmap => /fmap_Some[ov [Hov ->]].
      eapply Forall2_lookup_l in H as (ot' & Hot' & Hty'); last done.
      eapply Forall2_lookup_l in Hwf as ([name' ly'] & Hnamed & [Hwf' Hlayout]); last done.
      assert (Hnamed' : named_fields (sl_members sl) !! field_idx_of_idx (sl_members sl) i = Some (name, ly)).
      { rewrite /named_fields. by eapply field_members_idx_lookup. }
      rewrite Hnamed in Hnamed'. injection Hnamed' as [= <- <-]. simpl in Hlayout.
      assert (Hn2 : n2 = ly_size ly').
      { move: Hlook_ly.
        change ((ly_size <$> (snd <$> sl_members sl)) !! i = Some n2 → n2 = ly_size ly').
        rewrite !list_lookup_fmap Hlook_member /=. intros [= <-]. done. }
      rewrite Hn2 -Hlayout.
      exact (IH ot' (struct_ot_lookup_smaller sl ots _ _ Hot') ov Hwf' Hty').
    + subst. rewrite length_replicate.
      move: Hlook_ly. change ((ly_size <$> (snd <$> sl_members sl)) !! i = Some n2 → ly_size ly = n2).
      rewrite !list_lookup_fmap Hlook_member /=. intros [= <-]. done.
    + rewrite length_replicate.
       move: Hlook_ly. change ((ly_size <$> (snd <$> sl_members sl)) !! i = Some n2 → ly_size ly = n2).
       rewrite !list_lookup_fmap Hlook_member /=. intros [= <-]. done.
  - simpl in Hwf.
    rewrite length_join ly_size_mk_array_layout.
    rewrite (sum_list_fmap_same (ly_size (ot_layout ot))).
    + rewrite length_fmap H0. lia.
    + rewrite Forall_fmap.
      eapply Forall_impl; first exact H.
      intros element Hty.
      exact (IH ot (array_ot_smaller ot len) element Hwf Hty).
  - pose proof (enum_variant_payload_wf el variant_ots tag_int variant ot Hwf H0) as Hwf_payload.
    pose proof (IH ot (enum_variant_ot_smaller el variant_ots tag_int variant ot H0)
      payload Hwf_payload Hty) as Hpayload_len.
    opose proof (enum_variant_lookup_in_bounds el variant _ _).
    { by eapply enum_variant_ot_lookup_has_variant. }
    rewrite (overwrite_val_length el.(el_data_offset) (encode_op_val payload)).
    + rewrite (overwrite_val_length 0 (i2v tag el.(el_tag_it))).
      * rewrite length_replicate. done.
      * rewrite i2v_length length_replicate.
        pose proof (el_tag_before_data el) as Htag_before.
        rewrite /it_layout /ly_size in Htag_before.
        lia.
    + rewrite (overwrite_val_length 0 (i2v tag el.(el_tag_it))).
      * rewrite length_replicate Hpayload_len.
        lia.
      * rewrite i2v_length length_replicate.
        pose proof (el_tag_before_data el) as Htag_before.
        rewrite /it_layout /ly_size in Htag_before.
        lia.
  - rewrite i2v_length. done.
  - rewrite l2v_length. done.
Qed.

Lemma pad_struct_encode_lengths sl fields ots :
  op_type_wf (StructOp sl ots) →
  Forall2 op_val_has_type fields ots →
  Forall2 (λ v sz, length v = sz)
    (pad_struct sl.(sl_members) (encode_op_val <$> fields)
      (λ ly, replicate (ly_size ly) MPoison))
    (ly_size <$> sl.(sl_members).*2).
Proof.
  intros Hwf Hty.
  apply Forall2_same_length_lookup_2.
  { rewrite pad_struct_length !length_fmap. done. }
  intros i v n Hlook Hsize.
  pose proof Hlook as Hlook'.
  apply pad_struct_lookup_Some_1 in Hlook as (name & ly & Hmember & Hor).
  destruct Hor as [[Hsome Hfield]|[[Hnone|Hlen] ->]].
  - destruct name as [name|]; last done.
    apply pad_struct_lookup_Some_Some with (n:=name) (ly:=ly) in Hlook' as Hfield'; last done.
    2: { rewrite length_fmap. trans (length ots); first by eapply Forall2_length.
         move: Hwf. simpl. rewrite -Forall2_Forall2_cb => Hwf'.
         trans (length (named_fields (sl_members sl))); first by eapply Forall2_length.
         by rewrite named_fields_field_names_length. }
    move: Hfield'. rewrite list_lookup_fmap => /fmap_Some[ov [Hov ->]].
    move: Hwf. simpl. rewrite -Forall2_Forall2_cb => Hwf'.
    eapply Forall2_lookup_l in Hty as (ot' & Hot' & Hty'); last done.
    eapply Forall2_lookup_l in Hwf' as ([name' ly'] & Hnamed & [Hwf_ot Hlayout]); last done.
    assert (Hnamed' : named_fields (sl_members sl) !! field_idx_of_idx (sl_members sl) i = Some (name, ly)).
    { rewrite /named_fields. by eapply field_members_idx_lookup. }
    rewrite Hnamed in Hnamed'. injection Hnamed' as [= <- <-]. simpl in Hlayout.
    assert (Hn : n = ly_size ly').
    { move: Hsize.
      change ((ly_size <$> (snd <$> sl_members sl)) !! i = Some n → n = ly_size ly').
      rewrite !list_lookup_fmap Hmember /=. intros [= <-]. done. }
    rewrite Hn -Hlayout.
    eapply encode_op_val_length; done.
  - subst. rewrite length_replicate.
    move: Hsize. change ((ly_size <$> (snd <$> sl_members sl)) !! i = Some n → ly_size ly = n).
    rewrite !list_lookup_fmap Hmember /=. intros [= <-]. done.
  - rewrite length_replicate.
    move: Hsize. change ((ly_size <$> (snd <$> sl_members sl)) !! i = Some n → ly_size ly = n).
    rewrite !list_lookup_fmap Hmember /=. intros [= <-]. done.
Qed.

Lemma reshape_encode_struct sl fields ots :
  op_type_wf (StructOp sl ots) →
  Forall2 op_val_has_type fields ots →
  reshape (ly_size <$> sl.(sl_members).*2)
    (mjoin (pad_struct sl.(sl_members) (encode_op_val <$> fields)
      (λ ly, replicate (ly_size ly) MPoison))) =
  pad_struct sl.(sl_members) (encode_op_val <$> fields)
    (λ ly, replicate (ly_size ly) MPoison).
Proof.
  intros Hwf Hty. apply reshape_join.
  by apply pad_struct_encode_lengths with (ots:=ots).
Qed.

Lemma reshape_replicate_sum {A} (szs : list nat) (x : A) :
  reshape szs (replicate (sum_list szs) x) = (λ sz, replicate sz x) <$> szs.
Proof.
  induction szs as [|sz szs IH]; simpl; first done.
  rewrite take_replicate_add drop_replicate_add IH. done.
Qed.

Lemma mjoin_replicate_chunks {A} (szs : list nat) (x : A) :
  mjoin ((λ sz, replicate sz x) <$> szs) = replicate (sum_list szs) x.
Proof.
  induction szs as [|sz szs IH]; simpl; first done.
  by rewrite IH replicate_add.
Qed.

Lemma mjoin_layout_replicate_chunks (lys : list layout) :
  mjoin ((λ ly, replicate (ly_size ly) MPoison) <$> lys) =
  replicate (sum_list (ly_size <$> lys)) MPoison.
Proof.
  induction lys as [|ly lys IH]; simpl; first done.
  by rewrite IH replicate_add.
Qed.

Lemma decode_struct_fields_encode sl ots rec members fields i :
  (∀ v ot Hot ov,
      op_type_wf ot →
      op_val_has_type ov ot →
      v = encode_op_val ov →
      rec v ot Hot = Some ov) →
  Forall2 op_val_has_type fields (drop i ots) →
  Forall2 (λ ot '(n, ly), op_type_wf ot ∧ ot_layout ot = ly)
    (drop i ots) (named_fields members) →
  (i ≤ length ots)%nat →
  decode_struct_fields sl ots rec members
    (pad_struct members (encode_op_val <$> fields)
      (λ ly, replicate (ly_size ly) MPoison)) i = Some fields.
Proof.
  intros Hrec.
  induction members as [|[name ly] members IH] in fields, i |-*.
  - simpl. intros Hty Hwf Hi.
    apply Forall2_length in Hty.
    apply Forall2_length in Hwf. simpl in Hwf.
    destruct fields as [|??]; last (simpl in Hty; lia).
    rewrite bool_decide_true; first done.
    rewrite length_drop in Hwf. lia.
  - destruct name as [name|]; simpl.
    + intros Hty Hwf Hi.
      destruct (drop i ots) as [|ot ots'] eqn:Hdrop; first by inversion Hwf.
      destruct fields as [|ov fields]; first by inversion Hty.
      inversion Hty as [|???? Hov Htys]; subst.
      rewrite /named_fields /= in Hwf.
      inversion Hwf as [|? ? ? ? Hwf_head Hwfs]; subst.
      destruct Hwf_head as [Hwf_ot Hlayout].
      assert (Hot : ots !! i = Some ot).
      { replace i with (i + 0)%nat by lia.
        rewrite -lookup_drop Hdrop. done. }
      simpl.
      destruct (lookup_struct_ot ots i) as [[ot' Hot']|] eqn:Hlookup.
      * assert (ot' = ot) as -> by congruence.
        assert (Hots' : ots' = drop (S i) ots).
        { pose proof (drop_S ots ot i Hot) as HdropS.
          rewrite Hdrop in HdropS. injection HdropS as [= ?]. done. }
        rewrite (Hrec (encode_op_val ov) ot (struct_ot_lookup_smaller sl ots i ot Hot') ov Hwf_ot Hov eq_refl) /=.
        rewrite (IH fields (S i)); first done.
        -- by rewrite -Hots'.
        -- by rewrite -Hots'.
        -- apply lookup_lt_Some in Hot. lia.
      * unfold lookup_struct_ot in Hlookup. rewrite Hot in Hlookup. done.
    + intros Hty Hwf Hi.
      rewrite /named_fields /= in Hwf.
      by apply IH.
Qed.

Lemma decode_struct_fields_poison_encode sl ots rec members fields i :
  (∀ v ot Hot ov,
      op_type_wf ot →
      v = replicate (ly_size (ot_layout ot)) MPoison →
      rec v ot Hot = Some ov →
      encode_op_val ov = v) →
  Forall2 (λ ot '(n, ly), op_type_wf ot ∧ ot_layout ot = ly)
    (drop i ots) (named_fields members) →
  (i ≤ length ots)%nat →
  decode_struct_fields sl ots rec members
    ((λ ly, replicate (ly_size ly) MPoison) <$> members.*2) i = Some fields →
  pad_struct members (encode_op_val <$> fields)
    (λ ly, replicate (ly_size ly) MPoison) =
  (λ ly, replicate (ly_size ly) MPoison) <$> members.*2.
Proof.
  intros Hrec.
  induction members as [|[name ly] members IH] in fields, i |-*; simpl.
  - intros _ _. case_bool_decide; intros Hdec; simplify_eq. done.
  - destruct name as [name|]; simpl.
    + intros Hwf Hi.
      destruct (drop i ots) as [|ot ots'] eqn:Hdrop; first by inversion Hwf.
      rewrite /named_fields /= in Hwf.
      inversion Hwf as [|? ? ? ? Hwf_head Hwf_tail]; subst.
      destruct Hwf_head as [Hwf_ot Hlayout].
      assert (Hot : ots !! i = Some ot).
      { replace i with (i + 0)%nat by lia.
        rewrite -lookup_drop Hdrop. done. }
      destruct (lookup_struct_ot ots i) as [[ot' Hot']|] eqn:Hlookup; last first.
      { unfold lookup_struct_ot in Hlookup. rewrite Hot in Hlookup. done. }
      assert (ot' = ot) as -> by congruence.
      intros Hdec. apply bind_Some in Hdec as (ov & Hov & Hdec).
      apply bind_Some in Hdec as (fields' & Hfields & [= <-]).
      assert (Hots' : ots' = drop (S i) ots).
      { pose proof (drop_S ots ot i Hot) as HdropS.
        rewrite Hdrop in HdropS. injection HdropS as [= ?]. done. }
      assert (Hchunk : replicate (ly_size ly) MPoison = replicate (ly_size (ot_layout ot)) MPoison).
      { by rewrite Hlayout. }
      simpl. rewrite (Hrec _ _ _ _ Hwf_ot Hchunk Hov). f_equal.
      eapply IH; last done.
      * by rewrite -Hots'.
      * apply lookup_lt_Some in Hot. lia.
    + intros Hwf Hi Hdec. f_equal. by eapply IH.
Qed.

Lemma decode_encode_op_val ov ot st :
  op_type_wf ot →
  op_val_has_type ov ot →
  decode_op_val (encode_op_val ov) ot st = Some ov.
Proof.
  revert ov.
  induction ot as [ot IH] using (well_founded_induction op_type_size_rel_wf).
  intros ov Hwf Hty.
  destruct Hty; simp decode_op_val; simpl.
  - by destruct b.
  - by rewrite val_to_Z_i2v.
  - by rewrite val_to_loc_Some_l2v.
  - by rewrite val_to_loc_Some_l2v.
  - rewrite bool_decide_true.
    2: { change (length (encode_op_val (OVStruct sl fields)) = ly_size (ot_layout (StructOp sl ots))).
         apply encode_op_val_length; first done. by constructor. }
    rewrite (reshape_encode_struct sl fields ots); [|done|done].
    assert (Hfields :
      decode_struct_fields sl ots
        (λ (v' : val) (ot : op_type) (_ : op_type_size_rel ot (StructOp sl ots)),
          decode_op_val v' ot st)
        (sl_members sl)
        (pad_struct (sl_members sl) (encode_op_val <$> fields)
          (λ ly : layout, replicate (ly_size ly) MPoison)) 0 = Some fields).
    { eapply decode_struct_fields_encode.
      + intros v ot Hot ov Hwf_ot Hty_ot ->.
        exact (IH ot Hot ov Hwf_ot Hty_ot).
      + by rewrite drop_0.
      + move: Hwf. simpl. rewrite -Forall2_Forall2_cb. by rewrite drop_0.
      + lia. }
    by rewrite Hfields.
  - simpl in Hwf.
    rewrite bool_decide_true.
    2: { change (length (encode_op_val (OVArray elements)) =
            ly_size (ot_layout (ArrayOp ot len))).
         apply encode_op_val_length; first done. by constructor. }
    assert (Hlengths : Forall2 (λ v sz, length v = sz)
        (encode_op_val <$> elements)
        (replicate len (ly_size (ot_layout ot)))).
    { subst len. induction H as [|element elements Hty Htys IHForall]; simpl; constructor.
      - exact (encode_op_val_length element ot Hwf Hty).
      - exact (IHForall IH). }
    rewrite (reshape_join _ _ Hlengths).
    apply bind_Some. exists elements. split; last done.
    apply list_map_option_alt.
    clear H0 Hlengths.
    induction H as [|element elements Hty Htys IHForall]; simpl; constructor.
    + exact (IH ot (array_ot_smaller ot len) element Hwf Hty).
    + exact IHForall.
  - pose proof (enum_variant_payload_wf el variant_ots tag_int variant ot Hwf H0) as Hwf_payload.
    pose proof (IH ot (enum_variant_ot_smaller el variant_ots tag_int variant ot H0)
      payload Hwf_payload Hty) as Hpayload_dec.
    pose proof (encode_op_val_length payload ot Hwf_payload Hty) as Hpayload_len.
    opose proof* enum_variant_ot_lookup_has_variant as Ha; [done .. | ].
    opose proof (enum_variant_lookup_in_bounds el variant _ _).
    { done. }
    rewrite bool_decide_true.
    2: { change (length (encode_op_val (OVEnum el variant tag payload)) = ly_size (ot_layout (EnumOp el variant_ots tag_int))).
         apply encode_op_val_length; first done. by econstructor. }
    rewrite take_overwrite_val_before.
    3: { pose proof (el_tag_before_data el). lia. }
    2: { rewrite overwrite_val_length.
         - rewrite length_replicate. lia.
         - rewrite i2v_length length_replicate.
           pose proof (el_tag_before_data el) as Htag_before.
           rewrite /it_layout /ly_size in Htag_before. lia. }
    rewrite /it_layout /ly_size.
    rewrite -(i2v_length tag el.(el_tag_it)).
    rewrite take_overwrite_val_0.
    2: { rewrite i2v_length length_replicate.
         pose proof (el_tag_before_data el) as Htag_before.
         rewrite /it_layout /ly_size in Htag_before. lia. }
    rewrite val_to_Z_i2v; last by eapply enum_tag_lookup_in_range.
    simpl.
    rewrite H /=.
    rewrite Ha /lookup_enum_variant_ot H0 /=.
    change (let (ly_size, _) := ot_layout ot in ly_size) with (ly_size (ot_layout ot)).
    rewrite -Hpayload_len.
    rewrite take_drop_overwrite_val.
    2: { rewrite overwrite_val_length.
         - rewrite length_replicate Hpayload_len. lia.
         - rewrite i2v_length length_replicate.
           pose proof (el_tag_before_data el) as Htag_before.
           rewrite /it_layout /ly_size in Htag_before.
           lia. }
    by rewrite Hpayload_dec.
  - rewrite bool_decide_true; first done.
    by rewrite /has_layout_val.
  - by rewrite val_to_char_i2v.
  - rewrite val_to_loc_Some_l2v; last done.
    by rewrite decide_True.
Qed.

Lemma decode_poison_encode_op_val ov ot st :
  op_type_wf ot →
  decode_op_val (replicate (ly_size (ot_layout ot)) MPoison) ot st = Some ov →
  encode_op_val ov = replicate (ly_size (ot_layout ot)) MPoison.
Proof.
  revert ov.
  induction ot as [ot IH] using (well_founded_induction op_type_size_rel_wf).
  intros ov Hwf Hdec.
  destruct ot; simp decode_op_val in Hdec; simpl in Hdec |-*.
  - by destruct (val_to_bool (replicate 1 MPoison)) as [b|] eqn:Hb; simpl in Hdec; simplify_eq.
  - move: Hdec => /fmap_Some[z[Hz ->]]. by apply i2v_of_val_to_Z.
  - done.
  - by destruct (val_to_loc (replicate (ly_size void*) MPoison)) as [l|] eqn:Hl;
      simpl in Hdec; simplify_eq;
      destruct (val_to_bytes (replicate (ly_size void*) MPoison)) as [v'|] eqn:Hv;
      simpl in Hdec; simplify_eq;
      destruct (val_to_Z v' USize) as [a|] eqn:Ha;
      simpl in Hdec; simplify_eq.
  - rewrite bool_decide_true in Hdec.
    2: { rewrite length_replicate. done. }
    apply bind_Some in Hdec as (fields & Hfields & [= <-]).
    rewrite /=.
    rewrite (decode_struct_fields_poison_encode sl ots
      (λ (v' : val) (ot : op_type) (_ : op_type_size_rel ot (StructOp sl ots)),
        decode_op_val v' ot st) (sl_members sl) fields 0); last first.
    { rewrite -Hfields. f_equal.
      rewrite /ly_size /= reshape_replicate_sum.
      rewrite -(list_fmap_compose (λ ly : layout, ly_size ly) (λ sz : nat, replicate sz MPoison)).
      done. }
    { lia. }
    { move: Hwf. simpl. rewrite -Forall2_Forall2_cb. by rewrite drop_0. }
    { intros v ot Hot ov' Hwf_ot Hv Hdec'.
      subst v. eapply IH; first exact Hot; done. }
    rewrite /ly_size /=. by rewrite mjoin_layout_replicate_chunks.
  - rewrite bool_decide_true in Hdec; last by rewrite length_replicate.
    apply bind_Some in Hdec as (elements & Helements & [= <-]).
    apply list_map_option_alt in Helements.
    assert (Hreshape :
        reshape (replicate len (ly_size (ot_layout ot)))
          (replicate (ly_size (mk_array_layout (ot_layout ot) len)) MPoison) =
        replicate len (replicate (ly_size (ot_layout ot)) MPoison)).
    { rewrite ly_size_mk_array_layout.
      replace (ly_size (ot_layout ot) * len)%nat with
        (len * ly_size (ot_layout ot))%nat by lia.
      rewrite -sum_list_replicate reshape_replicate_sum fmap_replicate. done. }
    rewrite Hreshape in Helements.
    clear Hreshape.
    simpl in Hwf.
    pose proof (IH ot (array_ot_smaller ot len)) as IH_ot.
    assert (Henc : encode_op_val <$> elements =
        replicate len (replicate (ly_size (ot_layout ot)) MPoison)).
    { induction len as [|len IHlen] in elements, Helements |-*.
      - inversion Helements. done.
      - simpl in Helements. inversion Helements as [|chunk element chunks elements' Hdec Hdecs]; subst.
        simpl. f_equal.
        + exact (IH_ot element Hwf Hdec).
        + by eapply IHlen. }
    change (mjoin (encode_op_val <$> elements) =
      replicate (ly_size (mk_array_layout (ot_layout ot) len)) MPoison).
    rewrite Henc ly_size_mk_array_layout.
    rewrite -(fmap_replicate (λ sz, replicate sz MPoison) len
      (ly_size (ot_layout ot))).
    rewrite mjoin_replicate_chunks sum_list_replicate. f_equal. lia.
  - rewrite bool_decide_true in Hdec; last by rewrite length_replicate.
    apply bind_Some in Hdec as (tag & Htag & Hdec).
    apply bind_Some in Hdec as (variant & Hvariant & Hdec).
    apply bind_Some in Hdec as (ly & Hly & Hdec).
    apply bind_Some in Hdec as (ot_sig & Hot & Hdec).
    apply bind_Some in Hdec as (payload & Hpayload & [= <-]).
    pose proof (projT2 ot_sig) as Hot_lookup.
    pose proof (enum_variant_payload_wf el variant_ots tag_int variant (projT1 ot_sig) Hwf Hot_lookup) as Hwf_payload.
    opose proof* (enum_variant_ot_lookup_has_variant _ _ _ _ (projT1 ot_sig)) as Ha; [done | apply Hot_lookup | ].
    opose proof (enum_variant_lookup_in_bounds el variant _ _); first done.
    rewrite Ha in Hly. injection Hly as Hpayload_layout.
    assert (Hpayload_poison : encode_op_val payload = replicate (ly_size ly) MPoison).
    { rewrite -Hpayload_layout.
      eapply IH with (y := projT1 ot_sig);
        first exact (enum_variant_ot_smaller el variant_ots tag_int variant (projT1 ot_sig) Hot_lookup).
      - exact Hwf_payload.
      - rewrite -Hpayload.
        rewrite take_drop_replicate.
        + by rewrite -Hpayload_layout.
        + change (ly_size el) with (el_size el).
          subst ly. lia. }
    assert (Htag_poison : i2v tag el.(el_tag_it) = replicate (bytes_per_int el.(el_tag_it)) MPoison).
    { apply i2v_of_val_to_Z.
      rewrite -Htag. rewrite /it_layout /ly_size.
      rewrite take_replicate. f_equal. f_equal.
      pose proof (el_tag_before_data el) as Htag_before.
      rewrite /it_layout /ly_size in Htag_before.
      subst ly. lia. }
    simpl. rewrite Hpayload_poison Htag_poison.
    rewrite overwrite_val_replicate.
    2: { pose proof (el_tag_before_data el) as Htag_before.
         rewrite /it_layout /ly_size in Htag_before.
         subst ly. lia. }
    rewrite overwrite_val_replicate; first done.
    subst ly. lia.
  - rewrite bool_decide_true in Hdec; last by rewrite length_replicate.
    simplify_eq. simpl. done.
  - by destruct (val_to_char (replicate 4 MPoison)) as [z|] eqn:Hz; simpl in Hdec; simplify_eq.
  - done.
Qed.

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
  revert v.
  induction ot as [ot IH] using (well_founded_induction op_type_size_rel_wf).
  intros v. destruct ot; simp decode_op_val; try done.
  - rewrite (decode_struct_fields_stable_lookup sl ots
      (λ v' ot Hot, decode_op_val v' ot st)
      (λ v' ot Hot, decode_op_val v' ot st')).
    + done.
    + intros j v' ot Hot Hlook. exact (IH ot Hot v').
  - destruct (bool_decide
      (length v = ly_size (mk_array_layout (ot_layout ot) len))); simpl; last done.
    generalize (reshape (replicate len (ly_size (ot_layout ot))) v) as chunks.
    intros chunks.
    assert (Hmaps : list_map_option (λ v', decode_op_val v' ot st) chunks =
        list_map_option (λ v', decode_op_val v' ot st') chunks).
    { induction chunks as [|chunk chunks IHchunks]; simpl; first done.
      rewrite (IH ot (array_ot_smaller ot len) chunk) IHchunks. done. }
    by rewrite Hmaps.
  - destruct (bool_decide (length v = ly_size el)); simpl; last done.
    destruct (val_to_Z (take (ly_size (it_layout (el_tag_it el))) v) (el_tag_it el)) as [tag|]; simpl; last done.
    destruct (enum_tag_lookup tag_int tag) as [variant|]; simpl; last done.
    destruct (enum_variant_lookup (el_variants el) variant) as [ly|] eqn:Hly; simpl; last done.
    destruct (lookup_enum_variant_ot variant_ots variant) as [[ot Hot]|] eqn:Hot_sig; simpl; last done.
    rewrite (IH ot (enum_variant_ot_smaller el variant_ots tag_int variant ot Hot)).
    done.
Qed.

Lemma val_to_loc_decode v st l :
  val_to_loc v = Some l →
  decode_op_val v PtrOp st = Some (OVPtr l).
Proof.
  intros Hv.
  simp decode_op_val.
  rewrite Hv//.
Qed.

Lemma val_to_loc_decode_ref v st l :
  val_to_loc v = Some l →
  l.(loc_a) ≠ 0 →
  decode_op_val v RefOp st = Some (OVPtr l).
Proof.
  intros Hv Hnonnull. simp decode_op_val. rewrite Hv /= decide_True //.
Qed.

Lemma decode_ptr_nonnull_ref v st l :
  decode_op_val v PtrOp st = Some (OVPtr l) →
  l.(loc_a) ≠ 0 →
  decode_op_val v RefOp st = Some (OVPtr l).
Proof.
  intros Hdec Hnonnull. simp decode_op_val in Hdec |- *.
  destruct (val_to_loc v) as [l'|] eqn:Hv.
  - injection Hdec as <-. by rewrite decide_True.
  - destruct (val_to_bytes v) as [v'|] eqn:Hbytes; simpl in Hdec |-*; last done.
    destruct (val_to_Z v' USize) as [a|] eqn:Ha; simpl in Hdec |-*; last done.
    injection Hdec as <-. by rewrite decide_True.
Qed.

Lemma decode_ref_inv v st l :
  decode_op_val v RefOp st = Some (OVPtr l) →
  decode_op_val v PtrOp st = Some (OVPtr l) ∧ l.(loc_a) ≠ 0.
Proof.
  simp decode_op_val.
  destruct (val_to_loc v) as [l'|] eqn:Hv.
  - case_decide as Hnonnull; last done. intros [= <-]. split; done.
  - destruct (val_to_bytes v) as [v'|] eqn:Hbytes; simpl; last done.
    destruct (val_to_Z v' USize) as [a|] eqn:Ha; simpl; last done.
    case_decide as Hnonnull; last done. intros [= <-]. split; done.
Qed.

Lemma decode_ref_no_ptr v st :
  decode_op_val v PtrOp st = None →
  decode_op_val v RefOp st = None.
Proof.
  simp decode_op_val.
  destruct (val_to_loc v); first done.
  by destruct (val_to_bytes v) as [v'|]; simpl; last done; destruct (val_to_Z v' USize).
Qed.

Lemma decode_ref_null v st l :
  decode_op_val v PtrOp st = Some (OVPtr l) →
  l.(loc_a) = 0 →
  decode_op_val v RefOp st = None.
Proof.
  intros Hdec Hnull. simp decode_op_val in Hdec |- *.
  destruct (val_to_loc v) as [l'|] eqn:Hv.
  - injection Hdec as <-. rewrite decide_False; congruence.
  - destruct (val_to_bytes v) as [v'|] eqn:Hbytes; simpl in Hdec |-*; last done.
    destruct (val_to_Z v' USize) as [a|] eqn:Ha; simpl in Hdec |-*; last done.
    injection Hdec as <-. rewrite decide_False; first done. simpl in Hnull. congruence.
Qed.

Lemma decode_op_val_array_app v1 v2 ot n1 n2 st :
  length v1 = (n1 * ly_size (ot_layout ot))%nat →
  length v2 = (n2 * ly_size (ot_layout ot))%nat →
  decode_op_val (v1 ++ v2) (ArrayOp ot (n1 + n2)) st =
    (ov1 ← decode_op_val v1 (ArrayOp ot n1) st;
     ov2 ← decode_op_val v2 (ArrayOp ot n2) st;
     match ov1, ov2 with
     | OVArray elements1, OVArray elements2 => Some (OVArray (elements1 ++ elements2))
     | _, _ => None
     end).
Proof.
  intros Hlen1 Hlen2. simp decode_op_val.
  rewrite !ly_size_mk_array_layout length_app Hlen1 Hlen2.
  rewrite !bool_decide_true; try lia.
  rewrite replicate_add reshape_app sum_list_replicate.
  rewrite take_app_length'; last lia.
  rewrite drop_app_length'; last lia.
  rewrite list_map_option_app.
  remember (list_map_option (λ v' : val, decode_op_val v' ot st)
    (reshape (replicate n1 (ly_size (ot_layout ot))) v1)) as result1.
  remember (list_map_option (λ v' : val, decode_op_val v' ot st)
    (reshape (replicate n2 (ly_size (ot_layout ot))) v2)) as result2.
  destruct result1 as [elements1|], result2 as [elements2|]; done.
Qed.

Lemma decode_op_val_array_app_inv v1 v2 ot n1 n2 st elements :
  length v1 = (n1 * ly_size (ot_layout ot))%nat →
  length v2 = (n2 * ly_size (ot_layout ot))%nat →
  decode_op_val (v1 ++ v2) (ArrayOp ot (n1 + n2)) st = Some (OVArray elements) →
  ∃ elements1 elements2,
    decode_op_val v1 (ArrayOp ot n1) st = Some (OVArray elements1) ∧
    decode_op_val v2 (ArrayOp ot n2) st = Some (OVArray elements2) ∧
    elements = elements1 ++ elements2.
Proof.
  intros Hlen1 Hlen2 Hdec.
  rewrite (decode_op_val_array_app v1 v2 ot n1 n2 st Hlen1 Hlen2) in Hdec.
  apply bind_Some in Hdec as (ov1 & Hdec1 & Hdec).
  apply bind_Some in Hdec as (ov2 & Hdec2 & Hdec).
  destruct ov1, ov2; try done.
  injection Hdec as <-. eauto.
Qed.
