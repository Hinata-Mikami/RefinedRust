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
| OVPtr (l : loc)
| OVStruct (sl : struct_layout) (fields : list op_val)
| OVEnum (el : enum_layout) (variant : var_name) (tag : Z)
    (sl : struct_layout) (fields : list op_val)
| OVUntyped (ly : layout) (v : val)
| OVChar (z : Z).

Inductive op_val_has_type : op_val → op_type → Prop :=
| OVBool_has_type b : op_val_has_type (OVBool b) BoolOp
| OVInt_has_type it z : z ∈ it → op_val_has_type (OVInt it z) (IntOp it)
| OVPtr_has_type l : l.(loc_a) ∈ USize → op_val_has_type (OVPtr l) PtrOp
| OVStruct_has_type sl fields ots :
    Forall2 op_val_has_type fields ots →
    op_val_has_type (OVStruct sl fields) (StructOp sl ots)
| OVUntyped_has_type ly v : v `has_layout_val` ly → op_val_has_type (OVUntyped ly v) (UntypedOp ly)
| OVChar_has_type z : is_valid_char z → op_val_has_type (OVChar z) CharOp.

Definition overwrite_val (off : nat) (w v : val) : val :=
  take off v ++ w ++ drop (off + length w) v.

Fixpoint encode_op_val (ov : op_val) : val :=
  match ov with
  | OVBool b => val_of_bool b
  | OVInt it z => i2v z it
  | OVPtr l => l2v l
  | OVStruct sl fields =>
      mjoin $ pad_struct sl.(sl_members) (encode_op_val <$> fields)
        (λ ly, replicate (ly_size ly) MPoison)
  | OVEnum el _ tag sl fields =>
      overwrite_val el.(el_data_offset)
        (mjoin $ pad_struct sl.(sl_members) (encode_op_val <$> fields)
          (λ ly, replicate (ly_size ly) MPoison)) $
      overwrite_val el.(el_tag_offset) (i2v tag el.(el_tag_it)) $
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
  let fix variant_op_type_list_size (variant_ots : list (var_name * list op_type)) : nat :=
    match variant_ots with
    | [] => 0%nat
    | (_, ots) :: variant_ots => Nat.add (op_type_list_size ots) (variant_op_type_list_size variant_ots)
    end in
  match ot with
  | StructOp _ ots => S (op_type_list_size ots)
  | EnumOp _ variant_ots _ => S (variant_op_type_list_size variant_ots)
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

Equations decode_op_val (v : val) (ot : op_type) (st : (gset addr * heap_state)) : option op_val by wf ot op_type_size_rel :=
  decode_op_val v BoolOp st := OVBool <$> val_to_bool v;
  decode_op_val v (IntOp it) st := OVInt it <$> val_to_Z v it;
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
  decode_op_val v (EnumOp _ _ _) st := None;
  decode_op_val v (UntypedOp ly) st :=
      if bool_decide (length v = ly_size ly) then Some (OVUntyped ly v) else None;
  decode_op_val v CharOp st := OVChar <$> val_to_char v.
Next Obligation.
  done.
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
  - destruct (val_to_loc v) as [l|] eqn:Hl.
    + apply val_to_loc_length. eexists. done.
    + apply bind_Some in Hdec as (v' & Hv & Hdec).
      apply bind_Some in Hdec as (a & Ha & Hov).
      apply val_to_Z_length in Ha.
      apply val_to_bytes_length in Hv.
      rewrite /has_layout_val /= -Hv Ha. done.
  - case_bool_decide as Hly; last done.
    rewrite /has_layout_val /=. done.
  - done.
  - case_bool_decide as Hly; last done.
    by rewrite /has_layout_val.
  - move: Hdec => /fmap_Some[z[Hz Hov]]. by apply val_to_char_length in Hz.
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
  - done.
  - case_bool_decide as Hly; last done.
    injection Hdec as <-. constructor. by rewrite /has_layout_val.
  - move: Hdec => /fmap_Some[z[Hz Hov]]. simplify_eq. constructor.
    rewrite /val_to_char in Hz.
    move: Hz => /bind_Some[z'[Hz Hvalid]].
    case_decide; simplify_eq; done.
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
  - rewrite i2v_length. done.
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
  - rewrite bool_decide_true; first done.
    by rewrite /has_layout_val.
  - by rewrite val_to_char_i2v.
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
  - done.
  - rewrite bool_decide_true in Hdec; last by rewrite length_replicate.
    simplify_eq. simpl. done.
  - by destruct (val_to_char (replicate 4 MPoison)) as [z|] eqn:Hz; simpl in Hdec; simplify_eq.
Qed.

(** ** MemCast: Transforming bytes read from memory.
  [mem_cast] should only be called with length of [v] matching [ot]
  The dependence on [st] is not necessary right now, but should one day make it easier to support exposed provenance casts. *)
Definition mem_cast (v : val) (ot : op_type) (st : (gset addr * heap_state)) : val :=
  resize (length v) MPoison $
    default (replicate (length v) MPoison) $
      encode_op_val <$> decode_op_val v ot st.

Definition mem_cast_id (v : val) (ot : op_type) : Prop :=
  ∀ st, mem_cast v ot st = v.

Lemma mem_cast_length v ot st:
  length (mem_cast v ot st) = length v.
Proof.
  rewrite /mem_cast length_resize. lia.
Qed.


Lemma mem_cast_id_loc' l v :
  val_of_loc l = Some v →
  mem_cast_id v PtrOp.
Proof.
  move => Hv st. rewrite /mem_cast. simp decode_op_val.
  rewrite (val_to_of_loc _ _ Hv) /=.
  rewrite (l2v_correct _ _ Hv). by rewrite resize_all.
Qed.
Lemma mem_cast_id_loc l v :
  val_to_loc v = Some l →
  mem_cast_id v PtrOp.
Proof.
  move => Hl st. rewrite /mem_cast. simp decode_op_val.
  rewrite Hl /= (l2v_correct' _ _ Hl). by rewrite resize_all.
Qed.
Lemma mem_cast_id_int it v n :
  val_to_Z v it = Some n →
  mem_cast_id v (IntOp it).
Proof.
  move => Hi st. rewrite /mem_cast. simp decode_op_val.
  rewrite Hi /= (i2v_of_val_to_Z _ _ _ Hi). by rewrite resize_all.
Qed.

Lemma mem_cast_id_bool v b :
  val_to_bool v = Some b →
  mem_cast_id v BoolOp.
Proof.
  move => Hb st. rewrite /mem_cast. simp decode_op_val.
  rewrite Hb /= (val_of_to_bool _ _ Hb). by rewrite resize_all.
Qed.

Lemma mem_cast_id_char v z :
  val_to_char v = Some z →
  mem_cast_id v CharOp.
Proof.
  move => Hz st. rewrite /mem_cast. simp decode_op_val.
  rewrite Hz /= (val_of_to_char _ _ Hz). by rewrite resize_all.
Qed.

Lemma mem_cast_struct_reshape sl v st ots fields:
  decode_op_val v (StructOp sl ots) st = Some (OVStruct sl fields) →
  reshape (ly_size <$> (sl_members sl).*2) (mem_cast v (StructOp sl ots) st) =
  reshape (ly_size <$> (sl_members sl).*2)
    (resize (length v) MPoison (encode_op_val (OVStruct sl fields))).
Proof.
  intros Hdec. rewrite /mem_cast Hdec /=. done.
Qed.

Lemma mem_cast_idemp v ot st st' :
  v `has_layout_val` (ot_layout ot) →
  op_type_wf ot →
  mem_cast (mem_cast v ot st) ot st' = mem_cast v ot st.
Proof.
  intros Hly Hwf.
  rewrite /mem_cast.
  destruct (decode_op_val v ot st) as [ov|] eqn:Hdec; simpl.
  - have Hty : op_val_has_type ov ot by eapply decode_op_val_has_type.
    have Hlen : length (encode_op_val ov) = length v.
    { rewrite (encode_op_val_length _ _ Hwf Hty). symmetry. exact Hly. }
    replace (resize (length v) MPoison (encode_op_val ov)) with (encode_op_val ov).
    2: { rewrite resize_all_alt; last by symmetry. done. }
    rewrite Hlen (decode_encode_op_val _ _ _ Hwf Hty) /=.
    by rewrite resize_all_alt.
  - rewrite !resize_replicate !length_replicate Hly.
    destruct (decode_op_val (replicate (ly_size (ot_layout ot)) MPoison) ot st') as [ov|] eqn:Hpoison; simpl.
    + rewrite (decode_poison_encode_op_val _ _ _ Hwf Hpoison). by rewrite resize_replicate.
    + by rewrite resize_replicate.
Qed.

Global Typeclasses Opaque mem_cast_id.
Arguments mem_cast : simpl never.
