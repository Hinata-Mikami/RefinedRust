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
| OVUntyped_has_type ly v : op_val_has_type (OVUntyped ly v) (UntypedOp ly)
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
      fields ← decode_struct_fields sl ots (λ v' ot Hot, decode_op_val v' ot st)
        sl.(sl_members) (reshape (ly_size <$> sl.(sl_members).*2) v) 0%nat;
      Some (OVStruct sl fields);
  decode_op_val v (EnumOp _ _ _) st := None;
  decode_op_val v (UntypedOp ly) st := Some (OVUntyped ly v);
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
  - apply bind_Some in Hdec as (fields & Hfields & Hov).
    injection Hov as <-. constructor.
    rewrite -(drop_0 ots).
    eapply decode_struct_fields_has_type; last done.
    intros v' ot' Hot ov' Hdec.
    exact (IH ot' Hot v' st ov' Hdec).
  - done.
  - injection Hdec as <-. constructor.
  - move: Hdec => /fmap_Some[z[Hz Hov]]. simplify_eq. constructor.
    rewrite /val_to_char in Hz.
    move: Hz => /bind_Some[z'[Hz Hvalid]].
    case_decide; simplify_eq; done.
Qed.

(** ** MemCast: Transforming bytes read from memory.
  [mem_cast] should only be called with length of [v] matching [ot]
  The dependence on [st] is not necessary right now, but should one day make it easier to support exposed provenance casts. *)
Fixpoint mem_cast (v : val) (ot : op_type) (st : (gset addr * heap_state)) : val :=
  default (replicate (length v) MPoison) (
  match ot with
  | PtrOp =>
    if val_to_loc v is Some l then Some v else
      (* interpret as an integer *)
      v' ← val_to_bytes v;
      a ← val_to_Z v' USize;
      val_of_loc (Loc ProvNone a)
  | IntOp it => val_to_bytes v
  | CharOp => if val_to_char v is Some _ then val_to_bytes v else None
  | BoolOp => if val_to_bool v is Some _ then val_to_bytes v else None
  (* The resize technically should not be necessary since mem_cast
  should only be called if the size is equal to the length of the
  value. But adding it makes proving mem_cast_length a lot easier. *)
  | StructOp sl ots =>
      (* TODO: maybe this should work by decoding the struct val first? *)
      (* We could also have a structured value representation (dependently indexed by op_type) *)
      Some $ resize (length v) MPoison $ mjoin $ zip_with (λ f x, f x)
      (pad_struct sl.(sl_members)
                  (((λ ot, λ v, mem_cast v ot st) <$> ots))
                  (λ ly _, (replicate (ly_size ly) MPoison)))
      (reshape (ly_size <$> sl.(sl_members).*2) v)
  | EnumOp _ _ _ => None
  | UntypedOp _ => Some v
  end).

Definition mem_cast_id (v : val) (ot : op_type) : Prop :=
  ∀ st, mem_cast v ot st = v.

Lemma mem_cast_length v ot st:
  length (mem_cast v ot st) = length v.
Proof.
  destruct ot => /=.
  - destruct (val_to_bool v) => /=.
    + destruct (val_to_bytes v) eqn:Hv => //=.
      * move: Hv => /length_mapM. lia.
      * by rewrite length_replicate.
    + by rewrite length_replicate.
  - destruct (val_to_bytes v) eqn:Hv => //=.
    + move: Hv => /length_mapM. lia.
    + by rewrite length_replicate.
  - case_match => //=.
    destruct (val_to_bytes v) as [v'|] eqn:Hv => //=. 2: by rewrite length_replicate.
    move: Hv => /length_mapM ->.
    destruct (val_to_Z v') eqn:Hv' => //=. 2: by rewrite length_replicate.
    specialize (val_to_Z_in_range _ _ _ Hv') as Hel.
    move: Hv' => /val_to_Z_length /=?.
    rewrite val_of_loc_Some; last done.
    rewrite val_of_loc_unchecked_length//.
  - by rewrite length_resize.
  - by rewrite length_replicate.
  - done.
  - destruct (val_to_char v) => /=.
    + destruct (val_to_bytes v) eqn:Hv => //=.
      * move: Hv => /length_mapM. lia.
      * by rewrite length_replicate.
    + by rewrite length_replicate.
Qed.


Lemma mem_cast_id_loc' l v :
  val_of_loc l = Some v →
  mem_cast_id v PtrOp.
Proof.
  move => ? st. rewrite /mem_cast /=.
  unfold mem_cast_id; simpl.
  rewrite (val_to_of_loc l); done.
Qed.
Lemma mem_cast_id_loc l v :
  val_to_loc v = Some l →
  mem_cast_id v PtrOp.
Proof.
  move => Hl st. rewrite /mem_cast /=.
  rewrite /mem_cast_id; simpl.
  intros. rewrite Hl//.
Qed.
Lemma mem_cast_id_int it v n :
  val_to_Z v it = Some n →
  mem_cast_id v (IntOp it).
Proof. move => Hi st. rewrite /mem_cast /=. by erewrite val_to_bytes_id. Qed.

Lemma mem_cast_id_bool v b :
  val_to_bool v = Some b →
  mem_cast_id v BoolOp.
Proof. move => Hb st. rewrite /mem_cast /= Hb. by erewrite val_to_bytes_id_bool. Qed.

Lemma mem_cast_id_char v z :
  val_to_char v = Some z →
  mem_cast_id v CharOp.
Proof. move => Hb st. rewrite /mem_cast /= Hb. by erewrite val_to_bytes_id_char. Qed.

Lemma mem_cast_struct_reshape sl v st ots:
  length ots = length (field_names (sl_members sl)) →
  v `has_layout_val` sl →
  (∀ i v' n ly,
      reshape (ly_size <$> (sl_members sl).*2) v !! i = Some v' →
      sl_members sl !! i = Some (Some n, ly) →
      v' `has_layout_val` ly) →
  reshape (ly_size <$> (sl_members sl).*2) (mem_cast v (StructOp sl ots) st) =
  (zip_with (λ f x, f x)
            (pad_struct (sl_members sl) ((λ ot v, mem_cast v ot st) <$> ots) (λ ly _, replicate (ly_size ly) MPoison))
            (reshape (ly_size <$> (sl_members sl).*2) v)).
Proof.
  move => ? Hv Hly. rewrite /mem_cast/=-/mem_cast resize_all_alt. 2: {
    rewrite length_join Hv {1}/ly_size /=.
    apply: sum_list_eq.
    (* TODO: This is the same proof as below. Somehow unify these two proofs. *)
    apply Forall2_same_length_lookup_2.
    { rewrite !length_fmap length_zip_with length_reshape pad_struct_length !length_fmap. lia. }
    move => i n1 n2. rewrite !list_lookup_fmap.
    move => /fmap_Some[?[/fmap_Some[?[??]]?]]; simplify_eq.
    move => /fmap_Some[?[/lookup_zip_with_Some[?[?[?[Hs?]]]]?]].
    move: Hs => /pad_struct_lookup_Some[|n[?[? Hor]]]. { by rewrite length_fmap. }
    unfold field_list in *. simplify_eq/=.
    destruct Hor as [[? Hl] | [??]]; simplify_eq/=. 2: by rewrite length_replicate.
    move: Hl. rewrite list_lookup_fmap. move => /fmap_Some[?[??]]. simplify_eq.
    destruct n as [n|] => //. rewrite mem_cast_length. by erewrite Hly.
  }
  rewrite reshape_join //.
  apply Forall2_same_length_lookup_2.
  { rewrite length_zip_with length_reshape pad_struct_length !length_fmap. lia. }
  move => i v' sz /lookup_zip_with_Some[?[?[?[/pad_struct_lookup_Some Hl ?]]]].
  move: Hl => [|n[?[Hin2 Hor]]]. { rewrite length_fmap //. } simplify_eq.
  rewrite !list_lookup_fmap => /fmap_Some[?[/fmap_Some[?[Hin ?]]?]]. rewrite Hin2 in Hin. simplify_eq/=.
  destruct Hor as [[? Hl] |[??]]; simplify_eq. 2: by rewrite length_replicate.
  move: Hl. rewrite list_lookup_fmap => /fmap_Some[?[??]]. simplify_eq. rewrite mem_cast_length.
  destruct n => //. by apply: Hly.
Qed.

Lemma mem_cast_idemp v ot st st' :
  v `has_layout_val` (ot_layout ot) →
  op_type_wf ot →
  mem_cast (mem_cast v ot st) ot st' = mem_cast v ot st.
Proof.
  intros Hly Hwf.
  induction ot as [ | | | sl ots IH | el variant_ots tag_int IH | | ] using op_type_recursor in v, Hly, Hwf|-*; simpl.
  - rewrite /mem_cast.
    destruct (val_to_bool v) as [b | ] eqn:Heq.
    + rewrite (val_to_bytes_id_bool _ b); last done. simpl.
      rewrite Heq. simpl. rewrite (val_to_bytes_id_bool _ b); done.
    + simpl. destruct v; simpl; first done. rewrite length_replicate. done.
  - rewrite /mem_cast.
    destruct (val_to_bytes v) as [v' | ] eqn:Heq; simpl.
    + erewrite val_to_bytes_idemp; done.
    + rewrite length_replicate.
      generalize (length v). intros []; done.
  - rewrite /mem_cast.
    destruct (val_to_loc v) as [l | ] eqn:Heq; simpl.
    { rewrite Heq. done. }
    destruct (val_to_bytes v) as [v' | ] eqn:Heq'; simpl.
    + destruct (val_to_Z v' USize) as [ z | ] eqn:Heq2; simpl.
      * rewrite val_of_loc_Some; last by eapply val_to_Z_in_range.
        rewrite (val_to_of_loc (Loc ProvNone z)) //.
        rewrite val_of_loc_Some//. by eapply val_to_Z_in_range.
      * destruct v; simpl; first done.
        rewrite length_replicate. done.
    + destruct v; simpl; first done.
      rewrite length_replicate //.
  - rewrite /mem_cast. fold mem_cast.
    simpl. rewrite length_resize.
    simpl in Hly.
    f_equiv. f_equiv.

    move: Hly Hwf.
    rewrite /has_layout_val /layout_of {1}/ly_size/=.
    generalize (sl_members sl) => f Hly Hwf.
    clear sl.

    induction f as [ | [name ly] f IH'] in v, ots, Hly, Hwf, IH |-*; simpl; first done.
    simpl in Hly.
    destruct name as [ name | ].
    + destruct ots as [ | ot ots]; simpl; first done.
      simpl in Hwf; destruct Hwf as ((Hwf1 & <-) & Hwf).
      rewrite take_resize.
      rewrite resize_app; first last.
      { rewrite mem_cast_length length_take//. }
      inversion IH as [ | ? IH1 ? IH2 ]; subst.

      f_equiv.
      * apply IH1; last done.
        rewrite /has_layout_val length_take. lia.
      * (* use IH *)
        specialize (IH' (drop (ly_size (ot_layout ot)) v) _ IH2).
        rewrite drop_resize_le; last lia.
        rewrite -{2}IH'; last done; first last.
        { rewrite length_drop. unfold fmap. lia. }
        f_equiv; first done.
        f_equiv; first done.
        rewrite length_drop.
        f_equiv.
        rewrite drop_app_length'; first done.
        rewrite mem_cast_length length_take. lia.
    + (* padding field *)
      f_equiv.
      rewrite drop_resize_le; last lia.
      specialize (IH' (drop (ly_size ly) v) _ IH).
      rewrite -{2}IH'; last done; first last.
      { rewrite length_drop. unfold fmap. lia. }
      f_equiv. f_equiv; first done.
      rewrite length_drop.
      f_equiv.
      rewrite drop_app_length'; first done.
      rewrite length_replicate//.
  - rewrite /mem_cast. rewrite !length_replicate. done.
  - done.
  - rewrite /mem_cast.
    destruct (val_to_char v) as [z | ] eqn:Heq.
    + rewrite (val_to_bytes_id_char _ z); last done. simpl.
      rewrite Heq. simpl. rewrite (val_to_bytes_id_char _ z); done.
    + rewrite length_replicate.
      generalize (length v) as n. simpl.
      clear.
      intros n. case_match eqn:Heq1; last done.
      destruct (val_to_bytes _) eqn:Heq; last done.
      clear -Heq. simpl.
      destruct n; simpl in Heq. { injection Heq as <-; done. }
      done.
Qed.

Global Typeclasses Opaque mem_cast_id.
Arguments mem_cast : simpl never.
