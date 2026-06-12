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
