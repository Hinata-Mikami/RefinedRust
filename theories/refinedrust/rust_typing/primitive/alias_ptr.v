From refinedrust Require Export type ltypes programs.
From refinedrust Require Import memcasts ltype_rules value int unit.
From refinedrust Require Import options.

(** * Raw pointers *)

(** A specialized version of values [value_t] for pointers.
  This is mainly useful if we want to specify ownership of allocations in an ADT separately (e.g. in RawVec) from the field of the struct actually containing the pointer.
  Disadvantage: this does not have any useful interaction laws with the AliasLtype, and we need to duplicate the place typing lemma for both of these. *)
Section alias.
  Context `{!typeGS Σ}.

  Definition alias_ptr_own_val_def (π : thread_id) (l : loc) (v : val) : iProp Σ :=
    ⌜val_decodes_to_loc v l⌝%I.
  Definition alias_ptr_own_val_aux : seal (@alias_ptr_own_val_def).
  Proof. by eexists. Qed.
  Definition alias_ptr_own_val := alias_ptr_own_val_aux.(unseal).
  Definition alias_ptr_own_val_unfold : @alias_ptr_own_val = @alias_ptr_own_val_def := alias_ptr_own_val_aux.(seal_eq).

  Lemma alias_ptr_own_val_to_decodes π l v :
    alias_ptr_own_val π l v -∗ ⌜val_decodes_to_loc v l⌝.
  Proof. rewrite alias_ptr_own_val_unfold. iIntros "%Hv". done. Qed.

  Lemma val_decodes_to_loc_in_usize v l :
    val_decodes_to_loc v l →
    l.(loc_a) ∈ USize.
  Proof.
    intros Hdec. specialize (Hdec inhabitant).
    pose proof (decode_op_val_has_type _ _ _ _ Hdec) as Hty.
    inversion Hty; done.
  Qed.

  Program Definition alias_ptr_t : type locRT := {|
    st_own π (l : loc) v :=
      alias_ptr_own_val π l v;
    st_syn_type := PtrSynType;
    st_has_op_type ot := is_ptr_ot ot;
  |}.
  Next Obligation.
    rewrite alias_ptr_own_val_unfold.
    iIntros (π l v Hv). iExists void*.
    iPureIntro. split; first by apply syn_type_has_layout_ptr.
    by apply val_decodes_to_loc_length in Hv.
  Qed.
  Next Obligation.
    unfold is_ptr_ot.
    iIntros (ot Hot).
    destruct ot; try done.
    - by apply syn_type_has_layout_ptr.
    - subst. by apply syn_type_has_layout_ptr.
  Qed.
  Next Obligation.
    unfold is_ptr_ot.
    intros ot Hot. destruct ot; done.
  Qed.
  Next Obligation. rewrite alias_ptr_own_val_unfold. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    rewrite alias_ptr_own_val_unfold.
    iIntros (ot st π l v Hot) "%Hv".
    iPureIntro.
    destruct ot as [| | | | | |ly| ]; simpl in Hot; try done.
    - exists (OVPtr l). apply Hv.
    - subst ly. exists (OVUntyped void* v). simp decode_op_val.
      rewrite bool_decide_true; first done.
      by apply val_decodes_to_loc_length in Hv.
  Qed.
  Next Obligation.
    rewrite alias_ptr_own_val_unfold.
    iIntros (ot st π l v v' Hot Hsame) "%Hv".
    iPureIntro. by eapply val_decodes_to_loc_same_decoded.
  Qed.
  Next Obligation.
    intros ly Hst. apply syn_type_has_layout_ptr_inv in Hst as ->.
    done.
  Qed.

  Global Instance alias_ptr_t_copy : Copyable (alias_ptr_t).
  Proof. apply _. Qed.
  Global Instance alias_ptr_t_sized : TySized (alias_ptr_t).
  Proof. apply _. Qed.

End alias.

Global Hint Unfold alias_ptr_t : tyunfold.

Section rules.
  Context `{!typeGS Σ}.

  (* TODO: expensive instance since this will always trigger on a prove_with_subtype.
    Consider using a weaker solver. *)
  Lemma alias_ptr_simplify_goal_fast π (l l2 : loc) m `{!CanSolve (l.(loc_a) ∈ USize)} T :
    (⌜l = l2⌝ ∗ ⌜m = MetaNone⌝ ∗ T)
    ⊢ simplify_goal (l ◁ᵥ{π, m} l2 @ alias_ptr_t) T.
  Proof.
    rewrite /simplify_goal.
    iIntros "(<- & -> & $)".
    unfold CanSolve in *.
    rewrite /ty_own_val/= alias_ptr_own_val_unfold. iR. iPureIntro.
    by apply l2v_decodes_to_loc.
  Qed.
  Definition alias_ptr_simplify_goal_fast_inst := [instance @alias_ptr_simplify_goal_fast with 0%N].
  Global Existing Instance alias_ptr_simplify_goal_fast_inst.

  (* Lower priority instance that requires a loc_in_bounds fact *)
  Lemma alias_ptr_simplify_goal (v : val) π (l : loc) m T :
    (⌜v = l⌝ ∗ ⌜m = MetaNone⌝ ∗ ∃ a b, loc_in_bounds l a b ∗ T)
    ⊢ simplify_goal (v ◁ᵥ{π, m} l @ alias_ptr_t) T.
  Proof.
    rewrite /simplify_goal.
    iIntros "(-> & -> & %a & %b & Hlb & $)".
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
    rewrite /ty_own_val/= alias_ptr_own_val_unfold. iR. iPureIntro.
    by apply l2v_decodes_to_loc.
  Qed.
  Definition alias_ptr_simplify_goal_inst := [instance @alias_ptr_simplify_goal with 1%N].
  Global Existing Instance alias_ptr_simplify_goal_inst.

  Global Program Instance learn_from_hyp_val_alias_ptr l :
    LearnFromHypVal (alias_ptr_t) l | 10 :=
    {| learn_from_hyp_val_Q := ⌜l.(loc_a) ∈ USize⌝ |}.
  Next Obligation.
    iIntros (??????) "Hv".
    rewrite /ty_own_val/= alias_ptr_own_val_unfold.
    iDestruct "Hv" as "(-> & %Hv)".
    iModIntro. iPureIntro.
    split; first done.
    by apply val_decodes_to_loc_in_usize in Hv.
  Qed.

  (* In case we introduce a value, override and get something stronger *)
  Global Program Instance learn_from_hyp_alias_ptr v π m l :
    LearnFromHyp (v ◁ᵥ{π, m} l @ alias_ptr_t) | 10 :=
    {| learn_from_hyp_Q := ⌜m = MetaNone⌝ ∗ ⌜l.(loc_a) ∈ USize⌝ |}.
  Next Obligation.
    iIntros (??????) "Hv".
    rewrite /ty_own_val/= alias_ptr_own_val_unfold.
    iDestruct "Hv" as "(-> & %Hv)".
    iModIntro. iPureIntro.
    split_and!; try done.
    by apply val_decodes_to_loc_in_usize in Hv.
  Qed.
End rules.

Section comparison.
  Context `{!typeGS Σ}.

  Lemma type_relop_ptr_ptr E L f v1 (l1 : loc) v2 (l2 : loc) (T : typed_val_expr_cont_t) b op :
    match op with
    | EqOp rit => Some (bool_decide (l1.(loc_a) = l2.(loc_a))%Z, rit)
    | NeOp rit => Some (bool_decide (l1.(loc_a) ≠ l2.(loc_a))%Z, rit)
    | LtOp rit => Some (bool_decide (l1.(loc_a) < l2.(loc_a))%Z, rit)
    | GtOp rit => Some (bool_decide (l1.(loc_a) > l2.(loc_a))%Z, rit)
    | LeOp rit => Some (bool_decide (l1.(loc_a) <= l2.(loc_a))%Z, rit)
    | GeOp rit => Some (bool_decide (l1.(loc_a) >= l2.(loc_a))%Z, rit)
    | _ => None
    end = Some (b, U8) →
    T L (val_of_bool b) MetaNone bool bool_t b
    ⊢ typed_bin_op E L f v1 (v1 ◁ᵥ{f.1, MetaNone} l1 @ alias_ptr_t) v2 (v2 ◁ᵥ{f.1, MetaNone} l2 @ alias_ptr_t) op (PtrOp) (PtrOp) T.
  Proof.
    rewrite /ty_own_val/= alias_ptr_own_val_unfold.
    iIntros "%Hop HT (_ & %Hv1) (_ & %Hv2)" (Φ) "#CTX #HE HL Hf HΦ".
    subst.
    iApply wp_ptr_relop; [done | done | | done | ].
    { by apply val_of_bool_iff_val_of_Z. }
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf") => //.
    rewrite /ty_own_val/= bool_own_val_unfold. by destruct b.
  Qed.

  Global Instance type_eq_ptr_ptr_inst E L f v1 l1 v2 l2 :
    TypedBinOpVal E L f v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (EqOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L f v1 l1 v2 l2 T (bool_decide (l1.(loc_a) = l2.(loc_a))) (EqOp U8) eq_refl).
  Global Instance type_ne_ptr_ptr_inst E L f v1 l1 v2 l2 :
    TypedBinOpVal E L f v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (NeOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L f v1 l1 v2 l2 T (bool_decide (l1.(loc_a) ≠ l2.(loc_a))) (NeOp U8) eq_refl).
  Global Instance type_lt_ptr_ptr_inst E L f v1 l1 v2 l2 :
    TypedBinOpVal E L f v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (LtOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L f v1 l1 v2 l2 T (bool_decide (l1.(loc_a) < l2.(loc_a))%Z) (LtOp U8) eq_refl).
  Global Instance type_gt_ptr_ptr_inst E L f v1 l1 v2 l2 :
    TypedBinOpVal E L f v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (GtOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L f v1 l1 v2 l2 T (bool_decide (l1.(loc_a) > l2.(loc_a))%Z) (GtOp U8) eq_refl).
  Global Instance type_le_ptr_ptr_inst E L f v1 l1 v2 l2 :
    TypedBinOpVal E L f v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (LeOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L f v1 l1 v2 l2 T (bool_decide (l1.(loc_a) <= l2.(loc_a))%Z) (LeOp U8) eq_refl).
  Global Instance type_ge_ptr_ptr_inst E L f v1 l1 v2 l2 :
    TypedBinOpVal E L f v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (GeOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L f v1 l1 v2 l2 T (bool_decide (l1.(loc_a) >= l2.(loc_a))%Z) (GeOp U8) eq_refl).
End comparison.

Section cast.
  Context `{!typeGS Σ}.

  Lemma type_cast_ptr_ptr E L f π(l : loc) v (T : typed_val_expr_cont_t) :
    (⌜π = f.1⌝ ∗ ∀ v, T L v MetaNone _ (alias_ptr_t) (l))
    ⊢ typed_un_op E L f v (v ◁ᵥ{π, MetaNone} l @ alias_ptr_t)%I (CastOp (PtrOp)) PtrOp T.
  Proof.
    rewrite /ty_own_val/= alias_ptr_own_val_unfold.
    iIntros "(-> & HT) (_ & %) %Φ #CTX #HE HL Hf HΦ".
    iApply wp_cast_loc; first done.
    iApply physical_step_intro. iNext. iApply ("HΦ" with "HL Hf [] HT").
    rewrite /ty_own_val/= alias_ptr_own_val_unfold. iR. done.
  Qed.
  Definition type_cast_ptr_ptr_inst := [instance @type_cast_ptr_ptr].
  Global Existing Instance type_cast_ptr_ptr_inst.

  Lemma type_cast_ptr_int π E L f (l : loc) v (T : typed_val_expr_cont_t) :
    (⌜π = f.1⌝ ∗ ∀ v, T L v MetaNone _ (int USize) (l.(loc_a)))
    ⊢ typed_un_op E L f v (v ◁ᵥ{π, MetaNone} l @ alias_ptr_t)%I (CastOp (IntOp USize)) PtrOp T.
  Proof.
    rewrite /ty_own_val/= alias_ptr_own_val_unfold.
    iIntros "(-> & HT) (_ & %Hdec) %Φ #CTX #HE HL Hf HΦ".
    opose proof* val_decodes_to_loc_in_usize as Husize; first done.
    odestruct (val_of_Z_is_Some _ _ _) as (? & ?); first apply Husize.
    iApply wp_cast_ptr_int; [done.. | ].
    iApply physical_step_intro. iNext. iApply ("HΦ" with "HL Hf [] HT") => //.
    rewrite /ty_own_val/= int_own_val_unfold.
    iR.
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_cast_ptr_int_inst := [instance @type_cast_ptr_int].
  Global Existing Instance type_cast_ptr_int_inst.

  Lemma type_cast_int_ptr π E L f (l : Z) v (T : typed_val_expr_cont_t) :
    (⌜π = f.1⌝ ∗ ((Loc ProvNone l ◁ₗ[π, Owned] .@ ◁ unit_t) -∗
      T L (l2v (Loc ProvNone l)) MetaNone _ alias_ptr_t (Loc ProvNone l)))
    ⊢ typed_un_op E L f v (v ◁ᵥ{π, MetaNone} l @ int USize)%I (CastOp PtrOp) (IntOp USize) T.
  Proof.
    rewrite /ty_own_val/= int_own_val_unfold.
    iIntros "(-> & HT) (_ & %Husize) %Φ #CTX #HE HL Hf HΦ".
    pose proof (val_to_Z_in_range _ _ _ Husize) as [Hmin Hmax].
    rewrite MinInt_unsigned_0 in Hmin; last done.
    (*odestruct (val_of_Z_is_Some _ _ _) as (? & ?); first apply Husize.*)
    iApply wp_cast_int_ptr_prov_none.
    { done. }
    { done. }
    { move: Hmax. rewrite MaxInt_eq. done. }
    { done. }
    iApply physical_step_intro. iNext. iIntros (v1) "%Hv Hl".

    set (l2 := Loc ProvNone l).
    iAssert (l2 ◁ₗ[f.1, Owned] .@ ◁ unit_t)%I with "[Hl]" as "Hl2".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists _. simpl.
      iSplitR. { iPureIntro. by apply syn_type_has_layout_unit. }
      iSplitR. { iPureIntro. rewrite /has_layout_loc/aligned_to.
        eapply Z.divide_1_l. }
      iSplitR; first done.
      iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
      iSplitR; first done.
      iExists (). iSplitR; first done.
      iModIntro. iExists []. iFrame. rewrite /ty_own_val /= //. }

    rewrite (l2v_correct _ v1); last done.
    iApply ("HΦ" with "HL Hf [] (HT Hl2)") => //.

    rewrite /ty_own_val/= alias_ptr_own_val_unfold. iR.
    iPureIntro. apply val_to_loc_decodes_to_loc. by apply val_to_of_loc.
  Qed.
  Definition type_cast_int_ptr_inst := [instance @type_cast_int_ptr].
  Global Existing Instance type_cast_int_ptr_inst.
End cast.

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_ofty_alias_ptr_owned E L f l l2 bmin0 P T :
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π2 = f.1⌝ ∗
      typed_place E L f l2 lt2 r2 UpdInit b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (◁ alias_ptr_t) (# l2)
              (l2 ◁ₗ[f.1, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place E L f l (◁ alias_ptr_t) (#l2) bmin0 (Owned) (DerefPCtx Na1Ord PtrOp :: P) T.
  Proof.
    iDestruct 1 as ((rt2 & [[[lt2 r2] b2] π2])) "(Hl2 & -> & HP)". simpl.
    iApply typed_place_ofty_access_val_owned. { rewrite ty_has_op_type_unfold; done. }
    iIntros (? v ?) "Hv !>". rewrite /ty_own_val /=.
    iDestruct "Hv" as "(_ & Hv)".
    iPoseProof (alias_ptr_own_val_to_decodes with "Hv") as "%Hv".
    iExists l2, _, _, _, _.
    iR.
    iFrame "Hv Hl2 HP". done.
  Qed.
  Definition typed_place_ofty_alias_ptr_owned_inst := [instance @typed_place_ofty_alias_ptr_owned].
  Global Existing Instance typed_place_ofty_alias_ptr_owned_inst | 30.

  Lemma typed_place_ofty_alias_ptr_uniq E L f l l2 bmin0 κ γ P T :
    ⌜lctx_lft_alive E L κ⌝ ∗
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π2 = f.1⌝ ∗
      typed_place E L f l2 lt2 r2 UpdInit b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (◁ alias_ptr_t) (# l2)
              (l2 ◁ₗ[f.1, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place E L f l (◁ alias_ptr_t) (#l2) bmin0 (Uniq κ γ) (DerefPCtx Na1Ord PtrOp :: P) T.
  Proof.
    iDestruct 1 as (Hal (rt2 & [[[lt2 r2] b2] π2])) "(Hl2 & -> & HP)". simpl.
    iApply typed_place_ofty_access_val_uniq. { rewrite ty_has_op_type_unfold; done. } iSplitR; first done.
    iIntros (? v ?) "Hv !>". rewrite /ty_own_val /=.
    iDestruct "Hv" as "(_ & Hv)".
    iPoseProof (alias_ptr_own_val_to_decodes with "Hv") as "%Hv".
    iExists l2, _, _, _, _.
    iR.
    iFrame "Hv Hl2 HP". done.
  Qed.
  Definition typed_place_ofty_alias_ptr_uniq_inst := [instance @typed_place_ofty_alias_ptr_uniq].
  Global Existing Instance typed_place_ofty_alias_ptr_uniq_inst | 30.

  Lemma typed_place_ofty_alias_ptr_shared E L f l l2 bmin0 κ P T :
    ⌜lctx_lft_alive E L κ⌝ ∗
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π2 = f.1⌝ ∗
      typed_place E L f l2 lt2 r2 UpdInit b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (◁ alias_ptr_t) (# l2)
              (l2 ◁ₗ[f.1, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place E L f l (◁ alias_ptr_t) (#l2) bmin0 (Shared κ) (DerefPCtx Na1Ord PtrOp :: P) T.
  Proof.
    iDestruct 1 as (Hal (rt2 & [[[lt2 r2] b2] π2])) "(Hl2 & -> & HP)". simpl.
    iApply typed_place_ofty_access_val_shared. { rewrite ty_has_op_type_unfold; done. } iSplitR; first done.
    iIntros (? v ?) "Hv !>". rewrite /ty_own_val /=.
    iDestruct "Hv" as "(_ & Hv)".
    iPoseProof (alias_ptr_own_val_to_decodes with "Hv") as "%Hv".
    iExists l2, _, _, _, _.
    iR.
    iFrame "Hv Hl2 HP". done.
  Qed.
  Definition typed_place_ofty_alias_ptr_shared_inst := [instance @typed_place_ofty_alias_ptr_shared].
  Global Existing Instance typed_place_ofty_alias_ptr_shared_inst | 30.

End place.

(** Rules for AliasLtype *)
Section alias_ltype.
  Context `{!typeGS Σ}.
  Implicit Types (rt : RT).

  (* TODO is there a better design that does not require us to essentially duplicate this?
     we have alias_ltype in the first place only because of the interaction with OpenedLtype, when we do a raw-pointer-addrof below references.
   *)

  Global Program Instance alias_ltype_owned_simplify_hyp π (rt : RT) st (l l2 : loc) (r : place_rfn rt) :
    SimplifyHyp (l ◁ₗ[π, Owned] r @ AliasLtype rt st l2) (Some 0%N) := {|
    simplify_hyp_Q := ⌜l = l2⌝;
  |}.
  Next Obligation.
    iIntros (??????) "Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    iDestruct "Hl" as "(%ly & Hst & -> & Hloc & Hlb)".
    done.
  Qed.

  (** Place typing for [AliasLtype].
    At the core this is really similar to the place lemma for alias_ptr_t - just without the deref *)
  Lemma typed_place_alias_owned E L f l l2 rt (r : place_rfn rt) st bmin0 P T :
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π2 = f.1⌝ ∗
      typed_place E L f l2 lt2 r2 UpdInit b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (AliasLtype rt st l2) r
              (l2 ◁ₗ[f.1, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place E L f l (AliasLtype rt st l2) r bmin0 (Owned) P T.
  Proof.
    iDestruct 1 as ((rt2 & [[[lt2 r2] b2] π2])) "(Hl2 & -> & HP)". simpl.
    iIntros (????) "#CTX #HE HL Hf Hl Hcont".
    simpl.
    iEval (rewrite ltype_own_alias_unfold /alias_lty_own) in "Hl".
    iDestruct "Hl" as "(%ly & % & -> & #? & #?)".
    iApply ("HP" with "[//] [//] CTX HE HL Hf Hl2").
    iIntros (L' κs l2 b0 bmin rti ltyi ri updcx) "Hl2 Hcl HT HL Hf".
    iApply ("Hcont" with "Hl2 [Hcl] HT HL Hf").

    iIntros (upd) "#Hincl Hl2 ? Hcond".
    iMod ("Hcl" with "Hincl Hl2 [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & ? & ? & ? & ? & ? & HL & ?)".
    iFrame. simpl.
    iSplitL.
    { rewrite ltype_own_alias_unfold /alias_lty_own. eauto 8 with iFrame. }
    iSplitL; last iApply upd_bot_min.
    iApply typed_place_cond_refl. iModIntro.
    iApply lft_list_incl_refl.
  Qed.
  Definition typed_place_alias_owned_inst := [instance @typed_place_alias_owned].
  Global Existing Instance typed_place_alias_owned_inst.

  Lemma typed_place_alias_shared E L f l l2 (rt : RT) (r : place_rfn rt) st bmin0 κ P T :
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π2 = f.1⌝ ∗
      typed_place E L f l2 lt2 r2 UpdInit b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (AliasLtype rt st l2) r
              (l2 ◁ₗ[f.1, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place E L f l (AliasLtype rt st l2) r bmin0 (Shared κ) P T.
  Proof.
    unfold find_in_context, typed_place.

    iDestruct 1 as ((rt2 & (((lt & r''') & b2) & π2))) "(Hl2 & -> & HP)". simpl.
    iIntros (????) "#CTX #HE HL Hf Hl Hcont".
    iEval (rewrite ltype_own_alias_unfold /alias_lty_own) in "Hl".
    iDestruct "Hl" as "(%ly & % & -> & #? & #?)".

    iApply ("HP" with "[//] [//] CTX HE HL Hf Hl2").
    iIntros (L' κs l2 b0 bmin rti ltyi ri updcx) "Hl2 Hcl HT HL".
    iApply ("Hcont" with "Hl2 [Hcl] HT HL").

    iIntros (upd) "#Hincl Hl2 ? Hcond".
    iMod ("Hcl" with "Hincl Hl2 [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & ? & ? & ? & ? & ? & HL & ?)".
    iFrame. simpl.
    iSplitL.
    { rewrite ltype_own_alias_unfold /alias_lty_own. eauto 8 with iFrame. }
    iSplitL; last iApply upd_bot_min.
    iApply typed_place_cond_refl. iModIntro.
    iApply lft_list_incl_refl.
  Qed.
  Definition typed_place_alias_shared_inst := [instance @typed_place_alias_shared].
  Global Existing Instance typed_place_alias_shared_inst.

  (** Core lemma for putting back ownership after raw borrows *)
  Lemma stratify_ltype_alias_owned π E L mdu ma {M} (m : M) l l2 rt st r `{!StratifyLtypeShouldCloseInv m Owned} (T : stratify_ltype_cont_t) :
    match ma with
    | StratNoRefold => T L True _ (AliasLtype rt st l2) r
    | _ =>
      find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
        ⌜π = π2⌝ ∗ ⌜syn_type_compat st (ltype_st lt2)⌝ ∗ ⌜b2 = Owned⌝ ∗
        (* recursively stratify *)
        stratify_ltype π E L mdu ma m l2 lt2 r2 b2 (λ L2 R rt2' lt2' r2',
          T L2 R rt2' lt2' r2'))
    end
    ⊢ stratify_ltype π E L mdu ma m l (AliasLtype rt st l2) r (Owned) T.
  Proof.
    iIntros "HT".
    destruct (decide (ma = StratNoRefold)) as [-> | ].
    { iIntros (????) "#CTX #HE HL Hl". iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iApply logical_step_intro. by iFrame. }
    iAssert (find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)), ⌜π = π2⌝ ∗ ⌜syn_type_compat st (ltype_st lt2)⌝ ∗ ⌜b2 = Owned⌝ ∗ stratify_ltype π E L mdu ma m l2 lt2 r2 b2 T))%I with "[HT]" as "HT".
    { destruct ma; done. }
    iDestruct "HT" as ([rt2 [[[lt2 r2] b2] π2]]) "(Hl2 & <- & %Hcomp & -> & HT)".
    simpl. iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    iDestruct "Hl" as "(%ly & %Halg & -> & %Hly & Hlb)".
    simp_ltypes.
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl2") as (L3 R rt2' lt2' r2') "(HL & %Hst & Hstep & HT)".
    iModIntro. iExists _, _, _, _, _. iFrame.
    iPureIntro.
    etrans; done.
  Qed.
  Definition stratify_ltype_alias_owned_inst := [instance @stratify_ltype_alias_owned].
  Global Existing Instance stratify_ltype_alias_owned_inst.

  Lemma stratify_ltype_alias_shared π E L mdu ma {M} (m : M) l l2 rt''' st r κ  `{!StratifyLtypeShouldCloseInv m (Shared κ)} (T : stratify_ltype_cont_t) :
    ( if decide (ma = StratNoRefold)
      then
        T L True _ (AliasLtype rt''' st l2) r
      else
        find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
          ⌜π = π2⌝ ∗ ⌜syn_type_compat st (ltype_st lt2)⌝ ∗ ⌜b2 = Owned⌝ ∗
          (* recursively stratify *)
          stratify_ltype π E L mdu ma m l2 lt2 r2 b2
            (λ L2 R rt2' lt2' r2',
               (T L2 ((l2 ◁ₗ[π, Owned] r2' @ lt2') ∗ R) rt''' (AliasLtype rt''' st l2) r))))
    ⊢ stratify_ltype π E L mdu ma m l (AliasLtype rt''' st l2) r (Shared κ) T.
  Proof.
    rewrite /stratify_ltype /find_in_context.
    iIntros "HT".

    destruct (decide (ma = StratNoRefold)) as [-> | ].
    { iIntros (????) "#CTX #HE HL Hl". iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iApply logical_step_intro. by iFrame. }

    iDestruct "HT" as ([rt2 [[[lt2 r2] b2] π2]]) "(Hl2 & <- & %Hcomp & -> & HT)"; simpl.

    iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    simp_ltypes.

    iDestruct "Hl" as "(%ly & %Halg & -> & %Hly & Hlb)".

    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl2") as (L3 R rt2' lt2' r2') "(HL & %Hst & Hstep & HT)".
    iModIntro. iExists _, _, _, _, _.
    iFrame; iR.

    iApply (logical_step_compose with "Hstep").
    iApply logical_step_intro.
    iIntros "($ & $)".

    rewrite ltype_own_alias_unfold /alias_lty_own.
    by iExists ly; iFrame.
  Qed.
  Definition stratify_ltype_alias_shared_inst := [instance @stratify_ltype_alias_shared].
  Global Existing Instance stratify_ltype_alias_shared_inst.


  (** Deinitialization: fold back AliasLtype *)
  Lemma owned_subltype_alias_typed_value π E L step l l2 {rt1 : RT} (r1 : place_rfn rt1) r2 st st2 T :
    find_in_context (FindLoc l2) (λ '(existT rt1' (lt1', r1', b1, π1')),
      ⌜π = π1'⌝ ∗ ⌜ltype_st lt1' = st⌝ ∗ ⌜b1 = Owned⌝ ∗
      owned_subltype_step π E L step l r1' r2 lt1' (◁ typed_value_t st2) T)
    ⊢ owned_subltype_step π E L step l r1 r2 (AliasLtype rt1 st l2) (◁ typed_value_t st2) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hl".
    iDestruct "HT" as ([rt1' [[[lt1' r1'] b1] π1']]) "(Hl2 & <- & <- & -> & HT)"; simpl.
    simp_ltypes. iApply ("HT" with "[//] [//] [//] CTX HE HL").
    rewrite ltype_own_alias_unfold /alias_lty_own.
    iDestruct "Hl" as "(%ly & %Halg & -> & %Hly & Hlb)".
    done.
  Qed.
  Definition owned_subltype_alias_typed_value_inst := [instance @owned_subltype_alias_typed_value].
  Global Existing Instance owned_subltype_alias_typed_value_inst.

  (** Addr-Of Instance for &raw mut, in the case that the place type is AliasLtype. This case is fairly trivial. *)
  Lemma typed_addr_of_mut_end_alias π E L l l2 st rt r b2 bmin (T : typed_addr_of_mut_end_cont_t) :
    (⌜l2 = l⌝ -∗ T L _ (alias_ptr_t) l2 _ (AliasLtype rt st l2) r)
    ⊢ typed_addr_of_mut_end π E L l (AliasLtype rt st l2) r b2 bmin T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own. destruct b2 as [| | ]; [| | done].
    - iDestruct "Hl" as "(%ly & %Hst & -> & %Hly & #Hlb)".
      iSpecialize ("HT" with "[//]").
      iApply logical_step_intro. iExists _, _, _, _, _, _, _. iFrame.
      iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
      rewrite !ltype_own_alias_unfold /alias_lty_own.
      iSplitL. { rewrite /ty_own_val/= alias_ptr_own_val_unfold. iR. iPureIntro. by apply l2v_decodes_to_loc. }
      iSplitL. { eauto 8 with iFrame. }
      iSplitR. { eauto 8 with iFrame. }
      done.
    - iDestruct "Hl" as "(%ly & %Hst & -> & %Hly & #Hlb)".
      iSpecialize ("HT" with "[//]").
      iApply logical_step_intro. iExists _, _, _, _, _, _, _. iFrame.
      iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
      iSplitL. { rewrite /ty_own_val/= alias_ptr_own_val_unfold. iR. iPureIntro. by apply l2v_decodes_to_loc. }
      rewrite !ltype_own_alias_unfold /alias_lty_own.
      iSplitL. { eauto 8 with iFrame. }
      iSplitR. { eauto 8 with iFrame. }
      done.
  Qed.
  Definition typed_addr_of_mut_end_alias_inst := [instance @typed_addr_of_mut_end_alias].
  Global Existing Instance typed_addr_of_mut_end_alias_inst | 10.


  (* TODO: should make typed_addr_of_mut_end available in cases where no strong updates are allowed.
      AliasLtype does now support that case. *)

  (** Cases for other ltypes *)
  Lemma typed_addr_of_mut_end_owned π E L l {rt} (lt : ltype rt) r bmin (T : typed_addr_of_mut_end_cont_t) :
    T L _ (alias_ptr_t) l _ (AliasLtype rt (ltype_st lt) l) r
    ⊢ typed_addr_of_mut_end π E L l lt r (Owned) bmin T.
  Proof.
    iIntros "Hvs".
    iIntros (????) "#CTX #HE HL Hl".
    iApply fupd_logical_step.
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & % & %)".
    iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
    iApply logical_step_fupd.
    iApply logical_step_intro.
    iIntros "!>!> ".
    iPoseProof (ltype_own_make_alias with "Hl") as "(Hl & Halias)".
    iExists _, _, _, _, _, _, _. iFrame. simp_ltypes.
    iL.
    rewrite /ty_own_val/= alias_ptr_own_val_unfold. iR. iPureIntro. by apply l2v_decodes_to_loc.
  Qed.
  Definition typed_addr_of_mut_end_owned_inst := [instance @typed_addr_of_mut_end_owned].
  Global Existing Instance typed_addr_of_mut_end_owned_inst.

  Lemma typed_addr_of_mut_end_uniq π E L l {rt} (lt : ltype rt) r κ γ bmin (T : typed_addr_of_mut_end_cont_t) :
    ltype_uniq_openable lt →
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    T L2 _ (alias_ptr_t) l _ (OpenedLtype (AliasLtype rt (ltype_st lt) l) lt lt (λ ri ri', ⌜ri = ri'⌝) (λ ri ri', llft_elt_toks κs)) r)
    ⊢ typed_addr_of_mut_end π E L l lt r (Uniq κ γ) bmin T.
  Proof.
    iIntros (Hopen). rewrite /lctx_lft_alive_count_goal.
    iDestruct 1 as (κs L2) "(%Hcount & HT)".
    iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & %Hly)".
    iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
    iApply fupd_logical_step.
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod ("Hcl_F") as "_".
    iPoseProof (Hopen with "CTX Htok Hcl_tok Hl") as "Hs"; first done.
    iApply logical_step_fupd.
    iMod "Hs". iApply logical_step_intro.
    iIntros "!>!>".
    iPoseProof (opened_ltype_acc_uniq with "Hs") as "(Hl & Hl_cl)".
    iPoseProof (ltype_own_make_alias with "Hl") as "(Hl & Halias)".
    iPoseProof ("Hl_cl" with "Halias []") as "Hopened".
    { simp_ltypes. done. }
    iExists _, _, _, _, _, _, _. iFrame. simp_ltypes.
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
    iL.
    rewrite /ty_own_val/= alias_ptr_own_val_unfold. iR. iPureIntro. by apply l2v_decodes_to_loc.
  Qed.

  Lemma typed_addr_of_mut_end_uniq_ofty π E L l {rt} (ty : type rt) r κ γ bmin (T : typed_addr_of_mut_end_cont_t) :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    T L2 _ (alias_ptr_t) l _ (OpenedLtype (AliasLtype rt (st_of ty MetaNone) l) (◁ ty) (◁ ty) (λ ri ri', ⌜ri = ri'⌝) (λ ri ri', llft_elt_toks κs)) r)
    ⊢ typed_addr_of_mut_end π E L l (◁ ty) r (Uniq κ γ) bmin T.
  Proof.
    iApply typed_addr_of_mut_end_uniq.
    apply ltype_uniq_openable_ofty.
  Qed.
  Definition typed_addr_of_mut_end_uniq_ofty_inst := [instance @typed_addr_of_mut_end_uniq_ofty].
  Global Existing Instance typed_addr_of_mut_end_uniq_ofty_inst.

  (* TODO more instances for other ltypes *)
End alias_ltype.

Global Typeclasses Opaque alias_ptr_t.
