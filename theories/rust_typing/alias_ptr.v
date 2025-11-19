From refinedrust Require Export type ltypes programs.
From refinedrust Require Import memcasts ltype_rules value int.
From refinedrust Require Import options.

(** * Raw pointers *)

(** A specialized version of values [value_t] for pointers.
  This is mainly useful if we want to specify ownership of allocations in an ADT separately (e.g. in RawVec) from the field of the struct actually containing the pointer.
  Disadvantage: this does not have any useful interaction laws with the AliasLtype, and we need to duplicate the place typing lemma for both of these. *)
Section alias.
  Context `{!typeGS Σ}.
  Program Definition alias_ptr_t : type locRT := {|
    st_own π (l : loc) v :=
      (⌜v = l⌝%I ∗
      ⌜l.2 ∈ USize⌝)%I;
    st_syn_type := PtrSynType;
    st_has_op_type ot mt := is_ptr_ot ot;
  |}.
  Next Obligation.
    iIntros (π l v [-> ?]). iExists void*.
    iPureIntro. split; first by apply syn_type_has_layout_ptr.
    done.
  Qed.
  Next Obligation.
    unfold is_ptr_ot.
    iIntros (ot mt Hot).
    destruct ot; try done.
    - by apply syn_type_has_layout_ptr.
    - subst. by apply syn_type_has_layout_ptr.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (ot mt st π l v Hot) "Hv".
    simpl in Hot.
    iPoseProof (mem_cast_compat_loc (λ v, ⌜v = val_of_loc l⌝ ∗ ⌜l.2 ∈ USize⌝)%I with "Hv") as "%Hid"; first done.
    { iIntros "(-> & ?)". eauto. }
    destruct mt; [done | | done].
    rewrite Hid. done.
  Qed.
  Next Obligation.
    intros mt ly Hst. apply syn_type_has_layout_ptr_inv in Hst as ->.
    done.
  Qed.

  Global Instance alias_ptr_t_copy : Copyable (alias_ptr_t).
  Proof. apply _. Qed.

End alias.

Global Hint Unfold alias_ptr_t : tyunfold.

Section rules.
  Context `{!typeGS Σ}.


  (* TODO interaction with ghost drop? *)
  Lemma alias_ptr_simplify_hyp (v : val) π (l : loc) T :
    (⌜v = l⌝ -∗ ⌜l.2 ∈ USize⌝ -∗ T)
    ⊢ simplify_hyp (v ◁ᵥ{π} l @ alias_ptr_t) T.
  Proof.
    iIntros "HT [%Hv %]". by iApply "HT".
  Qed.
  Global Instance alias_ptr_simplify_hyp_inst v π l :
    SimplifyHypVal v π (alias_ptr_t) l (Some 0%N) :=
    λ T, i2p (alias_ptr_simplify_hyp v π l T).

  Lemma alias_ptr_simplify_goal_fast π (l l2 : loc) `{!CanSolve (l.2 ∈ USize)} T :
    (⌜l = l2⌝ ∗ T)
    ⊢ simplify_goal (l ◁ᵥ{π} l2 @ alias_ptr_t) T.
  Proof.
    rewrite /simplify_goal.
    iIntros "[<- $]".
    unfold CanSolve in *.
    rewrite /ty_own_val/=. iR. done.
  Qed.
  Global Instance alias_ptr_simplify_goal_fast_inst π (l l2 : loc) `{!CanSolve (l.2 ∈ USize)} :
    SimplifyGoalVal l π (alias_ptr_t) l2 (Some 0%N) :=
    λ T, i2p (alias_ptr_simplify_goal_fast π l l2 T).

  (* Lower priority instance that requires a loc_in_bounds fact *)
  Lemma alias_ptr_simplify_goal (v : val) π (l : loc) T :
    (⌜v = l⌝ ∗ ∃ a b, loc_in_bounds l a b ∗ T)
    ⊢ simplify_goal (v ◁ᵥ{π} l @ alias_ptr_t) T.
  Proof.
    rewrite /simplify_goal.
    iIntros "(-> & %a & %b & Hlb & $)".
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
    rewrite /ty_own_val/=. iR.
    done.
  Qed.
  Global Instance alias_ptr_simplify_goal_inst v π l :
    SimplifyGoalVal v π (alias_ptr_t) l (Some 1%N) :=
    λ T, i2p (alias_ptr_simplify_goal v π l T).

  Global Program Instance learn_from_hyp_val_alias_ptr l :
    LearnFromHypVal (alias_ptr_t) l :=
    {| learn_from_hyp_val_Q := ⌜l.2 ∈ USize⌝ |}.
  Next Obligation.
    iIntros (?????) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(-> & %)".
    iModIntro. iPureIntro. split_and!; done.
  Qed.
End rules.

Section comparison.
  Context `{!typeGS Σ}.

  Lemma type_relop_ptr_ptr E L v1 (l1 : loc) v2 (l2 : loc) (T : typed_val_expr_cont_t) b op π :
    match op with
    | EqOp rit => Some (bool_decide (l1.2 = l2.2)%Z, rit)
    | NeOp rit => Some (bool_decide (l1.2 ≠ l2.2)%Z, rit)
    | LtOp rit => Some (bool_decide (l1.2 < l2.2)%Z, rit)
    | GtOp rit => Some (bool_decide (l1.2 > l2.2)%Z, rit)
    | LeOp rit => Some (bool_decide (l1.2 <= l2.2)%Z, rit)
    | GeOp rit => Some (bool_decide (l1.2 >= l2.2)%Z, rit)
    | _ => None
    end = Some (b, U8) →
    T L π (val_of_bool b) bool bool_t b
    ⊢ typed_bin_op E L v1 (v1 ◁ᵥ{π} l1 @ alias_ptr_t) v2 (v2 ◁ᵥ{π} l2 @ alias_ptr_t) op (PtrOp) (PtrOp) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT [%Hv1 ?] [%Hv2 ?]" (Φ) "#CTX #HE HL HΦ".
    subst.
    iApply wp_ptr_relop; [| | | done | ].
    { apply val_to_of_loc. }
    { apply val_to_of_loc. }
    { by apply val_of_bool_iff_val_of_Z. }
    iIntros "!> Hcred". iApply ("HΦ" with "HL") => //.
    rewrite /ty_own_val/=. by destruct b.
  Qed.

  Global Program Instance type_eq_ptr_ptr_inst E L v1 l1 v2 l2 π :
    TypedBinOpVal π E L v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (EqOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L v1 l1 v2 l2 T (bool_decide (l1.2 = l2.2)) _ π _).
  Solve Obligations with done.
  Global Program Instance type_ne_ptr_ptr_inst E L v1 l1 v2 l2 π :
    TypedBinOpVal π E L v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (NeOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L v1 l1 v2 l2 T (bool_decide (l1.2 ≠ l2.2)) _ π _).
  Solve Obligations with done.
  Global Program Instance type_lt_ptr_ptr_inst E L v1 l1 v2 l2 π :
    TypedBinOpVal π E L v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (LtOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L v1 l1 v2 l2 T (bool_decide (l1.2 < l2.2)%Z) _ π _).
  Solve Obligations with done.
  Global Program Instance type_gt_ptr_ptr_inst E L v1 l1 v2 l2 π :
    TypedBinOpVal π E L v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (GtOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L v1 l1 v2 l2 T (bool_decide (l1.2 > l2.2)%Z) _ π _).
  Solve Obligations with done.
  Global Program Instance type_le_ptr_ptr_inst E L v1 l1 v2 l2 π :
    TypedBinOpVal π E L v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (LeOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L v1 l1 v2 l2 T (bool_decide (l1.2 <= l2.2)%Z) _ π _).
  Solve Obligations with done.
  Global Program Instance type_ge_ptr_ptr_inst E L v1 l1 v2 l2 π :
    TypedBinOpVal π E L v1 (alias_ptr_t) l1 v2 (alias_ptr_t) l2 (GeOp U8) (PtrOp) (PtrOp) := λ T, i2p (type_relop_ptr_ptr E L v1 l1 v2 l2 T (bool_decide (l1.2 >= l2.2)%Z) _ π _).
  Solve Obligations with done.
End comparison.

Section cast.
  Context `{!typeGS Σ}.

  Lemma type_cast_ptr_ptr π E L l v (T : typed_val_expr_cont_t) :
    (∀ v, T L π v _ (alias_ptr_t) (l))
    ⊢ typed_un_op E L v (v ◁ᵥ{π} l @ alias_ptr_t)%I (CastOp (PtrOp)) PtrOp T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "HT [-> %] %Φ #CTX #HE HL HΦ".
    iApply wp_cast_loc.
    { apply val_to_of_loc. }
    iNext. iIntros "Hcred". iApply ("HΦ" with "HL [] HT").
    rewrite /ty_own_val/=. iR. done.
  Qed.
  Global Instance type_cast_ptr_ptr_inst E L v l π :
    TypedUnOpVal π E L v alias_ptr_t l (CastOp PtrOp) PtrOp :=
    λ T, i2p (type_cast_ptr_ptr π E L l v T).

  Lemma type_cast_ptr_int π E L l v (T : typed_val_expr_cont_t) :
    (∀ v, T L π v _ (int USize) (l.2))
    ⊢ typed_un_op E L v (v ◁ᵥ{π} l @ alias_ptr_t)%I (CastOp (IntOp USize)) PtrOp T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "HT [-> %Husize] %Φ #CTX #HE HL HΦ".
    odestruct (val_of_Z_is_Some _ _ _ _) as (? & ?); first apply Husize.
    iApply wp_cast_ptr_int.
    { apply val_to_of_loc. }
    { done. }
    iNext. iIntros "Hcred". iApply ("HΦ" with "HL [] HT") => //.
    rewrite /ty_own_val/=.
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Global Instance type_cast_ptr_int_inst E L v l π :
    TypedUnOpVal π E L v alias_ptr_t l (CastOp (IntOp USize)) PtrOp :=
    λ T, i2p (type_cast_ptr_int π E L l v T).
End cast.

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_ofty_alias_ptr_owned π E L l l2 bmin0 wl P T :
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π = π2⌝ ∗
      typed_place π E L l2 lt2 r2 UpdStrong b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (◁ alias_ptr_t) (# l2)
              (l2 ◁ₗ[π, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place π E L l (◁ alias_ptr_t) (#l2) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iDestruct 1 as ((rt2 & [[[lt2 r2] b2] π2])) "(Hl2 & <- & HP)". simpl.
    iApply typed_place_ofty_access_val_owned. { rewrite ty_has_op_type_unfold; done. }
    iIntros (? v ?) "[-> %] !>". iExists _, _, _, _, _.
    iSplitR; first done. iFrame "Hl2 HP". done.
  Qed.
  Definition typed_place_ofty_alias_ptr_owned_inst := [instance @typed_place_ofty_alias_ptr_owned].
  Global Existing Instance typed_place_ofty_alias_ptr_owned_inst | 30.

  Lemma typed_place_ofty_alias_ptr_uniq π E L l l2 bmin0 κ γ P T :
    ⌜lctx_lft_alive E L κ⌝ ∗
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π = π2⌝ ∗
      typed_place π E L l2 lt2 r2 UpdStrong b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (◁ alias_ptr_t) (# l2)
              (l2 ◁ₗ[π, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place π E L l (◁ alias_ptr_t) (#l2) bmin0 (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iDestruct 1 as (Hal (rt2 & [[[lt2 r2] b2] π2])) "(Hl2 & <- & HP)". simpl.
    iApply typed_place_ofty_access_val_uniq. { rewrite ty_has_op_type_unfold; done. } iSplitR; first done.
    iIntros (? v ?) "[-> %] !>". iExists _, _, _, _, _.
    iSplitR; first done. iFrame. done.
  Qed.
  Definition typed_place_ofty_alias_ptr_uniq_inst := [instance @typed_place_ofty_alias_ptr_uniq].
  Global Existing Instance typed_place_ofty_alias_ptr_uniq_inst | 30.

  Lemma typed_place_ofty_alias_ptr_shared π E L l l2 bmin0 κ P T :
    ⌜lctx_lft_alive E L κ⌝ ∗
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π = π2⌝ ∗
      typed_place π E L l2 lt2 r2 UpdStrong b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (◁ alias_ptr_t) (# l2)
              (l2 ◁ₗ[π, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place π E L l (◁ alias_ptr_t) (#l2) bmin0 (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iDestruct 1 as (Hal (rt2 & [[[lt2 r2] b2] π2])) "(Hl2 & <- & HP)". simpl.
    iApply typed_place_ofty_access_val_shared. { rewrite ty_has_op_type_unfold; done. } iSplitR; first done.
    iIntros (? v ?) "[-> %] !>". iExists _, _, _, _, _.
    iSplitR; first done. iFrame. done.
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

  Lemma alias_ltype_owned_simplify_hyp π (rt : RT) st wl (l l2 : loc) (r : place_rfn rt) T :
    (⌜l = l2⌝ -∗ T)
    ⊢ simplify_hyp (l ◁ₗ[π, Owned wl] r @ AliasLtype rt st l2) T.
  Proof.
    iIntros "HT Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    iDestruct "Hl" as "(%ly & Hst & -> & Hloc & Hlb)".
    by iApply "HT".
  Qed.
  Global Instance alias_ltype_owned_simplify_hyp_inst π rt st wl l l2 r :
    SimplifyHyp (l ◁ₗ[π, Owned wl] r @ AliasLtype rt st l2) (Some 0%N) :=
    λ T, i2p (alias_ltype_owned_simplify_hyp π rt st wl l l2 r T).

  (** Place typing for [AliasLtype].
    At the core this is really similar to the place lemma for alias_ptr_t - just without the deref *)
  Lemma typed_place_alias_owned π E L l l2 rt (r : place_rfn rt) st bmin0 wl P T :
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π = π2⌝ ∗
      typed_place π E L l2 lt2 r2 UpdStrong b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (AliasLtype rt st l2) r
              (l2 ◁ₗ[π, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place π E L l (AliasLtype rt st l2) r bmin0 (Owned wl) P T.
  Proof.
    iDestruct 1 as ((rt2 & [[[lt2 r2] b2] π2])) "(Hl2 & <- & HP)". simpl.
    iIntros (????) "#CTX #HE HL Hl Hcont".
    simpl.
    iEval (rewrite ltype_own_alias_unfold /alias_lty_own) in "Hl".
    iDestruct "Hl" as "(%ly & % & -> & #? & #? & Hcred)".
    iApply ("HP" with "[//] [//] CTX HE HL Hl2").
    iIntros (L' κs l2 b0 bmin rti ltyi ri updcx) "Hl2 Hcl HT HL".
    iApply ("Hcont" with "Hl2 [Hcl Hcred] HT HL").

    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hcl" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & ? & ? & ? & ? & ? & HL & ?)".
    iFrame. simpl.
    iSplitL "Hcred".
    { rewrite ltype_own_alias_unfold /alias_lty_own. eauto 8 with iFrame. }
    iR.
    iSplitL; last iApply upd_bot_min.
    iApply typed_place_cond_refl. iModIntro.
    iApply lft_list_incl_refl.
  Qed.
  Definition typed_place_alias_owned_inst := [instance @typed_place_alias_owned].
  Global Existing Instance typed_place_alias_owned_inst.

  Lemma typed_place_alias_shared π E L l l2 (rt : RT) (r : place_rfn rt) st bmin0 κ P T :
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π = π2⌝ ∗
      typed_place π E L l2 lt2 r2 UpdStrong b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
        T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (AliasLtype rt st l2) r
              (l2 ◁ₗ[π, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
          ))
    ⊢ typed_place π E L l (AliasLtype rt st l2) r bmin0 (Shared κ) P T.
  Proof.
    unfold find_in_context, typed_place.

    iDestruct 1 as ((rt2 & (((lt & r''') & b2) & π2))) "(Hl2 & <- & HP)". simpl.
    iIntros (????) "#CTX #HE HL Hl Hcont".
    iEval (rewrite ltype_own_alias_unfold /alias_lty_own) in "Hl".
    iDestruct "Hl" as "(%ly & % & -> & #? & #?)".

    iApply ("HP" with "[//] [//] CTX HE HL Hl2").
    iIntros (L' κs l2 b0 bmin rti ltyi ri updcx) "Hl2 Hcl HT HL".
    iApply ("Hcont" with "Hl2 [Hcl] HT HL").

    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hcl" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & ? & ? & ? & ? & ? & HL & ?)".
    iFrame. simpl.
    iSplitL.
    { rewrite ltype_own_alias_unfold /alias_lty_own. eauto 8 with iFrame. }
    iR.
    iSplitL; last iApply upd_bot_min.
    iApply typed_place_cond_refl. iModIntro.
    iApply lft_list_incl_refl.
  Qed.
  Definition typed_place_alias_shared_inst := [instance @typed_place_alias_shared].
  Global Existing Instance typed_place_alias_shared_inst.

  (** Core lemma for putting back ownership after raw borrows *)
  Lemma stratify_ltype_alias_owned π E L mu mdu ma {M} (m : M) l l2 rt st r wl (T : stratify_ltype_cont_t) :
    match ma with
    | StratNoRefold => T L True _ (AliasLtype rt st l2) r
    | _ =>
      find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
        ⌜π = π2⌝ ∗ ⌜ltype_st lt2 = st⌝ ∗ ⌜b2 = Owned wl⌝ ∗
        (* recursively stratify *)
        stratify_ltype π E L mu mdu ma m l2 lt2 r2 b2 (λ L2 R rt2' lt2' r2',
          T L2 R rt2' lt2' r2'))
    end
    ⊢ stratify_ltype π E L mu mdu ma m l (AliasLtype rt st l2) r (Owned wl) T.
  Proof.
    iIntros "HT".
    destruct (decide (ma = StratNoRefold)) as [-> | ].
    { iIntros (????) "#CTX #HE HL Hl". iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iApply logical_step_intro. by iFrame. }
    iAssert (find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)), ⌜π = π2⌝ ∗ ⌜ltype_st lt2 = st⌝ ∗ ⌜b2 = Owned wl⌝ ∗ stratify_ltype π E L mu mdu ma m l2 lt2 r2 b2 T))%I with "[HT]" as "HT".
    { destruct ma; done. }
    iDestruct "HT" as ([rt2 [[[lt2 r2] b2] π2]]) "(Hl2 & <- & <- & -> & HT)".
    simpl. iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    iDestruct "Hl" as "(%ly & %Halg & -> & %Hly & Hlb)".
    simp_ltypes.
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl2") as (L3 R rt2' lt2' r2') "(HL & %Hst & Hstep & HT)".
    iModIntro. iExists _, _, _, _, _. iFrame. done.
  Qed.
  Definition stratify_ltype_alias_owned_inst := [instance @stratify_ltype_alias_owned].
  Global Existing Instance stratify_ltype_alias_owned_inst.

  Lemma stratify_ltype_alias_shared π E L mu mdu ma {M} (m : M) l l2 rt''' st r κ (T : stratify_ltype_cont_t) :
    ( if decide (ma = StratNoRefold)
      then
        T L True _ (AliasLtype rt''' st l2) r
      else
        find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
          ⌜π = π2⌝ ∗ ⌜ltype_st lt2 = st⌝ ∗ ⌜b2 = Owned false⌝ ∗
          (* recursively stratify *)
          stratify_ltype π E L mu mdu ma m l2 lt2 r2 b2
            (λ L2 R rt2' lt2' r2',
               (T L2 ((l2 ◁ₗ[π, Owned false] r2' @ lt2') ∗ R) rt''' (AliasLtype rt''' st l2) r))))
    ⊢ stratify_ltype π E L mu mdu ma m l (AliasLtype rt''' st l2) r (Shared κ) T.
  Proof.
    rewrite /stratify_ltype /find_in_context.
    iIntros "HT".

    destruct (decide (ma = StratNoRefold)) as [-> | ].
    { iIntros (????) "#CTX #HE HL Hl". iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iApply logical_step_intro. by iFrame. }

    iDestruct "HT" as ([rt2 [[[lt2 r2] b2] π2]]) "(Hl2 & <- & <- & -> & HT)"; simpl.

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

  (** Addr-Of Instance for &raw mut, in the case that the place type is AliasLtype. This case is fairly trivial. *)
  Lemma typed_addr_of_mut_end_alias π E L l l2 st rt r b2 bmin (T : typed_addr_of_mut_end_cont_t) :
    (⌜l2 = l⌝ -∗ T L _ (alias_ptr_t) l2 _ (AliasLtype rt st l2) r)
    ⊢ typed_addr_of_mut_end π E L l (AliasLtype rt st l2) r b2 bmin T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own. destruct b2 as [wl | | ]; [| | done].
    - iDestruct "Hl" as "(%ly & %Hst & -> & %Hly & #Hlb & Hcred)".
      iSpecialize ("HT" with "[//]").
      iApply logical_step_intro. iExists _, _, _, _, _, _, _. iFrame.
      iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
      iSplitR; first done.
      rewrite !ltype_own_alias_unfold /alias_lty_own.
      iSplitL "Hcred". { eauto 8 with iFrame. }
      iSplitR. { eauto 8 with iFrame. }
      done.
    - iDestruct "Hl" as "(%ly & %Hst & -> & %Hly & #Hlb)".
      iSpecialize ("HT" with "[//]").
      iApply logical_step_intro. iExists _, _, _, _, _, _, _. iFrame.
      iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
      iSplitR; first done.
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
  Lemma typed_addr_of_mut_end_owned π E L l {rt} (lt : ltype rt) r wl bmin (T : typed_addr_of_mut_end_cont_t) :
    ltype_owned_openable lt →
    T L _ (alias_ptr_t) l _ (AliasLtype rt (ltype_st lt) l) (#r)
    ⊢ typed_addr_of_mut_end π E L l lt #r (Owned wl) bmin T.
  Proof.
    iIntros (Hopen) "Hvs".
    iIntros (????) "#CTX #HE HL Hl".
    iApply fupd_logical_step.
    iMod (ltype_owned_openable_elim_logstep with "Hl") as "(Hl & Hs)"; first done.
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & % & %)".
    iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
    iApply logical_step_fupd.
    iApply (logical_step_wand with "Hs").
    iIntros "!> Hcreds".
    iPoseProof (ltype_own_make_alias with "Hl Hcreds") as "(Hl & Halias)".
    iModIntro. iExists _, _, _, _, _, _, _. iFrame. simp_ltypes.
    iSplitR; done.
  Qed.

  Lemma typed_addr_of_mut_end_owned_ofty π E L l {rt} (ty : type rt) r wl bmin (T : typed_addr_of_mut_end_cont_t) :
    T L _ (alias_ptr_t) l _ (AliasLtype rt (st_of ty) l) (#r)
    ⊢ typed_addr_of_mut_end π E L l (◁ ty) #r (Owned wl) bmin T.
  Proof.
    iApply typed_addr_of_mut_end_owned.
    apply ltype_owned_openable_ofty.
  Qed.
  Definition typed_addr_of_mut_end_owned_ofty_inst := [instance @typed_addr_of_mut_end_owned_ofty].
  Global Existing Instance typed_addr_of_mut_end_owned_ofty_inst.
  (* TODO more instances for other ltypes *)

  Lemma typed_addr_of_mut_end_uniq π E L l {rt} (lt : ltype rt) r κ γ bmin (T : typed_addr_of_mut_end_cont_t) :
    ltype_uniq_openable lt →
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    T L2 _ (alias_ptr_t) l _ (OpenedLtype (AliasLtype rt (ltype_st lt) l) lt lt (λ ri ri', ⌜ri = ri'⌝) (λ ri ri', llft_elt_toks κs)) (#r))
    ⊢ typed_addr_of_mut_end π E L l lt #r (Uniq κ γ) bmin T.
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
    iPoseProof (ltype_own_make_alias false with "Hl [//]") as "(Hl & Halias)".
    iPoseProof ("Hl_cl" with "Halias []") as "Hopened".
    { simp_ltypes. done. }
    iExists _, _, _, _, _, _, _. iFrame. simp_ltypes.
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
    iSplitR; done.
  Qed.

  Lemma typed_addr_of_mut_end_uniq_ofty π E L l {rt} (ty : type rt) r κ γ bmin (T : typed_addr_of_mut_end_cont_t) :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    T L2 _ (alias_ptr_t) l _ (OpenedLtype (AliasLtype rt (st_of ty) l) (◁ ty) (◁ ty) (λ ri ri', ⌜ri = ri'⌝) (λ ri ri', llft_elt_toks κs)) (#r))
    ⊢ typed_addr_of_mut_end π E L l (◁ ty) #r (Uniq κ γ) bmin T.
  Proof.
    iApply typed_addr_of_mut_end_uniq.
    apply ltype_uniq_openable_ofty.
  Qed.
  (* TODO more instances for other ltypes *)
End alias_ltype.

Global Typeclasses Opaque alias_ptr_t.
