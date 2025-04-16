From refinedrust Require Export type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import uninit value alias_ptr programs.
From refinedrust.array Require Import def subltype unfold access.
From refinedrust Require Import options.

(** * An aliased pointer which has been offset from a base pointer.
  Used to help automation when offsetting into arrays. *)

Section offset_ptr.
  Context `{!typeGS Σ}.

  Program Definition offset_ptr_t st : type (loc * Z) := {|
    st_own π (p : loc * Z) v := let '(l, off) := p in ⌜v = l offsetst{st}ₗ off⌝%I;
    st_syn_type := PtrSynType;
    st_has_op_type ot mt := is_ptr_ot ot;
  |}.
  Next Obligation.
    iIntros (st π [l off] v ->). iExists void*. eauto.
  Qed.
  Next Obligation.
    iIntros (st ot mt Hot).
    destruct ot; try done.
    rewrite Hot. done.
  Qed.
  Next Obligation.
    iIntros (st π [l off] v). apply _.
  Qed.
  Next Obligation.
    iIntros (st ot mt sts π [l off] v Hot) "Hv".
    simpl in Hot. iPoseProof (mem_cast_compat_loc (λ v, ⌜v = l offsetst{st}ₗ off⌝)%I with "Hv") as "%Hid"; first done.
    { iIntros "->". eauto. }
    destruct mt; [done | | done].
    rewrite Hid. done.
  Qed.

  Global Instance offset_ptr_t_copy st : Copyable (offset_ptr_t st).
  Proof. apply _. Qed.
End offset_ptr.

Section subtype.
  Context `{!typeGS Σ}.

  (* TODO maybe we should also move out the value for the element then?
      Problem: at the point of the subsumption, this is too late already for function calls, since we already have the evar then...
  *)
  Lemma subsume_from_offset_ptr_t π E L step l base off st k {rt} (ty : type rt) r T :
    find_in_context (FindLoc base) (λ '(existT rt' (lt', r', k', π')),
      ⌜π = π'⌝ ∗
      typed_array_access π E L base off st lt' r' k' (λ L2 rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        base ◁ₗ[π, k2] #rs2 @ ArrayLtype ty2 len2 iml2 -∗
        (* TODO maybe this should also stratify? *)
        subsume_full E L2 step (l ◁ₗ[π, k2] re @ lte) (l ◁ₗ[π, k] r @ ◁ ty) T))
    ⊢ subsume_full E L step (l ◁ᵥ{π} (base, off) @ offset_ptr_t st) (l ◁ₗ[π, k] r @ ◁ ty) T.
  Proof.
    rewrite /find_in_context.
    iDestruct 1 as ([rt' [[[lt' r'] k'] π']]) "(Hl & <- & Ha)". simpl.
    iIntros (????) "#CTX #HE HL Hoffset".
    rewrite /typed_array_access.
    iMod ("Ha" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %k2 & %rt2 & %ty2 & %len2 & %iml2 & %rs2 & %rte & %re & %lte & Hb & Hl & HL & HT)".
    iEval (rewrite /ty_own_val/=) in "Hoffset". iDestruct "Hoffset" as "%Heq".
    apply val_of_loc_inj in Heq. subst l.
    iApply ("HT" with "Hb [//] [//] [//] CTX HE HL Hl").
  Qed.
  Global Instance subsume_from_offset_ptr_t_inst π E L step (l : loc) base off st k {rt} (ty : type rt) r :
    SubsumeFull E L step (l ◁ᵥ{π} (base, off) @ offset_ptr_t st) (l ◁ₗ[π, k] r @ (◁ ty)%I) | 50 :=
    λ T, i2p (subsume_from_offset_ptr_t π E L step l base off st k ty r T).

  Lemma owned_subtype_offset_alias π E L pers l (offset : Z) l2 st T :
    ⌜l2 = l offsetst{st}ₗ offset⌝ ∗ T L
    ⊢ owned_subtype π E L pers (l, offset) l2 (offset_ptr_t st) (alias_ptr_t) T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (????) "#CTX #HE HL". iExists L. iFrame.
    iModIntro. iApply bi.intuitionistically_intuitionistically_if.
    iModIntro.
    iSplitR; last iSplitR.
    - iPureIntro. simpl. iIntros (ly1 ly2 Hst1 Hst2).
      f_equiv. by eapply syn_type_has_layout_inj.
    - rewrite /ty_sidecond/=. done.
    - iIntros (v) "Hv". rewrite /ty_own_val/=. done.
  Qed.
  Global Instance owned_subtype_offset_alias_inst π E L pers l (offset : Z) l2 st :
    OwnedSubtype π E L pers (l, offset) l2 (offset_ptr_t st) (alias_ptr_t) :=
    λ T, i2p (owned_subtype_offset_alias π E L pers l offset l2 st T).

  Lemma owned_subtype_alias_offset π E L pers l l2 offset st T :
    ⌜l2 = l⌝ ∗ ⌜(offset = 0)%Z⌝ ∗ T L
    ⊢ owned_subtype π E L pers l (l2, offset) (alias_ptr_t) (offset_ptr_t st) T.
  Proof.
    iIntros "(-> & -> & HT)".
    iIntros (????) "#CTX #HE HL". iExists L. iFrame.
    iModIntro. iApply bi.intuitionistically_intuitionistically_if.
    iModIntro.
    iSplitR; last iSplitR.
    - iPureIntro. simpl. iIntros (ly1 ly2 Hst1 Hst2).
      f_equiv. by eapply syn_type_has_layout_inj.
    - rewrite /ty_sidecond/=. done.
    - rewrite /alias_ptr_t. iIntros (v) "->". rewrite /ty_own_val/=.
      rewrite /OffsetLocSt. rewrite Z.mul_0_r shift_loc_0//.
  Qed.
  Global Instance owned_subtype_alias_offset_inst π E L pers l (offset : Z) l2 st :
    OwnedSubtype π E L pers l (l2, offset) (alias_ptr_t) (offset_ptr_t st) :=
    λ T, i2p (owned_subtype_alias_offset π E L pers l l2 offset st T).

  Lemma offset_ptr_simplify_hyp (v : val) π (l : loc) st (off : Z) T :
    (⌜v = l offsetst{st}ₗ off⌝ -∗ introduce_direct (v ◁ᵥ{π} (l, off) @ offset_ptr_t st) -∗ T)
    ⊢ simplify_hyp (v ◁ᵥ{π} (l, off) @ offset_ptr_t st) T.
  Proof.
    iIntros "HT %Hv". rewrite /introduce_direct. by iApply "HT".
  Qed.
  Global Instance offset_ptr_simplify_hyp_inst (v : val) π l st (off : Z) :
    SimplifyHypVal v π (offset_ptr_t st) (l, off) (Some 0%N) :=
    λ T, i2p (offset_ptr_simplify_hyp v π l st off T).

  Lemma offset_ptr_simplify_goal (v : val) π (l : loc) st (off : Z) T :
    (⌜v = l offsetst{st}ₗ off⌝) ∗ T ⊢ simplify_goal (v ◁ᵥ{π} (l, off) @ offset_ptr_t st) T.
  Proof.
    iIntros "(-> & HT)". iFrame. done.
  Qed.
  Global Instance offset_ptr_simplify_goal_inst v π l st off :
    SimplifyGoalVal v π (offset_ptr_t st) (l, off) (Some 50%N) :=
    λ T, i2p (offset_ptr_simplify_goal v π l st off T).
End subtype.

Section place.
  Context `{!typeGS Σ}.


  (*      TODO: also should ideally formulate this so we can share this with the direct array offset rules.
     Potentially, we should just encode array offset in terms of this.

     Can I formulate this without the deref? Well, then I'd need to have an offset place type.
     Can I make the recursive part nicer? e.g. by just hooking on top of the alias ptr lemma?
  *)
  Lemma typed_place_offset_ptr_owned π E L l st base offset bmin P wl T :
    find_in_context (FindLoc base) (λ '(existT rt (lt, r, b, π')),
      ⌜π = π'⌝ ∗
      typed_array_access π E L base offset st lt r b (λ L2 rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        base ◁ₗ[ π, k2] # rs2 @ ArrayLtype ty2 len2 iml2 -∗
        typed_place π E L2 (base offsetst{st}ₗ offset) lte re k2 k2 P (λ L2 κs li bi bmin' rti lti ri mstrong,
          T L2 [] li bi bmin' rti lti ri
            (mk_mstrong (match mstrong.(mstrong_strong) with
             | Some strong => Some $ mk_strong (λ _, _) (λ _ _ _, (◁ offset_ptr_t st)) (λ _ _, #(base, offset)) (λ rti2 ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)
             | None => None
             end)
            (match mstrong.(mstrong_weak) with
             | Some weak => Some $ mk_weak (λ _ _, (◁ offset_ptr_t st)) (λ _, #(base, offset)) (λ ltyi2 ri2, llft_elt_toks κs ∗ (base offsetst{st}ₗ offset) ◁ₗ[π, k2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)
             | None =>
                 match mstrong.(mstrong_strong) with
                  | Some strong => Some $ mk_weak (λ _ _, (◁ offset_ptr_t st)) (λ _, #(base, offset)) (λ ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)
                  | None => None
                  end
              end)
            None
            )
    )))
    ⊢ typed_place π E L l (◁ offset_ptr_t st) (#(base, offset)) bmin (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /FindLoc.
    iDestruct 1 as ([rt [[[lt r] b] π']]) "(Hbase & <- & HT)". simpl.
    iIntros (????) "#CTX #HE HL Hincl Hl Hcont".
    iApply fupd_place_to_wp.
    rewrite /typed_array_access.
    iMod ("HT" with "[] [] [] CTX HE HL Hbase") as "(%L2 & %k2 & %rt2 & %ty2 & %len2 & %iml2 & %rs2 & %rte & %re & %lte & Hbase & Hoff & HL & HT)"; [done.. | ].
    iApply (typed_place_ofty_access_val_owned with "[Hbase Hoff HT] [//] [//] CTX HE HL Hincl Hl Hcont").
    { rewrite ty_has_op_type_unfold. done. }
    iIntros (F' v ?) "Hoffset".
    iEval (rewrite /ty_own_val/=) in "Hoffset". iDestruct "Hoffset" as "->".
    iModIntro. iExists _, _, _, _, _. iR. iFrame "Hoff".
    iSplitR. { rewrite /ty_own_val/=. done. }
    iSpecialize ("HT" with "Hbase").
    iApply "HT".
  Qed.
  Global Instance typed_place_offset_ptr_owned_inst π E L l st base offset bmin P wl :
    TypedPlace E L π l (◁ offset_ptr_t st)%I (#(base, offset)) bmin (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) |30 :=
    λ T, i2p (typed_place_offset_ptr_owned π E L l st base offset bmin P wl T).

  Lemma typed_place_offset_ptr_uniq π E L l st base offset bmin P κ γ T :
    find_in_context (FindLoc base) (λ '(existT rt (lt, r, b, π')),
      ⌜π = π'⌝ ∗
      typed_array_access π E L base offset st lt r b (λ L2 rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        base ◁ₗ[ π, k2] # rs2 @ ArrayLtype ty2 len2 iml2 -∗
        ⌜lctx_lft_alive E L2 κ⌝ ∗
        typed_place π E L2 (base offsetst{st}ₗ offset) lte re k2 k2 P (λ L2 κs li bi bmin' rti lti ri mstrong,
          T L2 κs li bi bmin' rti lti ri
            (mk_mstrong (option_map (λ strong, mk_strong (λ _, _) (λ _ _ _, (◁ offset_ptr_t st)) (λ _ _, #(base, offset)) (λ rti2 ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) mstrong.(mstrong_strong))
            (option_map (λ weak, mk_weak (λ _ _, (◁ offset_ptr_t st)) (λ _, #(base, offset)) (λ ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) mstrong.(mstrong_weak))
            None
            )
    )))
    ⊢ typed_place π E L l (◁ offset_ptr_t st) (#(base, offset)) bmin (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /FindLoc /typed_array_access.
    iDestruct 1 as ([rt [[[lt r] b] π']]) "(Hbase & <- & HT)". simpl.
    iIntros (????) "#CTX #HE HL Hincl Hl Hcont".
    iApply fupd_place_to_wp.
    iMod ("HT" with "[] [] [] CTX HE HL Hbase") as "(%L2 & %k2 & %rt2 & %ty2 & %len2 & %iml2 & %rs2 & %rte & %re & %lte & Hbase & Hoff & HL & HT)"; [done.. | ].
    iPoseProof ("HT" with "Hbase") as "(%Hal & HT)".
    iApply (typed_place_ofty_access_val_uniq  _ _ _ _ (offset_ptr_t st) with "[Hoff HT] [//] [//] CTX HE HL Hincl Hl Hcont").
    { rewrite ty_has_op_type_unfold. done. }
    iR. iIntros (F' v ?) "Hoffset".
    iEval (rewrite /ty_own_val/=) in "Hoffset". iDestruct "Hoffset" as "->".
    iModIntro. iExists _, _, _, _, _. iR. iFrame "Hoff".
    iSplitR. { rewrite /ty_own_val/=. done. }
    iApply "HT".
  Qed.
  Global Instance typed_place_offset_ptr_uniq_inst π E L l st base offset bmin P κ γ :
    TypedPlace E L π l (◁ offset_ptr_t st)%I (#(base, offset)) bmin (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) | 30:=
    λ T, i2p (typed_place_offset_ptr_uniq π E L l st base offset bmin P κ γ T).

  Lemma typed_place_offset_ptr_shared π E L l st base offset bmin P κ T :
    find_in_context (FindLoc base) (λ '(existT rt (lt, r, b, π')),
      ⌜π = π'⌝ ∗
      typed_array_access π E L base offset st lt r b (λ L2 rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        base ◁ₗ[ π, k2] # rs2 @ ArrayLtype ty2 len2 iml2 -∗
        ⌜lctx_lft_alive E L2 κ⌝ ∗
        typed_place π E L2 (base offsetst{st}ₗ offset) lte re k2 k2 P (λ L2 κs li bi bmin' rti lti ri mstrong,
          T L2 κs li bi bmin' rti lti ri
            (mk_mstrong (option_map (λ strong, mk_strong (λ _, _) (λ _ _ _, (◁ offset_ptr_t st)) (λ _ _, #(base, offset)) (λ rti2 ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) mstrong.(mstrong_strong))
            (option_map (λ weak, mk_weak (λ _ _, (◁ offset_ptr_t st)) (λ _, #(base, offset)) (λ ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) mstrong.(mstrong_weak))
            None
            )
    )))
    ⊢ typed_place π E L l (◁ offset_ptr_t st) (#(base, offset)) bmin (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /FindLoc /typed_array_access.
    iDestruct 1 as ([rt [[[lt r] b] π']]) "(Hbase & <- & HT)". simpl.
    iIntros (????) "#CTX #HE HL Hincl Hl Hcont".
    iApply fupd_place_to_wp.
    iMod ("HT" with "[] [] [] CTX HE HL Hbase") as "(%L2 & %k2 & %rt2 & %ty2 & %len2 & %iml2 & %rs2 & %rte & %re & %lte & Hbase & Hoff & HL & HT)"; [done.. | ].
    iPoseProof ("HT" with "Hbase") as "(%Hal & HT)".
    iApply (typed_place_ofty_access_val_shared with "[Hoff HT] [//] [//] CTX HE HL Hincl Hl Hcont").
    { rewrite ty_has_op_type_unfold. done. }
    iR. iIntros (F' v ?) "Hoffset".
    iEval (rewrite /ty_own_val/=) in "Hoffset". iDestruct "Hoffset" as "->".
    iModIntro. iExists _, _, _, _, _. iR. iFrame "Hoff".
    iSplitR. { rewrite /ty_own_val/=. done. }
    iApply "HT".
  Qed.
  Global Instance typed_place_offset_ptr_shared_inst π E L l st base offset bmin P κ :
    TypedPlace E L π l (◁ offset_ptr_t st)%I (#(base, offset)) bmin (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) |30 :=
    λ T, i2p (typed_place_offset_ptr_shared π E L l st base offset bmin P κ T).
End place.
