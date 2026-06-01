From refinedrust Require Export base type ltypes ltype_rules.
From refinedrust Require Import options.

(** * Definitions for place accesses *)

Section place.
  Context `{!typeGS Σ}.

  Lemma imp_unblockable_lft_incl κs1 κs2 {rt} (lt : ltype rt) :
    lft_list_incl κs1 κs2 -∗
    imp_unblockable κs1 lt -∗
    imp_unblockable κs2 lt.
  Proof.
    unfold lft_list_incl.
    iIntros "(_ & Hincl)".
    by iApply imp_unblockable_shorten.
  Qed.

  (** ** Condition on places: when is a client allowed to replace [lt] with [lt2]
    under a context where the intersected [bor_kind] is [b]?
    *)
  Inductive place_update_kind : Type :=
  (* strong updates *)
  | UpdStrong
  (* weak updates that don't change the refinement type *)
  | UpdWeak
  (* uniq updates: once all the lifetimes are dead, the place becomes unblockable *)
  (* This becomes degenerate if [κs = nil] -- then this means that updates are allowed as long as the core is equal *)
  | UpdUniq (κs : list lft)
  .


  Definition place_update_kind_incl (a b : place_update_kind) : iProp Σ :=
    match a, b with
    | _, UpdStrong => True
    | UpdWeak, UpdWeak => True
    | UpdUniq _, UpdWeak => True
    | UpdUniq κs1, UpdUniq κs2 =>
        lft_list_incl κs1 κs2
    | _, _ => False
    end.
  Definition place_update_kind_max (a b : place_update_kind) : place_update_kind :=
    match a, b with
    | UpdStrong, _ => UpdStrong
    | _, UpdStrong => UpdStrong
    | UpdWeak, _ => UpdWeak
    | _, UpdWeak => UpdWeak
    | UpdUniq κs1, UpdUniq κs2 =>
        UpdUniq (κs1 ++ κs2)
    end.

  (* We cannot easily define a notion of intersection for the [UpdUniq] case, but we can define intersection with a [place_restriction] *)
  Inductive place_restriction : Type :=
  | RestrictNone
  | RestrictWeak
  | RestrictUniq (κ : lft)
  .
  Definition place_update_kind_restrict (a : place_update_kind) (b : place_restriction) : place_update_kind :=
    match a, b with
    | UpdUniq κs1, RestrictUniq κ => UpdUniq ((λ κ1, κ1 ⊓ κ) <$> κs1)
    | UpdUniq κ1, _ => UpdUniq κ1
    | _, RestrictUniq κ1 => UpdUniq [κ1]
    | UpdWeak, _ => UpdWeak
    | _, RestrictWeak => UpdWeak
    | _, _ => UpdStrong
    end.
  Definition bor_kind_to_place_restriction (b : bor_kind) : place_restriction :=
    match b with
    | Uniq κ _ => RestrictUniq κ
    | _ => RestrictNone
    end.
  Global Coercion bor_kind_to_place_restriction : bor_kind >-> place_restriction.

  (* Bottom in the hierarchy *)
  Definition UpdBot := (UpdUniq []).

  Infix "⪯ₚ" := (place_update_kind_incl) (at level 51).
  Infix "⊔ₚₖ" := (place_update_kind_max) (at level 50).
  Infix "⊓ₚ" := (place_update_kind_restrict) (at level 50).

  Global Instance place_update_kind_incl_pers b1 b2 : Persistent (b1 ⪯ₚ b2).
  Proof. destruct b1, b2; try apply _. Qed.

  Lemma place_update_kind_incl_refl b:
    ⊢ (b ⪯ₚ b)%I.
  Proof.
    destruct b; try done.
    iApply lft_list_incl_refl.
  Qed.
  Lemma place_update_kind_incl_trans b1 b2 b3 :
    ⊢ (b1 ⪯ₚ b2 -∗ b2 ⪯ₚ b3 -∗ b1 ⪯ₚ b3)%I.
  Proof.
    destruct b1, b2, b3; simpl; iIntros "#Hx#Hy //".
    iApply lft_list_incl_trans; done.
  Qed.
  Lemma upd_bot_min b :
    ⊢ UpdBot ⪯ₚ b.
  Proof.
    destruct b; try done.
    simpl.
    iApply lft_list_incl_nil_l.
  Qed.

  Lemma place_update_kind_restrict_incl b r :
    ⊢ b ⊓ₚ r ⪯ₚ b.
  Proof.
    destruct b, r; simpl; try done.
    - iApply lft_list_incl_refl.
    - iApply lft_list_incl_refl.
    - iApply lft_list_incl_pointwise.
      iApply big_sepL2_intro.
      { rewrite length_fmap//. }
      iModIntro. iIntros (??? Hlook1 Hlook2).
      rewrite list_lookup_fmap Hlook2/= in Hlook1.
      injection Hlook1 as <-.
      iApply lft_intersect_incl_l.
  Qed.

  (** Properties about join *)
  Lemma place_update_kind_max_incl_l b1 b2 :
    ⊢ (b1 ⪯ₚ b1 ⊔ₚₖ b2)%I.
  Proof.
    destruct b1, b2; simpl; try done.
    iApply lft_list_incl_app_l.
  Qed.
  Lemma place_update_kind_max_incl_r b1 b2 :
    ⊢ (b2 ⪯ₚ b1 ⊔ₚₖ b2)%I.
  Proof.
    destruct b1, b2; simpl; try done.
    iApply lft_list_incl_app_r.
  Qed.
  Lemma place_update_kind_incl_lub b1 b2 b3 :
    b1 ⪯ₚ b3 -∗
    b2 ⪯ₚ b3 -∗
    b1 ⊔ₚₖ b2 ⪯ₚ b3.
  Proof.
    iIntros "#Hincl1 #Hincl2".
    destruct b1, b2, b3; unfold place_update_kind_max, place_update_kind_incl; simpl; try done.
    by iApply lft_list_incl_lub.
  Qed.


  Global Arguments place_update_kind_incl : simpl nomatch.

  Definition lctx_place_update_kind_incl (E : elctx) (L : llctx) b b' : Prop :=
    ∀ qL, llctx_interp_noend L qL -∗ □ (elctx_interp E -∗ b ⪯ₚ b').

  Lemma lctx_place_update_kind_incl_acc E L k1 k2 :
    lctx_place_update_kind_incl E L k1 k2 →
    elctx_interp E -∗ llctx_interp L -∗ k1 ⪯ₚ k2.
  Proof.
    intros Hincl. iIntros "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iApply (Hincl with "HL HE").
  Qed.

  Lemma lctx_place_update_kind_incl_use E L b1 b2 :
    lctx_place_update_kind_incl E L b1 b2 →
    elctx_interp E -∗
    llctx_interp L -∗
    b1 ⪯ₚ b2.
  Proof.
    iIntros (Hincl) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    by iPoseProof (Hincl with "HL HE") as "Ha".
  Qed.

  (** Outliving:
    Usually, we want to know that we can perform updates to a place at least until all the blocked lifetimes in the place are over.
    Otherwise, already something went wrong before.

    TODO: it would be nice if we could get this as an implicit property of our model.
  *)
  Definition place_update_kind_outlives (b : place_update_kind) (κs : list lft) : iProp Σ :=
    match b with
    | UpdUniq κs' =>
        lft_list_incl κs κs'
    | _ => True
    end.
  Global Instance place_update_kind_outlives_persistent b κ : Persistent (place_update_kind_outlives b κ).
  Proof. destruct b; apply _. Qed.
  Lemma place_update_kind_outlives_incl b b' κ :
    b ⪯ₚ b' -∗ place_update_kind_outlives b κ -∗ place_update_kind_outlives b' κ.
  Proof.
    iIntros "#Hincl1 #Hincl2".
    destruct b, b'; unfold place_update_kind_incl; simpl; try done.
    by iApply lft_list_incl_trans.
  Qed.

  Lemma place_update_kind_outlives_uniq_incl b κs :
    place_update_kind_outlives b κs -∗
    UpdUniq κs ⪯ₚ b.
  Proof.
    destruct b; simpl; by eauto.
  Qed.

  Definition lctx_place_update_kind_outlives (E : elctx) (L : llctx) (b : place_update_kind) (κs : list lft) :=
    ∀ qL, llctx_interp_noend L qL -∗ elctx_interp E -∗ place_update_kind_outlives b κs.
  Arguments lctx_place_update_kind_outlives : simpl nomatch.

  Lemma lctx_place_update_kind_outlives_use (E : elctx) (L : llctx) k κs :
    lctx_place_update_kind_outlives E L k κs →
    elctx_interp E -∗
    llctx_interp L -∗
    place_update_kind_outlives k κs.
  Proof.
    iIntros (Hf) "#HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iPoseProof (Hf with "HL HE") as "#Hout".
    done.
  Qed.
  Lemma lctx_place_update_kind_outlives_all_use (E : elctx) (L : llctx) k κs :
    Forall (lctx_place_update_kind_outlives E L k) κs →
    elctx_interp E -∗
    llctx_interp L -∗
    [∗ list] κ ∈ κs, place_update_kind_outlives k κ.
  Proof.
    iIntros (Hf) "#HE HL".
    iPoseProof (Forall_big_sepL _ (place_update_kind_outlives k) with "HL []") as "(Houtl & HL)"; first apply Hf.
    { iModIntro. iIntros (?) "HL _ %Hout". iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iPoseProof (Hout with "HL HE") as "#Hout". iPoseProof ("HL_cl"  with "HL") as "?". by iFrame. }
    done.
  Qed.


  (* How do I handle Opened now?
      I allow strong updates below.
      if the thing above doesn't allow strong updates, I'm stuck.
      I can rule that out already in the precondition of the place rule, so that's okay.
  *)

  Definition place_update_kind_rt_same (pupd : place_update_kind) : bool :=
    match pupd with
    | UpdStrong => false
    | _ => true
    end.
  Definition opt_place_update_eq (upd : place_update_kind) (rt1 rt2 : RT) : Prop :=
    if place_update_kind_rt_same upd then rt1 = rt2 else True.
  Definition opt_place_update_eq_refl `{upd : !place_update_kind} `{rt : !RT} : opt_place_update_eq upd rt rt.
  Proof.
    unfold opt_place_update_eq.
    destruct upd; simpl; [apply I | apply eq_refl..].
  Defined.
  Import EqNotations.
  Lemma opt_place_update_eq_lift (f : RT → RT) {b rt1 rt2} :
    opt_place_update_eq b rt1 rt2 →
    opt_place_update_eq b (f rt1) (f rt2).
  Proof.
    unfold opt_place_update_eq.
    destruct b; simpl.
    - intros. exact I.
    - intros Heq. exact (rew [λ rt, f rt1 = f rt] Heq in @eq_refl _ (f rt1)).
    - intros Heq. exact (rew [λ rt, f rt1 = f rt] Heq in @eq_refl _ (f rt1)).
  Defined.

  Lemma opt_place_update_eq_lift_join {rt1 rt2} b1 b2 :
    opt_place_update_eq b1 rt1 rt2 →
    opt_place_update_eq (b1 ⊔ₚₖ b2) rt1 rt2.
  Proof.
    unfold opt_place_update_eq.
    destruct b1, b2; simpl; done.
  Defined.

  Lemma opt_place_update_eq_use allowed old_rt pupd_rt :
    place_update_kind_rt_same allowed = true →
    opt_place_update_eq allowed old_rt pupd_rt →
    old_rt = pupd_rt.
  Proof.
    unfold opt_place_update_eq. intros ->.
    done.
  Defined.


  (* Note: I can't make the bound condition part of this because it is an iProp *)
  Record place_update (old_rt : RT) (allowed : place_update_kind) : Type := mkPUpd {
    pupd_rt : RT;
    pupd_lt : ltype pupd_rt;
    pupd_rfn : place_rfn pupd_rt;
    pupd_R : iProp Σ;
    pupd_performed : place_update_kind;
    (*pupd_bound *)
    pupd_eq_1 :
      opt_place_update_eq pupd_performed old_rt pupd_rt;
    pupd_eq_2 :
      opt_place_update_eq allowed old_rt pupd_rt;
  }.
  Add Printing Constructor place_update.
  Global Arguments pupd_rt {_ _}.
  Global Arguments pupd_lt {_ _}.
  Global Arguments pupd_rfn {_ _}.
  Global Arguments pupd_R {_ _}.
  Global Arguments pupd_performed {_ _}.
  Global Arguments pupd_eq_1 {_ _ _}.
  Global Arguments pupd_eq_2 {_ _ _}.

  Lemma pupd_performed_incl_uniq_rt old_rt allowed (upd : place_update old_rt allowed) κs  :
    upd.(pupd_performed) ⪯ₚ UpdUniq κs -∗
    ⌜old_rt = upd.(pupd_rt)⌝.
  Proof.
    destruct upd as [? ? ? ? [] ? ?]; simpl; eauto.
  Qed.

  Definition place_update_ctx (rti rto: RT) (allowed_inner allowed_outer : place_update_kind) : Type :=
      llctx →
      place_update rti allowed_inner →
      (place_update rto allowed_outer → iProp Σ) →
      iProp Σ.


  Import EqNotations.

  (** Condition on type changes from [lt] to [lt2] *)
  (* NOTE Now that ltype_eq involves the refinement, maybe we should merge this with the condition on the refinement?
      -> no. since the eq proof is used in the lifetime logic's inheritance vs in the Uniq case, we cannot fix to the current refinement, but rather need to have a proof for all refinements.
  *)
  Definition typed_place_cond {rt rt2} (b : place_update_kind) (lt : ltype rt) (lt2 : ltype rt2) : iProp Σ :=
    match b with
    | UpdStrong =>
        True
    | UpdWeak =>
        ⌜rt = rt2⌝
    | UpdUniq κs =>
        ∃ (Heq : rt = rt2),
        (* We could allow a disjunction here:
           - if we actually change the place type, then we change the contents of the borrow, and we must prove that we can actually unblock the new type [lt2] in time.
           - if we don't actually change the place type, we've proved this before, and it is fine.
            (this isn't completely true for products: we will need sideconditions for products to handle components that don't change, because we can't just extract this from the VS again when we change one component).
            TODO: pinned borrows actually allow to get the VS out now with the strong accessor, so there should be nothing stopping us from allowing this.
        *)
        (∀ b r, ltype_eq b r r (ltype_core lt) (ltype_core (rew <- [ltype] Heq in lt2))) ∗
        imp_unblockable κs lt2
        (* ∨ ⌜lt = rew <- [lty] Heq in lt2⌝ *)
    end%I.


  (* TODO: If we would allow viewshifts in the Uniq case of [ltype_incl], we could use [ltype_incl] for the RHS instead *)
  Lemma imp_unblockable_nil {rt} (lt : ltype rt) :
    imp_unblockable [] lt ⊣⊢
    (□ ∀ π b r l, l ◁ₗ[ π, b] r @ lt ={lftE}=∗ l ◁ₗ[ π, b] r @ ltype_core lt).
  Proof.
    iSplit.
    - iIntros "(#Hub1 & #Hub2)".
      iModIntro. iIntros (π b r l) "Hl".
      destruct b.
      + rewrite -ltype_own_core_equiv.
        iApply "Hub2"; last done.
        iApply lft_dead_list_nil_1.
      + iModIntro. by iApply ltype_own_shared_to_core.
      + rewrite -ltype_own_core_equiv.
        iApply "Hub1"; last done.
        iApply lft_dead_list_nil_1.
    - iIntros "#Hub".
      iSplitL; iModIntro.
      + iIntros (?????) "_".
        rewrite ltype_own_core_equiv.
        iApply "Hub".
      + iIntros (???) "_".
        rewrite ltype_own_core_equiv.
        iApply "Hub".
  Qed.

  (*  TODO: can I change UpdUniq such that UpdBot becomes satisfying?
  Lemma typed_place_cond_upd_eq {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) :
    typed_place_cond UpdEq lt1 lt2 ⊣⊢
    ((∃ Heq, (∀ b r, ltype_eq b r r lt1 ((rew <- [ltype] Heq in lt2))))).
  Proof.
    simpl. iSplit.
    - iIntros "(%Heq & Ha & Hub)".
      iExists Heq. subst.
      rewrite imp_unblockable_nil.
      done.
    - iIntros "(%Heq & Ha)".
      iExists Heq. iFrame.
      Search imp_unblockable.
      iApply imp_unblockable.
   *)

  Global Instance typed_place_cond_pers {rt rt2} b (lt : ltype rt) (lt2 : ltype rt2) :
    Persistent (typed_place_cond b lt lt2).
  Proof. destruct b; apply _. Qed.

  Lemma typed_place_cond_incl k1 k2 {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) :
    k1 ⪯ₚ k2 -∗
    typed_place_cond k1 lt1 lt2 -∗
    typed_place_cond k2 lt1 lt2.
  Proof.
    iIntros "#Hincl Hcond".
    destruct k2, k1; simpl in *; try done.
    - iDestruct "Hcond" as "(%Heq & ?)". done.
    - iDestruct "Hcond" as "(%Heq & ? & Hub)".
      iExists Heq. iFrame.
      iApply imp_unblockable_lft_incl; done.
  Qed.
  Lemma typed_place_cond_trans {rt1 rt2 rt3} (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) b :
    typed_place_cond b lt1 lt2 -∗
    typed_place_cond b lt2 lt3 -∗
    typed_place_cond b lt1 lt3 .
  Proof.
    destruct b; simpl.
    - iIntros "% % !%". congruence.
    - iIntros "-> ->". done.
    - iIntros "(%Heq & Heq & Hub) (%Heq' & Heq' & Hub')".
      subst.
      iExists eq_refl. iFrame. cbn.
      iIntros (b r). iApply (ltype_eq_trans with "Heq Heq'").
  Qed.

  Lemma imp_unblockable_incl_blocked_lfts {rt} κs (lt : ltype rt) :
    □ (lft_dead_list κs ={lftE}=∗ lft_dead_list (ltype_blocked_lfts lt)) -∗
    imp_unblockable κs lt.
  Proof.
    iIntros "#Houtl".
    iApply (imp_unblockable_shorten with "[Houtl]"); last iApply imp_unblockable_blocked_dead.
    done.
  Qed.

  Definition place_kind_outlives_unblock_lt {rt} (k : place_update_kind) (lt : ltype rt) : iProp Σ :=
    place_update_kind_outlives k (ltype_blocked_lfts lt).
  Lemma place_kind_outlives_unblock_lt_use F κs {rt} (lt : ltype rt) :
    lftE ⊆ F →
    place_kind_outlives_unblock_lt (UpdUniq κs) lt -∗
    lft_dead_list κs ={F}=∗
    lft_dead_list (ltype_blocked_lfts lt).
  Proof.
    iIntros (?) "Houtl".
    unfold place_kind_outlives_unblock_lt, place_update_kind_outlives.
    iApply lft_list_incl_acc_dead; done.
  Qed.

  (** Requires a sidecondition to make sure we can actually do the unblocking. *)
  (* NOTE: if we were to revise the use of unblocking and have a disjunct to just show ltype_eq instead of unblockable, we could get rid of the sidecondition *)
  Lemma typed_place_cond_refl {rt} b (lt : ltype rt) :
    place_kind_outlives_unblock_lt b lt -∗
    typed_place_cond b lt lt.
  Proof.
    iIntros "#Houtl".
    destruct b => /=.
    - by iPureIntro.
    - done.
    - iExists eq_refl. cbn. iSplitR.
      { iIntros (??). iApply ltype_eq_refl. }
      iApply imp_unblockable_incl_blocked_lfts.
      iModIntro. iApply lft_list_incl_acc_dead; done.
  Qed.

  Lemma typed_place_cond_refl_ofty {rt} b (ty : type rt) :
    ⊢ typed_place_cond b (◁ ty)%I (◁ ty)%I.
  Proof.
    destruct b.
    - done.
    - iPureIntro. done.
    - iApply (typed_place_cond_refl (UpdUniq _)).
      unfold place_kind_outlives_unblock_lt.
      simpl. iApply lft_list_incl_nil_l.
  Qed.

  Lemma typed_place_cond_uniq_core_eq {rt} (lt1 lt2 : ltype rt) κ :
    typed_place_cond (UpdUniq κ) lt1 lt2 -∗
    ∀ b r, ltype_eq b r r (ltype_core lt1) (ltype_core lt2).
  Proof.
    iIntros "(%Heq & Ha & _)". rewrite (UIP_refl _ _ Heq). done.
  Qed.
  Lemma typed_place_cond_uniq_unblockable {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs :
    typed_place_cond (UpdUniq κs) lt1 lt2 -∗
    imp_unblockable κs lt2.
  Proof.
    iIntros "(%Heq & _ & Ha)". done.
  Qed.
  Lemma typed_place_cond_shadowed_update_cur {rt_cur rt_cur' rt_full} (lt_cur : ltype rt_cur) (lt_cur' : ltype rt_cur') r_cur r_cur' (lt_full : ltype rt_full) k :
    place_kind_outlives_unblock_lt k lt_full -∗
    typed_place_cond k (ShadowedLtype lt_cur r_cur lt_full) (ShadowedLtype lt_cur' r_cur' lt_full).
  Proof.
    iIntros "#Hcond".
    destruct k; simpl; simp_ltypes.
    - done.
    - done.
    - iExists eq_refl. cbn. simp_ltypes.
      iSplitR. { iIntros (??). iApply ltype_eq_refl. }
      iApply shadowed_ltype_imp_unblockable.
      iApply imp_unblockable_incl_blocked_lfts.
      iModIntro. iIntros "Hdead".
      by iApply place_kind_outlives_unblock_lt_use.
  Qed.
  Lemma typed_place_cond_blocked_r_Uniq {rt} (lt : ltype rt) (ty : type rt) κs κ' :
    lft_list_incl [κ'] κs -∗
    typed_place_cond (UpdUniq κs) lt (◁ ty) -∗
    typed_place_cond (UpdUniq κs) lt (BlockedLtype ty κ').
  Proof.
    iIntros "#Hincl Hcond".
    iDestruct "Hcond" as "(%Heq & Heq & Hub)".
    rewrite (UIP_refl _ _ Heq).
    iExists eq_refl. cbn. simp_ltypes.
    iSplitL "Heq"; first done.
    iApply imp_unblockable_lft_incl; last iApply blocked_imp_unblockable.
    done.
  Qed.
  Lemma typed_place_cond_blocked_l {rt1 rt2} (lt : ltype rt1) (ty : type rt2) b κ' :
    typed_place_cond b (◁ ty) lt -∗
    typed_place_cond b (BlockedLtype ty κ') lt.
  Proof.
    iIntros "Hcond". destruct b; try done.
    iDestruct "Hcond" as "(%Heq & #Heq & #Hub)".
    subst rt2.
    iExists eq_refl. cbn. simp_ltypes.
    iSplitL; done.
  Qed.
  Lemma typed_place_cond_shrblocked_r_Uniq {rt} (lt : ltype rt) (ty : type rt) κs κ' :
    lft_list_incl [κ'] κs -∗
    typed_place_cond (UpdUniq κs) lt (◁ ty) -∗
    typed_place_cond (UpdUniq κs) lt (ShrBlockedLtype ty κ').
  Proof.
    iIntros "#Hincl Hcond".
    iDestruct "Hcond" as "(%Heq & Heq & Hub)".
    rewrite (UIP_refl _ _ Heq).
    iExists eq_refl. cbn. simp_ltypes.
    iSplitL "Heq"; first done.
    iApply imp_unblockable_lft_incl; last iApply shr_blocked_imp_unblockable.
    done.
  Qed.
  Lemma typed_place_cond_shrblocked_l {rt1 rt2} (lt : ltype rt1) (ty : type rt2) b κ' :
    typed_place_cond b (◁ ty) lt -∗
    typed_place_cond b (ShrBlockedLtype ty κ') lt.
  Proof.
    iIntros "Hcond". destruct b; try done.
    iDestruct "Hcond" as "(%Heq & #Heq & #Hub)".
    subst rt2.
    iExists eq_refl. cbn. simp_ltypes.
    iSplitL; done.
  Qed.
  Lemma typed_place_cond_coreable_r_Uniq {rt} (lt1 lt2 : ltype rt) κ κs :
    lft_list_incl κs κ -∗
    typed_place_cond (UpdUniq κ) lt1 lt2 -∗
    typed_place_cond (UpdUniq κ) lt1 (CoreableLtype κs lt2).
  Proof.
    iIntros "#Hincl (%Heq & Heq & Hub)".
    rewrite (UIP_refl _ _ Heq).
    iExists eq_refl. cbn.
    simp_ltypes. iSplitL "Heq"; first done.
    iApply imp_unblockable_lft_incl; last iApply coreable_ltype_imp_unblockable.
    done.
  Qed.
  Lemma typed_place_cond_coreable_l {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) b κs :
    typed_place_cond b lt1 lt2 -∗
    typed_place_cond b (CoreableLtype κs lt1) lt2.
  Proof.
    iIntros "Hcond". destruct b; try done.
    iDestruct "Hcond" as "(%Heq & Heq & Hub)".
    subst rt2.
    iExists eq_refl. cbn. simp_ltypes. by iFrame.
  Qed.

  Lemma typed_place_cond_shadowed_l {rt_cur rt_full rt2} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (lt2 : ltype rt2) b r_cur :
    typed_place_cond b lt_full lt2 -∗
    typed_place_cond b (ShadowedLtype lt_cur r_cur lt_full) lt2.
  Proof.
    unfold typed_place_cond. destruct b; try by eauto.
    iIntros "(%Heq & Ha & Hb)".
    subst rt2. iExists eq_refl. iFrame.
    simp_ltypes. done.
  Qed.
  Lemma typed_place_cond_shadowed_r {rt_cur rt_full rt2} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (lt2 : ltype rt2) b r_cur :
    typed_place_cond b lt2 lt_full -∗
    typed_place_cond b lt2 (ShadowedLtype lt_cur r_cur lt_full).
  Proof.
    unfold typed_place_cond. destruct b; try by eauto.
    iIntros "(%Heq & Ha & Hb)".
    subst rt2. iExists eq_refl.
    simp_ltypes. iFrame.
    iApply shadowed_ltype_imp_unblockable.
    done.
  Qed.

  Lemma typed_place_cond_core {rt} (lt : ltype rt) b :
    ⊢ typed_place_cond b lt (ltype_core lt).
  Proof.
    iStartProof.
    destruct b; simpl; try done.
    iExists eq_refl. cbn.
    iSplitL.
    - rewrite ltype_core_idemp.
      iIntros (??). iApply ltype_eq_refl.
    - iApply core_imp_unblockable.
  Qed.

  Global Arguments typed_place_cond : simpl never.

  (* controls conditions on refinement type changes *)
  Definition place_access_rt_rel (bmin : place_update_kind) (rt1 rt2 : RT) :=
    match bmin with
    | UpdStrong => True
    | _ => rt1 = rt2
    end.
  Lemma place_access_rt_rel_refl bmin rt : place_access_rt_rel bmin rt rt.
  Proof. by destruct bmin. Qed.

  Lemma typed_place_cond_Uniq_rt_eq {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) k κ :
    k ⪯ₚ UpdUniq κ -∗
    typed_place_cond k lt1 lt2 -∗
    ⌜rt1 = rt2⌝.
  Proof.
    iIntros "Hincl Hcond".
    destruct k; simpl; try done.
    all: iDestruct "Hcond" as "(%Heq & Ha)"; iClear "Ha"; by done.
  Qed.

  (* NOTE: if put the ltype_eq disjunct for the Uniq case into typed_place_cond,
      then we would get a direct subsumption lemma. *)
  Lemma ltype_eq_place_cond_ty_trans {rt rt2} (lt1 lt2 : ltype rt) (lt3 : ltype rt2) b :
    (∀ b' r, ltype_eq b' r r lt1 lt2) -∗
    typed_place_cond b lt2 lt3 -∗
    typed_place_cond b lt1 lt3.
  Proof.
    iIntros "Heq Hc".
    destruct b; simpl.
    - done.
    - done.
    - iDestruct "Hc" as "(%Heq & Heq' & $)". subst. iExists eq_refl.
      iIntros (??).
      iPoseProof (ltype_eq_core with "Heq") as "Heq".
      iApply (ltype_eq_trans with "Heq Heq'").
  Qed.
  Lemma place_cond_ltype_eq_trans b {rt1 rt2} (lt1 : ltype rt1) (lt2 lt3 : ltype  rt2) :
    typed_place_cond b lt1 lt2 -∗
    (∀ b' r, ltype_eq b' r r lt2 lt3) -∗
    typed_place_cond b lt1 lt3.
  Proof.
    iIntros "Hcond #Heq".
    destruct b; simpl.
    - done.
    - done.
    - iDestruct "Hcond" as "(%Heq & #Heq2 & Hub)". subst rt2.
      iExists eq_refl.
      iSplitR. { iIntros (??). iPoseProof (ltype_eq_core with "Heq") as "Heq'". iApply ltype_eq_trans; done. }
      iApply ltype_eq_imp_unblockable; done.
  Qed.
  Lemma ltype_eq_place_cond_trans {rt rt2} (lt1 lt2 : ltype rt) (lt3 : ltype rt2) b :
    (∀ b' r, ltype_eq b' r r lt1 lt2) -∗
    typed_place_cond b lt2 lt3 -∗
    typed_place_cond b lt1 lt3.
  Proof.
    iIntros "Heq Hc".
    iApply (ltype_eq_place_cond_ty_trans with "Heq Hc").
  Qed.

  Lemma typed_place_cond_ltype_eq_ofty {rt rt2} (lt1 : ltype rt) (lt2 : ltype rt2) (ty3 : type rt2) b :
    typed_place_cond b lt1 lt2  -∗
    (∀ b' r, ltype_eq b' r r lt2 (◁ ty3)%I) -∗
    typed_place_cond b lt1 (◁ ty3)%I.
  Proof.
    iIntros "Hc Heq".
    destruct b; simpl.
    - done.
    - done.
    - iDestruct "Hc" as "(%Heq & Heq' & Hub)". destruct Heq. iExists eq_refl. cbn.
      iSplitL. {
        iIntros (??).
        iApply (ltype_eq_trans with "Heq'").
        iApply (ltype_eq_core _ _ _ _ (◁ _)%I). done.
      }
      iApply ofty_imp_unblockable.
  Qed.

  (** We can mutably borrow from the place, assuming that the ownership [b] of the place is at least Uniq κ. *)
  Lemma ofty_blocked_place_cond b κ {rt} (ty : type rt) :
    UpdUniq [κ] ⪯ₚ b -∗
    typed_place_cond b (◁ ty)%I (BlockedLtype ty κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Ha". done.
    - iIntros "#Hincl".
      iExists eq_refl. cbn. iSplitR.
      + simp_ltypes. iIntros (??). iApply ltype_eq_refl.
      + iApply (imp_unblockable_lft_incl); last iApply blocked_imp_unblockable.
        done.
  Qed.

  (* Note: [ShrBlockedLtype] is not used for reborrowing shared borrows, so the sidecondition is okay *)
  Lemma ofty_shr_blocked_place_cond b κ {rt} (ty : type rt) :
    UpdUniq [κ] ⪯ₚ b -∗
    typed_place_cond b (◁ ty)%I (ShrBlockedLtype ty κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Ha". done.
    - iIntros "#Hincl".
      iExists eq_refl. cbn. iSplitR.
      + simp_ltypes. iIntros (??). iApply ltype_eq_refl.
      + iApply (imp_unblockable_lft_incl); last iApply shr_blocked_imp_unblockable.
        done.
  Qed.

  Definition bor_kind_writeable (b : bor_kind) :=
    match b with
    | Owned => True
    | Uniq _ _ => True
    | Shared _ => False
    end.
  Definition bor_kind_mut_borrowable (b : bor_kind) :=
    match b with
    | Shared _ => False
    | _ => True
    end.

  (** ** Prove a typed_place_cond (used together with [stratify_ltype]) *)
  Record place_update_kind_res (allowed : place_update_kind) (rt1 rt2 : RT) : Type := mkPUKRes{
    puk_res_k :> place_update_kind;
    puk_res_eq_1 : opt_place_update_eq puk_res_k rt1 rt2;
    puk_res_eq_2 : opt_place_update_eq allowed rt1 rt2;
  }.
  Global Arguments puk_res_eq_1 {_ _ _}.
  Global Arguments puk_res_eq_2 {_ _ _}.
  Global Arguments puk_res_k {_ _ _}.
  Global Arguments mkPUKRes {_ _ _}.

  (* Compose two updates *)
  Program Definition place_update_kind_res_trans {allowed} {rt1 rt2 rt3}
    (upd1 : place_update_kind_res allowed rt1 rt2)
    (upd2 : place_update_kind_res allowed rt2 rt3) :
    place_update_kind_res allowed rt1 rt3 :=
    mkPUKRes (upd1.(puk_res_k) ⊔ₚₖ upd2.(puk_res_k))  _ _.
  Next Obligation.
    intros ???? [pk1 Heq1 Heq2] [pk2 Heq3 Heq4].
    simpl.
    unfold opt_place_update_eq in *.
    destruct pk1, pk2; simpl in *; try done.
    all: subst; done.
  Defined.
  Next Obligation.
    intros ???? [pk1 Heq1 Heq2] [pk2 Heq3 Heq4].
    simpl.
    unfold opt_place_update_eq in *.
    destruct allowed; simpl in *; try done.
    all: subst; done.
  Defined.
End place.

Global Infix "⪯ₚ" := (place_update_kind_incl) (at level 51).
Global Infix "⊔ₚₖ" := (place_update_kind_max) (at level 50).
Global Infix "⊓ₚ" := (place_update_kind_restrict) (at level 50).
