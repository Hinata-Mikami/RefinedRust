From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype programs.
From refinedrust.enum Require Import def subltype.
From refinedrust Require Import options.


Section rules.
  Context `{!typeGS Σ}.

  Lemma enum_place_cond_nonuniq {rt} (en : enum rt)
      (variant1 variant2 : option enum_ltype_variant) b :
    UpdWeak ⪯ₚ b -∗
    typed_place_cond b (EnumLtype en variant1) (EnumLtype en variant2).
  Proof.
    iIntros "Hincl".
    destruct b; simpl in *; rewrite /typed_place_cond /=.
    - rewrite !ltype_st_enum. done.
    - rewrite !ltype_st_enum. done.
    - rewrite !ltype_st_enum. done.
    - iDestruct "Hincl" as "[]".
  Qed.

  Lemma enum_place_cond_uniq {rt} (en : enum rt)
      (variant1 variant2 : option enum_ltype_variant) κs :
    ⊢ typed_place_cond (UpdUniq κs) (EnumLtype en variant1) (EnumLtype en variant2).
  Proof.
    rewrite /typed_place_cond/=.
    rewrite ltype_st_enum. iR. iExists eq_refl.
    simp_ltypes. iSplitR.
    - (* need an ltype_eq lifting lemma. The problem is that this doesn't work if we have the refinement override. *)
      admit.
    - iApply enum_ltype_imp_unblockable.
  (*Qed.*)
  Abort.

  (* One idea to make this more usable:
    - refinement overrides enforce only work when we then put an OpenedLtype. But I don't want an Owned OpenedLtype. Also for Shared, this doesn't work so nicely.

    - I guess if I do a refinement override in Uniq mode though, this will get us to Opened.
    - and the place rules should always try to keep it in the mode without refinement overrides, only doing that when we actually get a strong update (i.e., the update mode is more permissive than UpdUniq.)
  *)

  Program Definition enum_tag_ty_inj' {rt} (en : enum rt) (r : rt) (tag : string) (Heq : enum_tag en r = Some tag) :
    sigT (λ e : enum_tag_sem rt, enum_tag_ty_inj en tag = Some e) :=
    (*match enum_tag_compat _ en r tag Heq with*)
    (*| existT vinj Heq' => existT (mk_enum_tag_sem (enum_rt en r) (enum_ty en r) vinj) Heq'*)
    (*end*)
    existT (mk_enum_tag_sem (enum_rt en r) (enum_ty en r)
      (match enum_tag_compat _ en r tag Heq with
      | existT vinj Heq' => vinj
      end))
      (match enum_tag_compat _ en r tag Heq with
      | existT vinj Heq' => Heq'
      end)
  .
  Next Obligation.
    simpl. intros. exact eq_refl.
  Defined.
  Definition enum_tag_rfn_inj {rt} (en : enum rt) (tag : string)
    (r_old : rt)
    (Heq : enum_tag en r_old = Some tag)
    : (enum_rt en r_old) → rt :=
    enum_tag_rt_inj (projT1 (enum_tag_ty_inj' en r_old tag Heq)).

  (*Definition enum_tag_rfn_inj' {rt} (en : enum rt) (tag : string)*)
    (*(r_old : rt)*)
    (*(Heq : enum_tag en r_old = Some tag)*)
    (*: (enum_tag_rt' en tag) → rt :=*)
    (*λ ri,*)
      (*enum_tag_rfn_inj en tag r_old Heq (rew <-[id] (enum_variant_rt_tag_rt_eq en r_old tag Heq) in ri).*)

  (*Definition placein_or_default {rt} (r : place_rfn rt) (def : rt) : rt :=*)
    (*match r with*)
    (*| PlaceIn r => r*)
    (*| _ => def*)
    (*end.*)

  Lemma typed_place_enum_data_field_owned {rt} E L f l (en : enum rt) (r : rt) bmin0 els tag'
      (variant : option enum_ltype_variant) P T :
    typed_place E L f l (EnumLtype en variant) (#r) bmin0 (Owned) (EnumDataPCtx els tag' :: P) T :-
      exhale (⌜en.(enum_els) = els⌝);
      exhale (⌜lctx_place_update_kind_incl E L UpdStrong bmin0⌝);
      return (let v := interp_enum_ltype_variant en variant r in
        typed_place E L f ((GetEnumDataLocSt l els)) v.(eltv_ltype) (PlaceIn v.(eltv_rfn)) bmin0 (Owned ) P (λ L2 κs l2 b2 bmin2 rti ltyi ri updcx,
        T L2 κs l2 b2 bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            (* we cannot borrow the whole variant itself in Rust *)
            ∃ r', ⌜upd'.(pupd_rfn) = #r'⌝ ∗
            cont (mkPUpd _ bmin0
              _
              (EnumLtype en (Some (mk_enum_ltype_variant v.(eltv_tag)
                upd'.(pupd_rt) upd'.(pupd_lt) r')))
              (* no update, as we are owned *)
              #r
              upd'.(pupd_R)
              UpdStrong
              opt_place_update_eq_refl
              opt_place_update_eq_refl)))
      )).
  Proof.
    iIntros "(%Hels & %Hstrong & Hp)".
    iIntros (Φ F ??) "#(LFT & LLCTX) #HE HL Hf Hl HΦ/=".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hstrong"; first apply Hstrong.
    iPoseProof (enum_ltype_acc_owned F with "Hl") as "(%el & %Halg & %Hly & #Hlb & Hb)"; first done.
    iApply fupd_wpe.
    iMod (fupd_mask_mono with "Hb") as "(%variant_ly & %Hcompat & %Hvariant & %Hst & Htag & Hpayload & Hcl)"; first done.

    (*iApply (wpe_logical_step with "Hcl"); [done | solve_ndisj.. | ].*)
    rewrite -Hels.
    iApply (wp_enum_data _ _ _ _ el
      (interp_enum_ltype_variant en variant r).(eltv_tag) variant_ly with "Hlb"); [done | done | ].
    iApply physical_step_intro. iModIntro. iNext. iIntros (v Hv).
    iExists (GetEnumDataLocSt l (enum_els en)). iSplitR.
    { done. }
    iApply ("Hp" with "[//] [//] [$LFT $LLCTX] HE HL Hf [Hpayload]").
    { rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=. iExact "Hpayload". }
    iIntros (L' κs l2 bmin b2 rti ltyi ri updcx) "Hli Hcont".
    iApply ("HΦ" $! _ _ _ bmin with "Hli").
    iIntros (upd) "#Hincl Hl2 HR Hcond".
    iMod ("Hcont" with "Hincl Hl2 HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl2 & Hcond & #Hmin & HR & Hupd & HL & Hf & Hcont)".
    iDestruct "Hcont" as (re') "(%Hre' & Hcont)". subst. rewrite Hre'.
    iPoseProof (typed_place_cond_syn_type_compat with "Hcond") as "%Hst_compat".
    pose proof (Hst_compat _ Hst) as Hst_new.
    iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "Hl2".
    iMod ("Hcl" $! _ upd'.(pupd_lt) re' r with "[] [] Htag Hl2") as "Hl".
    { done. }
    { done. }
    iModIntro. iExists (mkPUpd _ bmin0 _
      (EnumLtype en (Some (mk_enum_ltype_variant
        (interp_enum_ltype_variant en variant r).(eltv_tag)
        upd'.(pupd_rt) upd'.(pupd_lt) re'))) #r
      upd'.(pupd_R) UpdStrong opt_place_update_eq_refl opt_place_update_eq_refl).
    simpl. iFrame "Hl HR Hupd HL Hf Hcont".
    iSplitR.
     { simpl. iPureIntro. rewrite !ltype_st_enum //. }
    iFrame "Hstrong".
  Qed.
  Definition typed_place_enum_data_field_owned_inst := [instance @typed_place_enum_data_field_owned].
  Global Existing Instance typed_place_enum_data_field_owned_inst.

  Lemma typed_place_enum_data_field_shared {rt} E L f l (en : enum rt) (r : rt) bmin0 els tag'
      (variant : option enum_ltype_variant) κ P T :
    typed_place E L f l (EnumLtype en variant) (#r) bmin0 (Shared κ) (EnumDataPCtx els tag' :: P) T :-
      exhale (⌜en.(enum_els) = els⌝);
      exhale (⌜lctx_place_update_kind_incl E L UpdWeak bmin0⌝);
      return (let v := interp_enum_ltype_variant en variant r in
        typed_place E L f ((GetEnumDataLocSt l els)) v.(eltv_ltype) (#v.(eltv_rfn)) bmin0 (Shared κ) P (λ L2 κs l2 b2 bmin2 rti ltyi ri updcx,
        T L2 κs l2 b2 bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            ∃ r', ⌜upd'.(pupd_rfn) = #r'⌝ ∗
            cont (mkPUpd _ bmin0
              _
              (EnumLtype en (Some (mk_enum_ltype_variant v.(eltv_tag)
                upd'.(pupd_rt) upd'.(pupd_lt) r')))
              (* no update, as we are shared *)
              #r
              upd'.(pupd_R)
              (*upd'.(pupd_performed)*)
              UpdWeak
              opt_place_update_eq_refl
              opt_place_update_eq_refl)))
       )).
  Proof.
    iIntros "(%Hels & %Hweak & Hp)".
    iIntros (Φ F ??) "#(LFT & LLCTX) #HE HL Hf Hl HΦ/=".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hweak"; first apply Hweak.
    iPoseProof (enum_ltype_acc_shared F with "Hl") as "(%el & %Halg & %Hly & #Hlb & Hb)"; first done.
    iApply fupd_wpe.
    iMod (fupd_mask_mono with "Hb") as "(%variant_ly & %Hcompat & %Hvariant & %Hst & #Htag & #Hpayload & Hcl)"; first done.

    rewrite -Hels.
    iApply (wp_enum_data _ _ _ _ el
      (interp_enum_ltype_variant en variant r).(eltv_tag) variant_ly with "Hlb"); [done | done | ].
    iApply physical_step_intro. iModIntro. iNext. iIntros (v Hv).
    iExists (GetEnumDataLocSt l (enum_els en)). iSplitR.
    { done. }
    iApply ("Hp" with "[//] [//] [$LFT $LLCTX] HE HL Hf [Hpayload]").
    { rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=. iExact "Hpayload". }
    iIntros (L' κs l2 b2 bmin rti ltyi ri updcx) "Hli Hcont".
    iApply ("HΦ" with "Hli").
    iIntros (upd) "#Hincl Hl2 HR Hcond".
    iMod ("Hcont" with "Hincl Hl2 HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl2 & Hcond & #Hmin & HR & Hupd & HL & Hf & Hcont)".
    iDestruct "Hcont" as (re') "(%Hre' & Hcont)". subst. rewrite Hre'.
    iPoseProof (typed_place_cond_syn_type_compat with "Hcond") as "%Hst_compat".
    pose proof (Hst_compat _ Hst) as Hst_new.
    iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "Hl2".
    iMod ("Hcl" $! _ upd'.(pupd_lt) re' r with "[] [] Htag Hl2") as "Hl".
    { done. }
    { done. }
    iModIntro. iExists (mkPUpd _ bmin0 _
      (EnumLtype en (Some (mk_enum_ltype_variant
        (interp_enum_ltype_variant en variant r).(eltv_tag)
        upd'.(pupd_rt) upd'.(pupd_lt) re'))) #r
      upd'.(pupd_R) UpdWeak opt_place_update_eq_refl opt_place_update_eq_refl).
     simpl. iFrame "Hl HR Hupd HL Hf Hcont".
     iSplitR; last done.
     iApply enum_place_cond_nonuniq; done.
   Qed.
   Definition typed_place_enum_data_field_shared_inst := [instance @typed_place_enum_data_field_shared].
  Global Existing Instance typed_place_enum_data_field_shared_inst.

  (* NOTE for the uniq case, I'll need to know that the enum ty here is a struct. Will need some eqcasts, I guess.

    The interpretation will say that it is in the valid part,
      i.e.:
      - the refinement type matches up.
      - the refinement of the projection is in sync
     Moreover (implicit property as part of the borrow): we can unblock to it.
    I provide that equality there as an assumption.
     alternative: I prove it so that I get an eq_refl.

    If I do a strong update, I put OpenedLtype, which releases the constraint on the data field.

    If I do a weak update, I need to update the outer refinement as well.

  *)

  (*
  Lemma typed_place_enum_data_field_uniq {rt} E L f l (en : enum rt) (r : rt) bmin0 els tag tag' {rte} (lte : ltype rte) re κ γ P T :
    typed_place E L f l (EnumLtype en tag lte re) (#r) bmin0 (Uniq κ γ) (EnumDataPCtx els tag' :: P) T :-
      exhale (⌜en.(enum_els) = els⌝);
      exhale (⌜tag = tag'⌝);
      ∃ (Heq : enum_tag en r = Some tag),
      (* the variant is in sync with the tag
        (we could also assume this from the interpretation, but we want that this is eq_refl) *)
      ∃ (Heq2 : enum_rt en r = rte),
      inhale (⌜re = rew [RT_rt] Heq2 in (enum_r en r)⌝);
      (* access the struct field *)
      return (typed_place E L f ((GetEnumDataLocSt l els)) lte (#re) bmin0 (Uniq κ γ) P (λ L2 κs l2 b2 bmin2 rti ltyi ri updcx,
        T L2 κs l2 b2 bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            li_tactic (check_llctx_place_update_kind_incl_uniq_goal E L3 upd'.(pupd_performed) ([κ])) (λ oeq,
              match oeq with
              | Some Heq3 =>
                ∃ r', ⌜upd'.(pupd_rfn) = #r'⌝ ∗
                cont (mkPUpd _ bmin0 _
                  (EnumLtype en tag upd'.(pupd_lt) r')
                  (#(enum_tag_rfn_inj en tag r Heq (rew <- [RT_rt] Heq2 in (
                    rew <- opt_place_update_eq_use _ _ _ Heq3 upd'.(pupd_eq_1)  in r'))))
                  upd'.(pupd_R)
                  upd'.(pupd_performed)
                  opt_place_update_eq_refl
                  opt_place_update_eq_refl
                )
              | None =>
                (* TODO strong update with Opened *)
                False
              end
            )))
        )).
  Proof.
  Abort.
  *)
End rules.
