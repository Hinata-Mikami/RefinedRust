From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.struct Require Import def subtype subltype unfold.
From refinedrust Require Import options.

(** ** Subtyping instances for structs *)

Section subtype.
  Context `{!typeGS Σ}.

  Import EqNotations.

  (** Subtyping *)
  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subtype_struct E L {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) (rs1 : plist place_rfnRT rts1) (rs2 : plist place_rfnRT rts2)  sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗
    ⌜length rts1 = length rts2⌝ ∗
    foldr (λ '(existT rt1 (ty1, r1'), existT rt2 (ty2, r2')) T,
      match r1' with
      | #r1 => ∃ r2, ⌜r2' = #r2⌝ ∗ weak_subtype E L r1 r2 ty1 ty2 T
      | _ => ∃ (Heq : rt1 = rt2), ⌜r1' = rew <-[place_rfnRT] Heq in r2'⌝ ∗ mut_subtype E L ty1 (rew <- [type] Heq in ty2) T
      end) T (zip (hpzipl rts1 tys1 rs1) (hpzipl rts2 tys2 rs2))
    ⊢ weak_subtype E L rs1 rs2 (struct_t sls1 tys1) (struct_t sls2 tys2) T.
  Proof.
    iIntros "(-> & %Hlen & Hb)". iIntros (??) "#CTX #HE HL".
    match goal with |- context[foldr ?P _ _] => set (Q := P) end.
    iAssert (|={F}=> struct_t_incl_precond tys1 tys2 rs1 rs2 ∗ llctx_interp L ∗ T)%I with "[Hb HL]" as ">(Hp & $ & $)"; first last.
    { by iApply struct_t_type_incl. }
    iInduction rts1 as [ | rt1 rts1] "IH" forall (rts2 tys1 tys2 rs1 rs2 Hlen); destruct rts2 as [ | rt2 rts2]; simpl in Hlen; try done;
      inv_hlist tys2; inv_hlist tys1.
    { simpl. iFrame. by iApply big_sepL2_nil. }
    intros ty1 tys1 ty2 tys2.
    destruct rs1 as [r1 rs1]. destruct rs2 as [r2 rs2].
    simpl.
    destruct r1.
    - iDestruct "Hb" as "(%r2' & -> & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hi & HL & HT)".
      iMod ("IH" with "[] HT HL") as "(Hi2 & $ & $)"; last by iFrame.
      iPureIntro; lia.
    - iDestruct "Hb" as "(%Heq & %Heq' & %Hb & HT)". subst.
      iPoseProof (full_subtype_acc with "HE HL") as "#Hsub"; first apply Hb.
      iMod ("IH" with "[] HT HL") as "(Hi2 & $ & $)". { iPureIntro; lia. }
      rewrite {3}/struct_t_incl_precond; simpl. iFrame.
      iExists eq_refl. iR. done.
  Qed.
  Definition weak_subtype_struct_inst := [instance @weak_subtype_struct].
  Global Existing Instance weak_subtype_struct_inst | 20.

  (* TODO replace foldr with relate_hlist *)
  Lemma mut_subtype_struct E L {rts} (tys1 tys2 : hlist type rts) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗ foldr (λ '(existT rt (ty1, ty2)) T, mut_subtype E L ty1 ty2 T) T (hzipl2 _ tys1 tys2)
    ⊢ mut_subtype E L (struct_t sls1 tys1) (struct_t sls2 tys2) T.
  Proof.
    iIntros "(-> & Hb)".
    iAssert (⌜Forall (λ '(existT x (ty1, ty2)), full_subtype E L ty1 ty2) (hzipl2 rts tys1 tys2)⌝ ∗ T)%I with "[Hb]" as "(%Hsubt & $)"; first last.
    { iPureIntro. by apply  struct_t_full_subtype. }
    iInduction rts as [ | rt rts] "IH" forall (tys1 tys2); inv_hlist tys2; inv_hlist tys1.
    { iFrame. iPureIntro. simpl. done. }
    intros ty1 tys1 ty2 tys2.
    rewrite hzipl2_cons. simpl.
    iDestruct "Hb" as "(%Hsub & Hb)".
    iPoseProof ("IH"  with "Hb") as "(%Hsubt & $)".
    iPureIntro. constructor; done.
  Qed.
  Global Instance mut_subtype_struct_inst E L {rts} (tys1 tys2 : hlist type rts) sls1 sls2 :
    MutSubtype E L (struct_t sls1 tys1) (struct_t sls2 tys2) | 20 :=
    λ T, i2p (mut_subtype_struct E L tys1 tys2 sls1 sls2 T).

  (* TODO replace foldr with relate_hlist *)
  Lemma mut_eqtype_struct E L {rts} (tys1 tys2 : hlist type rts) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗ foldr (λ '(existT rt (ty1, ty2)) T, mut_eqtype E L ty1 ty2 T) T (hzipl2 _ tys1 tys2)
    ⊢ mut_eqtype E L (struct_t sls1 tys1) (struct_t sls2 tys2) T.
  Proof.
    iIntros "(-> & Hb)".
    iAssert (⌜Forall (λ '(existT x (ty1, ty2)), full_eqtype E L ty1 ty2) (hzipl2 rts tys1 tys2)⌝ ∗ T)%I with "[Hb]" as "(%Hsubt & $)"; first last.
    { iPureIntro. apply full_subtype_eqtype; apply struct_t_full_subtype.
      - eapply Forall_impl; first done. intros [? []]. apply full_eqtype_subtype_l.
      - rewrite hzipl2_swap Forall_fmap. eapply Forall_impl; first done.
        intros [? []]. apply full_eqtype_subtype_r. }
    iInduction rts as [ | rt rts] "IH" forall (tys1 tys2); inv_hlist tys2; inv_hlist tys1.
    { iFrame. iPureIntro. simpl. done. }
    intros ty1 tys1 ty2 tys2.
    rewrite hzipl2_cons. simpl.
    iDestruct "Hb" as "(%Hsub & Hb)".
    iPoseProof ("IH"  with "Hb") as "(%Hsubt & $)".
    iPureIntro. constructor; done.
  Qed.
  Global Instance mut_eqtype_struct_inst E L {rts} (tys1 tys2 : hlist type rts) sls1 sls2 :
    MutEqtype E L (struct_t sls1 tys1) (struct_t sls2 tys2) | 20 :=
    λ T, i2p (mut_eqtype_struct E L tys1 tys2 sls1 sls2 T).

  (** Subltyping *)
  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_owned_in E L {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) rs1 rs2 sls1 sls2 wl T  :
    ⌜sls1 = sls2⌝ ∗ ⌜length rts1 = length rts2⌝ ∗ foldr (λ '(existT rt1 (lt1, r1'), existT rt2 (lt2, r2')) T,
      weak_subltype E L (Owned false) r1' r2' lt1 lt2 T) T (zip (hpzipl rts1 lts1 rs1) (hpzipl rts2 lts2 rs2))
    ⊢ weak_subltype E L (Owned wl) (#rs1) (#rs2) (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & %Hlen & Ha)" (??) "#CTX #HE HL".
    iAssert (|={F}=> ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2, ltype_incl (Owned false) (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) ∗ llctx_interp L ∗ T)%I with "[Ha HL]" as ">(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl_owned_in lts1 lts2). done. }
    iInduction rts1 as [ | rt1 rts1] "IH" forall (rts2 lts1 lts2 rs1 rs2 Hlen); destruct rts2 as [ | rt2 rts2]; try done;
      inv_hlist lts2; inv_hlist lts1.
    { simpl. by iFrame. }
    intros lt1 lts1 lt2 lts2. simpl in Hlen.
    destruct rs1 as [r1 rs1]. destruct rs2 as [r2 rs2].
    simpl. iMod ("Ha" with "[//] CTX HE HL") as "(Hincl1 & HL & HT)".
    iMod ("IH" with "[] HT HL") as "(Hincl & $ & $)"; first (iPureIntro; lia).
    by iFrame.
  Qed.
  Global Instance weak_subltype_struct_owned_in_inst E L {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) rs1 rs2 sls1 sls2 wl :
    SubLtype E L (Owned wl) #rs1 #rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 10 :=
    λ T, i2p (weak_subltype_struct_owned_in E L lts1 lts2 rs1 rs2 sls1 sls2 wl T).

  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_owned E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 wl T  :
    ⌜sls1 = sls2⌝ ∗ ⌜rs1 = rs2⌝ ∗ foldr (λ '(existT rt1 (lt1, lt2)) T,
      mut_subltype E L lt1 lt2 T) T (hzipl2 rts lts1 lts2)
    ⊢ weak_subltype E L (Owned wl) (rs1) (rs2) (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & -> & HT)" (??) "#CTX #HE HL".
    iAssert (([∗ list] ltp ∈ hzipl2 rts lts1 lts2, ∀ r, ltype_incl (Owned false) r r (projT2 ltp).1 (projT2 ltp).2) ∗ llctx_interp L ∗ T)%I with "[HT HL]" as "(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl_owned lts1 lts2). done. }
    clear rs2.
    iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { simpl. iFrame. }
    intros lt1 lts1 lt2 lts2.
    simpl. iDestruct "HT" as "(%Hsubt & HT)".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl1"; first apply Hsubt.
    iPoseProof ("IH" with "HT HL")  as "(Hincl & $ & $)".
    iFrame. iIntros (?). iApply "Hincl1".
  Qed.
  Global Instance weak_subltype_struct_owned_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 wl :
    SubLtype E L (Owned wl) rs1 rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 11 :=
    λ T, i2p (weak_subltype_struct_owned E L lts1 lts2 rs1 rs2 sls1 sls2 wl T).

  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_shared_in E L {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) rs1 rs2 sls1 sls2 κ T  :
    ⌜sls1 = sls2⌝ ∗ ⌜length rts1 = length rts2⌝ ∗ foldr (λ '(existT rt1 (lt1, r1'), existT rt2 (lt2, r2')) T,
      weak_subltype E L (Shared κ) r1' r2' lt1 lt2 T) T (zip (hpzipl rts1 lts1 rs1) (hpzipl rts2 lts2 rs2))
    ⊢ weak_subltype E L (Shared κ) (#rs1) (#rs2) (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & %Hlen & Ha)" (??) "#CTX #HE HL".
    iAssert (|={F}=> ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2, ltype_incl (Shared κ) (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) ∗ llctx_interp L ∗ T)%I with "[Ha HL]" as ">(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl_shared_in lts1 lts2). done. }
    (* TODO duplicated *)
    iInduction rts1 as [ | rt1 rts1] "IH" forall (rts2 lts1 lts2 rs1 rs2 Hlen); destruct rts2 as [ | rt2 rts2]; try done;
      inv_hlist lts2; inv_hlist lts1.
    { simpl. by iFrame. }
    intros lt1 lts1 lt2 lts2. simpl in Hlen.
    destruct rs1 as [r1 rs1]. destruct rs2 as [r2 rs2].
    simpl. iMod ("Ha" with "[//] CTX HE HL") as "(Hincl1 & HL & HT)".
    iMod ("IH" with "[] HT HL") as "(Hincl & $ & $)"; first (iPureIntro; lia).
    by iFrame.
  Qed.
  Global Instance weak_subltype_struct_shared_in_inst E L {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) rs1 rs2 sls1 sls2 κ :
    SubLtype E L (Shared κ) #rs1 #rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 10 :=
    λ T, i2p (weak_subltype_struct_shared_in E L lts1 lts2 rs1 rs2 sls1 sls2 κ T).

  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_shared E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 κ T  :
    ⌜sls1 = sls2⌝ ∗ ⌜rs1 = rs2⌝ ∗ foldr (λ '(existT rt1 (lt1, lt2)) T,
      mut_subltype E L lt1 lt2 T) T (hzipl2 rts lts1 lts2)
    ⊢ weak_subltype E L (Shared κ) (rs1) (rs2) (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & -> & HT)" (??) "#CTX #HE HL". iModIntro.
    iAssert (([∗ list] ltp ∈ hzipl2 rts lts1 lts2, ∀ r, ltype_incl (Shared κ) r r (projT2 ltp).1 (projT2 ltp).2) ∗ llctx_interp L ∗ T)%I with "[HT HL]" as "(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl_shared lts1 lts2). done. }
    (* TODO duplicated *)
    clear rs2. iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { simpl. iFrame. }
    intros lt1 lts1 lt2 lts2.
    simpl. iDestruct "HT" as "(%Hsubt & HT)".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl1"; first apply Hsubt.
    iPoseProof ("IH" with "HT HL")  as "(Hincl & $ & $)".
    iFrame. iIntros (?). iApply "Hincl1".
  Qed.
  Global Instance weak_subltype_struct_shared_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 κ :
    SubLtype E L (Shared κ) rs1 rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 11 :=
    λ T, i2p (weak_subltype_struct_shared E L lts1 lts2 rs1 rs2 sls1 sls2 κ T).

  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_base E L {rts} (lts1 lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 k T :
    ⌜sls1 = sls2⌝ ∗ ⌜rs1 = rs2⌝ ∗ foldr (λ '(existT rt1 (lt1, lt2)) T,
      mut_eqltype E L lt1 lt2 T) T (hzipl2 rts lts1 lts2)
    ⊢ weak_subltype E L k rs1 rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & -> & HT)" (??) "#CTX #HE HL". iModIntro.
    iAssert ((∀ k, [∗ list] ltp ∈ hzipl2 rts lts1 lts2, ∀ r, ltype_eq k r r (projT2 ltp).1 (projT2 ltp).2) ∗ llctx_interp L ∗ T)%I with "[HT HL]" as "(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl lts1 lts2). done. }
    clear rs2. iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { simpl. by iFrame. }
    intros lt1 lts1 lt2 lts2.
    simpl. iDestruct "HT" as "(%Hsubt & HT)".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl1"; first apply Hsubt.
    iPoseProof ("IH" with "HT HL")  as "(Hincl & $ & $)".
    iFrame. iIntros (?). iSplitR.
    - iIntros (?). iApply "Hincl1".
    - iApply "Hincl".
  Qed.
  Global Instance weak_subltype_struct_base_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 k :
    SubLtype E L k rs1 rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 20 :=
    λ T, i2p (weak_subltype_struct_base E L lts1 lts2 rs1 rs2 sls1 sls2 k T).


  Program Definition MutEqltypeStructHFR (cap : nat) : HetFoldableRelation (A := RT) (G := ltype) := {|
    hfr_rel E L i rt lt1 lt2 T := mut_eqltype E L lt1 lt2 T;
    hfr_cap := cap;
    hfr_inv := True;
    hfr_core_rel E L i rt lt1 lt2 := ⌜full_eqltype E L lt1 lt2⌝%I;
    hfr_elim_mode := false
  |}.
  Next Obligation.
    iIntros (i0 E L i rt lt1 lt2 T) "(%Hsubt & HT)". by iFrame.
  Qed.
  Global Arguments MutEqltypeStructHFR : simpl never.

  Lemma mut_subltype_struct E L {rts} (lts1 lts2 : hlist ltype rts) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗
    relate_hlist E L [] rts lts1 lts2 0 (MutEqltypeStructHFR (length rts)) T
    ⊢ mut_subltype E L (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    rewrite /MutEqltypeStructHFR.
    iIntros "(-> & Ha & $)".
    iPoseProof ("Ha" with "[] [//]") as "Ha".
    { simpl. iPureIntro. lia. }
    simpl.
    iAssert (⌜Forall (λ lts, full_eqltype E L (projT2 lts).1 (projT2 lts).2) (hzipl2 rts lts1 lts2)⌝)%I with "[Ha]" as "%Hsubt"; first last.
    { iPureIntro. refine (struct_full_subltype _ _ lts1 lts2 _ _); done. }
    iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { iFrame. simpl; done. }
    intros lt1 lts1 lt2 lts2. rewrite hzipl2_cons. simpl.
    iDestruct "Ha" as "(%Hsubt & Ha)". iPoseProof ("IH" with "Ha") as "%Hsubt'".
    iPureIntro. constructor; done.
  Qed.
  Global Instance mut_subltype_struct_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) sls1 sls2 :
    MutSubLtype E L (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 20 :=
    λ T, i2p (mut_subltype_struct E L lts1 lts2 sls1 sls2 T).

  Lemma mut_eqltype_struct E L {rts} (lts1 lts2 : hlist ltype rts) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗
    relate_hlist E L [] rts lts1 lts2 0 (MutEqltypeStructHFR (length rts)) T
    ⊢ mut_eqltype E L (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    rewrite /MutEqltypeStructHFR.
    iIntros "(-> & Ha & $)".
    iPoseProof ("Ha" with "[] [//]") as "Ha".
    { simpl. iPureIntro. lia. }
    simpl.
    iAssert (⌜Forall (λ lts, full_eqltype E L (projT2 lts).1 (projT2 lts).2) (hzipl2 rts lts1 lts2)⌝)%I with "[Ha]" as "%Hsubt"; first last.
    { iPureIntro. by apply: (struct_full_eqltype _ _ _ _ _ _ ). }
    iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { iFrame. simpl; done. }
    intros lt1 lts1 lt2 lts2. rewrite hzipl2_cons. simpl.
    iDestruct "Ha" as "(%Hsubt & Ha)". iPoseProof ("IH" with "Ha") as "%Hsubt'".
    iPureIntro. constructor; done.
  Qed.
  Global Instance mut_eqltype_struct_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) sls1 sls2 :
    MutEqLtype E L (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 20 :=
    λ T, i2p (mut_eqltype_struct E L lts1 lts2 sls1 sls2 T).

  (* Ofty unfolding if necessary *)
  Lemma weak_subltype_struct_ofty_1_evar E L {rts1 rts2} (lts1 : hlist ltype rts1) (ty2 : type (plist place_rfnRT rts2)) sls k r1 r2 T :
    (∃ tys2, ⌜ty2 = struct_t sls tys2⌝ ∗ weak_subltype E L k r1 r2 (StructLtype lts1 sls) (StructLtype (@OfTy _ _ +<$> tys2) sls) T)
    ⊢ weak_subltype E L k r1 r2 (StructLtype lts1 sls) (◁ ty2) T.
  Proof.
    iIntros "(%tys2 & -> & Hsubt)" (??) "#CTX #HE HL".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply struct_t_unfold_2.
  Qed.
  Global Instance weak_subltype_struct_ofty_1_evar_inst E L {rts1 rts2} (lts1 : hlist ltype rts1) (ty2 : type (plist place_rfnRT rts2)) sls k rs1 rs2 `{!IsProtected ty2} :
    SubLtype E L k rs1 rs2 (StructLtype lts1 sls) (◁ ty2)%I | 30 :=
    λ T, i2p (weak_subltype_struct_ofty_1_evar E L lts1 ty2 sls k rs1 rs2 T).

  Lemma weak_subltype_struct_ofty_1 E L {rts1 rts2} (lts1 : hlist ltype rts1) (tys2 : hlist type rts2) sls1 sls2 k r1 r2 T :
    (⌜sls1 = sls2⌝ ∗ weak_subltype E L k r1 r2 (StructLtype lts1 sls1) (StructLtype (@OfTy _ _ +<$> tys2) sls2) T)
    ⊢ weak_subltype E L k r1 r2 (StructLtype lts1 sls1) (◁ struct_t sls2 tys2) T.
  Proof.
    iIntros "(-> & Hsubt)" (??) "#CTX #HE HL".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply struct_t_unfold_2.
  Qed.
  Global Instance weak_subltype_struct_ofty_1_inst E L {rts1 rts2} (lts1 : hlist ltype rts1) (tys2 : hlist type rts2) sls1 sls2 k rs1 rs2 :
    SubLtype E L k rs1 rs2 (StructLtype lts1 sls1) (◁ struct_t sls2 tys2)%I | 20 :=
    λ T, i2p (weak_subltype_struct_ofty_1 E L lts1 tys2 sls1 sls2 k rs1 rs2 T).


  Lemma weak_subltype_struct_ofty_2 E L {rts1 rts2} (tys1 : hlist type rts1) (lts2 : hlist ltype rts2) sls1 sls2 k r1 r2 T :
    (weak_subltype E L k r1 r2 (StructLtype (@OfTy _ _ +<$> tys1) sls1) (StructLtype lts2 sls2) T)
    ⊢ weak_subltype E L k r1 r2 (◁ struct_t sls1 tys1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "Hsubt" (??) "#CTX #HE HL".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "[] Hincl").
    iApply struct_t_unfold_1.
  Qed.
  Definition weak_subltype_struct_ofty_2_inst := [instance weak_subltype_struct_ofty_2].
  Global Existing Instance weak_subltype_struct_ofty_2_inst | 20.

  Lemma mut_subltype_struct_ofty_1 E L {rts} (lts1 : hlist ltype rts) (ty2 : type (plist place_rfnRT rts)) sls T :
    (∃ tys2, ⌜ty2 = struct_t sls tys2⌝ ∗ mut_subltype E L (StructLtype lts1 sls) (StructLtype (@OfTy _ _ +<$> tys2) sls) T)
    ⊢ mut_subltype E L (StructLtype lts1 sls) (◁ ty2) T.
  Proof.
    iIntros "(%tys21 & -> & %Hsubt & $)".
    iPureIntro.
    etrans; first apply Hsubt.
    apply full_eqltype_subltype_l. apply (struct_t_unfold_full_eqltype _ _ tys21).
  Qed.
  Global Instance mut_subltype_struct_ofty_1_inst E L {rts} (lts1 : hlist ltype rts) (ty2 : type (plist place_rfnRT rts)) sls :
    MutSubLtype E L (StructLtype lts1 sls) (◁ ty2)%I := λ T, i2p (mut_subltype_struct_ofty_1 E L lts1 ty2 sls T).

  Lemma mut_subltype_struct_ofty_2 E L {rts} (lts2 : hlist ltype rts) (tys1 : hlist type rts) sls1 sls2 T :
    (⌜sls1 = sls2⌝ ∗ mut_subltype E L (StructLtype (@OfTy _ _ +<$> tys1) sls1) (StructLtype lts2 sls1) T)
    ⊢ mut_subltype E L (◁ struct_t sls1 tys1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & %Hsubt & $)".
    iPureIntro. etrans; last apply Hsubt.
    apply full_eqltype_subltype_r. apply (struct_t_unfold_full_eqltype _ _ tys1).
  Qed.
  Global Instance mut_subltype_struct_ofty_2_inst E L {rts} (lts2 : hlist ltype rts) (tys1 : hlist type rts) sls1 sls2 :
    MutSubLtype E L (◁ struct_t sls1 tys1)%I (StructLtype lts2 sls2) := λ T, i2p (mut_subltype_struct_ofty_2 E L lts2 tys1 sls1 sls2 T).

  Lemma mut_eqltype_struct_ofty_1 E L {rts} (lts1 : hlist ltype rts) (ty2 : type (plist place_rfnRT rts)) sls T :
    (∃ tys2, ⌜ty2 = struct_t sls tys2⌝ ∗ mut_eqltype E L (StructLtype lts1 sls) (StructLtype (@OfTy _ _ +<$> tys2) sls) T)
    ⊢ mut_eqltype E L (StructLtype lts1 sls) (◁ ty2) T.
  Proof.
    iIntros "(%tys21 & -> & %Hsubt & $)".
    iPureIntro. etrans; first apply Hsubt. apply (struct_t_unfold_full_eqltype _ _ tys21).
  Qed.
  Global Instance mut_eqltype_struct_ofty_1_inst E L {rts} (lts1 : hlist ltype rts) (ty2 : type (plist place_rfnRT rts)) sls :
    MutEqLtype E L (StructLtype lts1 sls) (◁ ty2)%I := λ T, i2p (mut_eqltype_struct_ofty_1 E L lts1 ty2 sls T).

  Lemma mut_eqltype_struct_ofty_2 E L {rts} (lts2 : hlist ltype rts) (tys1 : hlist type rts) sls1 sls2 T :
    (⌜sls1 = sls2⌝ ∗ mut_eqltype E L (StructLtype (@OfTy _ _ +<$> tys1) sls1) (StructLtype lts2 sls1) T)
    ⊢ mut_eqltype E L (◁ struct_t sls1 tys1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & %Hsubt & $)".
    iPureIntro. etrans; last apply Hsubt. symmetry. apply (struct_t_unfold_full_eqltype _ _ tys1).
  Qed.
  Global Instance mut_eqltype_struct_ofty_2_inst E L {rts} (lts2 : hlist ltype rts) (tys1 : hlist type rts) sls1 sls2 :
    MutEqLtype E L (◁ struct_t sls1 tys1)%I (StructLtype lts2 sls2) := λ T, i2p (mut_eqltype_struct_ofty_2 E L lts2 tys1 sls1 sls2 T).

End subtype.

Global Typeclasses Opaque MutEqltypeStructHFR.
