From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def subtype subltype unfold.
From refinedrust Require Import options.

(** ** Subtyping instances for shared references *)

Section subtype.
  Context `{!typeGS Σ}.

  (** subtyping *)
  Lemma weak_subtype_shr_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ1 κ2 r1 r2 T :
    (⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subtype E L r1 r2 ty1 ty2 T)
    ⊢ weak_subtype E L #r1 #r2 (shr_ref κ1 ty1) (shr_ref κ2 ty2) T.
  Proof.
    iIntros "(%Hincl & HT)". iIntros (??) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE").
    iMod ("HT" with "[//] CTX HE HL") as "(#Hsub & $ & $)".
    iApply shr_ref_type_incl_in; done.
  Qed.
  Global Instance weak_subtype_shr_in_inst E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ1 κ2 r1 r2 :
    Subtype E L #r1 #r2 (shr_ref κ1 ty1) (shr_ref κ2 ty2) | 10:= λ T, i2p (weak_subtype_shr_in E L ty1 ty2 κ1 κ2 r1 r2 T).

  Lemma weak_subtype_shr E L {rt} (ty1 ty2 : type rt) κ1 κ2 r1 r2 T :
    (⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_subtype E L ty1 ty2 T)
    ⊢ weak_subtype E L r1 r2 (shr_ref κ1 ty1) (shr_ref κ2 ty2) T.
  Proof.
    iIntros "(-> & %Hincl & %Hsubt & HT)". iIntros (??) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE").
    iPoseProof (full_subtype_acc with "HE HL") as "#Hsub"; first done.
    iFrame. unshelve iApply shr_ref_type_incl; done.
  Qed.
  Global Instance weak_subtype_shr_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 r1 r2 :
    Subtype E L r1 r2 (shr_ref κ1 ty1) (shr_ref κ2 ty2) | 11 := λ T, i2p (weak_subtype_shr E L ty1 ty2 κ1 κ2 r1 r2 T).

  Lemma weak_subtype_shr_evar_lft E L {rt} (ty1 ty2 : type rt) κ1 κ2 r1 r2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ weak_subtype E L r1 r2 (shr_ref κ1 ty1) (shr_ref κ1 ty2) T
    ⊢ weak_subtype E L r1 r2 (shr_ref κ1 ty1) (shr_ref κ2 ty2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subtype_shr_evar_lft_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 r1 r2 `{!IsProtected κ2} :
    Subtype E L r1 r2 (shr_ref κ1 ty1) (shr_ref κ2 ty2) | 9 := λ T, i2p (weak_subtype_shr_evar_lft E L ty1 ty2 κ1 κ2 r1 r2 T).

  Lemma mut_subtype_shr E L {rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_subtype E L ty1 ty2 T
    ⊢ mut_subtype E L (shr_ref κ1 ty1) (shr_ref κ2 ty2) T.
  Proof.
    iIntros "(%Hincl & %Hsub & $)". iPureIntro. by eapply shr_ref_full_subtype.
  Qed.
  Global Instance mut_subtype_shr_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 :
    MutSubtype E L (shr_ref κ1 ty1) (shr_ref κ2 ty2) | 10 := λ T, i2p (mut_subtype_shr E L ty1 ty2 κ1 κ2 T).
  Lemma mut_subtype_shr_evar_lft E L {rt} (ty1 ty2 : type rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_subtype E L (shr_ref κ1 ty1) (shr_ref κ1 ty2) T
    ⊢ mut_subtype E L (shr_ref κ1 ty1) (shr_ref κ2 ty2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subtype_shr_evar_lft_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 `{!IsProtected κ2} :
    MutSubtype E L (shr_ref κ1 ty1) (shr_ref κ2 ty2) | 9:= λ T, i2p (mut_subtype_shr_evar_lft E L ty1 ty2 κ1 κ2 T).

  Lemma mut_eqtype_shr E L {rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqtype E L (shr_ref κ1 ty1) (shr_ref κ2 ty2) T.
  Proof.
    iIntros "(%Hincl & %Hsub & %Hsub2 & $)". iPureIntro. split.
    - eapply shr_ref_full_subtype; first done. by eapply full_eqtype_subtype_l.
    - eapply shr_ref_full_subtype; first done. by eapply full_eqtype_subtype_r.
  Qed.
  Global Instance mut_eqtype_shr_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 :
    MutEqtype E L (shr_ref κ1 ty1) (shr_ref κ2 ty2) | 10 := λ T, i2p (mut_eqtype_shr E L ty1 ty2 κ1 κ2 T).
  Lemma mut_eqtype_shr_evar_lft E L {rt} (ty1 ty2 : type rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_eqtype E L (shr_ref κ1 ty1) (shr_ref κ1 ty2) T
    ⊢ mut_eqtype E L (shr_ref κ1 ty1) (shr_ref κ2 ty2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqtype_shr_evar_lft_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 `{!IsProtected κ2} :
    MutEqtype E L (shr_ref κ1 ty1) (shr_ref κ2 ty2) | 9:= λ T, i2p (mut_eqtype_shr_evar_lft E L ty1 ty2 κ1 κ2 T).

  (** subltyping *)
  Lemma weak_subltype_shr_owned_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Shared κ1) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Owned wl) #r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (shr_ltype_incl_owned_in with "Hincl'").
    done.
  Qed.
  Global Instance weak_subltype_shr_owned_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 r1 r2 :
    SubLtype E L (Owned wl) #r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_shr_owned_in E L lt1 lt2 wl κ1 κ2 r1 r2 T).

 Lemma weak_subltype_shr_owned E L {rt} (lt1 : ltype rt) (lt2 : ltype rt) wl κ1 κ2 r1 r2 T :
    (⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_subltype E L lt1 lt2 T)
    ⊢ weak_subltype E L (Owned wl) r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(-> & %Hincl & %Hsubt & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hsub"; first apply Hsubt.
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (shr_ltype_incl_owned); last done.
    iApply "Hsub".
  Qed.
  Global Instance weak_subltype_shr_owned_inst E L {rt} (lt1 : ltype rt) (lt2 : ltype rt) wl κ1 κ2 r1 r2 :
    SubLtype E L (Owned wl) r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 11 := λ T, i2p (weak_subltype_shr_owned E L lt1 lt2 wl κ1 κ2 r1 r2 T).

  Lemma weak_subltype_shr_shared_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ κ1 κ2 r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Shared (κ1)) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Shared κ) #r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (shr_ltype_incl_shared_in with "[Hincl']"); last done.
    done.
  Qed.
  Global Instance weak_subltype_shr_shared_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ κ1 κ2 r1 r2 :
    SubLtype E L (Shared κ) #r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_shr_shared_in E L lt1 lt2 κ κ1 κ2 r1 r2 T).

  Lemma weak_subltype_shr_shared E L {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ κ1 κ2 r1 r2 T :
    (⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_subltype E L lt1 lt2 T)
    ⊢ weak_subltype E L (Shared κ) r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(-> & %Hincl & %Hsubt & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hsub"; first apply Hsubt.
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (shr_ltype_incl_shared); last done.
    iApply "Hsub".
  Qed.
  Global Instance weak_subltype_shr_shared_inst E L {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ κ1 κ2 r1 r2 :
    SubLtype E L (Shared κ) r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 11 := λ T, i2p (weak_subltype_shr_shared E L lt1 lt2 κ κ1 κ2 r1 r2 T).

  (* Base instance that will trigger, e.g., for Uniq or PlaceGhost refinements *)
  Lemma weak_subltype_shr_base E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T :
    ⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(<- & %Hincl1 & %Hincl2 & %Hsubt & T)" (??) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first done.
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl1"; first apply Hincl1.
    iSpecialize ("Hincl1" with "HE").
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl2"; first apply Hincl2.
    iSpecialize ("Hincl2" with "HE").
    iFrame. iApply shr_ltype_incl; done.
  Qed.
  Global Instance weak_subltype_shr_base_inst E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 :
    SubLtype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 20 := λ T, i2p (weak_subltype_shr_base E L lt1 lt2 k κ1 κ2 r1 r2 T).

  Lemma weak_subltype_shr_evar_lft E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ1) T
    ⊢ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_shr_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 `{!IsProtected κ2} :
    SubLtype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 9 := λ T, i2p (weak_subltype_shr_evar_lft E L lt1 lt2 k κ1 κ2 r1 r2 T).

  Lemma mut_subltype_shr E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_subltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hsub1 & %Hsub2 & %Heq & $)".
    iPureIntro. by eapply shr_full_subltype.
  Qed.
  Global Instance mut_subltype_shr_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    MutSubLtype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 10 := λ T, i2p (mut_subltype_shr E L lt1 lt2 κ1 κ2 T).

  Lemma mut_subltype_shr_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_subltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ1) T
    ⊢ mut_subltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subltype_shr_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 `{!IsProtected κ2} :
    MutSubLtype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 9 := λ T, i2p (mut_subltype_shr_evar_lft E L lt1 lt2 κ1 κ2 T).

  Lemma mut_eqltype_shr E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_eqltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%Heq1 & %Heq2 & %Heq & $)".
    iPureIntro. by eapply shr_full_eqltype.
  Qed.
  Global Instance mut_eqltype_shr_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    MutEqLtype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 10 := λ T, i2p (mut_eqltype_shr E L lt1 lt2 κ1 κ2 T).

  Lemma mut_eqltype_shr_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_eqltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ1) T
    ⊢ mut_eqltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqltype_shr_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 `{!IsProtected κ2} :
    MutEqLtype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) := λ T, i2p (mut_eqltype_shr_evar_lft E L lt1 lt2 κ1 κ2 T).

  (* Ofty unfolding if necessary *)
  Lemma weak_subltype_shr_ofty_1_evar E L {rt1 rt2} (lt1 : ltype rt1) (ty2 : type (place_rfnRT rt2)) k κ1 r1 r2 T :
    (∃ ty2', ⌜ty2 = shr_ref κ1 ty2'⌝ ∗ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (◁ (shr_ref κ1 ty2')) T)
    ⊢ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance weak_subltype_shr_ofty_1_evar_inst E L {rt1 rt2} (lt1 : ltype rt1) (ty2 : type (place_rfnRT rt2)) k κ1 r1 r2 `{!IsProtected ty2} :
    SubLtype E L k r1 r2 (ShrLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (weak_subltype_shr_ofty_1_evar E L lt1 ty2 k κ1 r1 r2 T).

  Lemma weak_subltype_shr_ofty_1 E L {rt1 rt2} (lt1 : ltype rt1) (ty2 : type (rt2)) k κ1 κ2 r1 r2 T :
    weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype (◁ ty2) κ2) T
    ⊢ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (◁ (shr_ref κ2 ty2)) T.
  Proof.
    iIntros "HT". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply shr_ref_unfold_1.
  Qed.
  Global Instance weak_subltype_shr_ofty_1_inst E L {rt1 rt2} (lt1 : ltype (rt1)) (ty2 : type rt2) k r1 r2 κ1 κ2 :
    SubLtype E L k r1 r2 (ShrLtype lt1 κ1) (◁ (shr_ref κ2 ty2))%I | 12 := λ T, i2p (weak_subltype_shr_ofty_1 E L lt1 ty2 k κ1 κ2 r1 r2 T).

  Lemma weak_subltype_shr_ofty_2 E L {rt1 rt2} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 T :
    (weak_subltype E L k r1 r2 (ShrLtype (◁ ty1) κ1) (ShrLtype lt2 κ2) T)
    ⊢ weak_subltype E L k r1 r2 (◁ (shr_ref κ1 ty1)) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "[] Hincl").
    iApply shr_ref_unfold_2.
  Qed.
  Global Instance weak_subltype_shr_ofty_2_inst E L {rt1 rt2} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 :
    SubLtype E L k r1 r2 (◁ (shr_ref κ1 ty1))%I (ShrLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_shr_ofty_2 E L ty1 lt2 k r1 r2 κ1 κ2 T).

  (* same for [mut_subltype] *)
  Lemma mut_subltype_shr_ofty_1_evar E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt))  κ1 T :
    (∃ ty2', ⌜ty2 = shr_ref κ1 ty2'⌝ ∗ mut_subltype E L (ShrLtype lt1 κ1) (◁ (shr_ref κ1 ty2')) T)
    ⊢ mut_subltype E L (ShrLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance mut_subltype_shr_ofty_1_evar_inst E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt)) κ1 `{!IsProtected ty2} :
    MutSubLtype E L (ShrLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (mut_subltype_shr_ofty_1_evar E L lt1 ty2 κ1 T).

  Lemma mut_subltype_shr_ofty_1 E L {rt} `(lt1 : ltype rt) (ty2 : type (rt)) κ1 κ2 T :
    mut_subltype E L (ShrLtype lt1 κ1) (ShrLtype (◁ ty2) κ2) T
    ⊢ mut_subltype E L (ShrLtype lt1 κ1) (◁ (shr_ref κ2 ty2)) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; first done. eapply full_eqltype_subltype_l. by eapply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_shr_ofty_1_inst E L {rt} (lt1 : ltype (rt)) (ty2 : type rt) κ1 κ2 :
    MutSubLtype E L (ShrLtype lt1 κ1) (◁ (shr_ref κ2 ty2))%I | 12 := λ T, i2p (mut_subltype_shr_ofty_1 E L lt1 ty2 κ1 κ2 T).

  Lemma mut_subltype_shr_ofty_2 E L {rt} (ty1 : type rt) (lt2 : ltype rt) κ1 κ2 T :
    (mut_subltype E L (ShrLtype (◁ ty1) κ1) (ShrLtype lt2 κ2) T)
    ⊢ mut_subltype E L (◁ (shr_ref κ1 ty1)) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; last done. eapply full_eqltype_subltype_r. by eapply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_shr_ofty_2_inst E L {rt} (ty1 : type rt) (lt2 : ltype rt) κ1 κ2 :
    MutSubLtype E L (◁ (shr_ref κ1 ty1))%I (ShrLtype lt2 κ2) | 10 := λ T, i2p (mut_subltype_shr_ofty_2 E L ty1 lt2 κ1 κ2 T).

  (* same for [mut_eqltype] *)
  Lemma mut_eqltype_shr_ofty_1_evar E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt))  κ1 T :
    (∃ ty2', ⌜ty2 = shr_ref κ1 ty2'⌝ ∗ mut_eqltype E L (ShrLtype lt1 κ1) (◁ (shr_ref κ1 ty2')) T)
    ⊢ mut_eqltype E L (ShrLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance mut_eqltype_shr_ofty_1_evar_inst E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt)) κ1 `{!IsProtected ty2} :
    MutEqLtype E L (ShrLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (mut_eqltype_shr_ofty_1_evar E L lt1 ty2 κ1 T).

  Lemma mut_eqltype_shr_ofty_1 E L {rt} (lt1 : ltype rt) (ty2 : type (rt)) κ1 κ2 T :
    mut_eqltype E L (ShrLtype lt1 κ1) (ShrLtype (◁ ty2) κ2) T
    ⊢ mut_eqltype E L (ShrLtype lt1 κ1) (◁ (shr_ref κ2 ty2)) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; first done. by eapply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_shr_ofty_1_inst E L {rt} (lt1 : ltype (rt)) (ty2 : type rt) κ1 κ2 :
    MutEqLtype E L (ShrLtype lt1 κ1) (◁ (shr_ref κ2 ty2))%I | 12 := λ T, i2p (mut_eqltype_shr_ofty_1 E L lt1 ty2 κ1 κ2 T).

  Lemma mut_eqltype_shr_ofty_2 E L {rt} (ty1 : type rt) (lt2 : ltype rt) κ1 κ2 T :
    (mut_eqltype E L (ShrLtype (◁ ty1) κ1) (ShrLtype lt2 κ2) T)
    ⊢ mut_eqltype E L (◁ (shr_ref κ1 ty1)) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; last done. symmetry. by eapply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_shr_ofty_2_inst E L {rt} (ty1 : type rt) (lt2 : ltype rt) κ1 κ2 :
    MutEqLtype E L (◁ (shr_ref κ1 ty1))%I (ShrLtype lt2 κ2) | 10 := λ T, i2p (mut_eqltype_shr_ofty_2 E L ty1 lt2 κ1 κ2 T).
End subtype.
