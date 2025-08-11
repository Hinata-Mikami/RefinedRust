From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def subtype subltype unfold.
From refinedrust Require Import options.

(** ** Subtyping automation instances *)

Section subtype.
  Context `{!typeGS Σ}.

  (** Subtyping instances *)
  Lemma weak_subtype_mut E L {rt} (ty1 ty2 : type rt) r1 r2 κ1 κ2 T :
    ⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ weak_subtype E L r1 r2 (mut_ref κ1 ty1) (mut_ref κ2 ty2) T.
  Proof.
    iIntros "(-> & %Hincl & %Heq & HT)".
    iIntros (??) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE").
    iPoseProof (full_eqtype_acc with "HE HL") as "#Heq"; first done.
    iFrame. iApply mut_ref_type_incl; [done | ..].
    - iIntros (r). iDestruct ("Heq" $! r) as "($ & _)".
    - iModIntro. iIntros (r). iDestruct ("Heq" $! r) as "(_ & $)".
  Qed.
  Global Instance weak_subtype_mut_inst E L {rt} (ty1 ty2 : type rt) r1 r2 κ1 κ2 :
    Subtype E L r1 r2 (mut_ref κ1 ty1) (mut_ref κ2 ty2) :=
    λ T, i2p (weak_subtype_mut E L ty1 ty2 r1 r2 κ1 κ2 T).

  Lemma mut_subtype_mut E L {rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_subtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Hsub & HT)". iFrame "HT".
    iPureIntro. apply mut_ref_full_subtype; done.
  Qed.
  Global Instance mut_subtype_mut_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 :
    MutSubtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2) :=
    λ T, i2p (mut_subtype_mut E L ty1 ty2 κ1 κ2 T).

  Lemma mut_eqtype_mut E L {rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & HT)". iFrame "HT".
    iPureIntro. apply full_subtype_eqtype; apply mut_ref_full_subtype; done.
  Qed.
  Global Instance mut_eqtype_mut_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 :
    MutEqtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2) :=
    λ T, i2p (mut_eqtype_mut E L ty1 ty2 κ1 κ2 T).
End subtype.

Section subltype.
  Context `{!typeGS Σ}.

  (** Subltyping instances *)
  (* generic in [r2] to handle the case that it is an evar *)
  Lemma weak_subltype_mut_owned_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 γ r1 r2 T :
    (∃ r2', ⌜r2 = #(r2', γ)⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Uniq κ1 γ) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Owned wl) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (mut_ltype_incl_owned_in with "Hincl'").
    done.
  Qed.
  Global Instance weak_subltype_mut_owned_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 γ r1 r2 :
    SubLtype E L (Owned wl) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_mut_owned_in E L lt1 lt2 wl κ1 κ2 γ r1 r2 T).

  (* instance to destruct the pair if necessary *)
  Lemma weak_subltype_mut_owned_in' E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 r1 r2 T :
    (∀ r1' γ, ⌜r1 = (r1', γ)⌝ -∗ weak_subltype E L (Owned wl) #(r1', γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T)
    ⊢ weak_subltype E L (Owned wl) #r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "Ha". destruct r1. by iApply "Ha".
  Qed.
  Global Instance weak_subltype_mut_owned_in'_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 r1 r2 :
    SubLtype E L (Owned wl) #r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 12 := λ T, i2p (weak_subltype_mut_owned_in' E L lt1 lt2 wl κ1 κ2 r1 r2 T).

  Lemma weak_subltype_mut_shared_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ κ1 κ2 γ r1 r2 T :
    (∃ r2', ⌜r2 = #(r2', γ)⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Shared (κ1 ⊓ κ)) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Shared κ) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (mut_ltype_incl_shared_in with "[Hincl']"); last done.
    done.
  Qed.
  Global Instance weak_subltype_mut_shared_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ κ1 κ2 γ r1 r2 :
    SubLtype E L (Shared κ) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_mut_shared_in E L lt1 lt2 κ κ1 κ2 γ r1 r2 T).

  (* Base instance that will trigger, e.g., for Uniq or PlaceGhost refinements *)
  (* TODO can have more specific instances for PlaceGhost for Shared and Owned *)
  Lemma weak_subltype_mut_base E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T :
    ⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(<- & %Hincl1 & %Hincl2 & %Hsubt & T)" (??) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first done.
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl1"; first apply Hincl1.
    iSpecialize ("Hincl1" with "HE").
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl2"; first apply Hincl2.
    iSpecialize ("Hincl2" with "HE").
    iFrame. iApply mut_ltype_incl; done.
  Qed.
  Global Instance weak_subltype_mut_base_inst E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 :
    SubLtype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 20 := λ T, i2p (weak_subltype_mut_base E L lt1 lt2 k κ1 κ2 r1 r2 T).

  Lemma weak_subltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_mut_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 `{!IsProtected κ2} :
    SubLtype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 9 := λ T, i2p (weak_subltype_mut_evar_lft E L lt1 lt2 k κ1 κ2 r1 r2 T).

  Lemma mut_subltype_mut E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & $)".
    iPureIntro. apply mut_full_subltype; done.
  Qed.
  Global Instance mut_subltype_mut_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    MutSubLtype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 10 := λ T, i2p (mut_subltype_mut E L lt1 lt2 κ1 κ2 T).

  Lemma mut_subltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subltype_mut_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 `{!IsProtected κ2} :
    MutSubLtype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 9 := λ T, i2p (mut_subltype_mut_evar_lft E L lt1 lt2 κ1 κ2 T).

  Lemma mut_eqltype_mut E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & $)".
    iPureIntro. apply mut_full_eqltype; done.
  Qed.
  Global Instance mut_eqltype_mut_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    MutEqLtype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) := λ T, i2p (mut_eqltype_mut E L lt1 lt2 κ1 κ2 T).

  Lemma mut_eqltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqltype_mut_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 `{!IsProtected κ2} :
    MutEqLtype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) := λ T, i2p (mut_eqltype_mut_evar_lft E L lt1 lt2 κ1 κ2 T).

  (* Ofty unfolding if necessary *)
  Lemma weak_subltype_mut_ofty_1_evar E L {rt1 rt2 : RT} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2 * gname)%type) k κ1 r1 r2 T :
    (∃ ty2', ⌜ty2 = mut_ref κ1 ty2'⌝ ∗ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ (mut_ref κ1 ty2')) T)
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance weak_subltype_mut_ofty_1_evar_inst E L {rt1 rt2 : RT} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2 * gname)%type) k κ1 r1 r2 `{!IsProtected ty2} :
    SubLtype E L k r1 r2 (MutLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (weak_subltype_mut_ofty_1_evar E L lt1 ty2 k κ1 r1 r2 T).

  Lemma weak_subltype_mut_ofty_1 E L {rt1 rt2} (lt1 : ltype rt1) (ty2 : type rt2) k κ1 κ2 r1 r2 T :
    weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2)) T.
  Proof.
    iIntros "HT". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply mut_ref_unfold_1.
  Qed.
  Global Instance weak_subltype_mut_ofty_1_inst E L {rt1 rt2} (lt1 : ltype rt1) (ty2 : type rt2) k κ1 κ2 r1 r2 :
    SubLtype E L k r1 r2 (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2))%I | 11 := λ T, i2p (weak_subltype_mut_ofty_1 E L lt1 ty2 k κ1 κ2 r1 r2 T).

  Lemma weak_subltype_mut_ofty_2 E L {rt1 rt2} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 T :
    (weak_subltype E L k r1 r2 (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ weak_subltype E L k r1 r2 (◁ (mut_ref κ1 ty1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "[] Hincl").
    iApply mut_ref_unfold_2.
  Qed.
  Global Instance weak_subltype_mut_ofty_2_inst E L {rt1 rt2} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 :
    SubLtype E L k r1 r2 (◁ (mut_ref κ1 ty1))%I (MutLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_mut_ofty_2 E L ty1 lt2 k r1 r2 κ1 κ2 T).

  (* Same for mut_subltype *)
  Lemma mut_subltype_mut_ofty_1_evar E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)%type) κ1 T :
    (∃ ty2', ⌜ty2 = mut_ref κ1 ty2'⌝ ∗ mut_subltype E L (MutLtype lt1 κ1) (◁ (mut_ref κ1 ty2')) T)
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance mut_subltype_mut_ofty_1_evar_inst E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)%type) κ1 `{!IsProtected ty2} :
    MutSubLtype E L (MutLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (mut_subltype_mut_ofty_1_evar E L lt1 ty2 κ1 T).

  Lemma mut_subltype_mut_ofty_1 E L {rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 T :
    mut_subltype E L (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2)) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; first done.
    eapply full_eqltype_subltype_l. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_mut_ofty_1_inst E L {rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 :
    MutSubLtype E L (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2))%I | 10 := λ T, i2p (mut_subltype_mut_ofty_1 E L lt1 ty2 κ1 κ2 T).

  Lemma mut_subltype_mut_ofty_2 E L {rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 T :
    (mut_subltype E L (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ mut_subltype E L (◁ (mut_ref κ1 ty1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; last done.
    eapply full_eqltype_subltype_r. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_mut_ofty_2_inst E L {rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 :
    MutSubLtype E L (◁ (mut_ref κ1 ty1))%I (MutLtype lt2 κ2) | 10 := λ T, i2p (mut_subltype_mut_ofty_2 E L ty1 lt2 κ1 κ2 T).

  (* Same for mut_eqltype *)
  Lemma mut_eqltype_mut_ofty_1_evar E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)%type) κ1 T :
    (∃ ty2', ⌜ty2 = mut_ref κ1 ty2'⌝ ∗ mut_eqltype E L (MutLtype lt1 κ1) (◁ (mut_ref κ1 ty2')) T)
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance mut_eqltype_mut_ofty_1_evar_inst E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)%type) κ1 `{!IsProtected ty2} :
    MutEqLtype E L (MutLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (mut_eqltype_mut_ofty_1_evar E L lt1 ty2 κ1 T).

  Lemma mut_eqltype_mut_ofty_1 E L {rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 T :
    mut_eqltype E L (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2)) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; first done. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_mut_ofty_1_inst E L {rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 :
    MutEqLtype E L (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2))%I | 10 := λ T, i2p (mut_eqltype_mut_ofty_1 E L lt1 ty2 κ1 κ2 T).

  Lemma mut_eqltype_mut_ofty_2 E L {rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 T :
    (mut_eqltype E L (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ mut_eqltype E L (◁ (mut_ref κ1 ty1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; last done. symmetry. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_mut_ofty_2_inst E L {rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 :
    MutEqLtype E L (◁ (mut_ref κ1 ty1))%I (MutLtype lt2 κ2) | 10 := λ T, i2p (mut_eqltype_mut_ofty_2 E L ty1 lt2 κ1 κ2 T).

End subltype.
