From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def subtype subltype unfold.
From refinedrust Require Import options.

(** ** Subtyping automation instances *)

Section subtype.
  Context `{!typeGS Σ}.

  (** Subtyping instances *)

  Lemma weak_subtype_mut_lft_evar E L {rt} (ty1 ty2 : type rt) r1 r2 κ1 κ2 `{!IsProtected κ2} T :
    weak_subtype E L r1 r2 (mut_ref κ1 ty1) (mut_ref κ2 ty2) T :-
      exhale (⌜κ1 = κ2⌝);
      return weak_subtype E L r1 r2 (mut_ref κ1 ty1) (mut_ref κ2 ty2) T.
  Proof.
    iIntros "(<- & HT)". done.
  Qed.
  Definition weak_subtype_mut_lft_evar_inst := [instance @weak_subtype_mut_lft_evar].
  Global Existing Instance weak_subtype_mut_lft_evar_inst | 10.

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
  Definition weak_subtype_mut_inst := [instance @weak_subtype_mut].
  Global Existing Instance weak_subtype_mut_inst | 15.

  Lemma mut_subtype_mut_lft_evar E L {rt} (ty1 ty2 : type rt) κ1 κ2 `{!IsProtected κ2} T :
    mut_subtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2) T :-
      exhale (⌜κ1 = κ2⌝);
      return (mut_subtype E L (mut_ref κ1 ty1) (mut_ref κ1 ty2) T).
  Proof.
    iIntros "(-> & HT)". done.
  Qed.
  Definition mut_subtype_mut_lft_evar_inst := [instance @mut_subtype_mut_lft_evar].
  Global Existing Instance mut_subtype_mut_lft_evar_inst | 10.

  Lemma mut_subtype_mut E L {rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_subtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Hsub & HT)". iFrame "HT".
    iPureIntro. apply mut_ref_full_subtype; done.
  Qed.
  Definition mut_subtype_mut_inst := [instance @mut_subtype_mut].
  Global Existing Instance mut_subtype_mut_inst | 15.

  Lemma mut_eqtype_mut_lft_evar E L {rt} (ty1 ty2 : type rt) κ1 κ2 `{!IsProtected κ2} T :
    mut_eqtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2) T :-
      exhale (⌜κ1 = κ2⌝);
      return (mut_eqtype E L (mut_ref κ1 ty1) (mut_ref κ1 ty2) T).
  Proof.
    iIntros "(-> & HT)". done.
  Qed.
  Definition mut_eqtype_mut_lft_evar_inst := [instance @mut_eqtype_mut_lft_evar].
  Global Existing Instance mut_eqtype_mut_lft_evar_inst | 10.

  Lemma mut_eqtype_mut E L {rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & HT)". iFrame "HT".
    iPureIntro. apply full_subtype_eqtype; apply mut_ref_full_subtype; done.
  Qed.
  Definition mut_eqtype_mut_inst := [instance @mut_eqtype_mut].
  Global Existing Instance mut_eqtype_mut_inst | 15.
End subtype.

Section subltype.
  Context `{!typeGS Σ}.

  (** Subltyping instances *)
  (* generic in [r2] to handle the case that it is an evar *)
  Lemma weak_subltype_mut_owned_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 γ r1 r2 T :
    (∃ r2', ⌜r2 = #(r2', γ)⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Uniq κ1 γ) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Owned) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (mut_ltype_incl_owned_in with "Hincl'").
    done.
  Qed.
  Definition weak_subltype_mut_owned_in_inst := [instance @weak_subltype_mut_owned_in].
  Global Existing Instance weak_subltype_mut_owned_in_inst | 10.

  (* instance to destruct the pair if necessary *)
  Lemma weak_subltype_mut_owned_in' E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 r1 r2 T :
    (∀ r1' γ, ⌜r1 = (r1', γ)⌝ -∗ weak_subltype E L (Owned) #(r1', γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T)
    ⊢ weak_subltype E L (Owned) #r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "Ha". destruct r1. by iApply "Ha".
  Qed.
  Definition weak_subltype_mut_owned_in'_inst := [instance @weak_subltype_mut_owned_in'].
  Global Existing Instance weak_subltype_mut_owned_in'_inst | 12.

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
  Definition weak_subltype_mut_shared_in_inst := [instance @weak_subltype_mut_shared_in].
  Global Existing Instance weak_subltype_mut_shared_in_inst | 10.

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
  Definition weak_subltype_mut_base_inst := [instance @weak_subltype_mut_base].
  Global Existing Instance weak_subltype_mut_base_inst | 20.

  Lemma weak_subltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Definition weak_subltype_mut_evar_lft_inst := [instance @weak_subltype_mut_evar_lft].
  Global Existing Instance weak_subltype_mut_evar_lft_inst | 9.

  Lemma mut_subltype_mut E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & $)".
    iPureIntro. apply mut_full_subltype; done.
  Qed.
  Definition mut_subltype_mut_inst := [instance @mut_subltype_mut].
  Global Existing Instance mut_subltype_mut_inst | 10.

  Lemma mut_subltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Definition mut_subltype_mut_evar_lft_inst := [instance @mut_subltype_mut_evar_lft].
  Global Existing Instance mut_subltype_mut_evar_lft_inst | 9.

  Lemma mut_eqltype_mut E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & $)".
    iPureIntro. apply mut_full_eqltype; done.
  Qed.
  Definition mut_eqltype_mut_inst := [instance @mut_eqltype_mut].
  Global Existing Instance mut_eqltype_mut_inst.

  Lemma mut_eqltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Definition mut_eqltype_mut_evar_lft_inst := [instance @mut_eqltype_mut_evar_lft].
  Global Existing Instance mut_eqltype_mut_evar_lft_inst.

  (* Ofty unfolding if necessary *)
  Lemma weak_subltype_mut_ofty_1_evar E L {rt1 rt2 : RT} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2 * gname)%type) k κ1 r1 r2 `{!IsProtected ty2} T :
    (∃ ty2', ⌜ty2 = mut_ref κ1 ty2'⌝ ∗ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ (mut_ref κ1 ty2')) T)
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Definition weak_subltype_mut_ofty_1_evar_inst := [instance @weak_subltype_mut_ofty_1_evar].
  Global Existing Instance weak_subltype_mut_ofty_1_evar_inst | 10.

  Lemma weak_subltype_mut_ofty_1 E L {rt1 rt2} (lt1 : ltype rt1) (ty2 : type rt2) k κ1 κ2 r1 r2 T :
    weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2)) T.
  Proof.
    iIntros "HT". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply mut_ref_unfold_1.
  Qed.
  Definition weak_subltype_mut_ofty_1_inst := [instance @weak_subltype_mut_ofty_1].
  Global Existing Instance weak_subltype_mut_ofty_1_inst.

  Lemma weak_subltype_mut_ofty_2 E L {rt1 rt2} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 T :
    (weak_subltype E L k r1 r2 (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ weak_subltype E L k r1 r2 (◁ (mut_ref κ1 ty1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "[] Hincl").
    iApply mut_ref_unfold_2.
  Qed.
  Definition weak_subltype_mut_ofty_2_inst := [instance @weak_subltype_mut_ofty_2].
  Global Existing Instance weak_subltype_mut_ofty_2_inst.

  (* Same for mut_subltype *)
  Lemma mut_subltype_mut_ofty_1_evar E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)%type) κ1  `{!IsProtected ty2} T :
    (∃ ty2', ⌜ty2 = mut_ref κ1 ty2'⌝ ∗ mut_subltype E L (MutLtype lt1 κ1) (◁ (mut_ref κ1 ty2')) T)
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Definition mut_subltype_mut_ofty_1_evar_inst := [instance @mut_subltype_mut_ofty_1_evar].
  Global Existing Instance mut_subltype_mut_ofty_1_evar_inst | 10.

  Lemma mut_subltype_mut_ofty_1 E L {rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 T :
    mut_subltype E L (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2)) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; first done.
    eapply full_eqltype_subltype_l. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Definition mut_subltype_mut_ofty_1_inst := [instance @mut_subltype_mut_ofty_1].
  Global Existing Instance mut_subltype_mut_ofty_1_inst | 10.

  Lemma mut_subltype_mut_ofty_2 E L {rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 T :
    (mut_subltype E L (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ mut_subltype E L (◁ (mut_ref κ1 ty1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; last done.
    eapply full_eqltype_subltype_r. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Definition mut_subltype_mut_ofty_2_inst := [instance @mut_subltype_mut_ofty_2].
  Global Existing Instance mut_subltype_mut_ofty_2_inst | 10.

  (* Same for mut_eqltype *)
  Lemma mut_eqltype_mut_ofty_1_evar E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)%type) κ1 `{!IsProtected ty2} T :
    (∃ ty2', ⌜ty2 = mut_ref κ1 ty2'⌝ ∗ mut_eqltype E L (MutLtype lt1 κ1) (◁ (mut_ref κ1 ty2')) T)
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Definition mut_eqltype_mut_ofty_1_evar_inst := [instance @mut_eqltype_mut_ofty_1_evar].
  Global Existing Instance mut_eqltype_mut_ofty_1_evar_inst | 10.

  Lemma mut_eqltype_mut_ofty_1 E L {rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 T :
    mut_eqltype E L (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (◁ (mut_ref κ2 ty2)) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; first done. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Definition mut_eqltype_mut_ofty_1_inst := [instance @mut_eqltype_mut_ofty_1].
  Global Existing Instance mut_eqltype_mut_ofty_1_inst | 10.

  Lemma mut_eqltype_mut_ofty_2 E L {rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 T :
    (mut_eqltype E L (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ mut_eqltype E L (◁ (mut_ref κ1 ty1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; last done. symmetry. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Definition mut_eqltype_mut_ofty_2_inst := [instance @mut_eqltype_mut_ofty_2].
  Global Existing Instance mut_eqltype_mut_ofty_2_inst | 10.
End subltype.
