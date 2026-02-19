From refinedrust Require Export type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import uninit value alias_ptr programs.
From refinedrust.array Require Import def subltype unfold.
From refinedrust Require Import options.

(** * Judgment for accessing an array component in a general fashion *)

Section access.
  Context `{!typeGS Σ}.

  Lemma typed_array_access_unfold π E L base off st {rt} (ty : type rt) len (rs : place_rfn (list (place_rfn rt))) k T :
    typed_array_access π E L base off st (ArrayLtype ty len []) rs k T
    ⊢ typed_array_access π E L base off st (◁ array_t len ty) rs k T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (array_t_unfold k ty len rs) as "((_ & HIncl & _) & _)".
    iMod (ltype_incl'_use with "HIncl Hl") as "Hl"; first done.
    iApply ("HT" with "[//] [//] [//] CTX HE HL Hl").
  Qed.
  Definition typed_array_access_unfold_inst := [instance @typed_array_access_unfold].
  Global Existing Instance typed_array_access_unfold_inst.

  Lemma typed_array_access_array_owned π E L base (off : Z) st {rt} (ty : type rt) (len : nat) iml rs (T : typed_array_access_cont_t) :
    (⌜(off < len)%Z⌝ ∗ ⌜(0 ≤ off)%Z⌝ ∗ ⌜st = ty_syn_type ty MetaNone⌝ ∗
      ∀ lt r, ⌜interpret_iml (◁ ty)%I len iml !! Z.to_nat off = Some lt⌝ -∗ ⌜rs !! Z.to_nat off = Some r⌝ -∗
      T L _ ty len ((Z.to_nat off, AliasLtype _ st (base offsetst{st}ₗ off)) :: iml) (rs) (Owned) _ lt r)
    ⊢ typed_array_access π E L base off st (ArrayLtype ty len iml) (#rs) (Owned) T.
  Proof.
    iIntros "(%Hoff & %Hoff' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (array_ltype_acc_owned with "Hl") as "(%ly & %Halg & % & % & Hlb & >(Hb & Hcl))"; first done.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen".
    rewrite length_interpret_iml in Hlen.
    specialize (lookup_lt_is_Some_2 rs (Z.to_nat off)) as (r & Hr).
    { lia. }
    specialize (lookup_lt_is_Some_2 (interpret_iml (◁ ty)%I len iml) (Z.to_nat off)) as (lt & Hlt).
    { rewrite length_interpret_iml. lia. }
    iPoseProof (big_sepL2_insert_acc _ _ _ (Z.to_nat off) with "Hb") as "((%Hst' & Hel) & Hcl_b)"; [done.. | ].
    iPoseProof (ltype_own_make_alias _ _ r with "Hel") as "(Hel & Halias)".
    iPoseProof ("Hcl_b" $! (AliasLtype _ (ty_syn_type ty MetaNone) (base offsetst{st}ₗ off)) r with "[Halias]") as "Ha".
    { simp_ltypes. iR. rewrite /OffsetLocSt /offset_loc /use_layout_alg' Hst Halg /=. rewrite Hst'. rewrite !Z2Nat.id; last done. done. }
    iMod ("Hcl" $! _ ty ((Z.to_nat off, AliasLtype rt st (base offsetst{st}ₗ off)) :: iml) rs with "[//] [Ha]") as "Ha".
    { simpl. rewrite (list_insert_id rs (Z.to_nat off) r); last done. rewrite Hst.  done. }
    iPoseProof ("HT" with "[//] [//]") as "HT".
    iModIntro. iExists _, _, _, _, _, _, _, _. iExists _, _. iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Hst Halg Z2Nat.id //.
  Qed.
  Definition typed_array_access_array_owned_inst := [instance @typed_array_access_array_owned].
  Global Existing Instance typed_array_access_array_owned_inst.

  (* NOTE: this will misbehave if we've moved the value out before already! *)
  Lemma typed_array_access_array_shared π E L base off st {rt} (ty : type rt) (len : nat) iml rs κ (T : typed_array_access_cont_t) :
    (⌜(off < len)%Z⌝ ∗ ⌜(0 ≤ off)%Z⌝ ∗ ⌜st = ty_syn_type ty MetaNone⌝ ∗ ∀ lt r, ⌜interpret_iml (◁ ty)%I len iml !! Z.to_nat off = Some lt⌝ -∗ ⌜rs !! Z.to_nat off = Some r⌝ -∗
      T L _ ty len iml (rs) (Shared κ) _ lt r)
    ⊢ typed_array_access π E L base off st (ArrayLtype ty len iml) (#rs) (Shared κ) T.
  Proof.
    iIntros "(%Hoff & %Hoff' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (array_ltype_acc_shared with "Hl") as "(%ly & %Halg & % & % & Hlb & >(#Hb & Hcl))"; first done.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen".
    rewrite length_interpret_iml in Hlen.
    specialize (lookup_lt_is_Some_2 rs (Z.to_nat off)) as (r & Hr).
    { lia. }
    specialize (lookup_lt_is_Some_2 (interpret_iml (◁ ty)%I len iml) (Z.to_nat off)) as (lt & Hlt).
    { rewrite length_interpret_iml. lia. }
    iPoseProof (big_sepL2_lookup _ _ _ (Z.to_nat off) with "Hb") as "(%Hst' & Hel)"; [done.. | ].
    iMod ("Hcl" $! ty iml with "[//] [//] Hb") as "Ha".
    iPoseProof ("HT" with "[//] [//]") as "HT".
    iModIntro. iExists _, _, _, _, _, _, _, _. iExists _, _. iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Hst Halg Z2Nat.id //.
  Qed.
  Definition typed_array_access_array_shared_inst := [instance @typed_array_access_array_shared].
  Global Existing Instance typed_array_access_array_shared_inst.
End access.
