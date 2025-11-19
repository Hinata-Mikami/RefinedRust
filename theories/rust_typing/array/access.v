From refinedrust Require Export type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import uninit value alias_ptr programs.
From refinedrust.array Require Import def subltype unfold.
From refinedrust Require Import options.

(** * Judgment for accessing an array component in a general fashion *)

Section access.
  Context `{!typeGS Σ}.
  (* TODO maybe we also generally want this to unblock/stratify first? *)
  Definition typed_array_access_cont_t : Type := llctx → ∀ (rt' : RT), type rt' → nat → list (nat * ltype rt') → list (place_rfn rt') → bor_kind → ∀ rte, ltype rte → place_rfn rte → iProp Σ.
  Definition typed_array_access (π : thread_id) (E : elctx) (L : llctx) (base : loc) (off : Z) (st : syn_type) {rt} (lt : ltype rt) (r : place_rfn rt) (k : bor_kind) (T : typed_array_access_cont_t) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    base ◁ₗ[π, k] r @ lt ={F}=∗
    ∃ L' k' rt' (ty' : type rt') (len : nat) (iml : list (nat * ltype rt')) rs' (rte : RT) re (lte : ltype rte),
      (* updated array assignment *)
      base ◁ₗ[π, k'] #rs' @ ArrayLtype ty' len iml ∗
      (base offsetst{st}ₗ off) ◁ₗ[π, k'] re @ lte ∗
      llctx_interp L' ∗
      T L' _ ty' len iml rs' k' rte lte re.
  Class TypedArrayAccess (π : thread_id) (E : elctx) (L : llctx) (base : loc) (off : Z) (st : syn_type) {rt} (lt : ltype rt) (r : place_rfn rt) (k : bor_kind) : Type :=
    typed_array_access_proof T : iProp_to_Prop (typed_array_access π E L base off st lt r k T).


  Lemma typed_array_access_unfold π E L base off st {rt} (ty : type rt) len (rs : place_rfn (list (place_rfn rt))) k T :
    typed_array_access π E L base off st (ArrayLtype ty len []) rs k T
    ⊢ typed_array_access π E L base off st (◁ array_t len ty) rs k T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (array_t_unfold k ty len rs) as "((_ & HIncl & _) & _)".
    iMod (ltype_incl'_use with "HIncl Hl") as "Hl"; first done.
    iApply ("HT" with "[//] [//] [//] CTX HE HL Hl").
  Qed.
  Global Instance typed_array_access_unfold_inst π E L base off st {rt} (ty : type rt) len rs k :
    TypedArrayAccess π E L base off st (◁ array_t len ty)%I rs k :=
    λ T, i2p (typed_array_access_unfold π E L base off st ty len rs k T).

  Lemma typed_array_access_array_owned π E L base (off : Z) st {rt} (ty : type rt) (len : nat) iml rs (wl : bool) (T : typed_array_access_cont_t) :
    (⌜(off < len)%Z⌝ ∗ ⌜(0 ≤ off)%Z⌝ ∗ ⌜st = ty_syn_type ty⌝ ∗
      prove_with_subtype E L false ProveDirect (if wl then £ 1 else True) (λ L2 κs Q, Q -∗
      ∀ lt r, ⌜interpret_iml (◁ ty)%I len iml !! Z.to_nat off = Some lt⌝ -∗ ⌜rs !! Z.to_nat off = Some r⌝ -∗
      introduce_with_hooks E L2 (maybe_creds wl) (λ L3,
      T L3 _ ty len ((Z.to_nat off, AliasLtype _ st (base offsetst{st}ₗ off)) :: iml) (rs) (Owned false) _ lt r)))
    ⊢ typed_array_access π E L base off st (ArrayLtype ty len iml) (#rs) (Owned wl) T.
  Proof.
    iIntros "(%Hoff & %Hoff' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & %κs & %Q & >(HP & HQ) & HL & HT)".
    iPoseProof ("HT" with "HQ") as "HT".
    iAssert (|={F}=> base ◁ₗ[ π, Owned false] # rs @ ArrayLtype ty len iml ∗ maybe_creds wl)%I with "[Hl HP]" as "Ha".
    { destruct wl; last eauto with iFrame.
      iPoseProof (ltype_own_Owned_true_false with "Hl") as "($ & Hl)"; first done.
      iApply (lc_fupd_add_later with "HP").
      iNext. eauto with iFrame. }
    iMod "Ha" as "(Hl & Hcred)".

    iPoseProof (array_ltype_acc_owned_cred with "Hl") as "(%ly & %Halg & % & % & Hlb & >(Hb & Hcl))"; first done.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen".
    rewrite length_interpret_iml in Hlen.
    specialize (lookup_lt_is_Some_2 rs (Z.to_nat off)) as (r & Hr).
    { lia. }
    specialize (lookup_lt_is_Some_2 (interpret_iml (◁ ty)%I len iml) (Z.to_nat off)) as (lt & Hlt).
    { rewrite length_interpret_iml. lia. }
    iPoseProof (big_sepL2_insert_acc _ _ _ (Z.to_nat off) with "Hb") as "((%Hst' & Hel) & Hcl_b)"; [done.. | ].
    iPoseProof (ltype_own_make_alias false _ _ r with "Hel [//]") as "(Hel & Halias)".
    iPoseProof ("Hcl_b" $! (AliasLtype _ (ty_syn_type ty) (base offsetst{st}ₗ off)) r with "[Halias]") as "Ha".
    { simp_ltypes. iR. rewrite /OffsetLocSt /offset_loc /use_layout_alg' Hst Halg /=. rewrite Hst'. rewrite !Z2Nat.id; last done. done. }
    iMod ("Hcl" $! _ ty ((Z.to_nat off, AliasLtype rt st (base offsetst{st}ₗ off)) :: iml) rs with "[//] [//] [Ha]") as "Ha".
    { simpl. rewrite (list_insert_id rs (Z.to_nat off) r); last done. rewrite Hst.  done. }
    iMod ("HT" with "[//] [//] [//] HE HL Hcred") as "(%L3 & HL & HT)".
    iModIntro. iExists _, _, _, _, _, _, _, _. iExists _, _. iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Hst Halg Z2Nat.id //.
  Qed.
  Global Instance typed_array_access_owned_inst π E L base (off : Z) st {rt} (ty : type rt) len iml rs wl :
    TypedArrayAccess π E L base off st (ArrayLtype ty len iml) (#rs) (Owned wl) :=
    λ T, i2p (typed_array_access_array_owned π E L base off st ty len iml rs wl T).

  (* NOTE: this will misbehave if we've moved the value out before already! *)
  Lemma typed_array_access_array_shared π E L base off st {rt} (ty : type rt) (len : nat) iml rs κ (T : typed_array_access_cont_t) :
    (⌜(off < len)%Z⌝ ∗ ⌜(0 ≤ off)%Z⌝ ∗ ⌜st = ty_syn_type ty⌝ ∗ ∀ lt r, ⌜interpret_iml (◁ ty)%I len iml !! Z.to_nat off = Some lt⌝ -∗ ⌜rs !! Z.to_nat off = Some r⌝ -∗
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
  Global Instance typed_array_access_shared_inst π E L base off st {rt} (ty : type rt) len iml rs κ :
    TypedArrayAccess π E L base off st (ArrayLtype ty len iml) (#rs) (Shared κ) :=
    λ T, i2p (typed_array_access_array_shared π E L base off st ty len iml rs κ T).
End access.


Global Hint Mode TypedArrayAccess + + + + + + + + + + + + : typeclass_instances.
Global Typeclasses Opaque typed_array_access.
