From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import programs.
From refinedrust.array Require Import def subtype subltype unfold.
From refinedrust Require Import options.

(** ** Subtyping instances for arrays *)

Section subtype.
  Context `{!typeGS Σ}.
  (** ** subtype instances *)

  (* TODO: should this really match on the addition in the conclusion? probably not. *)
  (*
  Lemma subsume_full_array_split_goal :
    subsume_full E L pers (l ◁ₗ[π, Owned false] r @ lt) (l ◁ₗ[π, Owned false] #(a1) @ ◁ array_t def (length a1)) (λ L R2,
      prove_with_subtype E L pers (l +ₗ ... ◁ₗ[π, Owned false] #a2 @ ◁ array_t def (len - length a1)) T)
    subsume_full E L pers (l ◁ₗ[π, Owned false] r @ lt) (l ◁ₗ[π, Owned false] #(a1 ++ a2) @ ◁ array_t def (len)) T.
  *)
  (* Alternative: do this splitting on prove_with_subtype for array values instead.
   *)
  (* Higher priority instance than direct search for the value: as a heuristic, we split app values *)
  (* TODO: how would that scale to more complex transformations? E.g. what about take etc. -- I guess for that we could have instances as well.
    Basically, I would imagine that we only want to look in the context for primitive values. *)
  Lemma prove_with_subtype_array_val_split π E L pm v1 v2 {rt} (ty : type rt) r1 r2 (len : nat) T :
    ⌜(size_of_st (ty_syn_type ty) * len ≤ MaxInt ISize)%Z⌝ ∗
    ⌜length r1 ≤ len⌝ ∗
    prove_with_subtype E L false pm (v1 ◁ᵥ{π} r1 @ array_t (length r1) ty) (λ L2 κs1 R2,
      prove_with_subtype E L2 false pm (v2 ◁ᵥ{π} r2 @ array_t (len - length r1) ty) (λ L3 κs2 R3, T L3 (κs1 ++ κs2) (R2 ∗ R3)%I))
    ⊢ prove_with_subtype E L false pm ((v1 ++ v2) ◁ᵥ{π} r1 ++ r2 @ array_t len ty) T.
  Proof.
    iIntros "(% & % & HT)" (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & %κs1 & %R2 & >(Hv1 & HR2) & HL & HT)".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L3 & %κs2 & %R3 & >(Hv2 & HR3) & HL & HT)".
    iModIntro. iExists L3, _, _. iFrame.
    destruct pm.
    - iEval (replace len with ((length r1) + (len - length r1)) by lia).
      iApply (array_t_own_val_merge with "Hv1 Hv2").
      nia.
    - iModIntro. rewrite lft_dead_list_app. iIntros "(Hdead1 & Hdead2)".
      iMod ("Hv1" with "Hdead1") as "Hv1". iMod ("Hv2" with "Hdead2") as "Hv2".
      iEval (replace len with ((length r1) + (len - length r1)) by lia).
      iApply (array_t_own_val_merge with "Hv1 Hv2").
      nia.
  Qed.
  Global Instance prove_with_subtype_array_val_split_inst π E L pm v1 v2 {rt} (ty : type rt) r1 r2 (len : nat) :
    ProveWithSubtype E L false pm ((v1 ++ v2) ◁ᵥ{π} r1 ++ r2 @ array_t len ty) | 20 :=
    λ T, i2p (prove_with_subtype_array_val_split π E L pm v1 v2 ty r1 r2 len T).


  (* TODO: we could strengthen this by taking into account the refinements *)
  Lemma weak_subtype_array E L {rt} (ty1 ty2 : type rt) len1 len2 rs1 rs2 T :
    ⌜len1 = len2⌝ ∗ ⌜rs1 = rs2⌝ ∗ mut_subtype E L ty1 ty2 T
    ⊢ weak_subtype E L rs1 rs2 (array_t len1 ty1) (array_t len2 ty2) T.
  Proof.
    iIntros "(<- & <- & %Hsubt & HT)".
    iIntros (??) "#CTX #HE HL". iPoseProof (full_subtype_acc with "HE HL") as "#Hincl"; first done.
    iPoseProof ("Hincl" $! inhabitant) as "(%Hst & _)".
    iFrame. iApply array_t_type_incl; done.
  Qed.
  Global Instance weak_subtype_array_inst E L {rt} (ty1 ty2 : type rt) len1 len2 rs1 rs2 :
    Subtype E L rs1 rs2 (array_t len1 ty1) (array_t len2 ty2) :=
    λ T, i2p (weak_subtype_array E L ty1 ty2 len1 len2 rs1 rs2 T).

  Lemma mut_subtype_array E L {rt} (ty1 ty2 : type rt) len1 len2 T :
    ⌜len1 = len2⌝ ∗ mut_subtype E L ty1 ty2 T
    ⊢ mut_subtype E L (array_t len1 ty1) (array_t len2 ty2) T.
  Proof.
    iIntros "(<- & %Hsubt & HT)".
    iSplitR; last done. iPureIntro. by eapply array_t_full_subtype.
  Qed.
  Global Instance mut_subtype_array_inst E L {rt} (ty1 ty2 : type rt) len1 len2 :
    MutSubtype E L (array_t len1 ty1) (array_t len2 ty2) :=
    λ T, i2p (mut_subtype_array E L ty1 ty2 len1 len2 T).

  Lemma mut_eqtype_array E L {rt} (ty1 ty2 : type rt) len1 len2 T :
    ⌜len1 = len2⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqtype E L (array_t len1 ty1) (array_t len2 ty2) T.
  Proof.
    iIntros "(<- & %Hsubt & HT)".
    iSplitR; last done. iPureIntro.
    eapply full_subtype_eqtype.
    - eapply array_t_full_subtype. by apply full_eqtype_subtype_l.
    - eapply array_t_full_subtype. by apply full_eqtype_subtype_r.
  Qed.
  Global Instance mut_eqtype_array_inst E L {rt} (ty1 ty2 : type rt) len1 len2 :
    MutEqtype E L (array_t len1 ty1) (array_t len2 ty2) :=
    λ T, i2p (mut_eqtype_array E L ty1 ty2 len1 len2 T).

  Lemma owned_subtype_array π E L pers {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) len r1 r2 T :
    (∃ r1' r2', ⌜r1 = replicate len #r1'⌝ ∗ ⌜r2 = replicate len #r2'⌝ ∗
      li_tactic (compute_layout_goal (ty_syn_type ty2)) (λ _,
      owned_subtype π E L true r1' r2' ty1 ty2 T))
    ⊢ owned_subtype π E L pers r1 r2 (array_t len ty1) (array_t len ty2) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%r1' & %r2' & -> & -> & %ly' & %Hly' & HT)".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L' & #Hincl & ? & ?)".
    iModIntro. iExists L'. iFrame.
    iApply bi.intuitionistically_intuitionistically_if. iModIntro.
    iDestruct "Hincl" as "(%Hszeq & Hsceq & Hv)".
    iSplitR; last iSplitR.
    - iPureIntro. simpl. intros ly1 ly2 Hst1 Hst2.
      apply syn_type_has_layout_array_inv in Hst1 as (ly1' & Hst1 & -> & ?).
      apply syn_type_has_layout_array_inv in Hst2 as (ly2' & Hst2 & -> & ?).
      rewrite /mk_array_layout/ly_mult/=.
      specialize (Hszeq _ _ Hst1 Hst2) as ->. done.
    - simpl. done.
    - iIntros (v) "Ha".
      rewrite {3 4}/ty_own_val /=.
      iDestruct "Ha" as "(%ly & %Hst1 & % & <- & %Hvly & Ha)".
      iExists _. iR.
      assert (ly_size ly = ly_size ly') as Hlysz. { eapply Hszeq; done. }
      rewrite -Hlysz length_replicate. iR.
      rewrite length_replicate. iR.
      iSplitR. { iPureIntro. rewrite /has_layout_val/mk_array_layout/ly_mult/=. rewrite -Hlysz.
        rewrite length_replicate in Hvly. done. }
      clear.
      iInduction len as [ | len] "IH" forall (v); simpl; first done.
      iDestruct "Ha" as "((%r1 & -> & Ha) & Hr)".
      iPoseProof ("IH" with "Hr") as "$".
      iExists _. iR. by iApply "Hv".
  Qed.
  Global Instance owned_subtype_array_inst π E L pers {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) len r1 r2 :
    OwnedSubtype π E L pers r1 r2 (array_t len ty1) (array_t len ty2) :=
    λ T, i2p (owned_subtype_array π E L pers ty1 ty2 len r1 r2 T).

  (** Owned subtype for initialization *)
  Lemma owned_subtype_uninit_array π E L pers {rt} (ty : type rt) (st : syn_type) len r2 T :
    li_tactic (compute_layout_goal st) (λ ly1,
      li_tactic (compute_layout_goal (ty_syn_type ty)) (λ ly2,
        ⌜(ly_size ly1 = ly_size ly2 * len)%nat⌝ ∗
        owned_subtype π E L pers (replicate len #()) r2 (array_t len (uninit (ty_syn_type ty))) (array_t len ty) T))
    ⊢ owned_subtype π E L pers () r2 (uninit st) (array_t len ty) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1 & %Halg1 & %ly2 & %Halg2 & %Hszeq & HT)".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L' & Hincl & ? & ?)".
    iExists L'. iModIntro. iFrame.
    iAssert (owned_type_incl π (replicate len # ()) r2 (array_t len (uninit (ty_syn_type ty))) (array_t len ty) -∗ owned_type_incl π () r2 (uninit st) (array_t len ty))%I as "Hw"; first last.
    { destruct pers.
      { simpl. iDestruct "Hincl" as "#Hincl". iModIntro. by iApply "Hw". }
      { simpl. by iApply "Hw". } }
    iIntros "Hincl". iDestruct "Hincl" as "(%Hszeq' & _ & Hv)".
    iSplitR; last iSplitR.
    - iPureIntro. intros ly3 ly4 Hst1 Hst2.
      simpl in *.
      assert (ly3 = ly1) as -> by by eapply syn_type_has_layout_inj.
      rewrite Hszeq.
      specialize (syn_type_has_layout_array_inv _ _ _ Hst2) as (ly2' & Hst2' & -> & ?).
      assert (ly2' = ly2) as -> by by eapply syn_type_has_layout_inj.
      done.
    - simpl; done.
    - iIntros (v) "Hun".
      iApply "Hv". iApply array_val_from_uninit; last done.
      + done.
      + done.
      + lia.
  Qed.
  Global Instance owned_subtype_uninit_array_inst π E L pers {rt} (ty : type rt) st len r2 :
    OwnedSubtype π E L pers () r2 (uninit st) (array_t len ty) :=
    λ T, i2p (owned_subtype_uninit_array π E L pers ty st len r2 T).
End subtype.

Section instances.
  Context `{!typeGS Σ}.

  (** ** subltype *)

  (* we use the [relate_list] mechanism *)
  Program Definition weak_subltype_list_interp {rt1 rt2 : RT} (k : bor_kind) (rs1 : list (place_rfn rt1)) (rs2 : list (place_rfn rt2)) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2)) (T : iProp Σ) :=
        (∃ r1 r2,  ⌜rs1 !! i = Some r1⌝ ∗ ⌜rs2 !! i = Some r2⌝ ∗ weak_subltype E L k r1 r2 lt1 lt2 T)%I;
      fr_cap := length rs1;
      fr_inv := length rs1 = length rs2;
      fr_elim_mode := true;
      fr_core_rel E L (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2))  :=
        (∃ r1 r2,  ⌜rs1 !! i = Some r1⌝ ∗ ⌜rs2 !! i = Some r2⌝ ∗ ltype_incl k r1 r2 lt1 lt2)%I;
    |}.
  Next Obligation.
    iIntros (??? rs1 rs2 E L i a b T ? ?) "#CTX #HE HL (%r1 & %r2 & %Hlook1 & %Hlook2 & Hsubt)".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iModIntro. eauto with iFrame.
  Qed.

   (* options;
       - require homogeneous and then use mut_subltype in the assumption
       - what about array_t T <: array_t (maybe_uninit T)?
          for that, would need a pattern on replicate there too.
          this seems fine, but is difficult to implement. The problem is that we can't pattern on that easily. We'd first need to remove any leading inserts.
       TODO: Probably have both, with the first one as fallback.
     *)
  Lemma weak_subltype_list_replicate_1 (E : elctx) (L : llctx) {rt} (k : bor_kind) (lt1 : ltype rt) (lt2 : ltype rt) rs1 rs2 n ig i0 T :
    ⌜list_subequiv ig rs1 rs2⌝ ∗ mut_subltype E L lt1 lt2 T
    ⊢ relate_list E L ig (replicate n lt1) (replicate n lt2) i0 (weak_subltype_list_interp k rs1 rs2) T.
  Proof.
    iIntros "(%Heq & %Hsubt & HT)".
    iApply relate_list_replicate_elim_full; first done; last done.
    simpl. iIntros "#CTX HE HL %Hlen".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl"; first done.
    iModIntro. iIntros (i) "%Hlt %Hnel".
    specialize (Heq i) as (? & Hi).
    destruct (lookup_lt_is_Some_2 rs1 i) as (r1 & Hlook1). { lia. }
    destruct (lookup_lt_is_Some_2 rs2 i) as (r2 & Hlook2). { lia. }
    iExists r1, r2. iR. iR. assert (r1 = r2) as <-.
    { specialize (Hi Hnel). congruence. }
    iApply "Hincl".
  Qed.
  Global Instance weak_subltype_list_replicate_1_inst (E : elctx) (L : llctx) {rt} (k : bor_kind) (lt1 : ltype rt) (lt2 : ltype rt) rs1 rs2 n ig i0 :
    RelateList E L ig (replicate n lt1) (replicate n lt2) i0 (weak_subltype_list_interp k rs1 rs2) :=
    λ T, i2p (weak_subltype_list_replicate_1 E L k lt1 lt2 rs1 rs2 n ig i0 T).

  Program Definition mut_subltype_list_interp {rt} (cap : nat) (interp : bool) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt)) (lt2 : (ltype rt)) (T : iProp Σ) := (mut_subltype E L lt1 lt2 T)%I;
      fr_cap := cap;
      fr_inv := True;
      fr_elim_mode := interp;
      fr_core_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt)) (lt2 : (ltype rt)) :=
        if interp then (∀ k r,  ltype_incl k r r lt1 lt2)%I else ⌜full_subltype E L lt1 lt2⌝%I;
    |}.
  Next Obligation.
    iIntros (rt _ interp E L i a b). destruct interp.
    - iIntros (???) "#CTX #HE HL (%Hsubt & $)".
      iPoseProof (full_subltype_acc with "CTX HE HL") as "#$"; first done.
      by iFrame.
    - iIntros (?) "(% & $)"; done.
  Qed.

  Lemma mut_subltype_list_replicate (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) cap interp n ig i0 T :
    mut_subltype E L lt1 lt2 T
    ⊢ relate_list E L ig (replicate n lt1) (replicate n lt2) i0 (mut_subltype_list_interp cap interp) T.
  Proof.
    iIntros "(%Hsubt & HT)". destruct interp.
    - iApply relate_list_replicate_elim_full; first done; last done.
      simpl. iIntros "#CTX HE HL _".
      iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl"; first done.
      iModIntro. iIntros (i) "%Hlt %Hnel". done.
    - iApply relate_list_replicate_elim_weak; first done; last done.
      simpl. iIntros "_". eauto.
  Qed.
  Global Instance mut_subltype_list_replicate_inst (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) cap interp n ig i0 :
    RelateList E L ig (replicate n lt1) (replicate n lt2) i0 (mut_subltype_list_interp cap interp) :=
    λ T, i2p (mut_subltype_list_replicate E L lt1 lt2 cap interp n ig i0 T).

  Program Definition mut_eqltype_list_interp {rt} (cap : nat) (interp : bool) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt)) (lt2 : (ltype rt)) (T : iProp Σ) := (mut_eqltype E L lt1 lt2 T)%I;
      fr_cap := cap;
      fr_inv := True;
      fr_elim_mode := interp;
      fr_core_rel E L (i : nat) (lt1 : (ltype rt)) (lt2 : (ltype rt))  :=
        if interp then (∀ k r,  ltype_incl k r r lt1 lt2 ∗ ltype_incl k r r lt2 lt1)%I else ⌜full_eqltype E L lt1 lt2⌝%I;
    |}.
  Next Obligation.
    iIntros (rt _ interp E L i a b). destruct interp.
    - iIntros (T ? ?) "#CTX #HE HL (%Hsubt & $)".
      iPoseProof (full_eqltype_acc with "CTX HE HL") as "#$"; first done.
      by iFrame.
    - iIntros (T) "(%Heqt & $)". eauto.
  Qed.

  Lemma mut_eqltype_list_replicate (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) cap interp n ig i0 T :
    mut_eqltype E L lt1 lt2 T
    ⊢ relate_list E L ig (replicate n lt1) (replicate n lt2) i0 (mut_eqltype_list_interp cap interp) T.
  Proof.
    iIntros "(%Hsubt & HT)". destruct interp.
    - iApply relate_list_replicate_elim_full; first done; last done.
      simpl. iIntros "#CTX HE HL _".
      iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first done.
      iModIntro. iIntros (i) "%Hlt %Hnel". done.
    - iApply relate_list_replicate_elim_weak; first done; last done.
      simpl. iIntros "_". eauto.
  Qed.
  Global Instance mut_eqltype_list_replicate_inst (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) cap interp n ig i0 :
    RelateList E L ig (replicate n lt1) (replicate n lt2) i0 (mut_eqltype_list_interp cap interp) :=
    λ T, i2p (mut_eqltype_list_replicate E L lt1 lt2 cap interp n ig i0 T).

  Local Typeclasses Transparent weak_subltype_list_interp.
  Local Typeclasses Transparent mut_subltype_list_interp.
  Local Typeclasses Transparent mut_eqltype_list_interp.

  Lemma weak_subltype_array_evar_def E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 k T :
    ⌜def1 = def2⌝ ∗ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def1 len2 lts2) T
    ⊢ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_array_evar_def_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 k `{!IsProtected def2} :
    SubLtype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 8 :=
    λ T, i2p (weak_subltype_array_evar_def E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 k T).

  Lemma weak_subltype_array_evar_lts E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 k T :
    ⌜lts1 = lts2⌝ ∗ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts1) T
    ⊢ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_array_evar_lts_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 k `{!IsProtected lts2} :
    SubLtype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 9 :=
    λ T, i2p (weak_subltype_array_evar_lts E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 k T).

  Local Lemma weak_subltype_array_helper {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 b1 :
    length rs2 = len1 → length rs1 = len1 →
    ([∗ list] i↦a;b ∈ interpret_iml (◁ def1) len1 lts1; interpret_iml (◁ def2) len1 lts2, ∃ (r1 : place_rfn rt1) (r2 : place_rfn rt2), ⌜rs1 !! i = Some r1⌝ ∗ ⌜rs2 !! i = Some r2⌝ ∗ ltype_incl b1 r1 r2 a b) -∗
    [∗ list] lt1;lt2 ∈ zip (interpret_iml (◁ def1) len1 lts1) rs1; zip (interpret_iml (◁ def2) len1 lts2) rs2, ltype_incl b1 lt1.2 lt2.2 lt1.1 lt2.1.
  Proof.
    iIntros (??) "Ha".
    iPoseProof (big_sepL2_to_zip with "Ha") as "Ha".
    iPoseProof (big_sepL_extend_r (zip rs1 rs2) with "Ha") as "Ha".
    { rewrite !length_zip !length_interpret_iml. lia. }
    iApply big_sepL2_from_zip. { rewrite !length_zip !length_interpret_iml. lia. }
    rewrite zip_assoc_l [zip rs1 (zip _ _)]zip_assoc_r [zip rs1 (interpret_iml _ _ _)]zip_flip.
    rewrite !zip_fmap_l !zip_fmap_r. rewrite !zip_assoc_l !zip_fmap_r.
    rewrite zip_assoc_r -!list_fmap_compose big_sepL_fmap.
    iApply big_sepL2_to_zip'.
    iApply (big_sepL2_impl with "Ha").
    iModIntro. iIntros (k [lt1 lt2] [r1 r2] Hlook1 Hlook2); simpl.
    iIntros "(%r1' & %r2' & %Hlook1' & %Hlook2' & Hincl)".
    apply lookup_zip in Hlook2 as (Hlook21 & Hlook22).
    assert (r1' = r1) as -> by naive_solver. assert (r2' = r2) as -> by naive_solver.
    done.
  Qed.
  Lemma weak_subltype_array_owned_in E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 wl T :
    (⌜len1 = len2⌝ ∗
    ∃ rs2', ⌜rs2 = #rs2'⌝ ∗
    ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (weak_subltype_list_interp (Owned false) rs1 rs2') (
      ⌜length rs2' = len1⌝ ∗ T))
    ⊢ weak_subltype E L (Owned wl) #rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & %rs2' & -> & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & (%Hlen' & $))".
    iModIntro.
    iApply array_ltype_incl_owned_in; first done.
    simpl. iIntros (?). rewrite length_interpret_iml.
    iSpecialize ("Ha" with "[] []"). { iPureIntro. lia. } {iPureIntro. simpl in *. lia. }
    iR. setoid_rewrite Nat.add_0_r.
    iApply weak_subltype_array_helper; done.
  Qed.
  Global Instance weak_subltype_array_owned_in_inst E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 wl :
    SubLtype E L (Owned wl) #rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) |10 :=
    λ T, i2p (weak_subltype_array_owned_in E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 wl T).

  Lemma weak_subltype_array_owned E L {rt1 } (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 wl T :
    (⌜len1 = len2⌝ ∗ ⌜rs1 = rs2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
      relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (mut_subltype_list_interp len1 true) T)
    ⊢ weak_subltype E L (Owned wl) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & <- & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
    iModIntro.
    iApply array_ltype_incl_owned; first done.
    simpl. rewrite length_interpret_iml.
    iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
    iApply (big_sepL2_mono with "Ha"). eauto.
  Qed.
  Global Instance weak_subltype_array_owned_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 wl :
    SubLtype E L (Owned wl) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) |11 :=
    λ T, i2p (weak_subltype_array_owned E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 wl T).

  Lemma weak_subltype_array_shared_in E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 κ T :
    (⌜len1 = len2⌝ ∗
    ∃ rs2', ⌜rs2 = #rs2'⌝ ∗
    ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (weak_subltype_list_interp (Shared κ) rs1 rs2') (
      ⌜length rs2' = len1⌝ ∗ T))
    ⊢ weak_subltype E L (Shared κ) #rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & %rs2' & -> & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & (%Hlen' & $))".
    iModIntro.
    iApply array_ltype_incl_shared_in; first done.
    simpl. iIntros (?). rewrite length_interpret_iml.
    iSpecialize ("Ha" with "[] []"). { iPureIntro. lia. } {iPureIntro. simpl in *. lia. }
    iR. setoid_rewrite Nat.add_0_r.
    iApply weak_subltype_array_helper; done.
  Qed.
  Global Instance weak_subltype_array_shared_in_inst E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 κ :
    SubLtype E L (Shared κ) #rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) |10 :=
    λ T, i2p (weak_subltype_array_shared_in E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 κ T).

  Lemma weak_subltype_array_shared E L {rt1 } (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 κ T :
    (⌜len1 = len2⌝ ∗ ⌜rs1 = rs2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (mut_subltype_list_interp len1 true) T)
    ⊢ weak_subltype E L (Shared κ) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & <- & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
    iModIntro.
    iApply array_ltype_incl_shared; first done.
    simpl. rewrite length_interpret_iml.
    iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
    iApply (big_sepL2_mono with "Ha"). eauto.
  Qed.
  Global Instance weak_subltype_array_shared_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 κ :
    SubLtype E L (Shared κ) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) |11 :=
    λ T, i2p (weak_subltype_array_shared E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 κ T).

  Lemma weak_subltype_array_base E L {rt1 } (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 κ γ T :
    (⌜len1 = len2⌝ ∗ ⌜rs1 = rs2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (mut_eqltype_list_interp len1 true) T)
    ⊢ weak_subltype E L (Uniq κ γ) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & <- & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
    iModIntro.
    iApply array_ltype_incl_uniq; first done.
    simpl. rewrite length_interpret_iml.
    iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
    iApply (big_sepL2_mono with "Ha"). eauto.
  Qed.
  Global Instance weak_subltype_array_base_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 κ γ :
    SubLtype E L (Uniq κ γ) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 20 :=
    λ T, i2p (weak_subltype_array_base E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 κ γ T).

  (* for folding : *)
  Program Definition fold_overrides_list_interp {rt} (def : type rt) (cap : nat) (req : bool) : FoldablePredicate :=
    {|
      fp_pred (E : elctx) (L : llctx) (i : nat) (lt : ltype rt) (T : iProp Σ) :=
        if req then mut_subltype E L lt (◁ def)%I T else mut_eqltype E L lt (◁ def)%I T;
      fp_cap := cap;
      fp_inv := True;
      fp_elim_mode := req;
      fp_core_pred E L (i : nat) (lt : ltype rt) :=
        if req then (∀ k r, ltype_incl k r r lt (◁ def))%I else ⌜full_eqltype E L lt (◁ def)⌝%I;
    |}.
  Next Obligation.
    iIntros (rt def ? req E L i lt). destruct req.
    - iIntros (T ??) "#CTX #HE HL (%Hsubt & $)".
      iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl"; first apply Hsubt.
      iModIntro. iFrame. done.
    - iIntros (T) "(%Heqt & $)". done.
  Qed.

  Lemma fold_overrides_list_replicate {rt} E L (def : type rt) (lt : ltype rt) n ig i0 cap (req : bool) T :
    (if req then mut_subltype E L lt (◁ def) T else mut_eqltype E L lt (◁ def) T)
    ⊢ fold_list E L ig (replicate n lt) i0 (fold_overrides_list_interp def cap req) T.
  Proof.
    destruct req; iIntros "(%Hsubt & HT)".
    - iApply fold_list_replicate_elim_full; first done; last done.
      simpl. iIntros "#CTX #HE HL _".
      iPoseProof (full_subltype_acc with "CTX HE HL")as "#Hincl"; first apply Hsubt.
      iModIntro. iIntros (i ? k r). iApply "Hincl".
    - iApply fold_list_replicate_elim_weak; first done; last done.
      simpl. iIntros "_". eauto.
  Qed.
  Global Instance fold_overrides_list_replicate_inst {rt} E L (def : type rt) (lt : ltype rt) n ig i0 cap req :
    FoldList E L ig (replicate n lt) i0 (fold_overrides_list_interp def cap req) | 20 :=
    λ T, i2p (fold_overrides_list_replicate E L def lt n ig i0 cap req T).
  Local Typeclasses Transparent fold_overrides_list_interp.

  Lemma weak_subltype_array_ofty_r E L {rt1} (def1 : type rt1) ty len1 (lts1 : list (nat * ltype rt1)) rs1 rs2 k T :
    ⌜rs1 = rs2⌝ ∗ mut_eqtype E L (array_t len1 def1) ty
      (fold_list E L [] (interpret_iml (◁ def1) len1 lts1) 0 (fold_overrides_list_interp def1 len1 false) T)
    ⊢ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (◁ ty) T.
  Proof.
    iIntros "(-> & %Hsubt & Hf)".
    iIntros (??) "#CTX #HE HL".
    (*iMod ("Hf" with "[//] CTX HE HL") as "(Ha & HL & $)".*)
    rewrite /fold_list/=. iDestruct "Hf" as "(Hf & $)".
    simpl. iSpecialize ("Hf" with "[] []").
    { simpl. rewrite length_interpret_iml. iPureIntro. lia. }
    { simpl. done. }
    specialize (full_eqtype_eqltype _ _ _ _ Hsubt) as Hs.
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hb"; first apply Hs.
    iPoseProof (big_sepL_Forall with "Hf") as "%Ha".
    apply array_ltype_make_defaults_full_eqltype in Ha.
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hc"; first apply Ha.
    iFrame. iModIntro. iApply (ltype_incl_trans with "[Hf]"); first last.
    { iApply ltype_incl_trans.
      { iApply array_t_unfold_1. }
      iApply ltype_eq_ltype_incl_l.
      iApply "Hb". }
    iApply ltype_eq_ltype_incl_l. iApply "Hc".
  Qed.
  Global Instance weak_subltype_array_ofty_r_inst E L {rt1} (def1 : type rt1) ty len1 (lts1 : list (nat * ltype rt1)) rs1 rs2 k :
    SubLtype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (◁ ty)%I | 14 :=
    λ T, i2p (weak_subltype_array_ofty_r E L def1 ty len1 lts1 rs1 rs2 k T).

  Lemma weak_subltype_array_ofty_l E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts2 : list (nat * ltype rt2)) rs1 rs2 k T :
    weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 []) (ArrayLtype def2 len2 lts2) T
    ⊢ weak_subltype E L k rs1 rs2 (◁ array_t len1 def1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "Hsubt" (??) "#CTX #HE HL".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Ha & $ & $)".
    iModIntro. iApply ltype_incl_trans; last done.
    iApply array_t_unfold_2.
  Qed.
  Global Instance weak_subltype_array_ofty_l_inst E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts2 : list (nat * ltype rt2)) rs1 rs2 k :
    SubLtype E L k rs1 rs2 (◁ array_t len1 def1)%I (ArrayLtype def2 len2 lts2) | 14 :=
    λ T, i2p (weak_subltype_array_ofty_l E L def1 def2 len1 len2 lts2 rs1 rs2 k T).


  (** mut_subltype *)
  Lemma mut_subltype_array E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T:
    ⌜len1 = len2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len2 lts2) 0 (mut_eqltype_list_interp len1 false) T
    ⊢ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & %Hst & Hrel)".
    iPoseProof "Hrel" as "(Hr & $)".
    simpl. iSpecialize  ("Hr" with "[] [//]").
    { rewrite length_interpret_iml. iPureIntro. lia. }
    iPoseProof (big_sepL2_Forall2 with "Hr") as "%Ha".
    iPureIntro. eapply array_full_subltype; done.
  Qed.
  Global Instance mut_subltype_array_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) :
    MutSubLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 10 :=
    λ T, i2p (mut_subltype_array E L def1 def2 len1 len2 lts1 lts2 T).

  (* evar handling *)
  Lemma mut_subltype_array_evar_def E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T `{!IsProtected def2} :
    ⌜def1 = def2⌝ ∗ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def1 len2 lts2) T
    ⊢ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subltype_array_evar_def_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) `{!IsProtected def2} :
    MutSubLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 8 := λ T, i2p (mut_subltype_array_evar_def E L def1 def2 len1 len2 lts1 lts2 T).

  Lemma mut_subltype_array_evar_lts E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T `{!IsProtected lts2} :
    ⌜lts1 = lts2⌝ ∗ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts1) T
    ⊢ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subltype_array_evar_lts_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) `{!IsProtected lts2} :
    MutSubLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 9 := λ T, i2p (mut_subltype_array_evar_lts E L def1 def2 len1 len2 lts1 lts2 T).

  (* ofty unfolding *)
  Lemma mut_subltype_array_ofty_r E L {rt} (def1 : type rt) len1 lts1 ty T :
    mut_eqtype E L (array_t len1 def1) ty (fold_list E L [] (interpret_iml (◁ def1) len1 lts1) 0 (fold_overrides_list_interp def1 len1 false) T)
    ⊢ mut_subltype E L (ArrayLtype def1 len1 lts1) (◁ ty) T.
  Proof.
    iIntros "(%Heqt & Ha & $)".
    iSpecialize ("Ha" with "[] [//]"); simpl. { rewrite length_interpret_iml. iPureIntro. lia. }
    iPoseProof (big_sepL_Forall with "Ha") as "%Ha".
    iPureIntro. eapply full_eqltype_subltype_l.
    etrans; first last. { apply full_eqtype_eqltype; last apply Heqt. apply _. }
    trans (ArrayLtype def1 len1 []); first last.
    { symmetry. eapply array_t_unfold_full_eqltype. }
    apply array_ltype_make_defaults_full_eqltype. done.
  Qed.
  Global Instance mut_subltype_array_ofty_r_inst E L {rt} (def1 : type rt) len1 lts1 ty :
    MutSubLtype E L (ArrayLtype def1 len1 lts1)%I (◁ ty)%I | 14 :=
    λ T, i2p (mut_subltype_array_ofty_r E L def1 len1 lts1 ty T).

  Lemma mut_subltype_array_ofty_l E L {rt} (def1 : type rt) (def2 : type rt) len1 len2 (lts2 : list (nat * ltype rt)) T :
    mut_subltype E L (ArrayLtype def1 len1 []) (ArrayLtype def2 len2 lts2) T
    ⊢ mut_subltype E L (◁ array_t len1 def1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(%Hsubt & $)".
    iPureIntro. etrans; last apply Hsubt.
    apply full_eqltype_subltype_l.
    apply array_t_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_array_ofty_l_inst E L {rt} (def1 : type rt) (def2 : type rt) len1 len2 (lts2 : list (nat * ltype rt)) :
    MutSubLtype E L (◁ array_t len1 def1)%I (ArrayLtype def2 len2 lts2) | 14 :=
    λ T, i2p (mut_subltype_array_ofty_l E L def1 def2 len1 len2 lts2 T).

  (** eqltype *)
  Lemma mut_eqltype_array E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T:
    ⌜len1 = len2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len2 lts2) 0 (mut_eqltype_list_interp len1 false) T
    ⊢ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & %Hst & Hrel)".
    iPoseProof "Hrel" as "(Hr & $)".
    simpl. iSpecialize  ("Hr" with "[] [//]").
    { rewrite length_interpret_iml. iPureIntro. lia. }
    iPoseProof (big_sepL2_Forall2 with "Hr") as "%Ha".
    iPureIntro. eapply array_full_eqltype; done.
  Qed.
  Global Instance mut_eqltype_array_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) :
    MutEqLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 10 :=
    λ T, i2p (mut_eqltype_array E L def1 def2 len1 len2 lts1 lts2 T).

  (* evar handling *)
  Lemma mut_eqltype_array_evar_def E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T `{!IsProtected def2} :
    ⌜def1 = def2⌝ ∗ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def1 len2 lts2) T
    ⊢ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqltype_array_evar_def_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) `{!IsProtected def2} :
    MutEqLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 8 := λ T, i2p (mut_eqltype_array_evar_def E L def1 def2 len1 len2 lts1 lts2 T).

  Lemma mut_eqltype_array_evar_lts E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T `{!IsProtected lts2} :
    ⌜lts1 = lts2⌝ ∗ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts1) T
    ⊢ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqltype_array_evar_lts_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) `{!IsProtected lts2} :
    MutEqLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 9 := λ T, i2p (mut_eqltype_array_evar_lts E L def1 def2 len1 len2 lts1 lts2 T).

  Lemma mut_eqltype_array_ofty_r E L {rt} (def1 : type rt) len1 lts1 ty T :
    mut_eqtype E L (array_t len1 def1) ty (fold_list E L [] (interpret_iml (◁ def1) len1 lts1) 0 (fold_overrides_list_interp def1 len1 false) T)
    ⊢ mut_eqltype E L (ArrayLtype def1 len1 lts1) (◁ ty) T.
  Proof.
    iIntros "(%Heqt & Ha & $)".
    iSpecialize ("Ha" with "[] [//]"); simpl. { rewrite length_interpret_iml. iPureIntro. lia. }
    iPoseProof (big_sepL_Forall with "Ha") as "%Ha".
    iPureIntro.
    etrans; first last. { apply full_eqtype_eqltype; last apply Heqt. apply _. }
    trans (ArrayLtype def1 len1 []); first last.
    { symmetry. eapply array_t_unfold_full_eqltype. }
    apply array_ltype_make_defaults_full_eqltype. done.
  Qed.
  Global Instance mut_eqltype_array_ofty_r_inst E L {rt} (def1 : type rt) len1 lts1 ty :
    MutEqLtype E L (ArrayLtype def1 len1 lts1)%I (◁ ty)%I | 14 :=
    λ T, i2p (mut_eqltype_array_ofty_r E L def1 len1 lts1 ty T).

  Lemma mut_eqltype_array_ofty_l E L {rt} (def1 : type rt) (def2 : type rt) len1 len2 (lts2 : list (nat * ltype rt)) T :
    mut_eqltype E L (ArrayLtype def1 len1 []) (ArrayLtype def2 len2 lts2) T
    ⊢ mut_eqltype E L (◁ array_t len1 def1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(%Hsubt & $)".
    iPureIntro. etrans; last apply Hsubt.
    apply array_t_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_array_ofty_l_inst E L {rt} (def1 : type rt) (def2 : type rt) len1 len2 (lts2 : list (nat * ltype rt)) :
    MutEqLtype E L (◁ array_t len1 def1)%I (ArrayLtype def2 len2 lts2) | 14 :=
    λ T, i2p (mut_eqltype_array_ofty_l E L def1 def2 len1 len2 lts2 T).
End instances.

Global Typeclasses Opaque weak_subltype_list_interp.
Global Typeclasses Opaque mut_subltype_list_interp.
Global Typeclasses Opaque mut_eqltype_list_interp.

Global Typeclasses Opaque fold_overrides_list_interp.


