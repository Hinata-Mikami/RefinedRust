From refinedrust Require Export base type ltypes base.value.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import programs uninit.
From refinedrust.struct Require Import def subltype unfold.
From refinedrust Require Import options.

(** ** Lemmas about deinitializing *)

Section deinit.
  Context `{!typeGS Σ}.

  Fixpoint uninit_tys (ls : list syn_type) : hlist type (replicate (length ls) (unit : RT)) :=
    match ls with
    | [] => +[]
    | st :: sts =>
        typed_value_t st +:: uninit_tys sts
    end.
  Lemma uninit_tys_lookup_inv (sts : list syn_type) k x :
    hzipl _ (uninit_tys sts) !! k = Some x →
    ∃ st, sts !! k = Some st ∧ x = existT (unit : RT) (typed_value_t st).
  Proof.
    induction sts as [ | st sts IH] in k, x |-*; simpl; first done.
    destruct k as [ | k]; simpl.
    - intros [= <-]. eauto.
    - apply IH.
  Qed.

  Fixpoint uninit_rs (ls : list syn_type) : plist (@id RT) (replicate (length ls) (unit : RT)) :=
    match ls with
    | [] => *[]
    | st :: sts =>
        tt *:: uninit_rs sts
    end.
  Lemma uninit_rs_lookup_inv (sts : list syn_type) k x :
    pzipl _ (uninit_rs sts) !! k = Some x →
    ∃ st, sts !! k = Some st ∧ x = existT (unit : RT) tt.
  Proof.
    induction sts as [ | st sts IH] in k, x |-*; simpl; first done.
    destruct k as [ | k]; simpl.
    - intros [= <-]. eauto.
    - apply IH.
  Qed.

  Lemma uninit_tys_has_op_types (fields : list (string * syn_type)) ots :
    Forall2 (λ field ot, use_op_alg field.2 = Some ot) fields ots →
    Forall2
      (λ ty ot, ty_has_op_type (projT2 ty) ot)
    (hzipl (replicate (length fields.*2) (()%type : RT)) (uninit_tys fields.*2))
    ots.
  Proof.
    induction fields as [| [name st] fields IH] in ots |-*; intros Hots; simpl.
    - apply Forall2_nil_inv_l in Hots as ->. done.
    - apply Forall2_cons_inv_l in Hots as (ot & ots' & Hot & Hots & ->).
      econstructor; last by apply IH.
      rewrite ty_has_op_type_unfold. simpl.
      exists ot. split_and!; [done | by apply is_value_ot_core_refl | ].
      by eapply use_op_alg_layout_alg.
  Qed.

  Lemma ltype_deinit_struct F π (sls : struct_layout_spec) rs l :
    lftE ⊆ F →
    (l ◁ₗ[π, Owned] (#rs) @ (StructLtype (hmap (@OfTy _ _) (uninit_tys (sls_fields sls).*2)) sls)) ={F}=∗
    l ◁ₗ[π, Owned] #() @ (◁ typed_value_t sls).
  Proof.
    iIntros (?) "Hl".
    iPoseProof (struct_t_unfold_2_owned) as "#Ha".
    iMod (fupd_mask_subseteq lftE) as "Hcl"; first done.
    iMod ("Ha" with "Hl") as "Hl".
    iMod "Hcl" as "_". iClear "Ha".

    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & %Hl)".
    iMod (ofty_own_split_value_typed with "Hl") as "(%v & Hv & Hl)"; first done.
    { simpl in *. simp_ltypes in Halg. simpl in Halg.
      opose proof* syn_type_has_layout_op_alg as (ot & Hot & Heq); first apply Halg.
      subst ly.
      opose proof* use_op_alg_struct_inv as Ha; first apply Hot.
      destruct Ha as (sl & ots & Hsl & Hots & ->).
      eapply ty_has_op_type_struct_canonical.
      { done. }
      { rewrite /use_op_alg' Hot//. }
      by eapply uninit_tys_has_op_types. }
    simp_ltypes in Halg. simpl in Halg.
    iApply (ofty_owned_subtype_aligned with "[] Hl"); [ | done | ].
    { done. }
    iApply owned_type_incl_value_typed_value.
  Qed.
End deinit.

Section rules.
Context `{!typeGS Σ}.

  (* We iterate over all the fields to deinitialize them first, and then deinitialize the struct itself *)
  Lemma owned_subltype_step_struct_uninit π E L step l {rts} (lts : hlist ltype rts) rs (sls : struct_layout_spec) (st : syn_type) T :
     owned_subltype_step π E L step l (#rs) (#()) (StructLtype lts sls) (◁ typed_value_t st) T :-
    exhale (⌜st = sls⌝);
    L2, R2 ← iterate: zip (hpzipl rts lts rs) sls.(sls_fields) with L, True%I {{ '((existT rt (lt, r)), (field, stf)) T L2 R2,
      exhale (⌜(ltype_st lt) = stf⌝);
       return owned_subltype_step π E L2 step (l atst{sls}ₗ field) r (#()) lt (◁ typed_value_t stf) (λ L3 R3,
        T L3 (R2 ∗ R3))
      }};
    return T L2 R2.
  Proof.
    iIntros "(-> & Hit)".
    iIntros (????) "#CTX #HE HL Hl".

    rewrite ltype_own_struct_unfold/struct_ltype_own/=.
    iDestruct "Hl" as "(%sl & %Halg & %Hlen & %Hly & Hlb &  %rs' & -> & Hl)".
    iMod (fupd_mask_mono with "Hl") as "Hl"; first done.

    iPoseProof (struct_ltype_focus_components with "Hl") as "(Hl & Hclose_l)"; [done.. | ].

    set (INV := (λ (idx : nat) (L2 : llctx) (R2 : iProp Σ),
      llctx_interp L2 ∗
      ([∗ list] i↦'(existT rt (lt, r)) ∈ hpzipl rts lts rs',
          if decide (idx ≤ i) then
          ∃ (name : string) (st : syn_type), ⌜sls_fields sls !! i = Some (name, st)⌝ ∗ l atst{sls}ₗ name ◁ₗ[ π, Owned] r @ lt
          else True) ∗
      maybe_logical_step step F (R2 ∗
        ([∗ list] i↦'(existT rt (lt, r)) ∈ hpzipl rts lts rs',
          if decide (i < idx) then
          ∃ (name : string) (st : syn_type),
          ⌜sls_fields sls !! i = Some (name, st)⌝ ∗
          ⌜(ltype_st lt) = st⌝ ∗
          l atst{sls}ₗ name ◁ₗ[ π, Owned] #() @ ◁ typed_value_t st
          else True)
      ))%I).

    iMod (iterate_elim2_fupd INV with "Hit [Hl HL] []") as "(%L2 & %R2 & Hinv & HT)".
    { (* initialization *)
      unfold INV. iFrame. iApply maybe_logical_step_intro.
      iR. simpl. iApply big_sepL_intro.
      iIntros "!>" (? [? []] ?). done. }
    { (* preservation *)
      iModIntro. iIntros (i [[rt [lt r']] [name st']] T' L2 R2 Hlook) "Hinv Hsub".
      iDestruct "Hinv" as "(HL & Hinv & Hstep)".

      apply lookup_zip in Hlook as [Hlook1 Hlook2].
      iPoseProof (big_sepL_delete with "Hinv") as "(Ha & Hinv)"; first apply Hlook1.
      simpl. rewrite decide_True; last lia.
      iDestruct "Ha" as "(% & % & %Hlook2' & Ha)".
      rewrite Hlook2 in Hlook2'. injection Hlook2' as <- <-.
      iDestruct "Hsub" as "(% & Hsub)".
      iMod ("Hsub" with "[] [] [] CTX HE HL Ha") as "(%L3 & %R3 & Hs & HL & HT)"; [done.. | ].

      iModIntro. iExists _, _. iFrame.
      iSplitL "Hinv".
      { iApply (big_sepL_mono with "Hinv"). iIntros (? [? []] ?) "Ha".
        repeat case_decide; try done; lia. }
      iApply (maybe_logical_step_compose with "Hstep").
      iApply (maybe_logical_step_wand with "[] Hs").
      iIntros "(Ha & HR) (HR2 & Hb)". iFrame.
      iEval (rewrite -(list_insert_id (hpzipl rts lts rs') i _ Hlook1)).
      iApply big_sepL_insert.
      { by apply lookup_lt_is_Some_1. }
      simpl.
      iSplitL "Ha".
      { rewrite decide_True; last lia. eauto with iFrame. }
      iApply (big_sepL_mono with "Hb"). iIntros (? [? []] ?) "Ha".
      repeat case_decide; try done; lia. }
    iDestruct "Hinv" as "(HL & _ & Hs)".
    iModIntro. iExists L2, R2. iFrame "HL HT".
    iApply maybe_logical_step_fupd.
    iApply (maybe_logical_step_wand with "[Hclose_l Hlb] Hs").
    iIntros "(HR & Hx)". iFrame "HR".
    clear INV.

    (* extract pure info from invariant *)
    iAssert (⌜Forall2 (λ '(existT rt (lt, _)) st, (ltype_st lt) = st) (hpzipl rts lts rs') (sls_fields sls).*2⌝)%I with "[Hx]" as "%Hf".
    { iApply big_sepL2_Forall2.
      iPoseProof (big_sepL_extend_r with "Hx") as "Hx"; last iApply (big_sepL2_wand with "Hx").
      { rewrite length_fmap length_hpzipl Hlen//. }
      iApply big_sepL2_intro. { rewrite length_fmap length_hpzipl Hlen//. }
      iIntros "!>" (? [? []] ? Hlook1 Hlook2).
      apply list_lookup_fmap_Some in Hlook2 as ([name st'] & -> & Hlook2).
      rewrite decide_True; first last. { rewrite length_zip length_hpzipl Hlen.
        apply (hpzipl_lookup_inv _ _ rs') in Hlook1. apply lookup_lt_Some in Hlook1. lia. }
      iIntros "(% & % & %Hlook3 & % &  _)".
      simplify_eq/=. done. }

    set (lts' := (hmap (@OfTy _ _) (uninit_tys (sls_fields sls).*2))).
    set (rs'' := (pmap (λ _ x, #x) (uninit_rs  (sls_fields sls).*2))).
    iPoseProof ("Hclose_l" $! _ lts' rs'' with "[] [] [Hx]")as "Hx".
    { iPureIntro. rewrite -Hlen length_replicate length_fmap//. }
    { iPureIntro.
      eapply (Forall2_trans _ (λ st '(existT rt (lt, _)), st = (ltype_st lt))); [ | apply Hf | ].
      - intros [? []] st' [? []]; simpl.
        intros Hcomp1 Hcomp2.
        etrans; done.
      - unfold lts', rs''.
        (*apply use_struct_layout_alg_inv in Halg as (fields & _ & Hf2).*)
        apply use_struct_layout_alg_fields_layoutable in Halg.
        move: Halg.
        generalize (sls_fields sls).*2 as sts.
        clear. induction sts as [ | st sts IH]; simpl; first done.
        intros [(? & ?)?]%Forall_cons.
        econstructor.
        + simp_ltypes. done.
        + by eapply IH. }
    { iApply big_sepL2_elim_r.
      iPoseProof (big_sepL_extend_l with "Hx") as "Hx"; last iApply (big_sepL2_wand with "Hx").
      { rewrite !length_hpzipl length_replicate length_fmap -Hlen//. }
      iApply big_sepL2_intro.
      { rewrite !length_hpzipl length_replicate length_fmap -Hlen//. }
      iModIntro. iIntros (k [rt1 [lt1 rs1]] [rt2 [lt2 rs2]] Hlook1 Hlook2).

      apply (hpzipl_lookup_inv _ _ rs'') in Hlook1 as Hlook1'.
      apply lookup_replicate_1 in Hlook1' as (-> & Hk).
      rewrite length_fmap in Hk.
      rewrite decide_True; first last. { rewrite length_zip length_hpzipl. lia. }

      apply (hpzipl_lookup_inv_hzipl_pzipl _ _ rs'') in Hlook1 as (Hlook1_1 & Hlook1_2).
      subst lts'.
      eapply hzipl_hmap_lookup_inv in Hlook1_1 as (ty & Hlook1_1 & ->).
      apply uninit_tys_lookup_inv in Hlook1_1 as (st' & Hlook1_1 & Heq).
      apply existT_inj in Heq as ->.

      eapply pzipl_pmap_lookup_inv in Hlook1_2 as (ty & Hlook1_2 & ->).
      apply uninit_rs_lookup_inv in Hlook1_2 as (st'' & Hlook1_2 & Heq).
      apply existT_inj in Heq as ->.
      rewrite Hlook1_1 in Hlook1_2. injection Hlook1_2 as [= <-].

      iIntros "(%name & %st'' & %Hlook_fields & %Hcomp & Ha)".
      iExists name, _. iR.
      apply list_lookup_fmap_Some in Hlook1_1 as ([name' st'''] & -> & Hlook1_1).
      simplify_eq/=. simpl. done. }
    iApply (ltype_deinit_struct _ _ sls (rs'')); first done.

    rewrite ltype_own_struct_unfold/struct_ltype_own.
    iExists _. iR.
    iSplitR. { rewrite length_replicate length_fmap//. }
    iR. iFrame. iR. done.
  Qed.
  Definition owned_subltype_step_struct_uninit_inst := [instance owned_subltype_step_struct_uninit].
  Global Existing Instance owned_subltype_step_struct_uninit_inst | 20.

  (* TODO: extractop *)
End rules.
