From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.array Require Import def unfold.
From refinedrust Require Import options.

Section stratify.
  Context `{!typeGS Σ}.

  (** ** stratify_ltype *)
  (* 1. stratify all components
     -> Then have the new ArrayLtype.
     2. 1) If we should fold fully: subltype the core of this new array type to ◁ array_t (if it contains blocked things), and fold to Coreable (array_t).
            Or subtype it directly to array_t if it doesn't contain blocked things.
        2) Otherwise, leave the ArrayLtype as-is.

    Should stratify go to coreable (i.e., bubble blocked things up), even if it wasn't Opened previously?
     -> we should not stratify to coreable, as that imposes information loss. Would be an issue for dropping of local variables.


    //
    What happens to mut ref unfolding below?
      - We might have an OpenedLtype with homogeneous refinement.
      - this might get turned to coreable.
      - we need to fold all of them. if one of them doesn't go to the designated type, we need to go to coreable ourselves.
          (this is like bubbling up)
    Do we need this?
     - Rust's native indexing/dereferencing does use dedicated functions on mutrefs (really on slices).
       So also the drop/overwrite thing would go via an indirection.
     - Do we need it in unsafe use cases where we really directly work with the array type?
        + for Vec/VecDeque, we don't need that.
   *)

  Lemma stratify_ltype_array_iter_nil π E L mu md ma {M} (m : M) (l : loc) {rt} (def : type rt) (len : nat) (rs : list (place_rfn rt)) k ig (T : stratify_ltype_array_iter_cont_t rt) :
    T L True [] rs
    ⊢ stratify_ltype_array_iter π E L mu md ma m l ig def len [] rs k T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    iModIntro. iExists L, True%I, [], rs.
    iFrame. simpl. iR. iApply logical_step_intro; eauto.
  Qed.
  Definition stratify_ltype_array_iter_nil_inst := [instance @stratify_ltype_array_iter_nil].
  Global Existing Instance stratify_ltype_array_iter_nil_inst.

  Import EqNotations.
  Lemma stratify_ltype_array_iter_cons_no_ignore π E L mu mdu ma {M} (m : M) (l : loc) (ig : list nat) {rt} (def : type rt) (rs : list (place_rfn rt)) (len : nat) (iml : list (nat * ltype rt)) (lt : ltype rt) j k `{Hnel : !CanSolve (j ∉ ig)%nat} T :
    ⌜j < len⌝ ∗ (∀ r, ⌜rs !! j = Some r⌝ -∗
    stratify_ltype_array_iter π E L mu mdu ma m l (j :: ig) def len iml rs k (λ L2 R2 iml2 rs2,
      stratify_ltype π E L2 mu mdu ma m (l offsetst{ty_syn_type def MetaNone}ₗ j) lt r k (λ L3 R3 rt3 lty3 r3,
        if (decide (ma = StratRefoldFull)) then
          match ltype_blocked_lfts lty3 with
          | [] =>
              (* directly fold completely *)
              ∃ r4, weak_subltype E L3 k r3 r4 lty3 (◁ def) (T L3 (R3 ∗ R2) ((j, ◁ def) :: iml2) (<[j := r4]> rs2))
          | _ =>
              (* we directly try to go to Coreable here in order to use the syntactic hint by [def] on which refinement type we need to go to.
                  If arrays supported heterogeneous refinements, we could also defer this. *)
              (*∃ (Heq : rt3 = rt), T L3 (R3 ∗ R2) ((j, rew Heq in lty3) :: iml2) (<[j := rew Heq in r3]> rs2)*)
              ⌜if k is Owned then True else False⌝ ∗
              (* we cannot have blocked lfts below shared; TODO: also allow Uniq *)
              trigger_tc (SimpLtype (ltype_core lty3)) (λ lty3',
              ∃ r4,
              weak_subltype E L3 k r3 r4 lty3' (◁ def) (T L3 (R3 ∗ R2) ((j, CoreableLtype (ltype_blocked_lfts lty3) (◁ def)) :: iml2) (<[j := r4]> rs2)))
          end
        else
            ∃ (Heq : rt = rt3),
            T L3 (R3 ∗ R2) ((j, rew <- [ltype] Heq in lty3) :: iml2) (<[j := rew <-[place_rfnRT] Heq in r3]> rs2)
      )))
    ⊢ stratify_ltype_array_iter π E L mu mdu ma m l ig def len ((j, lt) :: iml) rs k T.
  Proof.
    iIntros "(%Hlen & HT)". iIntros (????) "#CTX #HE HL Hl".
    simpl.
    iPoseProof (big_sepL2_length with "Hl") as "%Hlen'".
    rewrite length_insert length_interpret_iml in Hlen'. subst len.
    edestruct (lookup_lt_is_Some_2 rs j) as (r & Hlook); first done.
    rewrite -{5}(list_insert_id _ _ _ Hlook).

    iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs) iml) rs j lt r (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ (l offsetst{ty_syn_type def MetaNone}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(Ha & _)".
    { rewrite length_interpret_iml. done. }
    { done. }
    iDestruct ("Ha" with "Hl") as "(Hl & Hl2)". iClear "Ha".
    simpl.
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL [Hl2]") as "(%L2' & %R2' & %iml2 & %rs2 & %Hleneq & Hstep & HL & HT)".
    { iApply (big_sepL2_mono with "Hl2"). intros ? ? ? Hlook1 Hlook2.
      case_decide.
      { subst. iIntros "_". rewrite decide_False; first done. set_solver. }
      iIntros "Ha". case_decide.
      - rewrite decide_True; first done. set_solver.
      - rewrite decide_False; first done. set_solver. }
    unfold CanSolve in *. rewrite decide_True; last set_solver.
    iDestruct "Hl" as "(%Hst & Hl)".
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl") as "(%L3 & %R3 & %rt' & %lt' & %r' & HL & %Hst' & Hstep' & HT)".

    destruct (decide (ma = StratRefoldFull)); first last.
    { iDestruct "HT" as "(%Heq & HT)".
      subst.
      iExists _, _, _, _. iFrame.
      iSplitR. { iPureIntro. rewrite length_insert//. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hstep'").
      iApply logical_step_intro.
      iIntros "!> (Hl & $) (Hl2 & $)".
      simpl.
      iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs2) iml2) rs2 j (lt')%I r' (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ (l offsetst{ty_syn_type def MetaNone}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(_ & Ha)".
      { rewrite length_interpret_iml. lia. }
      { lia. }
      rewrite -Hleneq. iApply "Ha".
      iSplitL "Hl".
      { rewrite decide_True; last set_solver. iFrame.
        iPureIntro. rewrite -Hst' Hst//. }
      iApply (big_sepL2_mono with "Hl2").
      iIntros (k0 ? ? Hlook1 Hlook2) "Ha".
      destruct (decide (k0 = j)); first done.
      simpl. destruct (decide (k0 ∉ ig)); last done.
      rewrite decide_True; last set_solver. done. }
    destruct (ltype_blocked_lfts lt') eqn:Hbl.
    - iDestruct "HT" as "(%r4 & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iDestruct "Hincl" as "(%Hsteq & Hincl & _)".
      iExists _, _, _, _. iFrame.
      iSplitR. { iPureIntro. rewrite length_insert//. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hstep'").
      iApply logical_step_intro.
      iIntros "!> (Hl & $) (Hl2 & $)".
      simpl.
      iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs2) iml2) rs2 j (◁ def)%I r4 (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ (l offsetst{ty_syn_type def MetaNone}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(_ & Ha)".
      { rewrite length_interpret_iml. lia. }
      { lia. }
      iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.
      rewrite -Hleneq. iApply "Ha".
      iSplitL "Hl".
      { rewrite decide_True; last set_solver. iFrame. rewrite -Hsteq -Hst'. done. }
      iApply (big_sepL2_mono with "Hl2").
      iIntros (k0 ? ? Hlook1 Hlook2) "Ha".
      destruct (decide (k0 = j)); first done.
      simpl. destruct (decide (k0 ∉ ig)); last done.
      rewrite decide_True; last set_solver. done.
    - (* *)
      iDestruct "HT" as "(%Hown & % & %Heq & %r4 & HT)".
      destruct Heq as [<-].
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iDestruct "Hincl" as "(%Hsteq & Hincl & _)".
      iExists _, _, _, _. iFrame.
      iSplitR. { iPureIntro. rewrite length_insert//. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hstep'").
      iApply logical_step_intro.
      iIntros "!> (Hl & $) (Hl2 & $)".
      simpl.
      iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs2) iml2) rs2 j (CoreableLtype (ltype_blocked_lfts lt') (◁ def))%I r4 (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ (l offsetst{ty_syn_type def MetaNone}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(_ & Ha)".
      { rewrite length_interpret_iml. lia. }
      { lia. }
      rewrite -Hleneq -Hbl. iApply "Ha". iClear "Ha".
      iSplitL "Hl".
      + iModIntro. rewrite decide_True; last set_solver.
        simp_ltypes. iR.
        destruct k as [ | |]; [ | done..].
        (* TODO this should also work for Uniq -- the only problem is that we need to split it up into the observation. Maybe we should just have a generic lemma for that for all ltypes. *)
        rewrite ltype_own_coreable_unfold /coreable_ltype_own.
        iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & %Hly)".
        iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
        iExists ly. simp_ltypes.
        match goal with H : ty_syn_type def MetaNone = ltype_st lt' |- _ => rename H into Hsteq end.
        rewrite Hsteq. iR.
        simpl. rewrite -Hsteq. iR. iR.
        iIntros "Hdead".
        iPoseProof (imp_unblockable_blocked_dead lt') as "(_ & #Himp)".
        iMod ("Himp" with "Hdead Hl") as "Hl". rewrite !ltype_own_core_equiv.
        iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.
        simp_ltypes. done.
      + iApply (big_sepL2_mono with "Hl2").
        iIntros (k0 ? ? Hlook1 Hlook2) "Ha".
        destruct (decide (k0 = j)); first done.
        simpl. destruct (decide (k0 ∉ ig)); last done.
        rewrite decide_True; last set_solver. done.
  Qed.
  Definition stratify_ltype_array_iter_cons_no_ignore_inst := [instance @stratify_ltype_array_iter_cons_no_ignore].
  Global Existing Instance stratify_ltype_array_iter_cons_no_ignore_inst.

  Lemma stratify_ltype_array_iter_cons_ignore π E L mu mdu ma {M} (m : M) (l : loc) (ig : list nat) {rt} (def : type rt) (rs : list (place_rfn rt)) (len : nat) (iml : list (nat * ltype rt)) (lt : ltype rt) j k T `{Hnel : !CanSolve (j ∈ ig)%nat} :
    ⌜j < len⌝ ∗ stratify_ltype_array_iter π E L mu mdu ma m l (ig) def len iml rs k T
    ⊢ stratify_ltype_array_iter π E L mu mdu ma m l ig def len ((j, lt) :: iml) rs k T.
  Proof.
    iIntros "(%Hlen & HT)". iIntros (????) "#CTX #HE HL Hl".
    unfold CanSolve in *.
    iPoseProof (big_sepL2_length with "Hl") as "%Hlen'".
    rewrite length_insert length_interpret_iml in Hlen'. subst len.
    iMod ("HT" with "[//] [//] [//] CTX HE HL [Hl]") as "(%L2 & %R2 & %iml2 & %rs2 & %Hleneq & Hstep & HL & HT)".
    { edestruct (lookup_lt_is_Some_2 rs j) as (r & Hlook). { lia. }
      rewrite -{2}(list_insert_id _ _ _ Hlook).
      simpl.
      iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs) iml) rs j lt r (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ (l offsetst{ty_syn_type def MetaNone}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(Ha & _)".
      { rewrite length_interpret_iml. done. }
      { done. }
      iDestruct ("Ha" with "Hl") as "(_ & Hl)". iClear "Ha".
      iApply (big_sepL2_mono with "Hl"). iIntros (??? Hlook1 Hlook2) "Ha".
      case_decide. { rewrite decide_False; first done. set_solver. }
      simpl. done.
    }
    iExists _, _, _, _. iFrame.
    done.
  Qed.
  Definition stratify_ltype_array_iter_cons_ignore_inst := [instance @stratify_ltype_array_iter_cons_ignore].
  Global Existing Instance stratify_ltype_array_iter_cons_ignore_inst.

  Lemma stratify_ltype_array_owned {rt} π E L mu mdu ma {M} (m : M) l (def : type rt) len iml rs (T : stratify_ltype_cont_t) :
    stratify_ltype_array_iter π E L mu mdu ma m l [] def len iml rs (Owned) (λ L2 R2 iml2 rs2,
      T L2 R2 _ (ArrayLtype def len iml2) (#rs2))
    ⊢ stratify_ltype π E L mu mdu ma m l (ArrayLtype def len iml) (#rs) (Owned) T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hsz & %Hly & Hlb & %r' & <- & Hl)".
    iMod (fupd_mask_mono with "Hl") as "(%Hlen & Hl)"; first done.
    subst len.
    iMod ("HT" with "[//] [//] [//] CTX HE HL [Hl]") as "(%L2 & %R2 & %iml2 & %rs2 & %Hleneq & Hstep & HL & HT)".
    { iApply (big_sepL2_mono with "Hl"). intros ? ? ? HLook1 Hlook2.
      rewrite /OffsetLocSt /use_layout_alg' Halg/=. done. }
    iModIntro. iExists L2, R2, _, _, _. iFrame. simp_ltypes. iR.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro).
    iIntros "(Ha & $)".
    iModIntro.
    rewrite ltype_own_array_unfold /array_ltype_own.
    iExists _. iFrame "∗%". iR.
    iApply (big_sepL2_mono with "Ha").
    intros ??? Hlook1 Hlook2.
    rewrite /OffsetLocSt /use_layout_alg' Halg/=. done.
  Qed.
  Definition stratify_ltype_array_owned_inst := [instance @stratify_ltype_array_owned].
  Global Existing Instance stratify_ltype_array_owned_inst.
  (* TODO Uniq *)

End stratify.
