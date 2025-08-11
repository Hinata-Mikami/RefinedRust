From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.struct Require Import def subltype.
From refinedrust Require Import options.

(** ** Stratification instances for structs *)

Section stratify.
  Context `{!typeGS Σ}.

  Definition stratify_ltype_struct_iter_cont_t := llctx → iProp Σ → ∀ rts' : list RT, hlist ltype rts' → plist place_rfnRT rts' → iProp Σ.
  Definition stratify_ltype_struct_iter (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (md : StratifyDescendUnfoldMode) (ma : StratifyAscendMode) {M} (m : M) (l : loc) (i0 : nat) (sls : struct_layout_spec) {rts} (ltys : hlist ltype rts) (rfns : plist place_rfnRT rts) (k : bor_kind) (T : stratify_ltype_struct_iter_cont_t) : iProp Σ :=
    ∀ F sl, ⌜lftE ⊆ F⌝ -∗
    ⌜lft_userE ⊆ F⌝ -∗
    ⌜shrE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ⌜struct_layout_spec_has_layout sls sl⌝ -∗
    ⌜i0 ≤ length sls.(sls_fields)⌝ -∗
    ⌜(i0 + length rts = length sls.(sls_fields))%nat⌝ -∗
    ([∗ list] i ↦ p ∈ hpzipl rts ltys rfns, let '(existT rt (lt, r)) := p in
      ∃ name st, ⌜sls.(sls_fields) !! (i + i0)%nat = Some (name, st)⌝ ∗
      (l atst{sls}ₗ name) ◁ₗ[π, k] r @ lt) ={F}=∗
    ∃ (L' : llctx) (R' : iProp Σ) (rts' : list RT) (ltys' : hlist ltype rts') (rfns' : plist place_rfnRT rts'),
      ⌜length rts = length rts'⌝ ∗
      ([∗ list] i ↦ p; p2 ∈ hpzipl rts ltys rfns; hpzipl rts' ltys' rfns',
          let '(existT rt (lt, r)) := p in
          let '(existT rt' (lt', r')) := p2 in
          ⌜ltype_st lt = ltype_st lt'⌝) ∗
      logical_step F (
        ([∗ list] i ↦ p ∈ hpzipl rts' ltys' rfns', let '(existT rt (lt, r)) := p in
          ∃ name st, ⌜sls.(sls_fields) !! (i + i0)%nat = Some (name, st)⌝ ∗
          (l atst{sls}ₗ name) ◁ₗ[π, k] r @ lt) ∗ R') ∗
      llctx_interp L' ∗
      T L' R' rts' ltys' rfns'.

  Lemma stratify_ltype_struct_iter_nil π E L mu md ma {M} (m : M) (l : loc) sls k i0 (T : stratify_ltype_struct_iter_cont_t) :
    T L True [] +[] -[]
    ⊢ stratify_ltype_struct_iter π E L mu md ma m l i0 sls +[] -[] k T.
  Proof.
    iIntros "HT". iIntros (?????) "#CTX #HE HL ??? Hl".
    iModIntro. iExists L, True%I, [], +[], -[].
    iR. iFrame. simpl. iR. iApply logical_step_intro; eauto.
  Qed.

  Lemma stratify_ltype_struct_iter_cons π E L mu mdu ma {M} (m : M) (l : loc) sls i0 {rts rt} (ltys : hlist ltype rts) (rfns : plist place_rfnRT (rt :: rts)) (lty : ltype rt) k T :
    (∃ r rfns0, ⌜rfns = r -:: rfns0⌝ ∗
    stratify_ltype_struct_iter π E L mu mdu ma m l (S i0) sls ltys rfns0 k (λ L2 R2 rts2 ltys2 rs2,
      (∀ name st, ⌜sls.(sls_fields) !! i0 = Some (name, st)⌝ -∗
      stratify_ltype π E L2 mu mdu ma m (l atst{sls}ₗ name) lty r k (λ L3 R3 rt3 lty3 r3,
        T L3 (R3 ∗ R2) (rt3 :: rts2) (lty3 +:: ltys2) (r3 -:: rs2)))))
    ⊢ stratify_ltype_struct_iter π E L mu mdu ma m l i0 sls (lty +:: ltys) (rfns) k T.
  Proof.
    iIntros "(%r &  %rfns0 & -> & HT)". iIntros (?????) "#CTX #HE HL %Halg %Hlen %Hleneq Hl".
    simpl. iDestruct "Hl" as "(Hl & Hl2)". simpl in *.
    iMod ("HT" with "[//] [//] [//] CTX HE HL [//] [] [] [Hl2]") as "(%L2' & %R2' & %rts2' & %ltys2' & %rfns2' & %Hlen' & Hst & Hl2 & HL & HT)".
    { rewrite -Hleneq. iPureIntro. lia. }
    { rewrite -Hleneq. iPureIntro. lia. }
    { iApply (big_sepL_mono with "Hl2"). intros ? [? []] ?. by rewrite Nat.add_succ_r. }
    iDestruct "Hl" as "(%name & %st & %Hlook & Hl)".
    (*edestruct (lookup_lt_is_Some_2 sls.(sls_fields) i0) as ([name ?] & Hlook); first by lia.*)
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL Hl") as "(%L3 & %R3 & %rt' & %lt' & %r' & HL & Hst1 & Hl & HT)".
    iModIntro. iExists L3, (R3 ∗ R2')%I, _, _, _. iFrame.
    iSplitR. { rewrite Hlen'. done. }
    iApply (logical_step_compose with "Hl2"). iApply (logical_step_wand with "Hl").
    iIntros "(Hl & HR1) (Hl2 & HR2)".
    simpl. iFrame "HR1 HR2".
    iSplitL "Hl". { iExists _, _. iFrame. done. }
    iApply (big_sepL_mono with "Hl2"). intros ? [? []] ?. by rewrite Nat.add_succ_r.
  Qed.

  (*
      Owned:
      - stratify all components
      - if we should refold:
          fold all of them to ofty via cast, then done.
            TODO: should i really do that? It seems like the subtyping should also be able to deal with that.
            and at other places, i anyways have cast_ltype.
            should check if I can.

     Uniq:
     - Basically, we want to stratify all the components
     - Then check if all of them obey the place cond
     - If they do not:
        + go to OpenedLtype
          Well, can this happen?
          Basically, only if we unfold an invariant etc.
          i.e. only if we use the stratification for unfolding.
          So I think this should be fine to omit, probably.
        (otherwise, if it is already unfolded before, this should already be in the Owned mode)
     - If they do:
        + if we don't need to refold, leave it
        + if we want to refold, just require that it is castable.

     Q: do we even need the Uniq case in practice?
        I guess only for unblocking. So we should have it.


     For implementation:
      basically want to be able to say
        - I get out a new hlist/plist
        - elementwise, compared to the old list, I get a place_cond (in Uniq case)
      Problem with existing stuff: I don't get an output. fold_list/relate_list are meant for proving stuff, not for computing something.

     maybe also compute a list, and each op can emit an element for the list?
     Or just have a specific stratify_ltype_list.
     e.g. what do I do with the R?
     I don't think it will be very re-usable anyways.


     How do I do it for arrays?
      Also a custom judgment?

     However, at least these won't need typeclasses I guess, just need to extend the liRJudgment tactics.

   *)
  (* TODO: stratification instance for StructLtype with optional refolding *)


  Lemma stratify_ltype_struct_owned {rts} π E L mu mdu ma {M} (m : M) l (lts : hlist ltype rts) (rs : plist place_rfnRT rts) sls wl (T : stratify_ltype_cont_t) :
    stratify_ltype_struct_iter π E L mu mdu ma m l 0 sls lts rs (Owned false) (λ L2 R2 rts' lts' rs',
      T L2 R2 (plist place_rfnRT rts') (StructLtype lts' sls) (#rs'))
    ⊢ stratify_ltype π E L mu mdu ma m l (StructLtype lts sls) (#rs) (Owned wl) T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    iDestruct "Hl" as "(%sl & %Halg & %Hlen & %Hly & Hlb & Hcreds & %r' & <- & Hl)".
    iMod (maybe_use_credit with "Hcreds Hl") as "(Hcred & Hat & Hl)"; first done.
    iPoseProof (struct_ltype_focus_components with "Hl") as "(Hl & Hlcl)"; [done | done | ].
    iMod ("HT" with "[//] [//] [//] CTX HE HL [//] [] [] [Hl]") as "(%L2 & %R2 & %rts' & %lts' & %rs' & %Hleneq & Hst & Hstep & HL & HT)".
    { iPureIntro. lia. }
    { rewrite Hlen.  done. }
    { iApply (big_sepL_mono with "Hl"). intros ? [? []] ?. rewrite Nat.add_0_r. done. }
    iModIntro. iExists L2, R2, _, _, _. iFrame. simp_ltypes. iR.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred2 !> (Ha & $)".
    iPoseProof ("Hlcl" $! rts' lts' rs' with "[//] [Hst] [Ha]") as "Hl".
    { iApply big_sepL2_Forall2.
      iApply (big_sepL2_impl with "Hst"). iModIntro. iIntros (? [? []] [? []] ? ?); done. }
    { iApply (big_sepL_mono with "Ha"). intros ? [? []] ?. rewrite Nat.add_0_r. eauto. }
    iModIntro.
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    iExists _. iFrame "∗%".
    iSplitR. { by rewrite -Hleneq. }
    done.
  Qed.
  Global Instance stratify_ltype_struct_owned_inst {rts} π E L mu mdu ma {M} (m : M) l (lts : hlist ltype rts) (rs : plist place_rfnRT rts) sls wl :
    StratifyLtype π E L mu mdu ma m l (StructLtype lts sls) (#rs) (Owned wl) :=
    λ T, i2p (stratify_ltype_struct_owned π E L mu mdu ma m l lts rs sls wl T).

  (* TODO uniq*)

End stratify.

Global Typeclasses Opaque stratify_ltype_struct_iter.
