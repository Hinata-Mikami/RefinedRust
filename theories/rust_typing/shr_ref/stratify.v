From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def subltype unfold.
From refinedrust Require Import options.

(** ** Stratification instances for shared references *)

Section stratify.
  Context `{!typeGS Σ}.

  (** Structural instances *)
  Lemma stratify_ltype_shr_owned mu mdu ma {rt} π E L {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl
      (T : stratify_ltype_cont_t) :
    (∀ l', stratify_ltype π E L mu mdu ma ml l' lt r (Shared κ) (λ L' R rt' lt' r',
      match ma with
      | StratRefoldFull =>
          ∃ (_ : Inhabited rt'), cast_ltype_to_type E L' lt' (λ ty', T L' R _ (◁ (shr_ref κ ty'))%I (#r'))
      | _ => T L' R _ (ShrLtype lt' κ) (#r')
      end))
    ⊢ stratify_ltype π E L mu mdu ma ml l (ShrLtype lt κ) (#r) (Owned wl) T.
  Proof.
    iIntros "Hs". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hb".
    iPoseProof (shr_ltype_acc_owned F with "[$LFT $TIME $LLCTX] Hb") as "Hb"; [done.. | ].
    iDestruct "Hb" as "(%Hly & #Hlb & >(%l' & Hl & Hb & Hcl))".
    iPoseProof ("Hs" with "[//] [//] [//] [$LFT $TIME $LLCTX] HE HL Hb") as "Hb".
    iMod "Hb" as "(%L' & %R & %rt' & %lt' & %r' & HL & %Hcond & Hstep & Hc)".
    destruct (decide (ma = StratRefoldFull)) as [Heq | ].
    - subst ma.
      iDestruct "Hc" as "(% & %ty' & %Heq & HT)".
      iPoseProof (eqltype_use F with "[$LFT $TIME $LLCTX] HE HL") as "(Hvs & HL)"; [done | .. ].
      { apply full_eqltype_alt. apply Heq. }
      (*iPoseProof (eqltype_acc with "[$LFT $TIME $LLCTX] HE HL") as "#Heq"; first done.*)
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      iMod ("Hvs" with "Hb") as "Hb".
      iMod ("Hcl" with "Hl Hb") as "Hb".
      iDestruct (shr_ref_unfold_1 ty' κ (Owned wl)) as "(_ & #Hi & _)".
      iMod (fupd_mask_mono with "(Hi Hb)") as "$"; first done.
      done.
    - iAssert (T L' R _ (ShrLtype lt' κ) (#r')) with "[Hc]" as "Hc".
      { destruct ma; done. }
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes; done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      by iMod ("Hcl" with "Hl Hb") as "$".
  Qed.
  Definition stratify_ltype_shr_owned_inst := [instance (@stratify_ltype_shr_owned StratMutNone) ].
  Global Existing Instance stratify_ltype_shr_owned_inst.

  (* TODO Uniq *)

  (* Notes on stratification of [Shared]:
     basically:
     when we are accessing, we are unfolding

    - in principle, this should "just work" by operating under these laters.
      Below shared references, the amount of unfolding we could have done is very limited: basically, we can only have
        ShrBlocked or Shadowed.
      For Shadowed: should easily be able to take it back.
      For ShrBlocked: this might be more of a problem.
          We actually need to execute the viewshift for the inheritance, right.
          However, do we ever have nested shrblocked (ie below Shared) in practice?
          => No. I cannot initialize a shrblocked from that, because I cannot initialize sharing.
            Rather, creating a shr reference from a shared place should copy the existing sharing.

      Then: I basically just want to be able to execute this stratification below the later.
        Issue with using this stratify: the lifetime context stuff.
        But in principle, shared stratification should also not use the lifetime context stuff.

      Maybe have a separate notion of shared stratification to account for that?
      That basically should just take the thing unter an iterated step_fupdN and also only need to provide the stratified thing under a step_fupdN.

      Eventually: what happens if we do interior mutability?
        then we will actually open an invariant and get some tokens for stuff back.
        Though we might just want to have that for primitive ofty things, not nested

      In the shared case, can we just set this up differently altogether?
        Maybe just require subtyping of core?
        Can Shared stuff always go directly to the core?
        => Yes, I think so, for now.
        Alternative: directly go to the core.
          i.e. would have to prove that for Shared we can always go to the core.
          For more advanced sharing patterns where we actually want to have shrblocked, this might not work though. but that is anyways far in the future now.
          This is anyways slightly incompatible with the current model/needs work.

      Options now:
      - have stratify_ltype version for Shared that operates below the laters. Basically, this would just be a fancy version of subtyping though.
      - use subtyping, by proving that it is a subtype of the core, and then folding that.
      - use the core, but have proved it once and for all.

    - maybe we also want to have the depth certificates here? *)
  (* This is loosing information by dropping potential [ShadowedLtype], so we should only do it when really necessary. *)
  Lemma stratify_ltype_shared {rt} π E L mu mdu ma {M} (ml : M) l (lt lt' : ltype rt) κ (r : place_rfn rt) `{Hsimp : !SimpLtype (ltype_core lt) lt'} (T : stratify_ltype_cont_t):
    (cast_ltype_to_type E L lt' (λ ty', T L True _ (◁ ty')%I (r)))
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r (Shared κ) T.
  Proof.
    destruct Hsimp as [<-].
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    iDestruct "HT" as "(%ty & %Heq & HT)".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heq.
    iPoseProof (ltype_own_shared_to_core with "Hl") as "Hl".
    iDestruct ("Heq" $! (Shared κ) r) as "((%Hsteq & #Hinc & _) & _)".
    iPoseProof ("Hinc" with "Hl") as "Hl".
    iExists L, _, _, _, _. iFrame.
    iModIntro. iSplitR. { simp_ltypes. done. }
    iApply logical_step_intro. iSplitL; done.
  Qed.
  Global Instance stratify_ltype_shared_inst1 {rt} π E L mu mdu {M} (ml : M) l (lt lt' : ltype rt) κ (r : place_rfn rt) `{!SimpLtype (ltype_core lt) lt'} :
    StratifyLtype π E L mu mdu StratRefoldFull ml l lt r (Shared κ) | 100 :=
    λ T, i2p (stratify_ltype_shared π E L mu mdu StratRefoldFull ml l lt lt' κ r T).
  (* TODO needed? *)
  (*Global Instance stratify_ltype_shared_inst2 {rt} π E L mu mdu {M} (ml : M) l (lt : ltype rt) κ (r : place_rfn rt) :*)
    (*StratifyLtype π E L mu mdu StratRefoldOpened ml l lt r (Shared κ) | 100 :=*)
    (*λ T, i2p (stratify_ltype_shared π E L mu mdu StratRefoldOpened ml l lt κ r T).*)

  Lemma stratify_ltype_ofty_shr {rt} π E L mu ma {M} (ml : M) l (ty : type rt) κ (r : place_rfn (place_rfn rt)) b T :
    stratify_ltype π E L mu StratDoUnfold ma ml l (ShrLtype (◁ ty) κ) r b T
    ⊢ stratify_ltype π E L mu StratDoUnfold ma ml l (◁ (shr_ref κ ty)) r b T.
  Proof.
    iIntros "Hp". iApply stratify_ltype_eqltype; iFrame.
    iPureIntro. iIntros (?) "HL CTX HE".
    iApply ltype_eq_sym. iApply shr_ref_unfold.
  Qed.
  Definition stratify_ltype_ofty_shr_inst := [instance @stratify_ltype_ofty_shr].
  Global Existing Instance stratify_ltype_ofty_shr_inst | 30.
End stratify.
