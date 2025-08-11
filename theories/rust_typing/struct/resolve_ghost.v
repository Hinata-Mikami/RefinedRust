From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.struct Require Import def.
From refinedrust Require Import options.

(** ** [resolve_ghost] instances for structs *)

Section resolve_ghost.
  Context `{!typeGS Σ}.

  (** resolve_ghost instances *)
  Lemma resolve_ghost_struct_Owned {rts} π E L l (lts : hlist ltype rts) sls γ wl rm lb T :
    find_observation ((plist place_rfnRT rts)) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L (PlaceIn $ r) True true
        end)
    ⊢ resolve_ghost π E L rm lb l (StructLtype lts sls) (Owned wl) (PlaceGhost γ) T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL Hl".
    iMod ("Ha" with "[//]") as "[(%r' & HObs & Ha) | (_ & Ha)]".
    - rewrite ltype_own_struct_unfold /struct_ltype_own.
      iDestruct "Hl" as "(%sl & ? & ? & ? & ? & ? & %rs & Hinterp & ?)".
      simpl. iPoseProof (gvar_pobs_agree_2 with "Hinterp HObs") as "#<-".
      iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_struct_unfold /struct_ltype_own.
      iExists _. by iFrame.
    - iExists _, _, _, _. iFrame.  iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition resolve_ghost_struct_Owned_inst := [instance @resolve_ghost_struct_Owned].
  Global Existing Instance resolve_ghost_struct_Owned_inst.

  Lemma resolve_ghost_struct_Uniq {rts} π E L l (lts : hlist ltype rts) sls γ rm lb κ γ' T :
    find_observation ((plist place_rfnRT rts)) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L (PlaceIn $ r) True true
        end)
    ⊢ resolve_ghost π E L rm lb l (StructLtype lts sls) (Uniq κ γ') (PlaceGhost γ) T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL Hl".
    iMod ("Ha" with "[//]") as "[(%r' & HObs & Ha) | (_ & Ha)]".
    - rewrite ltype_own_struct_unfold /struct_ltype_own.
      iDestruct "Hl" as "(%ly & ? & ? & ? & ? & ? & Hinterp & ?)".
      simpl.
      iPoseProof (Rel2_use_pobs with "HObs Hinterp") as "(%r2 & Hobs & ->)".
      iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_struct_unfold /struct_ltype_own.
      iExists _. iFrame. done.
    - iExists _, _, _, _. iFrame.  iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition resolve_ghost_struct_Uniq_inst := [instance @resolve_ghost_struct_Uniq].
  Global Existing Instance resolve_ghost_struct_Uniq_inst.

  Lemma resolve_ghost_struct_Shared {rts} π E L l (lts : hlist ltype rts) sls γ rm lb κ T :
    find_observation (plist place_rfnRT rts) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L (#r) True true
        end)
    ⊢ resolve_ghost π E L rm lb l (StructLtype lts sls) (Shared κ) (PlaceGhost γ) T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL Hl".
    iMod ("Ha" with "[//]") as "[(%r' & HObs & Ha) | (_ & Ha)]".
    - rewrite ltype_own_struct_unfold /struct_ltype_own.
      iDestruct "Hl" as "(%sl & ? & ? & ? & ? & %rs & Hinterp & ?)".
      simpl. iPoseProof (gvar_pobs_agree_2 with "Hinterp HObs") as "#<-".
      iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_struct_unfold /struct_ltype_own.
      iExists _. by iFrame.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition resolve_ghost_struct_Shared_inst := [instance @resolve_ghost_struct_Shared].
  Global Existing Instance resolve_ghost_struct_Shared_inst.

End resolve_ghost.
