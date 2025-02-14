From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def.
From refinedrust Require Import options.

(** [resolve_ghost] rules for mutable references *)

Section resolve_ghost.
  Context `{!typeGS Σ}.

  (** resolve_ghost *)
  Lemma resolve_ghost_mut_Owned {rt} π E L l (lt : ltype rt) γ rm lb κ wl T :
    find_observation (place_rfn rt * gname)%type γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L #r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Owned wl) (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & ? & %γ0 & %r'& Hrfn & ?)".
      simpl.
      iPoseProof (gvar_pobs_agree_2 with "Hrfn Hobs") as "%Heq". subst r.
      iModIntro. iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. do 2 iR. done.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_mut_owned_inst {rt} π E L l (lt : ltype rt) κ γ wl rm lb :
    ResolveGhost π E L rm lb l (MutLtype lt κ) (Owned wl) (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_mut_Owned π E L l lt γ rm lb κ wl T).

  Lemma resolve_ghost_mut_Uniq {rt} π E L l (lt : ltype rt) γ rm lb κ κ' γ' T :
    find_observation (place_rfn rt * gname)%type γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L #r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Uniq κ' γ') (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & ? & Hrfn & ?)".
      simpl.
      iPoseProof (Rel2_use_pobs with "Hobs Hrfn") as "(%r2 & Hobs & ->)".
      iModIntro. iExists _, _, _,_. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. done.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_mut_uniq_inst {rt} π E L l (lt : ltype rt) κ γ κ' γ' rm lb :
    ResolveGhost π E L rm lb l (MutLtype lt κ) (Uniq κ' γ') (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_mut_Uniq π E L l lt γ rm lb κ κ' γ' T).

  Lemma resolve_ghost_mut_shared {rt} π E L l (lt : ltype rt) γ rm lb κ κ' T :
    find_observation (place_rfn rt * gname)%type γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L #r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Shared κ') (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & %γ0 & %r'& Hrfn & ?)".
      simpl.
      iPoseProof (gvar_pobs_agree_2 with "Hrfn Hobs") as "%Heq". subst r.
      iModIntro. iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. do 2 iR. by iExists _.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_mut_shared_inst {rt} π E L l (lt : ltype rt) κ γ κ' rm lb :
    ResolveGhost π E L rm lb l (MutLtype lt κ) (Shared κ') (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_mut_shared π E L l lt γ rm lb κ κ' T).

End resolve_ghost.
