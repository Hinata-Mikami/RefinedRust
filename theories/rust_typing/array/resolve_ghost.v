From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** * Iterated version of resolve_ghost for arrays *)

Section resolve_ghost.
  Context `{!typeGS Σ}.

  (* TODO phrase this with fold_list instead *)
  (* Iteration is controlled by refinement [rs] *)
  Definition resolve_ghost_iter_cont_t rt : Type := llctx → list (place_rfn rt) → iProp Σ → bool → iProp Σ.
  Definition resolve_ghost_iter {rt} (π : thread_id) (E : elctx) (L : llctx) (rm : ResolutionMode) (lb : bool) (l : loc) (st : syn_type) (lts : list (ltype rt)) (b : bor_kind) (rs : list (place_rfn rt)) (ig : list nat) (i0 : nat) (T : resolve_ghost_iter_cont_t rt) : iProp Σ :=
    (∀ F : coPset,
      ⌜lftE ⊆ F⌝ -∗
      ⌜lft_userE ⊆ F⌝ -∗
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      ⌜length lts = (length rs)%nat⌝ -∗
      ([∗ list] i ↦ r; lt ∈ rs; lts, if decide ((i + i0) ∈ ig) then True else (l offsetst{st}ₗ (i + i0)) ◁ₗ[ π, b] r @ lt) ={F}=∗
      ∃ (L' : llctx) (rs' : list $ place_rfn rt) (R : iPropI Σ) (progress : bool),
      maybe_logical_step lb F (([∗ list] i ↦ r; lt ∈ rs'; lts, if decide ((i + i0) ∈ ig) then True else (l offsetst{st}ₗ (i + i0)) ◁ₗ[ π, b] r @ lt) ∗ R) ∗
      llctx_interp L' ∗ T L' rs' R progress).
  Class ResolveGhostIter {rt} (π : thread_id) (E : elctx) (L : llctx) (rm : ResolutionMode) (lb : bool) (l : loc) (st : syn_type) (lts : list (ltype rt)) (b : bor_kind) (rs : list (place_rfn rt)) (ig : list nat) (i0 : nat) : Type :=
    resolve_ghost_iter_proof T : iProp_to_Prop (resolve_ghost_iter π E L rm lb l st lts b rs ig i0 T).
  Global Hint Mode ResolveGhostIter + + + + + + + + + + + + + : typeclass_instances.

  Lemma resolve_ghost_iter_cons_not_ignored π E L rm lb l st {rt} (lts : list (ltype rt)) b (r : place_rfn rt) (rs : list (place_rfn rt)) ig (i0 : nat) T `{!CanSolve(i0 ∉ ig)} :
    (∃ lt lts', ⌜lts = lt :: lts'⌝ ∗
      resolve_ghost π E L rm lb (l offsetst{st}ₗ i0) lt b r (λ L2 r' R progress,
        resolve_ghost_iter π E L2 rm lb l st lts' b rs ig (S i0) (λ L3 rs2 R2 progress',
        T L3 (r' :: rs2) (R ∗ R2) (orb progress  progress'))))
    ⊢
    resolve_ghost_iter π E L rm lb l st lts b (r :: rs) ig i0 T.
  Proof.
    rename select (CanSolve _) into Helem.
    rewrite /CanSolve in Helem.
    iIntros "(%lt & %lts' & -> & HT)".
    iIntros (???) "#CTX #HE HL %Hlen (Hx & Hr)".
    rewrite decide_False; last done.
    iMod ("HT" with "[//] [//] CTX HE HL Hx") as "(%L2 & %r' & %R1 & %prog & Hs & HL & HT)".
    iMod ("HT" with "[//] [//] CTX HE HL [] [Hr]") as "Hx".
    { iPureIntro. simpl in *. lia. }
    { iApply (big_sepL2_impl with "Hr"). iModIntro. iIntros (??? ??) "Hx".
      rewrite !Nat.add_succ_r. rewrite -!Nat2Z.inj_add Nat.add_succ_r. done. }
    iDestruct "Hx" as "(%L3 & %rs' & %R2 & %prog' & Hs' & HL & HT)".
    iModIntro. iExists _, _, _, _. iFrame.
    iApply (maybe_logical_step_compose with "Hs").
    iApply (maybe_logical_step_compose with "Hs'").
    iApply maybe_logical_step_intro.
    iIntros "(Hx & $) (Hx2 & $)".
    simpl. rewrite decide_False; last done. iFrame "Hx2".
    iApply (big_sepL2_impl with "Hx"). iModIntro. iIntros (??? ??) "Hx".
      rewrite !Nat.add_succ_r. rewrite -!Nat2Z.inj_add Nat.add_succ_r. done.
  Qed.
  Global Instance resolve_ghost_iter_cons_not_ignored_inst π E L rm lb l st {rt} (lts : list (ltype rt)) b (r : place_rfn rt) rs ig i0 `{!CanSolve(i0 ∉ ig)}:
    ResolveGhostIter π E L rm lb l st lts b (r :: rs) ig i0 := λ T, i2p (resolve_ghost_iter_cons_not_ignored π E L rm lb l st lts b r rs ig i0 T).

  Lemma resolve_ghost_iter_cons_ignored π E L rm lb l st {rt} (lts : list (ltype rt)) b (r : place_rfn rt) (rs : list (place_rfn rt)) ig (i0 : nat) T `{!CanSolve(i0 ∈ ig)} :
    (∃ lt lts', ⌜lts = lt :: lts'⌝ ∗
      resolve_ghost_iter π E L rm lb l st lts' b rs ig (S i0) (λ L2 rs2 R progress,
        T L2 (r :: rs2) (R) (progress)))
    ⊢
    resolve_ghost_iter π E L rm lb l st lts b (r :: rs) ig i0 T.
  Proof.
    rename select (CanSolve _) into Helem.
    rewrite /CanSolve in Helem.
    iIntros "(%lt & %lts' & -> & HT)".
    iIntros (???) "#CTX #HE HL %Hlen (Hx & Hr)".
    iMod ("HT" with "[//] [//] CTX HE HL [] [Hr]") as "Hr".
    { iPureIntro. simpl in *. lia. }
    { iApply (big_sepL2_impl with "Hr"). iModIntro. iIntros (??? ??) "Hx".
      rewrite !Nat.add_succ_r. rewrite -!Nat2Z.inj_add Nat.add_succ_r. done. }
    iDestruct "Hr" as "(%L2 & %rs' & %R & %prog & Hs' & HL & HT)".
    iModIntro. iExists _, _, _, _. iFrame.
    iApply (maybe_logical_step_wand with "[] Hs'").
    iIntros "(Hx & $)".
    simpl. rewrite decide_True; last done. iR.
    iApply (big_sepL2_impl with "Hx"). iModIntro. iIntros (??? ??) "Hx".
      rewrite !Nat.add_succ_r. rewrite -!Nat2Z.inj_add Nat.add_succ_r. done.
  Qed.
  Global Instance resolve_ghost_iter_cons_ignored_inst π E L rm lb l st {rt} (lts : list (ltype rt)) b (r : place_rfn rt) rs ig i0 `{!CanSolve(i0 ∈ ig)}:
    ResolveGhostIter π E L rm lb l st lts b (r :: rs) ig i0 := λ T, i2p (resolve_ghost_iter_cons_ignored π E L rm lb l st lts b r rs ig i0 T).

  Lemma resolve_ghost_iter_nil π E L rm lb l st {rt} (lts : list (ltype rt)) b ig i0 T :
    T L [] True%I true
    ⊢ resolve_ghost_iter π E L rm lb l st lts b [] ig i0 T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL %Hlen".
    destruct lts; last done.
    iIntros "_". iModIntro.
    iExists _, _, _, _. iFrame.
    iApply maybe_logical_step_intro.
    iL. done.
  Qed.
  Global Instance resolve_ghost_iter_nil_inst π E L rm lb l st {rt} (lts : list (ltype rt)) b ig i0 :
    ResolveGhostIter π E L rm lb l st lts b [] ig i0 := λ T, i2p (resolve_ghost_iter_nil π E L rm lb l st lts b ig i0 T).
End resolve_ghost.

Global Hint Mode ResolveGhostIter + + + + + + + + + + + + + + + : typeclass_instances.
Global Typeclasses Opaque resolve_ghost_iter.


