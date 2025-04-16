From refinedrust Require Export type ltypes programs.
From refinedrust Require Import uninit int ltype_rules.
From lrust.lifetime Require Import na_borrow.
From refinedrust Require Import options.

Record na_ex_inv_def `{!typeGS Σ} (X : Type) (Y : Type) : Type := na_mk_ex_inv_def' {
  na_inv_xr : Type;
  na_inv_xr_inh : Inhabited na_inv_xr;
  na_inv_xrt : na_inv_xr → Y;

  (* NOTE: Make persistent part (Timeless) + non-persistent part inside &na *)
  na_inv_P : thread_id → X → Y → iProp Σ;

  na_inv_P_lfts : list lft;
  na_inv_P_wf_E : elctx;
}.

(* Stop Typeclass resolution for the [inv_P_pers] argument, to make it more deterministic. *)
Definition na_mk_ex_inv_def `{!typeGS Σ} {X Y : Type} (YR : Type) `{!Inhabited YR}
  (inv_xrt : YR → Y)

  (inv_P : thread_id → X → Y → iProp Σ)

  inv_P_lfts
  (inv_P_wf_E : elctx)

  := na_mk_ex_inv_def' _ _ _ _ _ _
       inv_xrt inv_P inv_P_lfts inv_P_wf_E.

Global Arguments na_inv_xr {_ _ _ _ _}.
Global Arguments na_inv_xrt {_ _ _ _ _}.
Global Arguments na_inv_P {_ _ _ _}.
Global Arguments na_inv_P_lfts {_ _ _ _}.
Global Arguments na_inv_P_wf_E {_ _ _ _}.

(** Smart constructor for persistent and timeless [P] *)
Program Definition na_mk_pers_ex_inv_def
  `{!typeGS Σ} {X : Type} {Y : Type}
  (YR : Type) `{!Inhabited YR} (xtr : YR → Y)
  (P : X → Y → iProp Σ) :=
    na_mk_ex_inv_def YR xtr (λ _, P) [] [] (* _ *).

Class NaExInvDefNonExpansive `{!typeGS Σ} {rt X Y : Type} (F : type rt → na_ex_inv_def X Y) : Type := {
  ex_inv_def_ne_lft_mor : DirectLftMorphism (λ ty, (F ty).(na_inv_P_lfts)) (λ ty, (F ty).(na_inv_P_wf_E));

  ex_inv_def_ne_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist n ty ty' →
      ∀ π x y,
        (F ty).(na_inv_P) π x y ≡{n}≡ (F ty').(na_inv_P) π x y;
}.

Class NaExInvDefContractive `{!typeGS Σ} {rt X Y : Type} (F : type rt → na_ex_inv_def X Y) : Type := {
  ex_inv_def_contr_lft_mor : DirectLftMorphism (λ ty, (F ty).(na_inv_P_lfts)) (λ ty, (F ty).(na_inv_P_wf_E));

  ex_inv_def_contr_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist2 n ty ty' →
      ∀ π x y,
        (F ty).(na_inv_P) π x y ≡{n}≡ (F ty').(na_inv_P) π x y;
}.

Section insts.
  Context `{!typeGS Σ}.

  Global Instance na_ex_inv_def_contractive_const {rt X Y} (v : na_ex_inv_def X Y) :
    NaExInvDefContractive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
  Qed.

  Global Instance na_ex_inv_def_ne_const {rt X Y} (v : na_ex_inv_def X Y) :
    NaExInvDefNonExpansive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
  Qed.

  (* TODO: instance for showing non-expansiveness from contractiveness *)

End insts.

Section na_ex.
  Context `{!typeGS Σ}.
  Context (X Y : Type) (P : na_ex_inv_def X Y).

  Program Definition na_ex_plain_t (ty : type X) : type Y := {|
    ty_xt := P.(na_inv_xr);
    ty_xrt := P.(na_inv_xrt);

    ty_own_val π r v := ∃ x : X, P.(na_inv_P) π x r ∗ ty.(ty_own_val) π x v;
    ty_shr κ π r l :=
      (* TODO: Add persistant part that cannot depends on the refined value *)
      ty.(ty_sidecond) ∗
      &na{κ, π, shrN.@l}(∃ x, l ↦: ty.(ty_own_val) π x ∗ P.(na_inv_P) π x r) ∗
      (∃ ly : layout, ⌜l `has_layout_loc` ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type ty) ly⌝);

    ty_syn_type := ty.(ty_syn_type);
    _ty_has_op_type ot mt := ty_has_op_type ty ot mt;
    ty_sidecond := ty.(ty_sidecond);

    _ty_lfts := P.(na_inv_P_lfts) ++ ty_lfts ty;
    _ty_wf_E := P.(na_inv_P_wf_E) ++ ty_wf_E ty;
  |}%I.

  (* ty_xt_inhabited *)
  Next Obligation.
    intros. apply P.
  Qed.

  (* ty_has_layout *)
  Next Obligation.
    iIntros (????) "(% & _ & ?)".
    by iApply ty_has_layout.
  Qed.

  (* _ty_op_type_stable *)
  Next Obligation.
    iIntros (????).
    by eapply ty_op_type_stable.
  Qed.

  (* ty_own_val_sidecond *)
  Next Obligation.
    iIntros (????) "(% & _ & ?)".
    by iApply ty_own_val_sidecond.
  Qed.

  (* ty_shr_sidecond *)
  Next Obligation.
    iIntros (?????) "($ & _ & _)".
  Qed.

  (* ty_shr_aligned *)
  Next Obligation.
    iIntros (?????) "(_ & _ & $)".
  Qed.

  (* ty_share *)
  Next Obligation.
    iIntros (ty E κ l ly π r q ?) "#(LFT & TIME & LLCTX) Htok %Halg %Hly Hlb Hbor".
    iEval (setoid_rewrite bi.sep_exist_l) in "Hbor".
    iEval (setoid_rewrite bi_exist_comm) in "Hbor".

    rewrite lft_intersect_list_app -!lft_tok_sep.
    iDestruct "Htok" as "(Htok & ? & ?)".

    iApply fupd_logical_step; iApply logical_step_intro.

    iPoseProof (bor_iff _ _ (∃ x: X, l ↦: ty_own_val ty π x ∗ P.(na_inv_P) π x r) with "[] Hbor") as "Hbor".
    { iNext. iModIntro. iSplit; [iIntros "(% & % & ? & ? & ?)" | iIntros "(% & (% & ? & ?) & ?)"]; eauto with iFrame. }

    iMod (bor_get_persistent _ (ty_sidecond ty) with "LFT [] Hbor Htok") as "(Hty & Hbor & Htok)"; first solve_ndisj.
    { iIntros "Hinv".
      iDestruct "Hinv" as (v) "((% & Hl & HP) & Hv)".
      iPoseProof (ty_own_val_sidecond with "HP") as "#>Hsc".
      iModIntro; iSplit; [iNext | done].
      iExists v; iFrame. }

    iMod (bor_na with "Hbor") as "Hbor"; first solve_ndisj.

    iModIntro; iFrame.
    iExists ly; eauto with iFrame.
  Qed.

  (* ty_shr_mono *)
  Next Obligation.
    iIntros (ty κ κ' π r l) "Hincl ($ & Hbor & %ly & ? & ?)".
    iSplitL "Hincl Hbor".
    - iApply (na_bor_shorten with "Hincl Hbor").
    - iExists ly. iFrame.
  Qed.

  (* _ty_memcast_compat *)
  Next Obligation.
    iIntros (ty ot mt st π r v Hot) "(%x & ? & Hv)".
    iPoseProof (ty_memcast_compat with "Hv") as "Hm"; first done.
    destruct mt; eauto with iFrame.
  Qed.
End na_ex.

Section contr.
  Context `{!typeGS Σ}.

  Global Instance na_ex_inv_def_contractive {rt X Y : Type}
    (P : type rt → na_ex_inv_def X Y)
    (F : type rt → type X) :
    NaExInvDefContractive P →
    TypeContractive F →
    TypeContractive (λ ty, na_ex_plain_t X Y (P ty) (F ty)).
  Proof.
    intros HP HF.
    constructor; simpl.
    - apply HF.
    - destruct HP as [Hlft _].
      destruct HF as [_ Hlft' _ _ _ _].
      apply ty_lft_morphism_of_direct.
      apply ty_lft_morphism_to_direct in Hlft'.
      simpl in *.
      rewrite ty_wf_E_unfold.
      rewrite ty_lfts_unfold.
      apply direct_lft_morphism_app; done.
    - rewrite ty_has_op_type_unfold. eapply HF.
    - simpl. eapply HF.
    - intros n ty ty' ?.
      intros π r v. rewrite /ty_own_val/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' Hd.
      intros ????. rewrite /ty_shr/=.
      do 1 f_equiv.
      { rewrite type_ctr_sidecond; first done.
        apply Hd. }
      f_equiv.
      { f_contractive. do 3 f_equiv.
        - do 4 solve_type_proper_step.
          eapply type_dist_later2_dist2; first done.
          unfold CanSolve. lia.
        - apply HP.
          eapply type_dist_later2_dist2; first done.
          unfold CanSolve. lia. }
      do 5 f_equiv.
      apply HF.
  Qed.

  Global Instance na_ex_inv_def_ne {rt X Y : Type}
    (P : type rt → na_ex_inv_def X Y)
    (F : type rt → type X)
    :
    NaExInvDefNonExpansive P →
    TypeNonExpansive F →
    TypeNonExpansive (λ ty, na_ex_plain_t X Y (P ty) (F ty)).
  Proof.
    intros HP HF.
    constructor; simpl.
    - apply HF.
    - destruct HP as [Hlft _].
      destruct HF as [_ Hlft' _ _ _ _].
      apply ty_lft_morphism_of_direct.
      apply ty_lft_morphism_to_direct in Hlft'.
      simpl in *.
      rewrite ty_wf_E_unfold.
      rewrite ty_lfts_unfold.
      apply direct_lft_morphism_app; done.
    - rewrite ty_has_op_type_unfold. intros.
      eapply HF; first done.
      rewrite ty_has_op_type_unfold. done.
    - simpl. eapply HF.
    - intros n ty ty' ?.
      intros π r v. rewrite /ty_own_val/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' Hd.
      intros ????. rewrite /ty_shr/=.
      do 1 f_equiv.
      { rewrite type_ne_sidecond; first done; apply Hd. }
      do 1 f_equiv.
      { f_contractive. do 3 f_equiv.
        - do 4 solve_type_proper_step.
          eapply type_dist2_dist; first done.
          unfold CanSolve. lia.
        - apply HP.
          eapply type_dist2_dist; first done.
          unfold CanSolve. lia. }
      do 5 f_equiv.
      apply HF. apply Hd.
  Qed.
End contr.

Notation "'∃na;' P ',' τ" := (na_ex_plain_t _ _ P τ) (at level 40) : stdpp_scope.

Section na_subtype.
  Context `{!typeGS Σ}.
  Context {rt X : Type} (P : na_ex_inv_def rt X).

  Lemma owned_subtype_na_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
    (prove_with_subtype E L false ProveDirect (P.(na_inv_P) π r r') (λ L1 _ R, R -∗ T L1))
    ⊢ owned_subtype π E L false r r' ty (∃na; P, ty) T.
  Proof.
    unfold owned_subtype, prove_with_subtype.

    (* Nothing has changed *)
    iIntros "HT".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
    iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
    iSplitR; last iSplitR.
    - simpl. iPureIntro.
      intros ly1 ly2 Hly1 HLy2. f_equiv. by eapply syn_type_has_layout_inj.
    - simpl. eauto.
    - iIntros (v) "Hv0".
      iEval (rewrite /ty_own_val/=).
      eauto with iFrame.
  Qed.

  Global Instance owned_subtype_na_ex_plain_t_inst π E L (ty : type rt) (r : rt) (r' : X) :
    OwnedSubtype π E L false r r' ty (∃na; P, ty) :=
    λ T, i2p (owned_subtype_na_ex_plain_t π E L ty r r' T).

  Lemma na_ex_plain_t_open_owned F π (ty : type rt) (wl : bool) (l : loc) (x : X) :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] PlaceIn x @ (◁ (∃na; P, ty)) ={F}=∗
    ∃ r : rt, P.(na_inv_P) π r x ∗
    l ◁ₗ[π, Owned false] PlaceIn r @ (◁ ty) ∗
    (∀ rt' (lt' : ltype rt') (r' : place_rfn rt'),
      l ◁ₗ[π, Owned false] r' @ lt' -∗
      ⌜ltype_st lt' = ty_syn_type ty⌝ -∗
      l ◁ₗ[π, Owned wl] r' @
        (OpenedLtype lt' (◁ ty) (◁ ∃na; P, ty)
          (λ (r : rt) (x : X), P.(na_inv_P) π r x)
          (λ r x, True)))%I.
  Proof.
    (* Nothing has changed *)
    iIntros (?) "Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & %x' & Hrfn & Hb)".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.

    unfold ty_own_val, na_ex_plain_t at 2.
    iDestruct "Hb" as "(%v & Hl & %r & HP & Hv)".

    iDestruct "Hrfn" as "<-".
    iModIntro. iExists r. iFrame.
    iSplitL "Hl Hv".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iFrame "#%". iSplitR; first done.
      iExists r. iSplitR; first done. iModIntro. eauto with iFrame. }

    iIntros (rt' lt' r') "Hb %Hst".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iExists ly. rewrite Hst.
    do 5 iR; iFrame.

    clear -Halg Hly.
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred' !>".
    iIntros (r' r'' κs) "HP".
    iSplitR; first done.
    iIntros "Hdead Hl".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & _ & _ & Hsc' & _ & _ & %r0 & -> & >Hb)".
    iDestruct "Hb" as "(%v' & Hl & Hv)".
    iMod ("HP" with "Hdead" ) as "HP".
    iModIntro.
    rewrite ltype_own_core_equiv. simp_ltypes.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly. simpl. iFrame "#%". by iFrame.
  Qed.

  Lemma typed_place_na_ex_plain_t_owned π E L l (ty : type rt) x wl bmin K T :
    (∀ r, introduce_with_hooks E L (P.(na_inv_P) π r x)
      (λ L2, typed_place π E L2 l
              (OpenedLtype (◁ ty) (◁ ty) (◁ (∃na; P, ty)) (λ (r : rt) (x : X), P.(na_inv_P) π r x) (λ r x, True))
              (#r) bmin (Owned wl) K
        (λ L2 κs li b2 bmin' rti ltyi ri mstrong,
          (* no weak update possible - after all, we have just opened this invariant *)
          T L2 κs li b2 bmin' rti ltyi ri (mk_mstrong mstrong.(mstrong_strong) None None))))
    ⊢ typed_place π E L l (◁ (∃na; P, ty))%I (#x) bmin (Owned wl) K T.
  Proof.
    unfold introduce_with_hooks, typed_place.

    (* Nothing has changed *)
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hincl Hb Hcont".
    iApply fupd_place_to_wp.
    iMod (na_ex_plain_t_open_owned with "Hb") as "(%r & HP & Hb & Hcl)"; first done.
    iPoseProof ("Hcl" with "Hb []") as "Hb"; first done.
    iMod ("HT" with "[] HE HL HP") as "(%L2 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] CTX HE HL Hincl Hb").
    iModIntro. iIntros (L' κs l2 b2 bmin0 rti ltyi ri [strong weak]) "Hincl Hl Hc".
    iApply ("Hcont" with "Hincl Hl").
    iSplit; last done.
    iDestruct "Hc" as "[Hc _]".
    destruct strong; last done.
    simp_ltypes. done.
  Qed.

  Global Instance na_typed_place_ex_plain_t_owned_inst π E L l (ty : type rt) x wl bmin K `{!TCDone (K ≠ [])} :
    TypedPlace E L π l (◁ (∃na; P, ty))%I #x bmin (Owned wl) K | 15 :=
    λ T, i2p (typed_place_na_ex_plain_t_owned π E L l ty x wl bmin K T).


  Lemma opened_na_ltype_acc_owned π {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost l wl r :
    l ◁ₗ[π, Owned wl] r @ OpenedNaLtype lt_cur lt_inner Cpre Cpost -∗
    l ◁ₗ[π, Owned false] r @ lt_cur ∗
    (∀ rt_cur' (lt_cur' : ltype rt_cur') r',
      l ◁ₗ[π, Owned false] r' @ lt_cur' -∗
      ⌜ltype_st lt_cur' = ltype_st lt_cur⌝ -∗
      l ◁ₗ[π, Owned wl] r' @ OpenedNaLtype lt_cur' lt_inner Cpre Cpost).
  Proof.
    (* Nothing has changed *)

    rewrite ltype_own_opened_na_unfold /opened_na_ltype_own.
    iIntros "(%ly & ? & ? & ? & ? & $ & Hcl)".
    iIntros (rt_cur' lt_cur' r') "Hown %Hst".
    rewrite ltype_own_opened_na_unfold /opened_ltype_own.
    iExists ly. rewrite Hst. eauto with iFrame.
  Qed.

  Lemma typed_place_opened_na_owned π E L {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost r bmin0 l wl P''' T :
    typed_place π E L l lt_cur r bmin0 (Owned false) P''' (λ L' κs l2 b2 bmin rti ltyi ri mstrong,
      T L' κs l2 b2 bmin rti ltyi ri
        (mk_mstrong
        (option_map (λ strong, mk_strong strong.(strong_rt)
          (λ rti2 ltyi2 ri2, OpenedNaLtype (strong.(strong_lt) _ ltyi2 ri2) lt_inner Cpre Cpost)
          (λ rti2 ri2, strong.(strong_rfn) _ ri2)
          strong.(strong_R)) mstrong.(mstrong_strong))
        (* no weak access possible -- we currently don't have the machinery to restore and fold invariants at this point, though we could in principle enable this *)
        None None))
    ⊢ typed_place π E L l (OpenedNaLtype lt_cur lt_inner Cpre Cpost) r bmin0 (Owned wl) P''' T.
  Proof.
    unfold introduce_with_hooks, typed_place.

    (* Nothing has changed *)
    iIntros "HT". iIntros (Φ F ??) "#CTX #HE HL #Hincl0 Hl HR".
    iPoseProof (opened_na_ltype_acc_owned with "Hl") as "(Hl & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL [] Hl").
    { destruct bmin0; done. }
    iIntros (L' ??????? [strong weak]) "? Hl Hv".
    iApply ("HR" with "[$] Hl").
    iSplit; last done.
    destruct strong as [ strong | ]; last done.
    iIntros (???) "Hl Hst".
    iDestruct "Hv" as "[Hv _]".
    iMod ("Hv" with "Hl Hst") as "(Hl & %Hst & $)".
    iPoseProof ("Hcl" with "Hl [//]") as "Hl".
    cbn. eauto with iFrame.
  Qed.

  Global Instance typed_place_opened_na_owned_inst π E L {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost r bmin0 l wl P :
    TypedPlace E L π l (OpenedNaLtype lt_cur lt_inner Cpre Cpost) r bmin0 (Owned wl) P | 5 :=
        λ T, i2p (typed_place_opened_na_owned π E L lt_cur lt_inner Cpre Cpost r bmin0 l wl P T).

  Lemma na_ex_plain_t_open_shared E F π (ty : type rt) q κ l (x : X) :
    lftE ⊆ E →
    ↑shrN.@l ⊆ E →
    (shr_locsE l 1 ⊆ F) →

    lft_ctx -∗
    na_own π F -∗
    £ 1 -∗ (* Required: P.(na_inv_P) is not Timeless *)

    q.[κ] -∗
    l ◁ₗ[π, Shared κ] (#x) @ (◁ (∃na; P, ty)) ={E}=∗

    ∃ r : rt,
      P.(na_inv_P) π r x ∗
      (l ◁ₗ[π, Owned false] (#r) @ (◁ ty)) ∗
      &na{κ,π,shrN.@l} (∃ r' : rt, l ↦: ty_own_val ty π r' ∗ na_inv_P P π r' x) ∗

      ( ∀ r' : rt,
          l ◁ₗ[π, Owned false] #r' @ (◁ ty) ∗ P.(na_inv_P) π r' x ={E}=∗
          q.[κ] ∗ na_own π F ).
  Proof.
    iIntros (???) "#LFT Hna Hcred Hq #Hb".
    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hb".
    iDestruct "Hb" as (ly Halg Hly) "(Hsc & Hlb & %v & -> & #Hb)".

    iMod (fupd_mask_mono with "Hb") as "#Hb'"; first done; iClear "Hb".
    iEval (unfold ty_shr, na_ex_plain_t) in "Hb'".
    iDestruct "Hb'" as "(Hscr & Hbor & %ly' & %Hly' & %Halg')".

    iMod (na_bor_acc with "LFT Hbor Hq Hna") as "((%r & Hl & HP) & Hna & Hvs)"; [ set_solver.. |].
    iApply (lc_fupd_add_later with "Hcred").

    do 2 iModIntro; iExists r; iFrame.

    iSplitL "Hl".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly => /=.
      iFrame (Halg Hly) "Hlb Hscr"; iR.
      iExists r; iR.
      by iModIntro. }

    iR; iIntros (r') "(Hl & HP)".
    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
    iDestruct "Hl" as (???) "(_ & _ & _ & (% & <- & Hl)) /=".
    iMod (fupd_mask_mono with "Hl") as "Hl"; first solve_ndisj.

    iApply ("Hvs" with "[Hl HP] Hna").
    iExists r'; iFrame.
  Qed.

  Lemma na_own_split π E E' :
    E' ⊆ E ->
    na_own π E -∗ na_own π E' ∗ na_own π (E ∖ E').
  Proof.
    iIntros (?) "Hna".
    rewrite comm.

    iApply na_own_union.
    { set_solver. }

    replace E with ((E ∖ E') ∪ E') at 1; first done.

    set_unfold.
    split; first intuition.
    destruct (decide (x ∈ E')); intuition.
  Qed.

  Lemma typed_place_na_ex_plain_t_shared π E L l (ty : type rt) x κ bmin K T :
    find_in_context (FindNaOwn) (λ '(π', mask),
      ⌜π = π'⌝ ∗
      ⌜↑shrN.@l ⊆ mask⌝ ∗
      prove_with_subtype E L false ProveDirect (£ 1) (λ L1 _ R, R -∗
        li_tactic (lctx_lft_alive_count_goal E L1 κ) (λ '(κs, L2),
          ∀ r, introduce_with_hooks E L2
            (P.(na_inv_P) π r x ∗
            l ◁ₗ[π, Owned false] (#r) @
              (OpenedNaLtype (◁ ty) (◁ ty)
                (λ rfn, P.(na_inv_P) π rfn x)
                (λ _, na_own π (↑shrN.@l) ∗ llft_elt_toks κs)) ∗
            na_own π (mask ∖ ↑shrN.@l))
            (λ L3,
              typed_place π E L3 l
                (ShadowedLtype (AliasLtype _ (ty_syn_type ty) l) #tt (◁ (∃na; P, ty)))
                (#x) (bmin ⊓ₖ Shared κ) (Shared κ) K
                (λ L4 κs li b2 bmin' rti ltyi ri mstrong,
                  T L4 κs li b2 bmin' rti ltyi ri (mk_mstrong mstrong.(mstrong_strong) None None))))))
    ⊢ typed_place π E L l (◁ (∃na; P, ty))%I (#x) bmin (Shared κ) K T.
  Proof.
    rewrite /find_in_context.
    iDestruct 1 as ([π' mask]) "(Hna & <- & % & HT) /=".

    rewrite /typed_place /introduce_with_hooks.
    iIntros (Φ ???) "#(LFT & TIME & LLCTX) #HE HL ? Hl Hcont".

    rewrite /prove_with_subtype.
    iApply fupd_place_to_wp.

    iMod ("HT" with "[] [] [] [$LFT $TIME $LLCTX] HE HL")
        as "(% & % & % & >(Hcred & HR) & HL & HT)"; [ done.. |].
    iSpecialize ("HT" with "HR").

    rewrite /li_tactic /lctx_lft_alive_count_goal.
    iDestruct "HT" as (???) "HT".

    iMod (fupd_mask_subseteq (lftE ∪ shrE)) as "Hf"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as (q) "(Htok & Htokcl & HL)"; [ solve_ndisj.. |].
    iPoseProof (na_own_split with "Hna") as "(Hna & Hna')"; first done.
    iMod (na_ex_plain_t_open_shared with "LFT Hna Hcred Htok Hl") as (r) "(HP & Hl & #Hbor & Hvs)"; [ try solve_ndisj.. |].

    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
    iDestruct "Hl" as (ly Halg Hly) "(#Hsc & #Hlb & _ & (% & <- & Hl))".

    iMod ("HT" with "[] HE HL [$HP Hl Htokcl Hvs Hna']") as "HT"; first solve_ndisj.
    { rewrite ltype_own_opened_na_unfold /opened_na_ltype_own.
      iFrame.
      iExists ly; repeat iR.

      iSplitL "Hl".
      { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly; repeat iR.
        by iExists r; iR. }

      iApply logical_step_intro.

      iIntros (r') "Hinv Hl".
      iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
      iDestruct "Hl" as (ly' Halg' Hly') "(_ & #Hlb' & _ & (% & <- & Hl))".

      iMod ("Hvs" with "[Hl Hinv]") as "(? & ?)".
      { iFrame.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly'; repeat iR.
        by iExists r'; iR. }

      iFrame.
      by iApply "Htokcl". }

    iDestruct "HT" as (?) "(HL & HT)".

    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] []").
    { iApply bor_kind_min_incl_r. }
    { rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.

      iR; iSplitL.
      { rewrite ltype_own_alias_unfold /alias_lty_own.
        iExists ly. by repeat iR. }

      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly; repeat iR.
      iExists x; repeat iR.

      rewrite /ty_shr /na_ex_plain_t.
      repeat iR.
      by iExists ly; repeat iR. }

    iMod "Hf" as "_".
    iIntros "!>" (? ? ? ? ? ? ? ? [strong weak]) "Hincl Hl [ Hstrong _ ]".

    iApply ("Hcont" with "Hincl Hl").
    destruct strong; iSplit; [| done.. ].
    by simp_ltypes.
  Qed.

  Global Instance typed_place_na_ex_plain_t_shared_inst π E L l (ty : type rt) x κ bmin K `{!TCDone (K ≠ [])} :
    TypedPlace E L π l (◁ (∃na; P, ty))%I #x bmin (Shared κ) K | 15 :=
    λ T, i2p (typed_place_na_ex_plain_t_shared π E L l ty x κ bmin K T).

  Lemma typed_place_alias_shared π E L l l2 rt''' (r : place_rfn rt''') st bmin0 κ P''' T :
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π = π2⌝ ∗
      typed_place π E L l2 lt2 r2 b2 b2 P''' (λ L' κs li b3 bmin rti ltyi ri mstrong,
        T L' κs li b3 bmin rti ltyi ri
          (mk_mstrong
          (fmap (λ strong, mk_strong (λ _, _) (λ _ _ _, AliasLtype rt''' st l2) (λ _ _, r)
            (* give back ownership through R *)
            (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) mstrong.(mstrong_strong))
          None None)))
    ⊢ typed_place π E L l (AliasLtype rt''' st l2) r bmin0 (Shared κ) P''' T.
  Proof.
    unfold find_in_context, typed_place.

    iDestruct 1 as ((rt2 & (((lt & r''') & b2) & π2))) "(Hl2 & <- & HP)". simpl.
    iIntros (????) "#CTX #HE HL #Hincl Hl Hcont".
    iEval (rewrite ltype_own_alias_unfold /alias_lty_own) in "Hl".
    iDestruct "Hl" as "(%ly & % & -> & #? & #?)".

    iApply ("HP" with "[//] [//] CTX HE HL [] Hl2").
    { iApply bor_kind_incl_refl. }
    iIntros (L' κs l2 b0 bmin rti ltyi ri [strong weak]) "#Hincl1 Hl2 Hcl HT HL".
    iApply ("Hcont" with "[//] Hl2 [Hcl] HT HL").

    iSplit; last done.

    destruct strong as [ strong |]; last done.
    iDestruct "Hcl" as "[Hcl _]"; simpl.

    iIntros (rti2 ltyi2 ri2) "Hl2 %Hst".
    iMod ("Hcl" with "Hl2 [//]") as "(Hl & % & Hstrong)".
    iModIntro.

    rewrite ltype_own_alias_unfold /alias_lty_own.
    iFrame. iSplit; [| done].
    iExists ly; by repeat iR.
  Qed.
  Global Instance typed_place_alias_shared_inst π E L l l2 rt r st bmin0 κ P :
    TypedPlace E L π l (AliasLtype rt st l2) r bmin0 (Shared κ) P :=
    λ T, i2p (typed_place_alias_shared π E L l l2 rt r st bmin0 κ P T).

  Lemma stratify_ltype_alias_shared π E L mu mdu ma {M} (m : M) l l2 rt''' st r κ (T : stratify_ltype_cont_t) :
    ( if decide (ma = StratNoRefold)
      then
        T L True _ (AliasLtype rt''' st l2) r
      else
        find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
          ⌜π = π2⌝ ∗ ⌜ltype_st lt2 = st⌝ ∗ ⌜b2 = Owned false⌝ ∗
          (* recursively stratify *)
          stratify_ltype π E L mu mdu ma m l2 lt2 r2 b2
            (λ L2 R rt2' lt2' r2',
               (T L2 ((l2 ◁ₗ[π, Owned false] r2' @ lt2') ∗ R) rt''' (AliasLtype rt''' st l2) r))))
    ⊢ stratify_ltype π E L mu mdu ma m l (AliasLtype rt''' st l2) r (Shared κ) T.
  Proof.
    rewrite /stratify_ltype /find_in_context.
    iIntros "HT".

    destruct (decide (ma = StratNoRefold)) as [-> | ].
    { iIntros (????) "#CTX #HE HL Hl". iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iApply logical_step_intro. by iFrame. }

    iDestruct "HT" as ([rt2 [[[lt2 r2] b2] π2]]) "(Hl2 & <- & <- & -> & HT)"; simpl.

    iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    simp_ltypes.

    iDestruct "Hl" as "(%ly & %Halg & -> & %Hly & Hlb)".

    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl2") as (L3 R rt2' lt2' r2') "(HL & %Hst & Hstep & HT)".
    iModIntro. iExists _, _, _, _, _.
    iFrame; iR.

    iApply (logical_step_compose with "Hstep").
    iApply logical_step_intro.
    iIntros "($ & $)".

    rewrite ltype_own_alias_unfold /alias_lty_own.
    by iExists ly; iFrame.
  Qed.
  Global Instance stratify_ltype_alias_shared_inst π E L mu mdu ma {M} (m : M) l l2 rt st r κ :
    StratifyLtype π E L mu mdu ma m l (AliasLtype rt st l2) r (Shared κ) :=
    λ T, i2p (stratify_ltype_alias_shared π E L mu mdu ma m l l2 rt st r κ T).

  Lemma stratify_ltype_opened_na_Owned {rt_cur rt_inner} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner)
      (Cpre Cpost : rt_inner → iProp Σ) r (T : stratify_ltype_cont_t) :
    stratify_ltype π E L mu mdu ma ml l lt_cur r (Owned false)
      (λ L' R rt_cur' lt_cur' (r' : place_rfn rt_cur'),
        if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R _ (OpenedNaLtype lt_cur' lt_inner Cpre Cpost) r'
        else (* fold the invariant *)
          ∃ ri,
            (* show that the core of lt_cur' is a subtype of lt_inner *)
            weak_subltype E L' (Owned false) (r') (#ri) lt_cur' lt_inner (
              (* re-establish the invariant *)
              prove_with_subtype E L' true ProveDirect (Cpre ri)
                (λ L'' _ R2, T L'' (Cpost ri ∗ R2 ∗ R) unit (AliasLtype unit (ltype_st lt_inner) l) #tt)))
    ⊢ stratify_ltype π E L mu mdu ma ml l (OpenedNaLtype lt_cur lt_inner Cpre Cpost) r (Owned false) T.
  Proof.
    rewrite /stratify_ltype /weak_subltype /prove_with_subtype.

    iIntros "Hstrat" (F ???) "#CTX #HE HL Hl".
    rewrite ltype_own_opened_na_unfold /opened_na_ltype_own.

    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hlb & %Hst & Hl & Hcl)".
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt_cur' & %lt_cur' & %r' & HL & %Hst' & Hstep & HT)".

    destruct (decide (ma = StratNoRefold)) as [-> | ].
    - (* don't fold *)
      iModIntro.
      iExists _, _, _, _, _; iFrame; iR.

      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro.
      iIntros "(Hl & $)".

      rewrite ltype_own_opened_na_unfold /opened_na_ltype_own.
      iExists ly; iFrame.
      rewrite -Hst'; do 3 iR.
      done.

    - (* fold it again *)
      iDestruct "HT" as "(%ri & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hincl & HL & HT)".
      iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L3 & %κs & %R2 & Hstep' & HL & HT)".

      iExists L3, _, _, _, _; iFrame.
      iSplitR.
      { by simp_ltypes. }

      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iPoseProof (logical_step_mask_mono with "Hcl") as "Hcl"; first done.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep'").
      iApply logical_step_intro.

      iIntros "!> (Hpre & $) Hcl (Hl & $)".
      iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.

      iPoseProof ("Hcl" with "Hpre Hl") as "Hvs".
      iSplitL "".
      { rewrite ltype_own_alias_unfold /alias_lty_own.
        rewrite -Hst.

        by iExists ly; repeat iR. }

      iMod (fupd_mask_mono with "Hvs") as "Hvs"; first set_solver.
      done.
  Qed.

  Global Instance stratify_ltype_opened_na_owned_inst {rt_cur rt_inner} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (Cpre Cpost : rt_inner → iProp Σ) r:
    StratifyLtype π E L mu mdu ma ml l (OpenedNaLtype lt_cur lt_inner Cpre Cpost) r (Owned false) := λ T, i2p (stratify_ltype_opened_na_Owned π E L mu mdu ma ml l lt_cur lt_inner Cpre Cpost r T).

End na_subtype.
