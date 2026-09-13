From iris.proofmode Require Import rocq_tactics reduction string_ident.
From refinedrust.base Require Import programs value.
From refinedrust Require Import program_rules array.array automation.
From refinedrust Require Import options.


(** * Proofmode support for manual proofs *)

Section updateable.
  Context `{!typeGS Σ}.

  Definition updateable (E : elctx) (L : llctx) (f : frame_path) (T : llctx → iProp Σ) : iProp Σ :=
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L ={⊤}=∗
    ∃ L2, llctx_interp L2 ∗ T L2.
  Class Updateable (P : iProp Σ) := {
    updateable_E : elctx;
    updateable_L : llctx;
    updateable_f : frame_path;
    updateable_core : elctx → llctx → iProp Σ;
    updateable_prove E L : updateable E L updateable_f (λ L2, updateable_core E L2) -∗ updateable_core E L;
    updateable_eq : updateable_core updateable_E updateable_L ⊣⊢ P
  }.

  Lemma updateable_mono E L f T1 T2 :
    updateable E L f T1 -∗
    (∀ L, T1 L -∗ T2 L) -∗
    updateable E L f T2.
  Proof.
    iIntros "HT Hw".
    iIntros "#CTX #HE HL".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iSpecialize ("Hw" with "HT").
    iExists L2. by iFrame.
  Qed.
  Lemma updateable_intro E L f T :
    T L ⊢ updateable E L f T.
  Proof.
    iIntros "HT #CTX HE HL".
    iExists L. by iFrame.
  Qed.

  Lemma add_updateable P `{!Updateable P} :
    updateable updateable_E updateable_L updateable_f (λ L2, updateable_core updateable_E L2) ⊢ P.
  Proof.
    iIntros "HT".
    iApply updateable_eq.
    iApply updateable_prove.
    iApply (updateable_mono with "HT").
    eauto.
  Qed.

  Global Program Instance updateable_typed_val_expr E L f e T :
    Updateable (typed_val_expr E L f e T) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_f := f;
      updateable_core E L := typed_val_expr E L f e T;
  |}.
  Next Obligation.
    iIntros (_ _ ? e T E L).
    rewrite /typed_val_expr.
    iIntros "HT" (?) "#CTX #HE HL Hf Hc".
    iApply fupd_wpe. iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL Hf Hc").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.

  Global Program Instance updateable_typed_call E L f κs etys v (P : iProp Σ) vl tys destination normal unwind T U :
    Updateable (typed_call E L f κs etys v P vl tys destination normal unwind T U) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_f := f;
      updateable_core E L := typed_call E L f κs etys v P vl tys destination normal unwind T U;
  |}.
  Next Obligation.
    iIntros (? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?).
    rewrite /typed_call.
    iIntros "HT HP Ha".
    iIntros (Q Ψ Ψunwind) "#CTX #HE HL Hf Hc".
    iApply fupd_wps. iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "HP Ha CTX HE HL Hf Hc").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.


  Global Program Instance updateable_typed_stmt E L f s rf R U ϝ :
    Updateable (typed_stmt E L f s rf R U ϝ) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_f := f;
      updateable_core E L := typed_stmt E L f s rf R U ϝ;
  |}.
  Next Obligation.
    iIntros (_ _ ? ? ? ? ? ? E L).
    iIntros "HT". rewrite /typed_stmt.
    iIntros (Φ Φunwind) "#CTX #HE HL Hf Hcont".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL Hf Hcont").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.

  Global Program Instance updateable_updateable E L f T :
    Updateable (updateable E L f T) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_f := f;
      updateable_core E L := updateable E L f T;
    |}.
  Next Obligation.
    iIntros (_ _ ? ? ? ?) "HT".
    rewrite /updateable.
    iIntros "#CTX #HE HL".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL").
  Qed.
  Next Obligation.
    eauto.
  Qed.

  Lemma fupd_typed_val_expr `{!typeGS Σ} E L f e T :
    (|={⊤}=> typed_val_expr E L f e T) -∗ typed_val_expr E L f e T.
  Proof.
    rewrite /typed_val_expr.
    iIntros "HT" (?) "CTX HE HL Hf Hc".
    iApply fupd_wpe. iMod ("HT") as "HT". iApply ("HT" with "CTX HE HL Hf Hc").
  Qed.
  Lemma fupd_typed_call `{!typeGS Σ} E L f κs etys v (P : iProp Σ) vl tys destination normal unwind T U :
    (|={⊤}=> typed_call E L f κs etys v P vl tys destination normal unwind T U) -∗
    typed_call E L f κs etys v P vl tys destination normal unwind T U.
  Proof.
    rewrite /typed_call.
    iIntros "HT HP Ha".
    iIntros (Q Ψ Ψunwind) "CTX HE HL Hf Hc".
    iApply fupd_wps. iMod ("HT") as "HT". iApply ("HT" with "HP Ha CTX HE HL Hf Hc").
  Qed.

  Lemma fupd_typed_stmt `{!typeGS Σ} E L f s rf R U ϝ :
    ⊢ (|={⊤}=> typed_stmt E L f s rf R U ϝ) -∗ typed_stmt E L f s rf R U ϝ.
  Proof.
    iIntros "HT". rewrite /typed_stmt. iIntros (Φ Φunwind) "CTX HE HL Hf Hcont".
    iMod ("HT") as "HT". iApply ("HT" with "CTX HE HL Hf Hcont").
  Qed.
End updateable.

Section updateable_rules.
  Context `{!typeGS Σ} {P} `{!Updateable P}.

  Lemma updateable_add_fupd :
    (|={⊤}=> updateable_core updateable_E updateable_L)
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "CTX HE HL".
    iMod "HT" as "$". by iFrame.
  Qed.

  (** Access an array element, moving its ownership out *)
  Lemma updateable_typed_array_access l off st :
    find_in_context (FindLoc l) (λ '(existT _ (lt, r, k, π)),
      typed_array_access π updateable_E updateable_L l off st lt r k (λ L2 rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        l ◁ₗ[π, k2] #rs2 @ ArrayLtype ty2 len2 iml2 -∗
        (l offsetst{st}ₗ off) ◁ₗ[π, k2] re @ lte -∗
        updateable_core updateable_E L2))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context/=.
    iDestruct "HT" as ([rt [[[lt r] k] π]]) "(Ha & Hb)".
    rewrite /typed_array_access.
    iMod ("Hb" with "[] [] [] CTX HE HL Ha") as "(%L2 & %k2 & %rt2 & %ty2 & %len & %iml & %rs2 & %rte & %re & %lte & Hl & He & HL & HT)";
    [set_solver.. | ].
    iPoseProof ("HT" with "Hl He") as "Ha".
    iModIntro. iExists _. iFrame.
  Qed.

  (** Forget an observation *)
  Lemma updateable_forget_observation l :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ ty γ, ⌜lt = ◁ty⌝ ∗ ⌜r = 👻 γ⌝ ∗
      (∀ r, l ◁ₗ[π, bk] #r @ (◁ ty) -∗
        updateable_core updateable_E updateable_L))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & Hb)"; simpl.
    iDestruct "Hb" as "(%ty & %γ & -> & -> & HT)".
    iPoseProof (ltype_own_ofty_forget_obs with "Ha") as "(% & Ha)".
    iPoseProof ("HT" with "Ha") as "HT".
    iModIntro. iExists _. iFrame.
  Qed.

  (* Extract an untyped value *)
  Lemma updateable_extract_untyped_value l :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ ty r', ⌜bk = Owned⌝ ∗ ⌜lt = ◁ty⌝ ∗ ⌜r = #r'⌝ ∗
      (∀ v3, v3 ◁ᵥ{π, MetaNone} r' @ ty -∗
        l ◁ₗ[π, Owned] #v3 @ (◁ value_t false (ty.(ty_syn_type) MetaNone)) -∗
        updateable_core updateable_E updateable_L))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & Hb)"; simpl.
    iDestruct "Hb" as "(%ty & %r' & -> & -> & -> & HT)".
    iMod (ofty_own_split_value_untyped with "Ha") as "Ha"; [done.. | ].
    iDestruct "Ha" as "(%v & Hv & Hl)".
    iPoseProof ("HT" with "Hv Hl") as "HT".
    iModIntro. iExists _. iFrame.
  Qed.

  (* Extract a typed value *)
  Lemma updateable_extract_typed_value l :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ ty r', ⌜bk = Owned⌝ ∗ ⌜lt = ◁ty⌝ ∗ ⌜r = #r'⌝ ∗
      find_tc_inst (TySized ty) (λ _,
      ⌜ty_allows_reads ty⌝ ∗
      (∀ v3, v3 ◁ᵥ{π, MetaNone} r' @ ty -∗
        l ◁ₗ[π, Owned] #v3 @ (◁ value_t true (st_of ty MetaNone)) -∗
        updateable_core updateable_E updateable_L)))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & Hb)"; simpl.
    iDestruct "Hb" as "(%ty & %r' & -> & -> & -> & %Hsz & %Hot & HT)".
    iMod (ofty_own_split_value_typed with "Ha") as "Ha"; [done.. | ].
    iDestruct "Ha" as "(%v & Hv & Hl)".
    iPoseProof ("HT" with "Hv Hl") as "HT".
    iModIntro. iExists _. iFrame.
  Qed.

  (** Merge a value *)
  Lemma updateable_merge_typed_value l :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ v st,
        ⌜bk = Owned⌝ ∗
        owned_subltype_step π updateable_E updateable_L false l r (#v) lt (◁ value_t true st)
        (λ L2 R2,
        find_in_context (FindVal v) (λ '(existT rt (ty', r', π', m')),
        ⌜π' = π⌝ ∗ ⌜m' = MetaNone⌝ ∗
        find_tc_inst (TySized ty') (λ _,
        ⌜ty_has_op_type ty' (use_op_alg' (ty'.(ty_syn_type) MetaNone)) ⌝ ∗
        ⌜ty'.(ty_syn_type) MetaNone = st⌝ ∗
        introduce_with_hooks updateable_E L2 ((l ◁ₗ[π, Owned] #r' @ ◁ ty') ∗ R2)%I (λ L3,
          updateable_core updateable_E L3)))))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & %v & %st & -> & HT)"; simpl.
    rewrite /owned_subltype_step/subsume_full.
    iMod ("HT" with "[] [] [] CTX HE HL Ha") as "(%L2 & %R2 & >(Hl & HR) & HL & HT)"; [done.. | ].
    iDestruct "HT" as ([rt' [[[ty' r'] π'] m']]) "(Hv & -> & -> & % & %Hot & %Heq & HT)" => /=.
    iPoseProof (ltype_own_has_layout with "Hl") as "#(%ly & %Hst &_)".
    subst st.
    iPoseProof (ofty_own_merge_value_typed with "Hv Hl") as "Ha".
    { done. }
    rewrite /introduce_with_hooks.
    iMod ("HT" with "[] CTX HE HL [$Ha $HR]") as "(%L3 & HL & HT)"; first done.
    by iFrame.
  Qed.

  (** Split an into two parts *)
  Lemma updateable_split_array l (k : nat) :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
    ∃ rt', ⌜rt = listRT (place_rfnRT rt')⌝ ∗
      ∃ rs n (ty : type rt'),
        ⌜bk = Owned⌝ ∗
        owned_subltype_step π updateable_E updateable_L false l r (#rs) lt (◁ array_t n ty) (λ L2 R2,
        ⌜k ≤ n⌝ ∗
        ((l ◁ₗ[π, Owned] #(take k rs) @ (◁ array_t k ty) -∗
         (l offsetst{st_of ty MetaNone}ₗ k) ◁ₗ[π, Owned] #(drop k rs) @ (◁ array_t (n - k) ty) -∗
         introduce_with_hooks updateable_E L2 R2 (λ L3,
          updateable_core updateable_E L3)))))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & %rt' & -> & %rs & %n & %ty & -> & HT)"; simpl.
    rewrite /owned_subltype_step/subsume_full.
    iMod ("HT" with "[] [] [] CTX HE HL Ha") as "(%L2 & %R2 & >(Hl & HR) & HL & %Hlt & HT)"; [done.. | ].
    iMod (array_t_ofty_split _ _ _ k (n - k) with "Hl") as "(Hl1 & Hl2)"; [done | lia | ].
    unfold introduce_with_hooks.
    iPoseProof  ("HT" with "Hl1 Hl2 [//] CTX HE HL HR") as "HT".
    iMod (fupd_mask_mono with "HT") as "(%L3 & HL & HT)"; first done.
    by iFrame.
  Qed.

  (** Reshape an array *)
  Lemma updateable_reshape_array l num size :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ rt', ⌜rt = listRT (place_rfnRT rt')⌝ ∗
      ∃ rs n (ty : type rt'),
        ⌜bk = Owned⌝ ∗
        owned_subltype_step π updateable_E updateable_L false l r (#rs) lt (◁ array_t n ty) (λ L2 R2,
        ⌜n = (num * size)%nat⌝ ∗
        ⌜num ≠ 0%nat⌝ ∗
        (l ◁ₗ[π, Owned] #(<#> reshape (replicate num size) rs) @ (◁ array_t num (array_t size ty)) -∗
         introduce_with_hooks updateable_E L2 R2 (λ L3,
          updateable_core updateable_E L3))))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & %rt' & -> & %rs & %n & %ty & -> & HT)"; simpl.
    rewrite /owned_subltype_step/subsume_full.
    iMod ("HT" with "[] [] [] CTX HE HL Ha") as "(%L2 & %R2 & >(Hl & HR) & HL & -> & % & HT)"; [done.. | ].
    iMod (array_t_ofty_reshape _ _ _ _ _ _ size num with "Hl") as "Hl"; [done | lia | lia | ].
    unfold introduce_with_hooks.
    iPoseProof  ("HT" with "Hl [//] CTX HE HL HR") as "HT".
    iMod (fupd_mask_mono with "HT") as "(%L3 & HL & HT)"; first done.
    by iFrame.
  Qed.


  (** Subtype a location to a given place type *)
  Lemma updateable_subsume_to l {rt2} (lt2 : ltype rt2) (r2 : place_rfn rt2) :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ⌜bk = Owned⌝ ∗
      owned_subltype_step π updateable_E updateable_L false l r r2 lt lt2 (λ L2 R2,
        introduce_with_hooks updateable_E L2 (l ◁ₗ[π, Owned] r2 @ lt2 ∗ R2) (λ L3,
          updateable_core updateable_E L3)))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & -> & Hb)"; simpl.
    rewrite /owned_subltype_step/subsume_full.
    iMod ("Hb" with "[] [] [] CTX HE HL Ha") as "(%L2 & %R2 & Hs & HL & HT)"; [done.. | ].
    simpl. iMod "Hs" as "Hs".
    rewrite /introduce_with_hooks.
    iMod ("HT" with "[] CTX HE HL Hs") as "(%L3 & HL & HT)"; first done.
    by iFrame.
  Qed.

  Lemma updateable_subsume_uninit_to l (st : syn_type) :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ⌜bk = Owned⌝ ∗
      owned_subltype_step π updateable_E updateable_L false l r (PlaceIn ()) lt (◁ uninit st) (λ L2 R2,
        introduce_with_hooks updateable_E L2 (l ◁ₗ[π, Owned] .@ (◁ uninit st) ∗ R2) (λ L3,
          updateable_core updateable_E L3)))
    ⊢ P.
  Proof.
    iApply updateable_subsume_to.
  Qed.

  (* TODO: add lemma for unfolding / subtyping? *)


  Lemma updateable_copy_lft n1 n2 :
    (∃ M, named_lfts updateable_f M ∗
      li_tactic (compute_list_map_lookup_nofail_goal M n2) (λ κ2,
      li_tactic (simplify_lft_map_goal ((n1, κ2) :: (map_list_delete M n1))) (λ M',
        named_lfts updateable_f M' -∗ updateable_core updateable_E updateable_L)))
    ⊢ P.
  Proof.
    rewrite /compute_list_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ2 & _ & Hs)".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    unfold simplify_lft_map_goal. iDestruct "Hs" as "(%M' & _ & Hs)".
    iModIntro. iExists updateable_L.
    iFrame. iApply ("Hs" with "Hnamed").
  Qed.

  Lemma updateable_strip_guards :
    iterate_with_hooks updateable_E updateable_L StripGuarded (λ L _,
      updateable_core updateable_E L)
    ⊢ P.
  Proof.
    iIntros "HT". unshelve iApply add_updateable; first apply _.
    iIntros "#CTX HE HL".
    unfold iterate_with_hooks.
    iMod ("HT" with "[] CTX HE HL") as "(%L2 & % & HL & Ha)"; first done.
    by iFrame.
  Qed.

  (** Discard the opened invariant on an owned location, removing the obligation to re-establish the invariant *)
  Lemma opened_owned_discard (rt_cur rt_inner rt_full : RT) (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Pre Post π l r :
    l ◁ₗ[π, Owned] r @ OpenedLtype lt_cur lt_inner lt_full Pre Post -∗
    l ◁ₗ[π, Owned] r @ lt_cur.
  Proof.
    rewrite ltype_own_opened_unfold.
    iIntros "(%ly & % & % & ? & % & % & Hcur & _)".
    done.
  Qed.

End updateable_rules.

Ltac add_updateable :=
  match goal with
  | |- envs_entails _ ?P =>
      unshelve notypeclasses refine (tac_fast_apply (add_updateable P) _);
      [ apply _ | apply _ | ]
  end.
Tactic Notation "apply_update" uconstr(H) :=
  unshelve refine (tac_fast_apply H _);
  [apply _ .. | ].

Section test.
  Context `{!typeGS Σ}.

  Lemma updateable_updateable_b E L f (l : loc) (off : Z) (st : syn_type) :
    ⊢ updateable E L f (λ _, True).
  Proof.
    iStartProof.
    add_updateable.
    add_updateable.
    unshelve iApply (updateable_typed_array_access l off st).
    idtac.
  Abort.

  Lemma typed_s_updateable E L f s rf R U ϝ (l : loc) (off : Z) (st : syn_type) :
    ⊢ typed_stmt E L f s rf R U ϝ.
  Proof.
    iStartProof.
    unshelve apply_update (updateable_typed_array_access l off st).
    idtac.
  Abort.
End test.

From refinedrust.primitive Require Import mutual_fixpoint existentials.

Section extra_rules.
  Context `{!typeGS Σ}.

  Lemma ltype_own_mut_fixpoint_unfold {rts : list RT} (F : mut_type_fun rts)
      `{Hne : !TCNoResolve (MutTypeNonExpansive F)}
      `{Hcontr : !TCNoResolve (MutTypeContractive (mut_iter F (length rts)))}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      {rt : RT} `{!Inhabited (RT_xt rt)} (i : nat)
      (Hlook : rts !! i = Some rt) π l (r : rt) :
    l ◁ₗ[π, Owned] #r @ ◁ (mut_type_project_simpl
      (F (mut_fixpoint F (Hne := Hne) (Hcontr := Hcontr))) i Hlook) -∗
    l ◁ₗ[π, Owned] #r @ ◁
      (mut_type_project (mut_fixpoint F (Hne := Hne) (Hcontr := Hcontr)) i Hlook).
  Proof.
    iIntros "Hl".
    iPoseProof (mut_type_project_fixpoint_subtype_2 F i Hlook [] [] r 1%Qp) as "Hsub".
    iSpecialize ("Hsub" with "[]").
    { rewrite /llctx_interp_noend. done. }
    iSpecialize ("Hsub" with "[]").
    { rewrite /elctx_interp. done. }
    iDestruct "Hsub" as "(%Hst & #Hincl)".
    iDestruct "Hincl" as "(#Hsc & #Hown & _)".
    iApply (type_ltype_incl_owned_in_strong with "Hown Hsc Hl").
    rewrite Hst. apply syn_type_compat_refl.
  Qed.

  Lemma ltype_own_ex_plain_t_intro {X Y : RT} (P : ex_inv_def X Y)
      (ty : type X) π l (x : Y) :
    (∃ r, P.(inv_P) π r x ∗ l ◁ₗ[π, Owned] #r @ ◁ ty) -∗
    l ◁ₗ[π, Owned] #x @ ◁ (ex_plain_t X Y P ty).
  Proof.
    iIntros "(%r & Hinv & Hl)".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as (ly Hst) "(Hly & Hsc & Hlb & %r' & -> & Hl)".
    iExists ly. iSplitR.
    { iPureIntro. exact Hst. }
    iFrame.
    iExists x. iSplitR; first done.
    iMod "Hl" as (v) "(Hl & Hv)".
    iModIntro. iExists v. iFrame "Hl".
    rewrite ex_plain_t_unfold_val.
    iExists r'. iFrame.
  Qed.

  (* TODO: ideally, we could do this anytime, not just at prove_with_subtype, by using logical_step receipts. *)
  Lemma prove_with_subtype_stratify l E L pm Q A T :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      stratify_ltype_unblock π E L StratRefoldFull l lt r bk (λ L2 R rt' lt' r',
      cast_ltype_to_type E L2 lt' (λ ty,
        prove_with_subtype E L2 true pm (l ◁ₗ[π, bk] r' @ (◁ ty) -∗ R -∗ Q) A T)))
    ⊢ prove_with_subtype E L true pm Q A T.
  Proof.
    unfold find_in_context,FindLoc. simpl.
    iIntros "(%x & Ha)".
    destruct x as [rt (((lt & r) & bk) & π)].
    iDestruct "Ha" as "(Hl & HT)".
    rewrite /prove_with_subtype.
    iIntros (?????) "#CTX #HE HL HA".
    rewrite /stratify_ltype_unblock/stratify_ltype.
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt' & %lt' & %r' & HL & %Hst' & Hstep & HT)".
    rewrite /cast_ltype_to_type.
    iDestruct "HT" as "(%ty & %Heqt & HT)".
    iPoseProof (full_eqltype_use F with "CTX HE HL") as "(Hincl & HL)"; first done; first apply Heqt.
    iMod ("HT" with "[//] [//] [//] CTX HE HL HA") as "(%L3 & %κs2 & %R' & Hstep' & HL & HT)".
    simpl. iFrame.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_wand with "Hstep'").
    iModIntro. iIntros "($ & Ha & $) (Hl & HR)".
    destruct pm.
    - iMod ("Hincl" with "Hl") as "Hl". iApply ("Ha" with "[$] [$]").
    - iMod ("Hincl" with "Hl") as "Hl". iModIntro.
      iIntros "Hdead". iMod ("Ha" with "Hdead") as "Ha".
      iModIntro. iApply ("Ha" with "[$] [$]").
  Qed.

  Lemma prove_with_subtype_inherit_manual E L step pm κ κ' P Q A T :
    lctx_lft_incl E L (lft_intersect_list κ') (lft_intersect_list κ) →
    Inherit κ' Q -∗
    (Q -∗ P) -∗
    T L [] A -∗
    prove_with_subtype E L step pm (Inherit κ P) A T.
  Proof.
    iIntros (Hi1) "Hinh HQP HT".
    rewrite /prove_with_subtype.
    iIntros (?????) "#CTX #HE HL HA".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl1"; first apply Hi1.
    (*iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl2"; first apply Hi2. *)
    iPoseProof (Inherit_mono with "Hincl1 Hinh") as "Hinh".
    iPoseProof (Inherit_update with "[HQP] Hinh") as "Hinh".
    { iIntros (?) "HQ". iApply ("HQP" with "HQ"). }
    iExists _, _, _. iFrame.
    iApply (maybe_logical_step_compose with "HA").
    iApply maybe_logical_step_intro.
    iModIntro. iIntros "($ & $)".
    destruct pm; iFrame. eauto.
  Qed.
End extra_rules.

Section credits.
  Context `{!typeGS Σ}.

  Lemma tac_credit_store_acquire_guard P :
    find_in_context FindCreditStore (λ '(n, m),
      ⌜fast_lia_hint (5 ≤ n)⌝ ∗
      ⌜fast_lia_hint (1 ≤ m)⌝ ∗
      (credit_store (n - 5) (m - 1) -∗ have_creds -∗ P))
    ⊢ P.
  Proof.
    rewrite /FindCreditStore/find_in_context/=.
    iIntros "(%p & Hstore & HT)". destruct p as [n m].
    unfold fast_lia_hint.
    iDestruct "HT" as "(% & % & HT)".
    iPoseProof (credit_store_scrounge 5 with "Hstore") as "(Hcred & Hstore)".
    { done. }
    iPoseProof (credit_store_scrounge_tr 1 with "Hstore") as "(Htr & Hstore)".
    { done. }
    iApply ("HT" with "Hstore").
    iFrame.
  Qed.

  Lemma tac_credit_store_acquire_one_credit P :
    find_in_context FindCreditStore (λ '(n, m),
      ⌜fast_lia_hint (1 ≤ n)⌝ ∗
      (credit_store (n - 1) (m) -∗ £1 -∗ P))
    ⊢ P.
  Proof.
    rewrite /FindCreditStore/find_in_context/=.
    iIntros "(%p & Hstore & HT)". destruct p as [n m].
    unfold fast_lia_hint.
    iDestruct "HT" as "(% & HT)".
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)".
    { done. }
    iApply ("HT" with "Hstore").
    iFrame.
  Qed.
End credits.
Tactic Notation "iAcquireCredits" "as" constr(H) :=
  iApply tac_credit_store_acquire_guard;
  repeat (liFindInContext || liSep || liSideCond);
  li_unfold_lets_in_context;
  iIntros "?";
  iIntros H.

Tactic Notation "iAcquireCredit" "as" constr(H) :=
  iApply tac_credit_store_acquire_one_credit;
  repeat (liFindInContext || liSep || liSideCond);
  li_unfold_lets_in_context;
  iIntros "?";
  iIntros H.


Lemma tac_typed_val_expr_bind' `{!typeGS Σ} E L f K e T :
  typed_val_expr E L f (W.to_expr e) (λ L' v m rt ty r,
    introduce_with_hooks E L' (v ◁ᵥ{f.1, m} r @ ty) (λ L2,
      typed_val_expr E L2 f (W.to_expr (W.fill K (W.Val v))) T)) -∗
  typed_val_expr E L f (W.to_expr (W.fill K e)) T.
Proof.
  iIntros "He".
  rewrite /typed_val_expr.
  iIntros (Φ) "#CTX #HE HL Hf Hcont".
  iApply tac_wpe_bind'.
  iApply ("He" with "CTX HE HL Hf").
  iIntros (L' v m rt ty r) "HL Hf Hv Hcont'".
  rewrite /introduce_with_hooks.
  iMod ("Hcont'" with "[] CTX HE HL Hv") as "(%L2 & HL & Hcont')"; first done.
  iApply ("Hcont'" with "CTX HE HL Hf"). done.
Qed.
Lemma tac_typed_val_expr_bind `{!typeGS Σ} E L f e Ks e' T :
  W.find_expr_fill e false = Some (Ks, e') →
  typed_val_expr E L f (W.to_expr e') (λ L' v m rt ty r,
    if Ks is [] then T L' v m rt ty r else
    introduce_with_hooks E L' (v ◁ᵥ{f.1, m} r @ ty) (λ L2,
      typed_val_expr E L2 f (W.to_expr (W.fill Ks (W.Val v))) T)) -∗
  typed_val_expr E L f (W.to_expr e) T.
Proof.
  move => /W.find_expr_fill_correct ->. move: Ks => [|K Ks] //.
  { auto. }
  move: (K::Ks) => {K}Ks. by iApply tac_typed_val_expr_bind'.
Qed.

Tactic Notation "typed_val_expr_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (typed_val_expr ?E ?L ?f ?e ?T) =>
    let e' := W.of_expr e in change (typed_val_expr E L f e T) with (typed_val_expr E L f (W.to_expr e') T);
    iApply tac_typed_val_expr_bind; [done |];
    unfold W.to_expr; simpl
  | _ => fail "typed_val_expr_bind: not a 'typed_val_expr'"
  end.

Lemma tac_typed_stmt_bind `{!typeGS Σ} E L f s e Ks fn ϝ T U :
  W.find_stmt_fill s = Some (Ks, e) →
  typed_val_expr E L f (W.to_expr e) (λ L' v m rt ty r,
    introduce_with_hooks E L' (v ◁ᵥ{f.1, m} r @ ty) (λ L2,
      typed_stmt E L2 f (W.to_stmt (W.stmt_fill Ks (W.Val v))) fn T U ϝ)) -∗
  typed_stmt E L f (W.to_stmt s) fn T U ϝ.
Proof.
  move => /W.find_stmt_fill_correct ->. iIntros "He".
  rewrite /typed_stmt.
  iIntros (Φ Φunwind) "#CTX #HE HL Hf Hcont".
  rewrite stmt_wp_eq. iIntros (Φ0 Φ0unwind rf ?) "Hresult".
  have [Ks' HKs']:= W.stmt_fill_correct Ks f.1 rf. rewrite HKs'.
  iApply wp_bind.
  rewrite /typed_val_expr.
  iApply wp_fupd.
  iAssert (WPe{f.1} W.to_expr e {{ λ v,
      |={⊤}=> WP fill Ks' (RTVal v) {{ runtime_post Φ0 Φ0unwind }} }})%I
      with "[He HL Hf Hcont Hresult]" as "He".
  { iApply ("He" with "CTX HE HL Hf").
    iIntros (L' v m rt ty r) "HL Hf Hv Htyped".
    rewrite /introduce_with_hooks.
    iMod ("Htyped" with "[] CTX HE HL Hv") as "(%L2 & HL & Htyped)"; first done.
    iModIntro.
    rewrite -(HKs' (W.Val _)) /W.to_expr.
    iSpecialize ("Htyped" with "CTX HE HL Hf Hcont").
    rewrite stmt_wp_eq/stmt_wp_def/=.
    iApply ("Htyped" $! Φ0 Φ0unwind rf with "[] Hresult"). done. }
  rewrite expr_wp_unfold.
  iApply (wp_wand with "He").
  iIntros ([v|]) "HWP" => /=; last done.
  iApply "HWP".
Qed.

Tactic Notation "typed_stmt_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (typed_stmt ?E ?L ?f ?s ?fn ?R ?U ?ϝ) =>
    let s' := W.of_stmt s in change (typed_stmt E L f s fn R U ϝ) with (typed_stmt E L f (W.to_stmt s') fn R U ϝ);
    iApply tac_typed_stmt_bind; [done |];
    unfold W.to_expr, W.to_stmt; simpl; unfold W.to_expr; simpl
  | _ => fail "typed_stmt_bind: not a 'typed_stmt'"
  end.

Lemma intro_typed_stmt `{!typeGS Σ} rf R U π f ϝ E L s Φ Φunwind :
  rrust_ctx -∗
  elctx_interp E -∗
  llctx_interp L -∗
  current_frame π f -∗
  (typed_stmt_post_cond (π, f) rf R Φ ∧
   typed_stmt_unwind_post_cond (π, f) rf U Φunwind) -∗
  typed_stmt E L (π, f) s rf R U ϝ -∗
  WPs{π} s {{ f_code (rf), Φ | Φunwind }}.
Proof.
  iIntros "#CTX #HE HL Hf Hcont Hs".
  rewrite /typed_stmt.
  iApply ("Hs" with "CTX HE HL Hf Hcont").
Qed.

Ltac to_typed_stmt SPEC :=
  iStartProof;
  lazymatch goal with
  | FN : function |- envs_entails _ (WPs{?π} ?s {{ ?code, ?c | ?cu }}) =>
    iApply (intro_typed_stmt FN with SPEC)
  end.
