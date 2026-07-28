From refinedrust Require Export type lftmor.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import options.
Local Open Scope nat_scope.

(** * Array types *)

(** Design decisions:
  - our array's refinements are homogeneously typed.
  - we have a fixed capacity -- otherwise, we cannot define the syntype (it would be a dynamically sized type..)
  - the array does not own its deallocation permission -- because its value form is not a pointer type.
  - it is refined by a list (homogeneous), similarly for the ltype. (we could also refine the ltype by a vec - but that would make everything more complicated)
*)


Definition is_array_ot `{!typeGS Σ} {rt} (ty : type rt) (len : nat) (ot : op_type) : Prop :=
  match ot with
  | ArrayOp element_ot len' =>
      len' = len ∧
      ty_has_op_type ty element_ot ∧
      (ly_size (ot_layout element_ot) * len ≤ MaxInt ISize)%Z
  | UntypedOp ly =>
      syn_type_has_layout (ArraySynType (ty.(ty_syn_type) MetaNone) len) ly
  | _ => False
  end.
Global Typeclasses Opaque is_array_ot.

Lemma is_same_decoded_val_at_array_inv st v ot len v' :
  is_same_decoded_val_at st v (ArrayOp ot len) v' →
  Forall2 (λ v1 v2, is_same_decoded_val_at st v1 ot v2)
    (reshape (replicate len (ly_size (ot_layout ot))) v)
    (reshape (replicate len (ly_size (ot_layout ot))) v').
Proof.
  intros [Heq [ov Hdec]].
  pose proof (decode_op_val_has_layout _ _ _ _ Hdec) as Hly.
  assert (Hdec' : decode_op_val v' (ArrayOp ot len) st = Some ov) by congruence.
  pose proof (decode_op_val_has_layout _ _ _ _ Hdec') as Hly'.
  simp decode_op_val in Hdec, Hdec'.
  rewrite /has_layout_val in Hly, Hly'.
  rewrite bool_decide_true in Hdec; last done.
  rewrite bool_decide_true in Hdec'; last done.
  apply bind_Some in Hdec as (elements & Helements & Hov).
  apply bind_Some in Hdec' as (elements' & Helements' & Hov').
  injection Hov as <-. injection Hov' as <-.
  apply list_map_option_alt in Helements, Helements'.
  pose proof (Forall2_common_r _ _ _ _ Helements Helements') as Hsame.
  eapply Forall2_impl; first exact Hsame.
  intros x y (element & Hx & Hy). split; first congruence. eauto.
Qed.

Section array.
  Context `{!typeGS Σ}.
  Context {rt : RT}.

  Definition array_own_el_val (π : thread_id) (ty : type rt) (r : place_rfn rt) (v : val) : iProp Σ :=
    ∃ r', place_rfn_interp_owned r r' ∗ ty.(ty_own_val) π r' MetaNone v.

  Lemma array_own_el_val_decode_compat_list π (ty : type rt) ot st rs vs vs' :
    ty_has_op_type ty ot →
    length rs = length vs →
    Forall2 (λ v1 v2, is_same_decoded_val_at st v1 ot v2) vs vs' →
    ([∗ list] r;v ∈ rs;vs, array_own_el_val π ty r v) -∗
    [∗ list] r;v ∈ rs;vs', array_own_el_val π ty r v.
  Proof.
    intros Hot Hlen Hsame. induction Hsame as [|v1 v2 vs vs' Hsame Hrest IH]
      in rs, Hlen |-*.
    - destruct rs as [|r rs].
      + simpl. iIntros "_". done.
      + simpl in Hlen. lia.
    - destruct rs as [|r rs]; simpl in Hlen; first lia.
      simpl. iIntros "(Hv & Hvs)". iSplitL "Hv".
      + iDestruct "Hv" as "(%r' & Hrfn & Hv)". iExists r'. iFrame.
        by iApply (ty_decode_compat with "Hv").
      + iApply IH; first lia. done.
  Qed.

  Definition array_own_el_loc (π : thread_id) (q : Qp) (v : val) (i : nat) (ly : layout) (ty : type rt) (r : place_rfn rt) (l : loc) : iProp Σ :=
    ∃ r', (l offset{ly}ₗ i) ↦{q} v ∗ place_rfn_interp_owned r r' ∗ ty.(ty_own_val) π r' MetaNone v.
  Definition array_own_el_shr (π : thread_id) (κ : lft) (i : nat) (ly : layout) (ty : type rt) (r : place_rfn rt) (l : loc) : iProp Σ :=
    ∃ r', place_rfn_interp_shared r r' ∗ ty.(ty_shr) κ π r' MetaNone (offset_loc l ly i).

  Lemma array_own_val_join_pointsto (π : thread_id) (q : Qp) vs ly (ty : type rt) rs l len  :
    len = length rs →
    vs `has_layout_val` mk_array_layout ly len →
    l ↦{q} vs -∗
    ([∗ list] r;v ∈ rs;reshape (replicate len (ly_size ly)) vs, array_own_el_val π ty r v) -∗
    ([∗ list] i↦r ∈ rs, ∃ v : val, array_own_el_loc π q v i ly ty r l).
  Proof.
    intros ->.
    iIntros (Hvs) "Hl Ha".
    set (szs := replicate (length rs) (ly_size ly)).
    assert (length rs = length (reshape szs vs)).
    { subst szs. rewrite length_reshape length_replicate //. }
    rewrite -{1}(join_reshape szs vs); first last.
    { rewrite sum_list_replicate. rewrite Hvs /mk_array_layout /ly_mult {2}/ly_size. lia. }
    rewrite (heap_pointsto_mjoin_uniform _ _ (ly_size ly)); first last.
    { subst szs. intros v'.
      intros ?%reshape_replicate_elem_length; first done.
      rewrite Hvs. rewrite {1}/ly_size /mk_array_layout /=. lia. }
    iDestruct "Hl" as "(_ & Hl)".
    iPoseProof (big_sepL_extend_l rs with "Hl") as "Hl"; first done.
    iPoseProof (big_sepL2_sep with "[$Ha $Hl]") as "Hl".
    iApply (big_sepL2_elim_r).
    iApply (big_sepL2_impl with "Hl").
    iIntros "!>" (k ? ? _ _) "((% & ? &Hv) & Hl)".
    iExists _, _; iFrame.
  Qed.

  Lemma array_own_val_extract_pointsto π q ly ty rs l len :
    len = length rs →
    syn_type_has_layout (ty_syn_type ty MetaNone) ly →
    loc_in_bounds l 0 0 -∗
    ([∗ list] i↦r ∈ rs, ∃ v : val, array_own_el_loc π q v i ly ty r l) -∗
    ∃ vs, l ↦{q} vs ∗ ⌜vs `has_layout_val` (mk_array_layout ly len)⌝ ∗
      ([∗ list] r;v ∈ rs;reshape (replicate len (ly_size ly)) vs, array_own_el_val π ty r v).
  Proof.
    iIntros (-> ?) "#Hlb Ha".
    (* if rs is empty, we don't have any loc_in_bounds available.. we really need to require that in the sharing predicate. *)
    rewrite big_sepL_exists. iDestruct "Ha" as "(%vs & Hl)".
    setoid_rewrite <-bi.sep_exist_l.
    iExists (mjoin vs). rewrite big_sepL2_sep. iDestruct "Hl" as "(Hl & Hv)".
    iPoseProof (big_sepL2_length with "Hv") as "%Hlen'".
    iAssert (∀ v, ⌜v ∈ vs⌝ -∗ ⌜v `has_layout_val` ly⌝)%I with "[Hv]" as "%Ha".
    { iIntros (v (i & Hlook)%list_elem_of_lookup_1).
      assert (∃ r, rs !! i = Some r) as (r & Hlook').
      { destruct (rs !! i) eqn:Heq; first by eauto. exfalso.
        apply lookup_lt_Some in Hlook. apply lookup_ge_None_1 in Heq. lia. }
      iPoseProof (big_sepL2_lookup _ _ _ i with "Hv") as "Hv"; [done.. | ].
      iDestruct "Hv" as "(% & _ & Hv)". by iApply (ty_own_val_has_layout with "Hv"). }
    iSplitL "Hl". {
      rewrite big_sepL2_const_sepL_r. iDestruct "Hl" as "(_ & Hl)".
      iApply heap_pointsto_mjoin_uniform. { done. }
      iSplitR; done. }
    iSplitR. { rewrite /has_layout_val.
      rewrite length_join.
      rewrite (sum_list_fmap_same (ly_size ly)).
      - iPureIntro. rewrite -Hlen' Nat.mul_comm. done.
      - apply Forall_elem_of_iff. done. }
    rewrite reshape_join; first done.
    apply Forall2_lookup.
    intros i.
    destruct (vs !! i) eqn:Heq1; first last.
    { rewrite Heq1.
      rewrite (proj1 (lookup_replicate_None _ _ _)); first constructor.
      apply lookup_ge_None in Heq1. lia. }
    rewrite lookup_replicate_2; first last.
    { apply lookup_lt_Some in Heq1. lia. }
    rewrite Heq1. constructor. rewrite Ha; first last. { eapply list_elem_of_lookup_2. eauto. }
    done.
  Qed.
  Lemma array_own_val_extract_pointsto_fupd F π q ly ty rs l len :
    len = length rs →
    syn_type_has_layout (ty_syn_type ty MetaNone) ly →
    loc_in_bounds l 0 0 -∗
    ([∗ list] i↦r ∈ rs, |={F}=> ∃ v : val, array_own_el_loc π q v i ly ty r l) ={F}=∗
    ∃ vs, l ↦{q} vs ∗ ⌜vs `has_layout_val` (mk_array_layout ly len)⌝ ∗
      ([∗ list] r;v ∈ rs;reshape (replicate len (ly_size ly)) vs, array_own_el_val π ty r v).
  Proof.
    iIntros (-> ?) "#Hlb Ha".
    iMod (big_sepL_fupd with "Ha") as "Ha".
    by iApply array_own_val_extract_pointsto.
  Qed.

  Definition array_t_own_val_def (len : nat) (ty : type rt) π r m v : iProp Σ :=
      ∃ ly,
        ⌜m = MetaNone⌝ ∗
        ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗
        ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
        ⌜length r = len⌝ ∗
        ⌜v `has_layout_val` (mk_array_layout ly len)⌝ ∗
        [∗ list] r'; v' ∈ r; reshape (replicate len (ly_size ly)) v,
          array_own_el_val π ty r' v'.
  Definition array_t_own_val_aux : seal (@array_t_own_val_def).
  Proof. by eexists. Qed.
  Definition array_t_own_val := array_t_own_val_aux.(unseal).
  Definition array_t_own_val_unfold : @array_t_own_val = @array_t_own_val_def := array_t_own_val_aux.(seal_eq).

  Definition array_t_shr_def (len : nat) (ty : type rt) κ π r m l : iProp Σ :=
      ∃ ly,
        ⌜m = MetaNone⌝ ∗
        ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗
        ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
        ⌜length r = len⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        [∗ list] i ↦ r' ∈ r, array_own_el_shr π κ i ly ty r' l.
  Definition array_t_shr_aux : seal (@array_t_shr_def).
  Proof. by eexists. Qed.
  Definition array_t_shr := array_t_shr_aux.(unseal).
  Definition array_t_shr_unfold : @array_t_shr = @array_t_shr_def := array_t_shr_aux.(seal_eq).

  Program Definition array_t (len : nat) (ty : type rt) : type (list (place_rfn rt)) := {|
    ty_metadata_kind := MetadataNone;
    ty_trivial_drop := ty.(ty_trivial_drop);
    ty_own_val := array_t_own_val len ty;
    ty_shr := array_t_shr len ty;
    ty_syn_type _ := ArraySynType (ty.(ty_syn_type) MetaNone) len;
    _ty_has_op_type := is_array_ot ty len;
    ty_sidecond := True;
    _ty_ghost_drop π r := ([∗ list] r' ∈ r, ∃ r'', place_rfn_interp_owned r' r'' ∗ ty_ghost_drop ty π r'')%I;
    _ty_lfts := ty_lfts ty;
    _ty_wf_E := ty_wf_E ty;
  |}%I.
  Next Obligation.
    intros. econstructor.
    - rewrite array_t_own_val_unfold.
      iIntros (π r m v) "(%ly & -> & %Hst & %Hsz & %Hlen & %Hly & Hv)".
      iExists _.
      iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
      done.
    - iIntros (ot Hot).
      destruct ot; try done.
      destruct Hot as (-> & Hot & Hsz). simpl.
      eapply syn_type_has_layout_array; [done | | done].
      by eapply ty_op_type_stable.
    - intros ot Hot.
      destruct ot; simpl in *; try done.
      destruct Hot as (_ & Hot & _). by eapply ty_op_type_wf.
    - iIntros (π r m v) "_". done.
    - iIntros (κ π r m v) "_". done.
    - unfold TCNoResolve. rewrite array_t_shr_unfold. apply _.
    - rewrite array_t_shr_unfold.
      iIntros (κ π l m r) "(%ly & -> & %Hst & %Hsz & %Hlen & %Hly & Hv)".
      iExists (mk_array_layout ly len). iSplitR; first done.
      iPureIntro. by eapply syn_type_has_layout_array.
    -
      iIntros (E κ l ly π r m q ?).
    iIntros "#(LFT & LCTX) #Hna Htok %Hst %Hly #Hlb Hb".
    rewrite array_t_own_val_unfold array_t_shr_unfold.
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htok')".
    iApply fupd_logical_step.
    (* reshape the borrow - we must not freeze the existential over v to initiate recursive sharing *)
    iPoseProof (bor_iff _ _ (∃ ly', ⌜m = MetaNone⌝ ∗ ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly'⌝ ∗ ⌜(ly_size ly' * len ≤ MaxInt ISize)%Z⌝ ∗  ⌜length r = len⌝ ∗ [∗ list] i ↦ r' ∈ r, ∃ v, array_own_el_loc π 1%Qp v i ly' ty r' l)%I with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "(%v & Hl & %ly' & -> & %Hst' & %Hsz & %Hlen & %Hv & Hv)".
        iExists ly'. do 4 iR.
        iApply (array_own_val_join_pointsto with "Hl Hv"); done.
      - iIntros "(%ly' & -> & %Hst' & %Hsz & %Hlen & Hl)".
        apply syn_type_has_layout_array_inv in Hst as (ly0 & Hst0 & -> & ?).
        assert (ly0 = ly') as ->. { by eapply syn_type_has_layout_inj. }
        iPoseProof (array_own_val_extract_pointsto with "[Hlb] Hl") as "(%vs & Hl & % & Ha)"; [done.. | | ].
        { iApply loc_in_bounds_shorten_suf; last done. lia. }
        iExists vs. iFrame "Hl". iExists ly'. do 5 iR. done.
    }

    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>-> & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst' & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hsz & Hb)"; first done.
    iMod (bor_persistent with "LFT Hsz Htok") as "(>%Hsz & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hlen & Hb)"; first done.
    iMod (bor_persistent with "LFT Hlen Htok") as "(>%Hlen & Htok)"; first done.
    iMod (bor_big_sepL with "LFT Hb") as "Hb"; first done.
    iCombine "Htok Htok'" as "Htok". rewrite lft_tok_sep.
    (* fracture the tokens over the big_sep *)
    iPoseProof (Fractional_split_big_sepL (λ q, (q.[_])%I) len with "Htok") as "(%qs & %Hlen' & Htoks & Hcl_toks)".
    set (κ' := κ ⊓ foldr meet static (ty_lfts ty)).
    iAssert ([∗ list] i ↦ x; q' ∈ r; qs, &{κ} (∃ v r'', (l offset{ly'}ₗ i) ↦ v ∗ place_rfn_interp_owned x r'' ∗ v ◁ᵥ{π, MetaNone} r'' @ ty) ∗ q'.[κ'])%I with "[Htoks Hb]" as "Hb".
    { iApply big_sepL2_sep_sepL_r; iFrame. iApply big_sepL2_const_sepL_l. iSplitR; last done. rewrite Hlen Hlen' //. }

    eapply syn_type_has_layout_array_inv in Hst as (ly0 & Hst & -> & ?).
    assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
    iAssert ([∗ list] i ↦ x; q' ∈ r; qs, logical_step E (array_own_el_shr π κ i ly' ty x l ∗ q'.[κ']))%I with "[Hb]" as "Hb".
    { iApply (big_sepL2_wand with "Hb"). iApply big_sepL2_intro. { simpl in *. lia. }
      iModIntro. iIntros (k x q0 Hlook1 Hlook2) "(Hb & Htok)".
      rewrite bi_exist_comm.
      iApply fupd_logical_step.
      subst κ'.
      rewrite -{1}lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r' & Ha & Htok1)"; first done.
      iPoseProof (bor_iff _ _ (place_rfn_interp_owned x r' ∗ ∃ a, (l offset{ly'}ₗ k) ↦ a ∗ a ◁ᵥ{ π, MetaNone} r' @ ty)%I with "[] Ha") as "Ha".
      { iNext. iModIntro. iSplit.
        - iIntros "(%a & ? & ? & ?)". eauto with iFrame.
        - iIntros "(? & %a & ? & ?)". eauto with iFrame. }
      iMod (bor_sep with "LFT Ha") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Hrfn & Htok1)"; first done.
      iCombine "Htok1 Htok2" as "Htok". rewrite lft_tok_sep. iModIntro.
      iPoseProof (ty_share with "[$LFT $LCTX] Hna Htok [] [] [] Hb") as "Hb"; first done.
      - done.
      - iPureIntro.
        apply has_layout_loc_offset_loc.
        { eapply use_layout_alg_wf. done. }
        {  done. }
      - assert (1 + k ≤ len)%nat as ?.
        { eapply lookup_lt_Some in Hlook1. simpl in *. lia. }
        iApply loc_in_bounds_offset; last done.
        { done. }
        { rewrite /offset_loc. simpl. lia. }
        { rewrite /mk_array_layout /ly_mult {2}/ly_size. rewrite /offset_loc /=. nia. }
      - iApply (logical_step_wand with "Hb"). iIntros "(? & ?)".
        rewrite /array_own_el_shr. eauto with iFrame.
    }
    iPoseProof (logical_step_big_sepL2 with "Hb") as "Hb".
    iModIntro. iApply (logical_step_wand with "Hb"). iIntros "Hb".
    iPoseProof (big_sepL2_sep_sepL_r with "Hb") as "(Hb & Htok)".
    iPoseProof ("Hcl_toks" with "Htok") as "$".
    iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & Hb)".
    iExists _. do 5 iR. done.
    - iIntros (κ κ' π r m l) "#Hincl Hb".
    rewrite array_t_shr_unfold.
    iDestruct "Hb" as "(%ly & -> & Hst & Hsz & Hlen & Hly & Hb)".
    iExists ly. iFrame. iR.
    iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
    iIntros "!>" (k x Hlook) "(% & ? & Hb)".
    iExists _; iFrame. iApply ty_shr_mono; done.
    -
    rewrite array_t_own_val_unfold.
    iIntros (π r m v F ? Hdrop) "(%ly & -> & ? & ? & ? & ? & Hb)".
    iAssert (logical_step F $ [∗ list] r'; v' ∈ r; reshape (replicate len (ly_size ly)) v,
      ∃ r'', place_rfn_interp_owned r' r'' ∗ ty_ghost_drop ty π r'')%I with "[Hb]" as "Hb".
    { iApply logical_step_big_sepL2. iApply (big_sepL2_mono with "Hb"). iIntros (? r' ???).
      iIntros "(%r'' & Hrfn & Hb)".
      iApply (logical_step_wand with "[Hb]").
      { iApply (ty_own_ghost_drop_trivial with "Hb"); done. }
      iIntros "Hg". iExists _. iFrame. }
    iApply (logical_step_wand with "Hb").
    iIntros "Hb". iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & $)".
    - intros ot st π r v Hot.
    rewrite /array_t_own_val array_t_own_val_aux.(seal_eq) /array_t_own_val_def.
    iIntros "Hb".
    iDestruct "Hb" as "(%ly & _ & %Hst & %Hsz & %Hlen & %Hly & Hb)".
    rewrite /is_array_ot in Hot.
    destruct ot as [ | | | | | ot n | ? ? ? | ly' | | ]; try done.
    + destruct Hot as (-> & Hot & _).
      pose proof (ty_op_type_stable _ _ Hot) as Hot_layout.
      assert (ot_layout ot = ly) as Hotly by by eapply syn_type_has_layout_inj.
      iAssert ([∗ list] r';v' ∈ r;reshape (replicate len (ly_size ly)) v,
          ∃ ov, ⌜decode_op_val v' ot st = Some ov⌝)%I with "[Hb]" as "Hb".
      { iApply (big_sepL2_mono with "Hb").
        iIntros (k r' v' Hr' Hv') "(%r'' & Hrfn & Hv)".
        iPoseProof (ty_decodable _ ty ot st π r'' v' with "Hv") as (ov) "%Hdec"; first done.
        iExists ov. done. }
      iPoseProof (big_sepL2_exists_r with "Hb") as "(%elements & %Helements_len & Hb)".
      iPoseProof (big_sepL2_elim_l with "Hb") as "Hb".
      iPoseProof (big_sepL2_from_zip _ _ (λ _ v' ov, ⌜decode_op_val v' ot st = Some ov⌝)%I
        with "Hb") as "Hb"; first done.
      iPoseProof (big_sepL2_Forall2 with "Hb") as "%Helements".
      iExists (OVArray elements). iPureIntro. simp decode_op_val.
      rewrite Hotly.
      rewrite bool_decide_true; last exact Hly.
      apply bind_Some. exists elements. split; last done.
      by apply list_map_option_alt.
    + iExists (OVUntyped ly' v).
      iPureIntro.
      pose proof (syn_type_has_layout_array (ty_syn_type ty MetaNone) len ly (mk_array_layout ly len) eq_refl Hst Hsz) as Hst_array.
      assert (ly' = mk_array_layout ly len) as ->.
      { by eapply syn_type_has_layout_inj. }
      simp decode_op_val. rewrite bool_decide_true; first done.
      exact Hly.
    - iIntros (ot st π r v v' Hot Hsame) "Hv".
    rewrite /is_array_ot in Hot.
    destruct ot as [ | | | | | ot n | ? ? ? | ly | | ]; try done.
    + destruct Hot as (-> & Hot & _).
      rewrite /array_t_own_val array_t_own_val_aux.(seal_eq) /array_t_own_val_def.
      iDestruct "Hv" as "(%ly & _ & %Hst & %Hsz & %Hlen & %Hly & Hv)".
      pose proof (ty_op_type_stable _ _ Hot) as Hot_layout.
      assert (ot_layout ot = ly) as Hotly by by eapply syn_type_has_layout_inj.
      pose proof (is_same_decoded_val_at_array_inv st v ot len v' Hsame) as Hsame_elements.
      rewrite Hotly in Hsame_elements.
      pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
      iExists ly. do 4 iR. iSplitR.
      { iPureIntro. simpl in Hly'. rewrite Hotly in Hly'. exact Hly'. }
      iApply (array_own_el_val_decode_compat_list with "Hv"); [done | | done].
      rewrite length_reshape length_replicate. done.
    + pose proof (is_same_decoded_val_at_has_layout_l _ _ _ _ Hsame) as Hly.
      pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
      pose proof (is_same_decoded_val_at_untyped_inv _ _ _ _ Hly Hly' Hsame) as ->.
      done.
    - intros ly _ Hst.
    done.
    (*
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    simpl. eexists.
    split_and!; [done | | done | ].
    - rewrite ty_has_op_type_unfold.
      apply _ty_has_op_type_untyped; last done.
      (*apply ty_sized_metadata_none.*)
      admit.
    - by eapply use_layout_alg_wf.
     *)
    - apply _.
    - apply _.
  Qed.

  (* TODO copy *)


  Global Instance array_sized ty n : TySized (array_t n ty).
  Proof.
    econstructor; done.
  Qed.
End array.

Section ne.
  Context `{!typeGS Σ}.

  Global Program Instance array_t_dep_lft_morphism {rts rt} deps
      (T : mut_types rts → type rt) (n : nat) :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x, array_t n (T x)) :=
    λ HT, dep_lft_morph_make_id deps T (λ x, array_t n (T x)) HT _ _.
  Next Obligation.
    simpl. rewrite {1}ty_lfts_unfold. done.
  Qed.
  Next Obligation.
    simpl. rewrite {1}ty_wf_E_unfold. done.
  Qed.

  Global Instance array_t_ne {rt} (n : nat) :
    TypeNonExpansive (λ ty, array_t (rt:=rt) n ty).
  Proof.
    constructor; simpl.
    - done.
    - intros ?? ->. done.
    - rewrite ty_has_op_type_unfold/=.
      unfold is_array_ot.
      intros ?? _ Hst Hot.
      intros ot .
      destruct ot; try done.
      + split; intros (-> & Hot' & Hsize); split_and!; try done;
          rewrite ty_has_op_type_unfold in Hot' |- *; by apply Hot.
      + rewrite Hst. done.
    - done.
    - intros.
      rewrite /ty_own_val/= array_t_own_val_unfold.
      rewrite /array_t_own_val_def.
      unfold array_own_el_val.
      solve_type_proper.
    - intros.
      rewrite /ty_shr/= array_t_shr_unfold.
      rewrite /array_t_shr_def.
      unfold array_own_el_shr.
      solve_type_proper.
  Qed.
End ne.

Section lemmas.
  Context `{!typeGS Σ}.

  Lemma array_t_rfn_length_eq π {rt} (ty : type rt) len r v m :
    v ◁ᵥ{π, m} r @ array_t len ty -∗ ⌜length r = len⌝.
  Proof.
    rewrite /ty_own_val/= array_t_own_val_unfold. iIntros "(%ly & -> & %Hst & % & $ & _)".
  Qed.

  Lemma array_val_from_uninit π v st1 st2 ly1 ly2 len m :
    syn_type_has_layout st1 ly1 →
    syn_type_has_layout st2 ly2 →
    ly_size ly1 = (ly_size ly2 * len)%nat →
    v ◁ᵥ{π, m} .@ uninit st1 -∗
    v ◁ᵥ{π, m} replicate len (# ()) @ array_t len (uninit st2).
  Proof.
    intros Hst1 Hst2 Hly.
    rewrite /ty_own_val/= array_t_own_val_unfold.
    iDestruct 1 as "(-> & %ly0 & %Hly0 & %Hlyv0)".
    assert (ly0 = ly1) as ->. { by eapply syn_type_has_layout_inj. }
    (*assert (ly0 = ly1) as -> by by eapply syn_type_has_layout_inj.*)
    iExists _. iR.
    iSplitR. { iPureIntro. by apply syn_type_has_layout_untyped. }
    iSplitR. { iPureIntro. apply (use_layout_alg_size) in Hst1. lia. }
    rewrite length_replicate. iR.
    iSplitR. { rewrite /has_layout_val/mk_array_layout/ly_mult /= -Hly /=. done. }
    iApply big_sepL2_intro.
    { rewrite length_reshape !length_replicate//. }
    iModIntro. iIntros (k ?? Hlook1 Hlook2).
    apply lookup_replicate in Hlook1 as (-> & ?).
    iExists _.  iR.
    rewrite uninit_own_spec.
    iR.
    iExists _. iR.
    iPureIntro. rewrite /has_layout_val.
    apply list_elem_of_lookup_2 in Hlook2.
    apply reshape_replicate_elem_length in Hlook2; first done.
    rewrite Hlyv0. lia.
  Qed.

  Lemma array_t_own_val_split {rt} (ty : type rt) π n1 n2 v1 v2 rs1 rs2 m :
    length rs1 = n1 →
    length rs2 = n2 →
    length v1 = (n1 * size_of_st (ty.(ty_syn_type) m))%nat →
    length v2 = (n2 * size_of_st (ty.(ty_syn_type) m))%nat →
    (v1 ++ v2) ◁ᵥ{π, m} (rs1 ++ rs2) @ array_t (n1 + n2) ty -∗
    v1 ◁ᵥ{π, m} rs1 @ array_t n1 ty ∗ v2 ◁ᵥ{π, m} rs2 @ array_t n2 ty.
  Proof.
    intros Hrs1 Hrs2 Hv1 Hv2. rewrite /ty_own_val /= array_t_own_val_unfold.
    iIntros "(%ly & -> & %Halg & %Hsz & %Hlen & %Hly & Hb)".
    rewrite /size_of_st /use_layout_alg' Halg /= in Hv1.
    rewrite /size_of_st /use_layout_alg' Halg /= in Hv2.
    rewrite replicate_add. rewrite reshape_app.
    rewrite sum_list_replicate.
    rewrite take_app_length'; last lia.
    rewrite drop_app_length'; last lia.
    iPoseProof (big_sepL2_app_inv with "Hb") as "[Hb1 Hb2]".
    { rewrite length_reshape length_replicate. eauto. }
    iSplitL "Hb1".
    - iExists _. iR. iR. iSplitR. { iPureIntro. lia. }
      iR. iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
      done.
    - iExists _. iR. iR. iSplitR. { iPureIntro. lia. }
      iR. iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
      done.
  Qed.

  Lemma array_t_own_val_merge {rt} (ty : type rt) π (n1 n2 : nat) v1 v2 rs1 rs2 m :
    (size_of_st (ty.(ty_syn_type) m) * (n1 + n2) ≤ MaxInt ISize)%Z →
    v1 ◁ᵥ{π, m} rs1 @ array_t n1 ty -∗
    v2 ◁ᵥ{π, m} rs2 @ array_t n2 ty -∗
    (v1 ++ v2) ◁ᵥ{π, m} (rs1 ++ rs2) @ array_t (n1 + n2) ty.
  Proof.
    rewrite /ty_own_val/= array_t_own_val_unfold.
    iIntros (Hsz) "(%ly1 & -> & %Halg1 & %Hsz1 & %Hlen1 & %Hv1 & Hb1) (%ly2 & _ & %Halg2 & %Hsz2 & %Hlen2 & %Hv2 & Hb2)".
    assert (ly1 = ly2) as <- by by eapply syn_type_has_layout_inj. clear Halg2.
    rewrite /size_of_st /use_layout_alg' Halg1 /= in Hsz.
    iExists ly1. do 2 iR. iSplitR. { iPureIntro. lia. }
    rewrite /has_layout_val ly_size_mk_array_layout in Hv1.
    rewrite /has_layout_val ly_size_mk_array_layout in Hv2.
    rewrite length_app -Hlen1 -Hlen2. iR.
    iSplitR. { iPureIntro. rewrite /has_layout_val length_app Hv1 Hv2 ly_size_mk_array_layout. lia. }
    rewrite replicate_add. rewrite reshape_app.
    rewrite sum_list_replicate.
    rewrite take_app_length'; last lia.
    rewrite drop_app_length'; last lia.
    iApply (big_sepL2_app with "Hb1 Hb2").
  Qed.

  Lemma array_t_shr_split {rt} (ty : type rt) π κ n1 n2 l rs1 rs2 m :
    length rs1 = n1 →
    length rs2 = n2 →
    l ◁ₗ{π, m, κ} (rs1 ++ rs2) @ array_t (n1 + n2) ty -∗
    l ◁ₗ{π, m, κ} rs1 @ array_t n1 ty ∗ (l offsetst{ty.(ty_syn_type) m}ₗ n1) ◁ₗ{π, m, κ} rs2 @ array_t n2 ty.
  Proof.
    rewrite /ty_shr/= array_t_shr_unfold. iIntros (Hlen1 Hlen2).
    iIntros "(%ly & -> & %Halg & %Hsz & %Hlen & %Hly & Hb)".
    rewrite big_sepL_app. iDestruct "Hb" as "(Hb1 & Hb2)".
    rewrite length_app in Hlen.
    iSplitL "Hb1".
    - iExists _. do 2 iR. iSplitR. { iPureIntro. lia. }
      iSplitR. { iPureIntro. lia. }
      iR. done.
    - iExists _. do 2 iR. iSplitR. { iPureIntro. lia. }
      iSplitR. { iPureIntro. lia. }
      rewrite /OffsetLocSt /use_layout_alg' Halg/=.
      iSplitR. { iPureIntro. eapply has_layout_loc_offset_loc; last done.
        by eapply use_layout_alg_wf. }
      rewrite /array_own_el_shr. setoid_rewrite offset_loc_offset_loc. rewrite Hlen1.
      setoid_rewrite Nat2Z.inj_add. done.
  Qed.

  Lemma array_t_shr_merge {rt} (ty : type rt) π κ (n1 n2 : nat) l rs1 rs2 m :
    (size_of_st (ty.(ty_syn_type) m) * (n1 + n2) ≤ MaxInt ISize)%Z →
    l ◁ₗ{π, m, κ} rs1 @ array_t n1 ty -∗
    (l offsetst{ty.(ty_syn_type) m}ₗ n1) ◁ₗ{π, m, κ} rs2 @ array_t n2 ty -∗
    l ◁ₗ{π, m, κ} (rs1 ++ rs2) @ array_t (n1 + n2) ty.
  Proof.
    rewrite /ty_shr/= array_t_shr_unfold. iIntros (Hsz).
    iIntros "(%ly1 & -> & %Halg1 & %Hsz1 & %Hlen1 & %Hly1 & Hb1) (%ly2 & _ & %Halg2 & %Hsz2 & %Hlen2 & %Hly2 & Hb2)".
    assert (ly2 = ly1) as -> by by eapply syn_type_has_layout_inj. clear Halg2.
    rewrite /size_of_st /use_layout_alg' Halg1 /= in Hsz.
    iExists _. do 2 iR. iSplitR. { iPureIntro. lia. }
    rewrite length_app. iSplitR. { iPureIntro. lia. }
    iR. iApply (big_sepL_app).
    iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Halg1 /=.
    rewrite /array_own_el_shr. setoid_rewrite offset_loc_offset_loc. rewrite -Hlen1.
    setoid_rewrite Nat2Z.inj_add. done.
  Qed.

  Lemma array_t_own_val_split_reshape {rt} (ty : type rt) π (n : nat) v rs (num size : nat) ly :
    n = (num * size)%nat →
    syn_type_has_layout (st_of ty MetaNone) ly →
    v ◁ᵥ{π, MetaNone} rs @ array_t n ty -∗
    ⌜mjoin (reshape (replicate num (ly_size ly * size)%nat) v) = v⌝ ∗
    [∗ list] v'; r' ∈ reshape (replicate num (ly_size ly * size)%nat) v; reshape (replicate num size) rs,
      v' ◁ᵥ{π, MetaNone} r' @ array_t size ty.
  Proof.
    iIntros (-> Hst) "Hv".
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Hst' & %Hlyv)".
    apply syn_type_has_layout_array_inv in Hst' as (ly'' & Hst'' & -> & Hsz).
    assert (ly'' = ly) as -> by by eapply syn_type_has_layout_inj.
    opose proof (join_reshape (replicate num (ly_size ly * size)%nat) v _) as Hv_eq.
    { rewrite sum_list_replicate. rewrite Hlyv {2}/ly_size/=. lia. }
    opose proof (join_reshape (replicate num size) rs _) as Hrs_eq.
    { rewrite sum_list_replicate Hlen//. }
    rewrite -{1}Hv_eq -{1}Hrs_eq.
    iSplitR; first done.
    iInduction num as [ | num] "IH" forall (v rs Hlyv Hv_eq Hrs_eq Hlen); simpl; first done.
    iPoseProof (array_t_own_val_split with "Hv") as "($ & Hv2)".
    { rewrite length_take. lia. }
    { rewrite length_join.
      rewrite fmap_length_reshape; rewrite sum_list_replicate; first done.
      rewrite length_drop. lia. }
    { rewrite length_take /size_of_st.
      rewrite /use_layout_alg' Hst/=.
      rewrite Hlyv. rewrite ly_size_mk_array_layout. lia. }
    { rewrite length_join. rewrite fmap_length_reshape.
      { rewrite sum_list_replicate. rewrite /size_of_st /use_layout_alg' Hst/=. lia. }
      rewrite sum_list_replicate.
      rewrite length_drop.
      rewrite Hlyv ly_size_mk_array_layout. lia. }
    iApply "IH"; last done; iPureIntro.
    { rewrite ly_size_mk_array_layout. rewrite ly_size_mk_array_layout in Hsz. lia. }
    { rewrite /has_layout_val length_drop Hlyv !ly_size_mk_array_layout. lia. }
    { rewrite join_reshape; first done.
      rewrite sum_list_replicate length_drop.
      rewrite Hlyv ly_size_mk_array_layout. lia. }
    { rewrite join_reshape; first done. rewrite sum_list_replicate length_drop Hlen. lia. }
    { rewrite length_drop Hlen. lia. }
  Qed.
  Lemma array_t_own_val_merge_reshape {rt} (ty : type rt) π (n : nat) v rs (num size : nat) ly :
    n = (num * size)%nat →
    syn_type_has_layout (st_of ty MetaNone) ly →
    length rs * (ly_size ly * size) = length v →
    (Z.of_nat (length v) ≤ MaxInt ISize)%Z →
    ([∗ list] v'; r' ∈ reshape (replicate num (ly_size ly * size)%nat) v; rs,
      v' ◁ᵥ{π, MetaNone} r' @ array_t size ty) -∗
    v ◁ᵥ{π, MetaNone} (mjoin rs) @ array_t n ty.
  Proof.
    iIntros (-> Hst Hlyv Hsz_bound) "Hv".
    iPoseProof (big_sepL2_length with "Hv") as "%Hlen".
    rewrite length_reshape length_replicate in Hlen. subst num.
    opose proof (join_reshape (replicate (length rs) (ly_size ly * size)%nat) v _) as Hv_eq.
    { rewrite sum_list_replicate. done. }
    rewrite -{2}Hv_eq.
    clear Hv_eq.

    iInduction rs as [ | r rs] "IH" forall (v Hlyv Hsz_bound); simpl.
    { rewrite /ty_own_val/= array_t_own_val_unfold. iExists ly.
      iSplitR; first done. iSplitR; first done.
      rewrite Z.mul_0_r. iSplitR. { iPureIntro. specialize (MaxInt_ge_127 ISize). lia. }
      iSplitR; first done.
      iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout//. }
      done. }
    iDestruct "Hv" as "(Hv1 & Hv)".
    iPoseProof ("IH" with "[] [] Hv") as "Hv2".
    { iPureIntro. simpl in Hlyv. rewrite length_drop. lia. }
    { iPureIntro. simpl in Hlyv. rewrite length_drop. lia. }
    iPoseProof (array_t_own_val_merge with "Hv1 Hv2") as "Hv".
    { simpl in Hlyv. rewrite /size_of_st/use_layout_alg' Hst/=. lia. }
    done.
  Qed.

  Lemma array_t_own_val_reshape F v π {rt} (ty : type rt) rs (n m k : nat) :
    k ≠ 0%nat →
    n = (m * k)%nat →
    v ◁ᵥ{π, MetaNone} rs @ array_t n ty ={F}=∗
    v ◁ᵥ{π, MetaNone} (<#> reshape (replicate k m) rs) @ array_t k (array_t m ty).
  Proof.
    intros ? ->.
    iIntros "Hv".
    iPoseProof (ty_has_layout with "Hv") as "(%ly & %Hst & %Hlyv)".
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    rewrite ly_size_mk_array_layout in Hsz.
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    iPoseProof (array_t_own_val_split_reshape ty _ _ _ _ k m with "Hv") as "(%Hv & Hv)"; [lia | done | ].
    iEval (rewrite /ty_own_val/= array_t_own_val_unfold).
    iExists (mk_array_layout ly' m). iR.
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; [done.. | nia ]. }
    iSplitR. { iPureIntro. rewrite ly_size_mk_array_layout. lia. }
    iSplitR. { iPureIntro. rewrite length_fmap length_reshape length_replicate//. }
    iSplitR. { iPureIntro. rewrite /has_layout_val Hlyv !ly_size_mk_array_layout. lia. }
    rewrite ly_size_mk_array_layout.
    rewrite big_sepL2_flip.
    rewrite big_sepL2_fmap_l.
    iApply (big_sepL2_wand with "Hv").
    iApply big_sepL2_intro.
    { rewrite !length_reshape !length_replicate//. }
    iModIntro. iModIntro.
    iIntros (i r v' Hlook1 Hlook2).
    unfold array_own_el_val.
    eauto.
  Qed.

  (* Lemmas about ◁ₗ splitting in unfold.v *)

  (* Converting between arrays of integers of different sizes *)
  Lemma ty_own_val_array_int_to_int v π rs n (it it' : int_type) :
    (n * ly_size it)%nat = ly_size it' →
    v ◁ᵥ{π, MetaNone} rs @ array_t n (int it) -∗
    ∃ x, v ◁ᵥ{π, MetaNone} x @ int it'.
  Proof.
    iIntros (Hsz) "Hv".
    rewrite /ty_own_val/= array_t_own_val_unfold.
    iDestruct "Hv" as "(%ly & _ & %Hst & %Hsz' & <- & %Hlyv & Hv)".
    iPoseProof (big_sepL2_impl _ (λ _ r v, ⌜is_Some (val_to_Z v it)⌝)%I with "Hv []") as "Hv".
    { iModIntro. iIntros (??? ??). iIntros "(%r' & ? & _ & Hown)".
      by iApply (int_own_val_to_is_Some with "Hown"). }
    iPoseProof (big_sepL2_elim_l with "Hv") as "Hv".
    iPoseProof (big_sepL_Forall with "Hv") as "%Ha".

    apply syn_type_has_layout_int_inv in Hst as ->.
    move: Hlyv. rewrite /has_layout_val ly_size_mk_array_layout => Hlyv.

    destruct (val_to_Z v it') eqn:Heq; first by (iExists _; rewrite /ty_own_val/= int_own_val_unfold; eauto).
    exfalso.
    move: Heq.
    unfold val_to_Z.
    rewrite bool_decide_true; first last.
    { move: Hsz Hlyv. unfold ly_size; simpl. lia. }
    enough (is_Some (val_to_Z_go v)) as (? & ->).
    { simpl. case_match; done. }
    apply val_to_Z_go_is_Some.
    rewrite -(join_reshape (replicate (length rs) (ly_size it)) v); first last.
    { rewrite sum_list_replicate. rewrite Hlyv. rewrite Nat.mul_comm. done. }
    apply Forall_Forall_join.
    apply Forall_lookup_2.
    intros ?? Hx.
    apply val_to_Z_go_is_Some.
    opose proof (Forall_lookup_1 _ _ i x Ha Hx) as Hb.
    move: Hb.
    unfold val_to_Z.
    case_bool_decide; last done.
    destruct (val_to_Z_go _); done.
  Qed.
  Lemma ty_own_val_int_to_array_int v π x n (it it' : int_type) :
    (n * ly_size it)%nat = ly_size it' →
    v ◁ᵥ{π, MetaNone} x @ int it' -∗
    ∃ rs, v ◁ᵥ{π, MetaNone} (<#> rs) @ array_t n (int it).
  Proof.
    iIntros (Hsz) "Hv".
    rewrite /ty_own_val/= array_t_own_val_unfold int_own_val_unfold.
    iDestruct "Hv" as "(_ & %Hv)".
    apply val_to_Z_Some in Hv as (Hv & Hlen).
    unfold array_own_el_val.

    rewrite -(join_reshape (replicate n (ly_size it)) v) in Hv; first last.
    { rewrite sum_list_replicate. rewrite Hsz. unfold ly_size; simpl. done. }
    apply Forall_Forall_join in Hv.
    iPoseProof (Forall_big_sepL _ (λ v, ∃ r, v ◁ᵥ{π, MetaNone} r @ int it)%I True%I with "[//] []") as "(Ha & _)".
    { apply Hv. }
    { iModIntro. iIntros (?) "_ %Hel %Hx".
      opose proof (val_to_Z_Some_1 _ _ Hx _) as (r' & ?).
      { eapply reshape_replicate_elem_length in Hel; first apply Hel.
        move: Hsz. rewrite /ly_size/=. lia. }
      iL. iExists r'. iR. simpl. rewrite int_own_val_unfold. done. }
    iPoseProof (big_sepL_exists with "Ha") as "(%rs' & Ha')".
    iPoseProof (big_sepL2_length with "Ha'") as "%Hlen'".
    iExists rs'.
    iExists (it_layout it). iR.
    iSplitR. { iPureIntro. by apply syn_type_has_layout_int. }
    iSplitR. { iPureIntro. specialize (it_size_bounded it'). lia. }
    iSplitR. { iPureIntro. rewrite length_fmap -Hlen'.
      rewrite length_reshape length_replicate//. }
    iSplitR. { iPureIntro. rewrite /has_layout_val Hlen ly_size_mk_array_layout.
      move: Hsz Hlen. rewrite /ly_size/=. lia. }
    rewrite big_sepL2_flip big_sepL2_fmap_l. iApply (big_sepL2_impl with "Ha'").
    iModIntro. iIntros (??? ??) "Hv".
    iFrame. done.
  Qed.

  Lemma ty_own_val_array_subtype_strong F v π {rt} (ty : type rt) {rt'} (ty' : type rt') n rs R :
    syn_type_size_eq (st_of ty MetaNone) (st_of ty' MetaNone) →
    (□ ∀ v i r, ⌜rs !! i = Some r⌝ -∗ v ◁ᵥ{π, MetaNone} r @ ty ={F}=∗ ∃ r', R r r' ∗ v ◁ᵥ{π, MetaNone} r' @ ty') -∗
    v ◁ᵥ{π, MetaNone} (<#> rs) @ array_t n ty ={F}=∗
    ∃ rs', ([∗ list] r; r' ∈ rs; rs', R r r') ∗ v ◁ᵥ{π, MetaNone} (<#> rs') @ array_t n ty'.
  Proof.
    iIntros (Hsteq) "#Hv".
    iEval (rewrite /ty_own_val/= array_t_own_val_unfold).
    iIntros "(%ly & _ & %Hst & %Hsz & <- & %Hlyv & Ha)".
    rewrite big_sepL2_fmap_l. rewrite length_fmap.
    iPoseProof (big_sepL2_impl _ (λ _ r' v', |={F}=> ∃ r'', R r' r'' ∗ array_own_el_val π ty' (#r'') v')%I with "Ha []") as "Ha".
    { iModIntro. iIntros (??? Hlook1 Hlook2) "(%r0 & <- & Ha)".
      iMod ("Hv" with "[//] Ha") as "(% & ? & Ha)". iExists _. iFrame. done. }
    iMod (big_sepL2_fupd with "Ha") as "Ha".
    iPoseProof (big_sepL2_exists_r with "Ha") as "(%rs' & %Hlen & Ha)".
    iPoseProof (big_sepL2_sep with "Ha") as "(HR & Ha)".
    iPoseProof (big_sepL2_elim_l with "Ha") as "Ha".
    iPoseProof (big_sepL2_from_zip _ _ (λ _ v r, array_own_el_val π ty' (#r) v) with "Ha") as "Ha".
    { done. }
    iPoseProof (big_sepL2_length with "HR") as "%Hlen'".
    rewrite -(big_sepL2_fmap_r snd (λ _ a b, R a b)%I).
    rewrite snd_zip; last lia.
    (*rewrite length_reshape length_replicate in Hlen_eq.*)
    rewrite length_fmap in Hsz.
    iExists rs'.
    destruct (Hsteq _ Hst) as (ly' & Hst' & Hszeq).
    iFrame "HR".
    iModIntro. rewrite array_t_own_val_unfold.
    iExists ly'. iR. iR.
    iSplitR. { iPureIntro. rewrite -Hszeq. done. }
    rewrite length_fmap.
    iSplitR. { iPureIntro. rewrite -Hlen Hlen'. rewrite !length_reshape !length_zip length_reshape length_replicate//. }
    iSplitR. { iPureIntro. rewrite /has_layout_val Hlyv !ly_size_mk_array_layout.
      rewrite length_fmap. lia. }
    rewrite Hszeq. rewrite big_sepL2_fmap_l big_sepL2_flip.
    done.
  Qed.
End lemmas.
