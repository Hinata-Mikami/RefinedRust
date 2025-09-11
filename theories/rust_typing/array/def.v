From refinedrust Require Export type.
From refinedrust Require Import uninit_def int.
(*From refinedrust Require Import programs.*)
From refinedrust Require Import options.

(** * Array types *)

(** Design decisions:
  - our array's refinements are homogeneously typed.
  - we have a fixed capacity -- otherwise, we cannot define the syntype (it would be a dynamically sized type..)
  - the array does not own its deallocation permission -- because its value form is not a pointer type.
  - it is refined by a list (homogeneous), similarly for the ltype. (we could also refine the ltype by a vec - but that would make everything more complicated)
*)


(* TODO: should we also have an ArrayOp that reads the array elements at an op that is valid for the element types? *)
Definition is_array_ot `{!typeGS Σ} {rt} (ty : type rt) (len : nat) (ot : op_type) (mt : memcast_compat_type) : Prop :=
  match ot with
  | UntypedOp ly =>
      ∃ ly', ly = mk_array_layout ly' len ∧ ty_has_op_type ty (UntypedOp ly') mt ∧
        (* required for offsetting with LLVM's GEP *)
        (ly_size ly ≤ MaxInt ISize)%Z ∧
        (* enforced by Rust *)
        layout_wf ly'
  | _ => False
  end.
Global Typeclasses Opaque is_array_ot.

Section array.
  Context `{!typeGS Σ}.
  Context {rt : RT}.

  Definition array_own_el_val (π : thread_id) (ty : type rt) (r : place_rfn rt) (v : val) : iProp Σ :=
    ∃ r', place_rfn_interp_owned r r' ∗ ty.(ty_own_val) π r' v.
  Definition array_own_el_loc (π : thread_id) (q : Qp) (v : val) (i : nat) (ly : layout) (ty : type rt) (r : place_rfn rt) (l : loc) : iProp Σ :=
    ∃ r', (l offset{ly}ₗ i) ↦{q} v ∗ place_rfn_interp_owned r r' ∗ ty.(ty_own_val) π r' v.
  Definition array_own_el_shr (π : thread_id) (κ : lft) (i : nat) (ly : layout) (ty : type rt) (r : place_rfn rt) (l : loc) : iProp Σ :=
    ∃ r', place_rfn_interp_shared r r' ∗ ty.(ty_shr) κ π r' (offset_loc l ly i).

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
    iExists _, _; iFrame. rewrite /offset_loc. done.
  Qed.

  Lemma array_own_val_extract_pointsto π q ly ty rs l len :
    len = length rs →
    syn_type_has_layout (ty_syn_type ty) ly →
    loc_in_bounds l 0 (ly_size ly * len) -∗
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
      iSplitR; last done.
      rewrite -Hlen'. rewrite Nat.mul_comm. done. }
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
    syn_type_has_layout (ty_syn_type ty) ly →
    loc_in_bounds l 0 (ly_size ly * len) -∗
    ([∗ list] i↦r ∈ rs, |={F}=> ∃ v : val, array_own_el_loc π q v i ly ty r l) ={F}=∗
    ∃ vs, l ↦{q} vs ∗ ⌜vs `has_layout_val` (mk_array_layout ly len)⌝ ∗
      ([∗ list] r;v ∈ rs;reshape (replicate len (ly_size ly)) vs, array_own_el_val π ty r v).
  Proof.
    iIntros (-> ?) "#Hlb Ha".
    iMod (big_sepL_fupd with "Ha") as "Ha".
    by iApply array_own_val_extract_pointsto.
  Qed.

  Program Definition array_t (len : nat) (ty : type rt) : type (list (place_rfn rt)) := {|
    ty_own_val π r v :=
      ∃ ly,
        ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
        ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
        ⌜length r = len⌝ ∗
        ⌜v `has_layout_val` (mk_array_layout ly len)⌝ ∗
        [∗ list] r'; v' ∈ r; reshape (replicate len (ly_size ly)) v,
          array_own_el_val π ty r' v';
    ty_shr κ π r l :=
      ∃ ly,
        ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
        ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
        ⌜length r = len⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        [∗ list] i ↦ r' ∈ r, array_own_el_shr π κ i ly ty r' l;
    ty_syn_type := ArraySynType ty.(ty_syn_type) len;
    _ty_has_op_type := is_array_ot ty len;
    ty_sidecond := True;
    _ty_lfts := ty_lfts ty;
    _ty_wf_E := ty_wf_E ty;
  |}%I.
  Next Obligation.
    iIntros (len ty π r v) "(%ly & %Hst & %Hsz & %Hlen & %Hly & Hv)".
    iExists _.
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    done.
  Qed.
  Next Obligation.
    iIntros (len ty ot mt Hot).
    destruct ot; try done.
    destruct Hot as (ly' & -> & Hot & Hsz & Hwf).
    eapply ty_op_type_stable in Hot.
    eapply syn_type_has_layout_array.
    - done.
    - done.
    - rewrite /ly_size /mk_array_layout in Hsz. simpl in Hsz. lia.
  Qed.
  Next Obligation.
    iIntros (len ty π r v) "_". done.
  Qed.
  Next Obligation.
    iIntros (len ty ? π r v) "_". done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (len ty κ π l r) "(%ly & %Hst & %Hsz & %Hlen & %Hly & Hv)".
    iExists (mk_array_layout ly len). iSplitR; first done.
    iPureIntro. by eapply syn_type_has_layout_array.
  Qed.
  Next Obligation.
    iIntros (len ty E κ l ly π r q ?).
    iIntros "#(LFT & TIME & LCTX) Htok %Hst %Hly #Hlb Hb".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htok')".
    iApply fupd_logical_step.
    (* reshape the borrow - we must not freeze the existential over v to initiate recursive sharing *)
    iPoseProof (bor_iff _ _ (∃ ly', ⌜syn_type_has_layout (ty_syn_type ty) ly'⌝ ∗ ⌜(ly_size ly' * len ≤ MaxInt ISize)%Z⌝ ∗  ⌜length r = len⌝ ∗ [∗ list] i ↦ r' ∈ r, ∃ v, array_own_el_loc π 1%Qp v i ly' ty r' l)%I with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "(%v & Hl & %ly' & %Hst' & %Hsz & %Hlen & %Hv & Hv)".
        iExists ly'. iSplitR; first done. iSplitR; first done. iSplitR; first done.
        iApply (array_own_val_join_pointsto with "Hl Hv"); done.
      - iIntros "(%ly' & %Hst' & %Hsz & %Hlen & Hl)".
        apply syn_type_has_layout_array_inv in Hst as (ly0 & Hst0 & -> & ?).
        assert (ly0 = ly') as ->. { by eapply syn_type_has_layout_inj. }
        iPoseProof (array_own_val_extract_pointsto with "Hlb Hl") as "(%vs & Hl & % & Ha)"; [done.. | ].
        iExists vs. iFrame "Hl". iExists ly'. do 4 iR. done.
    }

    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst' & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hsz & Hb)"; first done.
    iMod (bor_persistent with "LFT Hsz Htok") as "(>%Hsz & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hlen & Hb)"; first done.
    iMod (bor_persistent with "LFT Hlen Htok") as "(>%Hlen & Htok)"; first done.
    iMod (bor_big_sepL with "LFT Hb") as "Hb"; first done.
    iCombine "Htok Htok'" as "Htok". rewrite lft_tok_sep.
    (* fracture the tokens over the big_sep *)
    iPoseProof (Fractional_split_big_sepL (λ q, q.[_]%I) len with "Htok") as "(%qs & %Hlen' & Htoks & Hcl_toks)".
    set (κ' := κ ⊓ foldr meet static (ty_lfts ty)).
    iAssert ([∗ list] i ↦ x; q' ∈ r; qs, &{κ} (∃ v r'', (l offset{ly'}ₗ i) ↦ v ∗ place_rfn_interp_owned x r'' ∗ v ◁ᵥ{ π} r'' @ ty) ∗ q'.[κ'])%I with "[Htoks Hb]" as "Hb".
    { iApply big_sepL2_sep_sepL_r; iFrame. iApply big_sepL2_const_sepL_l. iSplitR; last done. rewrite Hlen Hlen' //. }

    eapply syn_type_has_layout_array_inv in Hst as (ly0 & Hst & -> & ?).
    assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
    iAssert ([∗ list] i ↦ x; q' ∈ r; qs, logical_step E (array_own_el_shr π κ i ly' ty x l ∗ q'.[κ']))%I with "[Hb]" as "Hb".
    { iApply (big_sepL2_wand with "Hb"). iApply big_sepL2_intro; first by lia.
      iModIntro. iIntros (k x q0 Hlook1 Hlook2) "(Hb & Htok)".
      rewrite bi_exist_comm.
      iApply fupd_logical_step.
      subst κ'.
      rewrite -{1}lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r' & Ha & Htok1)"; first done.
      iPoseProof (bor_iff _ _ (place_rfn_interp_owned x r' ∗ ∃ a, (l offset{ly'}ₗ k) ↦ a ∗ a ◁ᵥ{ π} r' @ ty)%I with "[] Ha") as "Ha".
      { iNext. iModIntro. iSplit.
        - iIntros "(%a & ? & ? & ?)". eauto with iFrame.
        - iIntros "(? & %a & ? & ?)". eauto with iFrame. }
      iMod (bor_sep with "LFT Ha") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Hrfn & Htok1)"; first done.
      iCombine "Htok1 Htok2" as "Htok". rewrite lft_tok_sep. iModIntro.
      rewrite ty_lfts_unfold.
      iPoseProof (ty_share with "[$LFT $TIME $LCTX] Htok [] [] [] Hb") as "Hb"; first done.
      - done.
      - iPureIntro.
        apply has_layout_loc_offset_loc.
        { eapply use_layout_alg_wf. done. }
        {  done. }
      - assert (1 + k ≤ len)%nat as ?.
        { eapply lookup_lt_Some in Hlook1. lia. }
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
    iExists _. do 4 iR. done.
  Qed.
  Next Obligation.
    iIntros (len ty κ κ' π r l) "#Hincl Hb".
    iDestruct "Hb" as "(%ly & Hst & Hsz & Hlen & Hly & Hb)".
    iExists ly. iFrame.
    iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
    iIntros "!>" (k x Hlook) "(% & ? & Hb)".
    iExists _; iFrame. iApply ty_shr_mono; done.
  Qed.
  Next Obligation.
    iIntros (len ty ot mt st π r v Hot) "Hb".
    destruct ot as [ | | | | ly' | ]; try done.
    destruct Hot as (ly0 & -> & Hot & Hwf).
    destruct mt; [done | done | done].
    (* TODO maybe the second case should really change once we support an ArrayOpType? *)
  Qed.
  Next Obligation.
    intros len ty ly mt Hst.
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    simpl. eexists.
    split_and!; [done | | done | ].
    - by apply ty_has_op_type_untyped.
    - by eapply use_layout_alg_wf.
  Qed.

  Global Program Instance array_ghost_drop (ty : type rt) `{Hg : !TyGhostDrop ty} len : TyGhostDrop (array_t len ty) :=
    mk_ty_ghost_drop _ (λ π r,
      [∗ list] r' ∈ r, ∃ r'', place_rfn_interp_owned r' r'' ∗ ty_ghost_drop_for ty Hg π r'')%I _.
  Next Obligation.
    iIntros (ty Hg len π r v F ?) "(%ly & ? & ? & ? & ? & Hb)".
    iAssert (logical_step F $ [∗ list] r'; v' ∈ r; reshape (replicate len (ly_size ly)) v,
      ∃ r'', place_rfn_interp_owned r' r'' ∗ ty_ghost_drop_for ty Hg π r'')%I with "[Hb]" as "Hb".
    { iApply logical_step_big_sepL2. iApply (big_sepL2_mono with "Hb"). iIntros (? r' ???).
      iIntros "(%r'' & Hrfn & Hb)".
      iApply (logical_step_wand with "[Hb]").
      { iApply (ty_own_ghost_drop with "Hb"); done. }
      iIntros "Hg". iExists _. iFrame. }
    iApply (logical_step_wand with "Hb").
    iIntros "Hb". iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & $)".
  Qed.

  (* TODO copy *)
End array.

Section ne.
  Context `{!typeGS Σ}.

  Global Instance array_t_ne {rt} (n : nat) :
    TypeNonExpansive (array_t (rt:=rt) n).
  Proof.
    constructor; simpl.
    - intros ?? ->. done.
    - eapply ty_lft_morph_make_id.
      + rewrite {1}ty_lfts_unfold//.
      + rewrite {1}ty_wf_E_unfold//.
    - rewrite ty_has_op_type_unfold/=.
      unfold is_array_ot.
      rewrite ty_has_op_type_unfold/=.
      intros ?? Hst Hot.
      intros ot mt.
      destruct ot; try done.
      setoid_rewrite Hot.
      done.
    - done.
    - intros.
      rewrite /ty_own_val/=.
      unfold array_own_el_val.
      solve_type_proper.
    - intros.
      rewrite /ty_shr/=.
      unfold array_own_el_shr.
      solve_type_proper.
  Qed.
End ne.

Section lemmas.
  Context `{!typeGS Σ}.

  Lemma array_val_from_uninit π v st1 st2 ly1 ly2 len :
    syn_type_has_layout st1 ly1 →
    syn_type_has_layout st2 ly2 →
    ly_size ly1 = (ly_size ly2 * len)%nat →
    v ◁ᵥ{ π} .@ uninit st1 -∗
    v ◁ᵥ{ π} replicate len (# ()) @ array_t len (uninit st2).
  Proof.
    intros Hst1 Hst2 Hly.
    rewrite /ty_own_val/=.
    iDestruct 1 as "(%ly0 & %Hly0 & %Hlyv0)".
    assert (ly0 = ly1) as ->. { by eapply syn_type_has_layout_inj. }
    (*assert (ly0 = ly1) as -> by by eapply syn_type_has_layout_inj.*)
    iExists _. iR.
    iSplitR. { iPureIntro. apply (use_layout_alg_size) in Hst1. lia. }
    rewrite length_replicate. iR.
    iSplitR. { rewrite /has_layout_val/mk_array_layout/ly_mult /= -Hly /=. done. }
    iApply big_sepL2_intro.
    { rewrite length_reshape !length_replicate//. }
    iModIntro. iIntros (k ?? Hlook1 Hlook2).
    apply lookup_replicate in Hlook1 as (-> & ?).
    iExists _.  iR.
    rewrite uninit_own_spec.
    iExists _. iR.
    iPureIntro. rewrite /has_layout_val.
    apply list_elem_of_lookup_2 in Hlook2.
    apply reshape_replicate_elem_length in Hlook2; first done.
    rewrite Hlyv0. lia.
  Qed.

  Lemma array_t_own_val_split {rt} (ty : type rt) π n1 n2 v1 v2 rs1 rs2 :
    length rs1 = n1 →
    length rs2 = n2 →
    length v1 = (n1 * size_of_st ty.(ty_syn_type))%nat →
    length v2 = (n2 * size_of_st ty.(ty_syn_type))%nat →
    (v1 ++ v2) ◁ᵥ{π} (rs1 ++ rs2) @ array_t (n1 + n2) ty -∗
    v1 ◁ᵥ{π} rs1 @ array_t n1 ty ∗ v2 ◁ᵥ{π} rs2 @ array_t n2 ty.
  Proof.
    intros Hrs1 Hrs2 Hv1 Hv2. rewrite /ty_own_val /=.
    iIntros "(%ly & %Halg & %Hsz & %Hlen & %Hly & Hb)".
    rewrite /size_of_st /use_layout_alg' Halg /= in Hv1.
    rewrite /size_of_st /use_layout_alg' Halg /= in Hv2.
    rewrite replicate_add. rewrite reshape_app.
    rewrite sum_list_replicate.
    rewrite take_app_length'; last lia.
    rewrite drop_app_length'; last lia.
    iPoseProof (big_sepL2_app_inv with "Hb") as "[Hb1 Hb2]".
    { rewrite length_reshape length_replicate. eauto. }
    iSplitL "Hb1".
    - iExists _. iR. iSplitR. { iPureIntro. lia. }
      iR. iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
      done.
    - iExists _. iR. iSplitR. { iPureIntro. lia. }
      iR. iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
      done.
  Qed.

  Lemma array_t_own_val_merge {rt} (ty : type rt) π (n1 n2 : nat) v1 v2 rs1 rs2 :
    (size_of_st ty.(ty_syn_type) * (n1 + n2) ≤ MaxInt ISize)%Z →
    v1 ◁ᵥ{π} rs1 @ array_t n1 ty -∗
    v2 ◁ᵥ{π} rs2 @ array_t n2 ty -∗
    (v1 ++ v2) ◁ᵥ{π} (rs1 ++ rs2) @ array_t (n1 + n2) ty.
  Proof.
    rewrite /ty_own_val/=.
    iIntros (Hsz) "(%ly1 & %Halg1 & %Hsz1 & %Hlen1 & %Hv1 & Hb1) (%ly2 & %Halg2 & %Hsz2 & %Hlen2 & %Hv2 & Hb2)".
    assert (ly1 = ly2) as <- by by eapply syn_type_has_layout_inj. clear Halg2.
    rewrite /size_of_st /use_layout_alg' Halg1 /= in Hsz.
    iExists ly1. iR. iSplitR. { iPureIntro. lia. }
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

  Lemma array_t_shr_split {rt} (ty : type rt) π κ n1 n2 l rs1 rs2 :
    length rs1 = n1 →
    length rs2 = n2 →
    l ◁ₗ{π, κ} (rs1 ++ rs2) @ array_t (n1 + n2) ty -∗
    l ◁ₗ{π, κ} rs1 @ array_t n1 ty ∗ (l offsetst{ty.(ty_syn_type)}ₗ n1) ◁ₗ{π, κ} rs2 @ array_t n2 ty.
  Proof.
    rewrite /ty_shr/=. iIntros (Hlen1 Hlen2).
    iIntros "(%ly & %Halg & %Hsz & %Hlen & %Hly & Hb)".
    rewrite big_sepL_app. iDestruct "Hb" as "(Hb1 & Hb2)".
    rewrite length_app in Hlen.
    iSplitL "Hb1".
    - iExists _. iR. iSplitR. { iPureIntro. lia. }
      iSplitR. { iPureIntro. lia. }
      iR. done.
    - iExists _. iR. iSplitR. { iPureIntro. lia. }
      iSplitR. { iPureIntro. lia. }
      rewrite /OffsetLocSt /use_layout_alg' Halg/=.
      iSplitR. { iPureIntro. eapply has_layout_loc_offset_loc; last done.
        by eapply use_layout_alg_wf. }
      rewrite /array_own_el_shr. setoid_rewrite offset_loc_offset_loc. rewrite Hlen1.
      setoid_rewrite Nat2Z.inj_add. done.
  Qed.

  Lemma array_t_shr_merge {rt} (ty : type rt) π κ (n1 n2 : nat) l rs1 rs2 :
    (size_of_st ty.(ty_syn_type) * (n1 + n2) ≤ MaxInt ISize)%Z →
    l ◁ₗ{π, κ} rs1 @ array_t n1 ty -∗
    (l offsetst{ty.(ty_syn_type)}ₗ n1) ◁ₗ{π, κ} rs2 @ array_t n2 ty -∗
    l ◁ₗ{π, κ} (rs1 ++ rs2) @ array_t (n1 + n2) ty.
  Proof.
    rewrite /ty_shr/=. iIntros (Hsz).
    iIntros "(%ly1 & %Halg1 & %Hsz1 & %Hlen1 & %Hly1 & Hb1) (%ly2 & %Halg2 & %Hsz2 & %Hlen2 & %Hly2 & Hb2)".
    assert (ly2 = ly1) as -> by by eapply syn_type_has_layout_inj. clear Halg2.
    rewrite /size_of_st /use_layout_alg' Halg1 /= in Hsz.
    iExists _. iR. iSplitR. { iPureIntro. lia. }
    rewrite length_app. iSplitR. { iPureIntro. lia. }
    iR. iApply (big_sepL_app).
    iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Halg1 /=.
    rewrite /array_own_el_shr. setoid_rewrite offset_loc_offset_loc. rewrite -Hlen1.
    setoid_rewrite Nat2Z.inj_add. done.
  Qed.
  (* Lemmas about ◁ₗ splitting in unfold.v *)
End lemmas.
