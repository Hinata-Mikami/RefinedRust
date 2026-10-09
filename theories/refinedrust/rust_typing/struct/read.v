From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.struct Require Import def subltype.

(** Reading an owned struct is automated over the named fields only.  The
    concrete layout, including padding, is opened only by the outer rule. *)
Section read.
  Context `{!typeGS Σ}.

  Definition struct_read_value : Type :=
    sigT (λ rt : RT, (type rt * rt)%type).
  Definition struct_read_out : Type :=
    sigT (λ rt : RT, (type rt * place_rfn rt)%type).

  Definition struct_read_value_out (x : struct_read_value) : struct_read_out :=
    match x with existT rt (ty, r) => existT rt (ty, #r) end.

  Fixpoint struct_read_value_rts (xs : list struct_read_value) : list RT :=
    match xs with
    | [] => []
    | existT rt _ :: xs => rt :: struct_read_value_rts xs
    end.

  Fixpoint struct_read_value_types (xs : list struct_read_value) :
      hlist type (struct_read_value_rts xs) :=
    match xs with
    | [] => +[]
    | existT _ (ty, _) :: xs => ty +:: struct_read_value_types xs
    end.

  Fixpoint struct_read_value_rfns (xs : list struct_read_value) :
      plist place_rfnRT (struct_read_value_rts xs) :=
    match xs with
    | [] => -[]
    | existT _ (_, r) :: xs => #r -:: struct_read_value_rfns xs
    end.

  Lemma struct_read_value_rts_length xs :
    length (struct_read_value_rts xs) = length xs.
  Proof. induction xs as [|[rt [ty r]] xs IH]; simpl; congruence. Qed.

  Lemma struct_read_value_hpzipl xs :
    hpzipl (struct_read_value_rts xs) (struct_read_value_types xs)
      (struct_read_value_rfns xs) = struct_read_value_out <$> xs.
  Proof. by induction xs as [|[rt [ty r]] xs IH]; simpl; rewrite ?IH. Qed.

  Definition ltype_read_as_struct_iter_cont_t : Type :=
    llctx → iProp Σ → list struct_read_value → list val →
      place_update_kind → iProp Σ.

  (** The automation plan is deliberately phrased only in terms of the
      specification fields.  In particular, it cannot expose padding. *)
  Fixpoint ltype_read_as_struct_iter (π : thread_id) (E : elctx)
      (L : llctx) (l : loc) (sls : struct_layout_spec)
      (src : list (sigT (λ rt, (ltype rt * place_rfn rt)%type)))
      (fields : list (var_name * syn_type)) (k : bor_kind)
      (bmin : place_update_kind)
      (T : ltype_read_as_struct_iter_cont_t) : iProp Σ :=
    match src, fields with
    | [], [] => T L True%I [] [] UpdBot
    | existT rt (lt, r) :: src, (name, st) :: fields =>
        ltype_read_as_struct_iter π E L l sls src fields k bmin
          (λ L2 R2 tys vs upd2,
            ltype_read_as π E L2 (l atst{sls}ₗ name) lt r k bmin
              (use_op_alg' st)
              (λ L3 R3 v rt' ty r' res,
                T L3 (R3 ∗ R2)%I
                  (existT rt' (ty, r') :: tys) (v :: vs)
                  (res.(puk_res_k) ⊔ₚₖ upd2)))
    | _, _ => False%I
    end.

  Definition struct_read_named_source_k (π : thread_id) (k : bor_kind)
      (sls : struct_layout_spec) (l : loc) (i0 : nat)
      (src : list (sigT (λ rt, (ltype rt * place_rfn rt)%type))) : iProp Σ :=
    struct_ltype_named_own π k l sls i0 src.

  Definition struct_read_named_source π sls l i0 src :=
    struct_read_named_source_k π Owned sls l i0 src.

  Definition struct_read_named_el_loc (π : thread_id) (sls : struct_layout_spec)
      (l : loc) (i : nat) (out : struct_read_out) (q : Qp) (v : val) : iProp Σ :=
    ∃ name st r',
      ⌜sls.(sls_fields) !! i = Some (name, st)⌝ ∗
      place_rfn_interp_owned (projT2 out).2 r' ∗
      ty_sidecond (projT2 out).1 ∗
      (l atst{sls}ₗ name) ↦{q} v ∗
      ⌜syn_type_has_layout (st_of (projT2 out).1 MetaNone)
        (ot_layout (use_op_alg' st))⌝ ∗
      ⌜v `has_layout_val` ot_layout (use_op_alg' st)⌝ ∗
      v ◁ᵥ{π, MetaNone} r' @ (projT2 out).1.

  Definition struct_read_named_el_loc_later (π : thread_id)
      (sls : struct_layout_spec) (l : loc) (i : nat)
      (out : struct_read_out) (q : Qp) (v : val) : iProp Σ :=
    ∃ name st r',
      ⌜sls.(sls_fields) !! i = Some (name, st)⌝ ∗
      place_rfn_interp_owned (projT2 out).2 r' ∗
      ty_sidecond (projT2 out).1 ∗
      (l atst{sls}ₗ name) ↦{q} v ∗
      ⌜syn_type_has_layout (st_of (projT2 out).1 MetaNone)
        (ot_layout (use_op_alg' st))⌝ ∗
      ⌜v `has_layout_val` ot_layout (use_op_alg' st)⌝ ∗
      ▷ v ◁ᵥ{π, MetaNone} r' @ (projT2 out).1.

  Definition struct_read_named_locs (π : thread_id) (sls : struct_layout_spec)
      (l : loc) (i0 : nat) (outs : list struct_read_out)
      (qs : list Qp) (vs : list val) : iProp Σ :=
    [∗ list] i ↦ out; qv ∈ outs; zip qs vs,
      struct_read_named_el_loc π sls l (i0 + i)%nat out qv.1 qv.2.

  Definition struct_read_named_locs_later (π : thread_id)
      (sls : struct_layout_spec) (l : loc) (i0 : nat)
      (outs : list struct_read_out) (qs : list Qp) (vs : list val) : iProp Σ :=
    [∗ list] i ↦ out; qv ∈ outs; zip qs vs,
      struct_read_named_el_loc_later π sls l (i0 + i)%nat out qv.1 qv.2.

  Fixpoint struct_read_conds (bmin : place_update_kind)
      (src : list (sigT (λ rt, (ltype rt * place_rfn rt)%type))) : iProp Σ :=
    match src with
    | [] => True
    | existT _ (lt, _) :: src =>
        typed_place_cond bmin lt lt ∗ struct_read_conds bmin src
    end%I.

  Lemma struct_read_conds_mono b1 b2 src :
    b1 ⪯ₚ b2 -∗ struct_read_conds b1 src -∗ struct_read_conds b2 src.
  Proof.
    iIntros "Hincl". iInduction src as [|[rt [lt r]] src] "IH"; simpl;
      first done.
    iIntros "(Hcond & Hconds)". iSplit.
    - iApply (typed_place_cond_incl with "Hincl Hcond").
    - iApply ("IH" with "Hincl Hconds").
  Qed.

  Lemma ltype_read_as_struct_iter_elim π E L l sls i0 src fields k bmin T F :
    lftE ⊆ F → ↑rrustN ⊆ F → lft_userE ⊆ F → shrE ⊆ F →
    fields = drop i0 sls.(sls_fields) →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
    ltype_read_as_struct_iter π E L l sls src fields k bmin T -∗
    struct_read_named_source_k π k sls l i0 src ={F}=∗
    ∃ L' R tys qs vs upd,
      llctx_interp L' ∗ struct_read_conds upd src ∗
      upd ⪯ₚ bmin ∗
      ⌜Forall2 (λ x st, ty_has_op_type (projT2 x).1 (use_op_alg' st.2))
          tys fields⌝ ∗
      ⌜Forall (λ x, Copyable (projT2 x).1) tys⌝ ∗
      ⌜length tys = length qs ∧ length qs = length vs⌝ ∗
      struct_read_named_locs_later π sls l i0
        (struct_read_value_out <$> tys) qs vs ∗
      logical_step F
        (struct_read_named_locs π sls l i0
          (struct_read_value_out <$> tys) qs vs -∗ |={F}=>
          struct_read_named_source_k π k sls l i0 src ∗ R) ∗
      T L' R tys vs upd.
  Proof.
    iIntros (Hlft Hrrust Huser Hshr Hfields) "#CTX #HE HL HT Hsrc".
    iInduction src as [|p src] "IH" forall (L i0 fields T Hfields).
    { destruct fields; last done. simpl.
      iModIntro. iExists L, True%I, [], [], [], UpdBot. simpl.
      iFrame. rewrite /struct_read_named_locs_later /struct_read_named_locs
        /struct_read_named_source_k /struct_ltype_named_own. simpl.
      iSplit; first iApply upd_bot_min.
      do 3 (iSplit; first done).
      iSplit; first done. iApply logical_step_intro.
      iIntros "_". iModIntro. done. }
    destruct p as [rt [lt r]].
    destruct fields as [|[name st] fields]; simpl; first done.
    iEval (rewrite /struct_read_named_source_k /struct_ltype_named_own /=) in "Hsrc".
    iDestruct "Hsrc" as "(Hhead & Htail)".
    have Hfield0 : sls.(sls_fields) !! i0 = Some (name, st).
    { rewrite -(Nat.add_0_r i0) -lookup_drop -Hfields //. }
    have Hfields_tail : fields = drop (S i0) sls.(sls_fields).
    { rewrite (drop_S _ _ _ Hfield0) in Hfields. by injection Hfields. }
    iMod ("IH" $! L (S i0) fields _ with "[] HL HT [Htail]") as
      (L2 R2 tys qs vs upd2)
      "(HL & Hconds & Hincl2 & %Hhot & %Hcopy & %Hlens & Hlocs & Hclose & HT)".
    { done. }
    { rewrite /struct_read_named_source_k.
      iApply (big_sepL_mono with "Htail").
      iIntros (j p Hlook) "Hfield". simpl.
      replace (i0 + S j)%nat with (S i0 + j)%nat by lia. done. }
    iDestruct "Hhead" as (name' st') "(%Hfield & Hhead)".
    rewrite Nat.add_0_r Hfield0 in Hfield. injection Hfield as [= <- <-].
    iMod ("HT" with "[] [] [] [] CTX HE HL Hhead") as
      (L3 R3 q v rt' ty r' res)
      "(%Hlyl & %Hlyv & %Hdec & %Hot & %Hcopy' & HL & Hpt & Hv & Hincl & Hcond & Hcl & HT)";
      [done.. |].
    iPoseProof (ty_own_val_sidecond with "Hv") as "#>Hsc".
    iModIntro. iExists L3, (R3 ∗ R2)%I,
      (existT rt' (ty, r') :: tys), (q :: qs), (v :: vs),
      (res.(puk_res_k) ⊔ₚₖ upd2).
    iFrame "HL HT". simpl.
    iSplitL "Hcond Hconds".
    { simpl. iSplit.
      - iApply (typed_place_cond_incl with "[] Hcond").
        iApply place_update_kind_max_incl_l.
      - iApply (struct_read_conds_mono with "[] Hconds").
         iApply place_update_kind_max_incl_r. }
    iSplitL "Hincl Hincl2".
    { iApply (place_update_kind_incl_lub with "Hincl Hincl2"). }
    iSplit. { iPureIntro. constructor; done. }
    iSplit. { iPureIntro. constructor; done. }
    iSplit. { iPureIntro. lia. }
    iSplitL "Hpt Hv Hlocs".
    { rewrite /struct_read_named_locs_later /= Nat.add_0_r.
      iSplitL "Hpt Hv".
      { rewrite /struct_read_named_el_loc_later.
        iExists name, st, r'. iFrame "Hpt Hv Hsc".
        iPureIntro. repeat split; try done. by eapply ty_op_type_stable. }
      iApply (big_sepL2_mono with "Hlocs").
      iIntros (j out qv Hlook1 Hlook2) "Hloc". simpl.
      replace (i0 + S j)%nat with (S i0 + j)%nat by lia. done. }
    iPoseProof (logical_step_sep with "Hcl Hclose") as "Hclose".
    iApply (logical_step_wand with "Hclose").
    iIntros "(Hcl & Hclose)". rewrite /struct_read_named_locs /=.
    iIntros "(Hhead & Htail)".
    rewrite /struct_read_named_el_loc Nat.add_0_r.
    iDestruct "Hhead" as (name'' st'' r'')
      "(%Hfield' & Hrfn & Hsc' & Hpt & %Hst' & %Hlyv' & Hv)".
    rewrite Hfield0 in Hfield'. injection Hfield' as [= <- <-].
    iDestruct "Hrfn" as "<-".
    destruct (Hdec inhabitant) as (ov & Hdecode).
    iMod ("Hcl" $! inhabitant ov with "[] Hpt Hv") as "(_ & Hhead & HR3)";
      first done.
    iMod ("Hclose" with "[Htail]") as "(Htail & HR2)".
    { iApply (big_sepL2_mono with "Htail").
      iIntros (j out qv Hlook1 Hlook2) "Hloc". simpl.
      replace (S (i0 + j)) with (i0 + S j)%nat by lia. done. }
    iModIntro. iFrame "HR3 HR2".
    rewrite /struct_read_named_source_k /struct_ltype_named_own /=.
    iSplitL "Hhead".
    { iExists name, st. rewrite Nat.add_0_r. iFrame. done. }
    iApply (big_sepL_mono with "Htail").
    iIntros (j p Hlook) "Hfield". simpl.
    replace (i0 + S j)%nat with (S (i0 + j)) by lia. done.
  Qed.

  Local Definition struct_read_padding_source_cell (π : thread_id) (k : bor_kind)
      (l : loc) (fields : field_list) (i : nat) (pad : option layout) : iProp Σ :=
    (from_option (λ ly,
        ∃ ly', ⌜snd <$> fields !! i = Some ly'⌝ ∗
          ⌜syn_type_has_layout
            (ltype_st (projT2 (struct_make_uninit_ltype ly)).1) ly'⌝ ∗
          (l +ₗ offset_of_idx fields i) ◁ₗ[π, k]
            (projT2 (struct_make_uninit_ltype ly)).2 @
            (projT2 (struct_make_uninit_ltype ly)).1) True pad)%I.

  Local Definition struct_read_padding_source_at (π : thread_id) (k : bor_kind)
      (l : loc) (fields : field_list) (i0 : nat)
      (pads : list (option layout)) : iProp Σ :=
    [∗ list] i ↦ pad ∈ pads,
      struct_read_padding_source_cell π k l fields (i0 + i) pad.

  Local Definition struct_read_padding_source (π : thread_id) (k : bor_kind)
      (l : loc) (fields : field_list) (pads : list (option layout)) : iProp Σ :=
    struct_read_padding_source_at π k l fields 0 pads.

  Local Definition struct_read_padding_loc_cell (π : thread_id) (l : loc)
      (fields : field_list) (q : Qp) (i : nat) (pad : option layout) : iProp Σ :=
    (from_option (λ ly, ∃ v,
        struct_own_el_loc π q v i fields l
          (projT2 (struct_make_uninit_type ly)).2
          (projT2 (struct_make_uninit_type ly)).1) True pad)%I.

  Local Definition struct_read_padding_locs_at (π : thread_id) (l : loc)
      (fields : field_list) (i0 : nat) (pads : list (option layout))
      (q : Qp) : iProp Σ :=
    [∗ list] i ↦ pad ∈ pads,
      struct_read_padding_loc_cell π l fields q (i0 + i) pad.

  Local Definition struct_read_padding_locs (π : thread_id) (l : loc)
      (fields : field_list) (pads : list (option layout)) (q : Qp) : iProp Σ :=
    struct_read_padding_locs_at π l fields 0 pads q.

  Local Definition struct_read_padding_loc_later_cell (π : thread_id) (l : loc)
      (fields : field_list) (q : Qp) (i : nat) (pad : option layout) : iProp Σ :=
    (from_option (λ ly, ∃ v,
        struct_own_el_loc_later π q v i fields l
          (projT2 (struct_make_uninit_type ly)).2
          (projT2 (struct_make_uninit_type ly)).1) True pad)%I.

  Local Definition struct_read_padding_locs_later_at (π : thread_id) (l : loc)
      (fields : field_list) (i0 : nat) (pads : list (option layout))
      (q : Qp) : iProp Σ :=
    [∗ list] i ↦ pad ∈ pads,
      struct_read_padding_loc_later_cell π l fields q (i0 + i) pad.

  Local Definition struct_read_padding_locs_later (π : thread_id) (l : loc)
      (fields : field_list) (pads : list (option layout)) (q : Qp) : iProp Σ :=
    struct_read_padding_locs_later_at π l fields 0 pads q.

  Local Definition struct_read_padding_close_cell (π : thread_id) F (l : loc)
      fields i pad : iProp Σ :=
    struct_read_padding_loc_cell π l fields 1 i pad -∗ |={F}=>
      struct_read_padding_source_cell π Owned l fields i pad%I.

  Local Lemma struct_read_padding_open π F l fields pads :
    lftE ⊆ F →
    struct_read_padding_source π Owned l fields pads ={F}=∗
      struct_read_padding_locs_later π l fields pads 1 ∗
      logical_step F
        (struct_read_padding_locs π l fields pads 1 -∗ |={F}=>
          struct_read_padding_source π Owned l fields pads).
  Proof.
    iIntros (HF) "Hpad".
    rewrite /struct_read_padding_source /struct_read_padding_locs_later.
    iMod (big_sepL_fupd F
      (λ i pad, struct_read_padding_loc_later_cell π l fields 1 i pad ∗
        logical_step F (struct_read_padding_close_cell π F l fields i pad))%I
      pads with "[Hpad]") as "Hpad".
    { iApply (big_sepL_wand with "Hpad"). iApply big_sepL_intro.
      iModIntro. iIntros (i pad Hlook) "Hpad".
      destruct pad as [ly|]; rewrite /struct_read_padding_source_cell
        /struct_read_padding_loc_later_cell /struct_read_padding_close_cell
        /struct_read_padding_loc_cell /=.
    - iDestruct "Hpad" as (ly') "(%Hfield & %Hst & Hhead)".
      rewrite /struct_make_uninit_ltype /UninitLtype in Hst.
      iPoseProof (ofty_ltype_acc_owned with "Hhead") as
        "(%ly0 & %Halg & %Hloc & Hsc & Hlb & >(%v & Hpt & Hv & Hcl))";
        first done.
      assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
      simpl in Hst.
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      iModIntro. iSplitL "Hpt Hv".
      { iExists v.
        rewrite /struct_own_el_loc_later /struct_make_uninit_type.
        iExists (), ly'. simpl. iSplit; first done.
        iSplit; first by iPureIntro.
        iSplit; first by iPureIntro.
        iSplit; first done. iFrame "Hpt".
        iSplit; first by iPureIntro. iNext. iExact "Hv". }
      iApply (logical_step_wand with "Hcl").
      iIntros "Hcl".
      iIntros "Hhead".
      iDestruct "Hhead" as (v') "Hhead".
      iDestruct "Hhead" as (r' ly'')
        "(Hrfn & %Hfield' & %Hst' & Hsc' & Hpt & %Hlyv' & Hv)".
      simpl in *. iDestruct "Hrfn" as "<-".
      rewrite Hfield in Hfield'. injection Hfield' as <-.
      iMod ("Hcl" $! v' _ (uninit (LiteralSynType ly)) () with
        "Hpt [] Hsc' Hv") as "Hhead".
      { iPureIntro. reflexivity. }
      iModIntro. iExists ly'. iFrame. done.
    - iModIntro. iSplit; first done. iApply logical_step_intro.
      iIntros "_". done. }
    rewrite big_sepL_sep. iDestruct "Hpad" as "(Hpad & Hcls)".
    iPoseProof (logical_step_big_sepL with "Hcls") as "Hcls".
    iModIntro. iFrame "Hpad".
    iApply (logical_step_wand with "Hcls").
    iIntros "Hcls Hpad".
    rewrite /struct_read_padding_locs /struct_read_padding_source.
    iApply big_sepL_fupd.
    iPoseProof (big_sepL_sep_2 with "Hcls Hpad") as "Hboth".
    iApply (big_sepL_wand with "Hboth").
    iApply big_sepL_intro. iModIntro. iIntros (i pad Hlook) "(Hcl & Hpad)".
    destruct pad; simpl; iApply ("Hcl" with "Hpad").
  Qed.

  Local Definition struct_read_named_physical (π : thread_id) (l : loc)
      (fields : field_list) (sls : struct_layout_spec) (outs : list struct_read_out)
      (q : Qp) (qs : list Qp) (vs : list val) : iProp Σ :=
    [∗ list] i ↦ out; qv ∈ outs; zip qs vs,
      ∃ j ly name, ⌜fields !! j = Some (Some name, ly)⌝ ∗
        ⌜named_fields fields !! i = Some (name, ly)⌝ ∗
        struct_own_el_loc π q qv.2 j fields l (projT2 out).2 (projT2 out).1.

  Local Definition struct_read_named_physical_later (π : thread_id) (l : loc)
      (fields : field_list) (sls : struct_layout_spec) (outs : list struct_read_out)
      (q : Qp) (qs : list Qp) (vs : list val) : iProp Σ :=
    [∗ list] i ↦ out; qv ∈ outs; zip qs vs,
      ∃ j ly name, ⌜fields !! j = Some (Some name, ly)⌝ ∗
        ⌜named_fields fields !! i = Some (name, ly)⌝ ∗
        struct_own_el_loc_later π q qv.2 j fields l (projT2 out).2 (projT2 out).1.

  Local Lemma struct_read_named_physical_open π F l sls sl outs qs vs :
    struct_layout_spec_has_layout sls sl →
    length outs = length qs → length qs = length vs →
    struct_read_named_locs_later π sls l 0 outs qs vs -∗
    let q := foldr Qp.min 1%Qp qs in
    struct_read_named_physical_later π l (sl_members sl) sls outs q qs vs ∗
    logical_step F
      (struct_read_named_physical π l (sl_members sl) sls outs q qs vs -∗
        struct_read_named_locs π sls l 0 outs qs vs).
  Proof.
    iIntros (Halg Hlen1 Hlen2) "Hloc".
    set (q := foldr Qp.min 1%Qp qs).
    assert (∀ i qi, qs !! i = Some qi → (q ≤ qi)%Qp) as Hmin.
    { intros i qi Hlook. induction qs as [|q0 qs IH] in i, Hlook, q |-*;
        first done. subst q. destruct i as [|i]; simpl in *.
      - injection Hlook as ->. apply Qp.le_min_l.
      - etrans; first apply Qp.le_min_r. by eapply IH. }
    rewrite /struct_read_named_locs_later /struct_read_named_physical_later.
    iAssert (([∗ list] i ↦ out; qv ∈ outs; zip qs vs,
      (∃ j ly name, ⌜sl_members sl !! j = Some (Some name, ly)⌝ ∗
        ⌜named_fields (sl_members sl) !! i = Some (name, ly)⌝ ∗
        struct_own_el_loc_later π q qv.2 j (sl_members sl) l
          (projT2 out).2 (projT2 out).1) ∗
      (∀ name st, ⌜sls_fields sls !! i = Some (name, st)⌝ -∗
        (l atst{sls}ₗ name) ↦{q} qv.2 -∗
        (l atst{sls}ₗ name) ↦{qv.1} qv.2)))%I with "[Hloc]" as "Hloc".
    { iApply (big_sepL2_wand with "Hloc"). iApply big_sepL2_intro.
      { rewrite length_zip Hlen1 Hlen2. lia. }
      iModIntro. iIntros (i out [qi v] Hout Hqv) "Hloc".
      apply lookup_zip in Hqv as (Hqi & Hv); simpl in *.
      iDestruct "Hloc" as (name st r')
        "(%Hfield & Hrfn & Hsc & Hpt & %Hstout & %Hlyv & Hvown)".
      specialize (struct_layout_spec_has_layout_alt_2 _ _ Halg) as Halg2.
      eapply Forall2_lookup_l in Halg2 as (member & Hmember & Hrel); last done.
      destruct member as [name' ly]. simpl in Hrel.
      destruct Hrel as (Hst & Hname). subst name'.
      destruct (syn_type_has_layout_op_alg _ _ Hst) as (ot & Hot & Hotly).
      have Hop : use_op_alg' st = ot by rewrite /use_op_alg' Hot.
      rewrite Hop Hotly in Hstout Hlyv.
      specialize (named_fields_lookup_1 _ _ _ _ Hmember) as (j & Hmember').
      iPoseProof (Fractional_fractional_le
        (λ q0, (l atst{sls}ₗ name) ↦{q0} v)%I qi q with "Hpt")
        as "(Hpt & Hfrac)".
      { eapply Hmin. done. }
      have Hloc : l atst{sls}ₗ name = l +ₗ offset_of_idx (sl_members sl) j.
      { rewrite /GetMemberLocSt /use_struct_layout_alg' Halg /= /offset_of.
        erewrite sl_index_of_lookup_2; done. }
      iEval (rewrite Hloc) in "Hpt".
      iSplitL "Hpt Hvown Hrfn Hsc".
      { iExists j, ly, name. iSplit; first done. iSplit; first done.
        rewrite /struct_own_el_loc_later. iExists r', ly.
        iFrame "Hrfn Hsc Hpt Hvown".
        iPureIntro. repeat split.
        - by rewrite Hmember'.
        - exact Hstout.
        - exact Hlyv. }
      iIntros (name0 st0) "%Hfield0 Hpt".
      rewrite Hfield in Hfield0. injection Hfield0 as <- <-.
      iApply "Hfrac". done. }
    rewrite big_sepL2_sep. iDestruct "Hloc" as "(Hloc & Hfrac)".
    iSplitL "Hloc"; first done.
    iApply logical_step_intro. rewrite /struct_read_named_physical
      /struct_read_named_locs.
    iIntros "Hloc".
    iPoseProof (big_sepL2_sep_2 with "Hloc Hfrac") as "Hloc".
    iApply (big_sepL2_wand with "Hloc"). iApply big_sepL2_intro.
    { rewrite length_zip Hlen1 Hlen2. lia. }
    iModIntro. iIntros (i out [qi v] Hout Hqv) "(Hloc & Hfrac)".
    apply lookup_zip in Hqv as (Hqi & Hv); simpl in *.
    iDestruct "Hloc" as (j ly name)
      "(%Hmember & %Hnamed & Hloc)".
    iDestruct "Hloc" as (r' ly')
      "(Hrfn & %Hmember' & %Hst & Hsc & Hpt & %Hlyv & Hvown)".
    rewrite Hmember in Hmember'. injection Hmember' as <-.
    specialize (struct_layout_spec_has_layout_alt_2 _ _ Halg) as Halg2.
    eapply Forall2_lookup_r in Halg2 as (field & Hfield & Hrel); last done.
    destruct field as [name' st]. simpl in Hrel.
    destruct Hrel as (Hst' & Hname). subst name'.
    iExists name, st, r'. iFrame "Hrfn Hsc Hvown". iSplit; first done.
    iSplitL "Hfrac Hpt".
    { iApply ("Hfrac" $! name st with "[]").
      { iPureIntro. done. }
      rewrite /GetMemberLocSt /use_struct_layout_alg' Halg /= /offset_of.
      erewrite sl_index_of_lookup_2; last done. iExact "Hpt". }
    destruct (syn_type_has_layout_op_alg _ _ Hst') as (ot & Hot & Hotly).
    rewrite /use_op_alg' Hot Hotly. done.
  Qed.

  Local Lemma struct_read_value_types_copy tys :
    Forall (λ x, Copyable (projT2 x).1) tys →
    TCHForall (λ _, Copyable) (struct_read_value_types tys).
  Proof.
    induction tys as [|[rt [ty r]] tys IH]; simpl; intros Hcopy.
    - constructor.
    - inversion Hcopy. constructor; [done | by apply IH].
  Qed.

  Local Lemma struct_read_value_types_hot tys
      (fields : list (var_name * syn_type)) :
    Forall2 (λ (x : struct_read_value) st,
      ty_has_op_type (projT2 x).1 (use_op_alg' st.2)) tys fields →
    Forall2 (λ ty st, ty_has_op_type (projT2 ty) (use_op_alg' st))
      (hzipl _ (struct_read_value_types tys)) fields.*2.
  Proof.
    intros Hhot. induction Hhot as [|[rt [ty r]] [name st] tys fields Hty _ IH];
      simpl; constructor; done.
  Qed.

  Local Lemma struct_read_conds_place b {rts} (lts : hlist ltype rts) rs sls :
    struct_read_conds b (hpzipl rts lts rs) -∗
    typed_place_cond b (StructLtype lts sls) (StructLtype lts sls).
  Proof.
    iIntros "Hconds". iApply struct_ltype_place_cond.
    iInduction rts as [|rt rts] "IH" forall (lts rs); inv_hlist lts; simpl;
      first done.
    intros lt lts. destruct rs as [r rs]. simpl.
    iDestruct "Hconds" as "($ & Hconds)".
    iApply ("IH" with "Hconds").
  Qed.

  Local Lemma struct_read_conds_raw b {rts} (lts : hlist ltype rts) rs :
    struct_read_conds b (hpzipl rts lts rs) -∗
    struct_read_conds b (hpzipl rts lts rs) ∗
    ([∗ list] ty1; ty2 ∈ hzipl rts lts; hzipl rts lts,
      typed_place_cond b (projT2 ty1) (projT2 ty2)).
  Proof.
    iIntros "Hconds".
    iInduction rts as [|rt rts] "IH" forall (lts rs); inv_hlist lts;
      simpl; first done.
    intros lt lts. destruct rs as [r rs]. simpl.
    iDestruct "Hconds" as "(#Hcond & Hconds)".
    iPoseProof ("IH" with "Hconds") as "(Hconds & Hraw)".
    iFrame "Hcond Hconds Hraw".
  Qed.

  Local Lemma struct_read_padding_fraction_at π l fields i0 pads qhi qlo :
    (qlo ≤ qhi)%Qp →
    struct_read_padding_locs_later_at π l fields i0 pads qhi -∗
    struct_read_padding_locs_later_at π l fields i0 pads qlo ∗
      (struct_read_padding_locs_at π l fields i0 pads qlo -∗
        struct_read_padding_locs_at π l fields i0 pads qhi).
  Proof.
    iIntros (Hq) "Hpad".
    rewrite /struct_read_padding_locs_later_at /struct_read_padding_locs_at.
    destruct (decide (qlo = qhi)) as [->|Hne].
    { iFrame. iIntros "$". }
    have Hlt : (qlo < qhi)%Qp by apply Qp.le_lteq in Hq as [|]; done.
    set (qr := Qp_total_sub qhi qlo Hlt).
    have Hsum : (qr + qlo = qhi)%Qp by apply Qp_total_sub_eq.
    iAssert ([∗ list] i ↦ pad ∈ pads,
      struct_read_padding_loc_later_cell π l fields qlo (i0 + i) pad ∗
      (struct_read_padding_loc_cell π l fields qlo (i0 + i) pad -∗
        struct_read_padding_loc_cell π l fields qhi (i0 + i) pad))%I with "[Hpad]" as "Hpad".
    { iApply (big_sepL_wand with "Hpad"). iApply big_sepL_intro.
      iModIntro. iIntros (i pad Hlook) "Hpad".
      destruct pad as [ly|]; simpl; last by iSplit.
      iDestruct "Hpad" as (v r' ly')
        "(Hrfn & %Hfield & %Hst & Hsc & Hpt & %Hly & Hv)".
      rewrite -Hsum.
      iDestruct (fractional (Φ := λ q0,
        (l +ₗ offset_of_idx fields (i0 + i)) ↦{q0} v)%I qr qlo with "Hpt")
        as "(Hrest & Hpt)".
      iSplitL "Hrfn Hsc Hpt Hv".
      { iExists v, r', ly'. iFrame. done. }
      iIntros "Hpad".
      iDestruct "Hpad" as (v' r'' ly'')
        "(Hrfn & %Hfield' & %Hst' & Hsc & Hpt & %Hly' & Hv)".
      rewrite Hfield in Hfield'. injection Hfield' as <-.
      iPoseProof (heap_pointsto_agree with "Hrest Hpt") as "%Heq".
      { rewrite /has_layout_val Hly Hly'. done. }
      subst v'. iExists v, r'', ly'. iFrame.
      rewrite (fractional (Φ := λ q0,
        (l +ₗ offset_of_idx fields (i0 + i)) ↦{q0} v)%I qr qlo).
      iFrame. done. }
    rewrite big_sepL_sep. iDestruct "Hpad" as "($ & Hclose)".
    iIntros "Hpad".
    iPoseProof (big_sepL_sep_2 with "Hclose Hpad") as "Hpad".
    iApply (big_sepL_wand with "Hpad"). iApply big_sepL_intro.
    iModIntro. iIntros (i pad Hlook) "(Hclose & Hpad)".
    by iApply "Hclose".
  Qed.

  Local Lemma struct_read_padding_fraction π l fields pads qhi qlo :
    (qlo ≤ qhi)%Qp →
    struct_read_padding_locs_later π l fields pads qhi -∗
    struct_read_padding_locs_later π l fields pads qlo ∗
      (struct_read_padding_locs π l fields pads qlo -∗
        struct_read_padding_locs π l fields pads qhi).
  Proof.
    apply struct_read_padding_fraction_at.
  Qed.

  Local Lemma struct_read_padding_open_shared_at π F l fields pads i0 κ q R :
    lftE ∪ ↑shrN ⊆ F →
    rrust_ctx -∗ q.[κ] -∗ (q.[κ] ={F}=∗ R) -∗
    struct_read_padding_source_at π (Shared κ) l fields i0 pads ={F}=∗
    ∃ qread,
      struct_read_padding_locs_later_at π l fields i0 pads qread ∗
      logical_step F
        (struct_read_padding_locs_at π l fields i0 pads qread -∗ |={F}=>
          struct_read_padding_source_at π (Shared κ) l fields i0 pads ∗ R).
  Proof.
    iIntros (HF) "#CTX Htok Htok_close Hpad".
    iInduction pads as [|pad pads] "IH" forall (i0 q R).
    { rewrite /struct_read_padding_source_at
        /struct_read_padding_locs_later_at /struct_read_padding_locs_at /=.
      iModIntro. iExists 1%Qp. iSplit; first done.
      iApply logical_step_intro. iIntros "_".
      iMod ("Htok_close" with "Htok") as "HR".
      iModIntro. iFrame. }
    iEval (rewrite /struct_read_padding_source_at big_sepL_cons) in "Hpad".
    iDestruct "Hpad" as "(Hhead & Htail)".
    iAssert (struct_read_padding_source_at π (Shared κ) l fields (S i0) pads)
      with "[Htail]" as "Htail".
    { rewrite /struct_read_padding_source_at.
      iApply (big_sepL_mono with "Htail").
      iIntros (i pad' Hlook) "Hpad". simpl.
      replace (i0 + S i) with (S (i0 + i)) by lia. done. }
    destruct pad as [ly|].
    - iDestruct "Hhead" as (ly') "(%Hfield & %Hst & #Hhead)".
      iEval (rewrite -{1}(Qp.div_2 q)
        (fractional (Φ := λ q, q.[κ])%I)) in "Htok".
      iDestruct "Htok" as "(Htok1 & Htok2)".
      iPoseProof (ofty_ltype_acc_shared with "Hhead") as
        "(%ly0 & %Halg & %Hloc & Hlb & >Hshr)"; first set_solver.
      iMod (copy_shr_acc with "CTX Hshr Htok1") as
        "(%ly1 & >%Hst1 & >%Hloc1 & %qhead & %v & (>Hpt & #Hv) & Hhead_close)";
        first done.
      iEval (rewrite Nat.add_0_r) in "Hpt Hhead_close".
      rewrite /struct_make_uninit_ltype /UninitLtype in Hst.
      assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
      assert (ly1 = ly') as -> by by eapply syn_type_has_layout_inj.
      simpl in Hst.
      iDestruct (ty_own_val_has_layout with "Hv") as "#>%Hlyv"; first done.
      iEval (rewrite -{1}(Qp.div_2 qhead)
        (fractional (Φ := λ q0,
          (l +ₗ offset_of_idx fields i0) ↦{q0} v)%I)) in "Hpt".
      iDestruct "Hpt" as "(Hhead_rest & Hpt)".
      iAssert (struct_read_padding_loc_later_cell π l fields (qhead / 2)%Qp i0
          (Some ly)) with "[Hpt]" as "Hhead_loc".
      { iExists v. rewrite /struct_own_el_loc_later /struct_make_uninit_type.
        iExists (), ly'. simpl. iSplit; first done.
        iSplit. { iPureIntro. rewrite Nat.add_0_r in Hfield. exact Hfield. }
        iSplit. { iPureIntro. exact Halg. }
        iSplit; first done. iFrame "Hpt".
        iSplit; first done. iExact "Hv". }
      iMod ("IH" $! (S i0) (q / 2)%Qp (((q / 2)%Qp).[κ])%I with
        "Htok2 [] Htail") as (qtail) "(Htail_loc & Htail_close)".
      { iIntros "Htok2". iModIntro. iExact "Htok2". }
      set (qread := Qp.min (qhead / 2)%Qp qtail).
      iPoseProof (struct_read_padding_fraction_at π l fields i0 [Some ly]
        (qhead / 2)%Qp qread with "[Hhead_loc]") as
        "(Hhead_loc & Hhead_frac)".
      { apply Qp.le_min_l. }
      { rewrite /struct_read_padding_locs_later_at /= Nat.add_0_r. iFrame. }
      iPoseProof (struct_read_padding_fraction_at π l fields (S i0) pads
        qtail qread with "Htail_loc") as "(Htail_loc & Htail_frac)".
      { apply Qp.le_min_r. }
      iModIntro. iExists qread.
      iSplitL "Hhead_loc Htail_loc".
      { rewrite /struct_read_padding_locs_later_at big_sepL_cons.
        iSplitL "Hhead_loc".
        { iEval (rewrite /struct_read_padding_locs_later_at /=) in "Hhead_loc".
          iDestruct "Hhead_loc" as "($ & _)". }
        rewrite /struct_read_padding_locs_later_at.
        iApply (big_sepL_mono with "Htail_loc").
        iIntros (i pad' Hlook) "Hpad". simpl.
        replace (i0 + S i) with (S i0 + i) by lia. done. }
      iAssert (logical_step F
          (struct_read_padding_locs_at π l fields i0 [Some ly] qread -∗
            |={F}=> ((q / 2)%Qp).[κ])) with
          "[Hhead_frac Hhead_rest Hhead_close]" as "Hhead_step".
      { iApply logical_step_intro.
        iIntros "Hloc".
        iPoseProof ("Hhead_frac" with "Hloc") as "Hloc".
        iEval (rewrite /struct_read_padding_locs_at /=) in "Hloc".
        iDestruct "Hloc" as "(Hloc & _)".
        iDestruct "Hloc" as (v' r' ly'')
          "(Hrfn & %Hfield' & %Hst' & Hsc & Hpt & %Hlyv' & Hv')".
        simpl in *. iDestruct "Hrfn" as "<-".
        rewrite Hfield in Hfield'. injection Hfield' as <-.
        iEval (rewrite Nat.add_0_r) in "Hpt".
        iPoseProof (heap_pointsto_agree with "Hhead_rest Hpt") as "%Heq".
        { rewrite /has_layout_val Hlyv Hlyv'. done. }
        subst v'. iCombine "Hhead_rest Hpt" as "Hpt".
        iMod ("Hhead_close" with "Hpt") as "Htok1".
        iModIntro. iExact "Htok1". }
      iPoseProof (logical_step_sep with "Hhead_step Htail_close") as "Hclose".
      iApply (logical_step_wand with "Hclose").
      iIntros "(Htok1 & Htail_close) Hloc".
      rewrite /struct_read_padding_locs_at big_sepL_cons.
      iDestruct "Hloc" as "(Hhead_loc & Htail_loc)".
      iMod ("Htok1" with "[Hhead_loc]") as "Htok1".
      { rewrite /struct_read_padding_locs_at /=. iFrame. }
      iPoseProof ("Htail_frac" with "[Htail_loc]") as "Htail_loc".
      { rewrite /struct_read_padding_locs_at.
        iApply (big_sepL_mono with "Htail_loc").
        iIntros (i pad' Hlook) "Hpad". simpl.
        replace (i0 + S i) with (S (i0 + i)) by lia. done. }
      iMod ("Htail_close" with "Htail_loc") as "(Htail & Htok2)".
      iCombine "Htok1 Htok2" as "Htok".
      iMod ("Htok_close" with "Htok") as "HR".
      iModIntro. iSplitR "HR"; last iExact "HR".
      rewrite /struct_read_padding_source_at big_sepL_cons.
      iSplitL "Hhead".
      { iExists ly'. iFrame "#". done. }
      rewrite /struct_read_padding_source_at.
      iApply (big_sepL_mono with "Htail").
      iIntros (i pad' Hlook) "Hpad". simpl.
      replace (i0 + S i) with (S i0 + i) by lia. done.
    - iMod ("IH" $! (S i0) q R with "Htok Htok_close Htail")
        as (qread) "(Htail_loc & Htail_close)".
      iModIntro. iExists qread.
      iSplitL "Htail_loc".
      { rewrite /struct_read_padding_locs_later_at big_sepL_cons /=.
        iSplit; first done.
        rewrite /struct_read_padding_locs_later_at.
        iApply (big_sepL_mono with "Htail_loc").
        iIntros (i pad' Hlook) "Hpad". simpl.
        replace (i0 + S i) with (S i0 + i) by lia. done. }
      iApply (logical_step_wand with "Htail_close").
      iIntros "Htail_close Hloc".
      rewrite /struct_read_padding_locs_at big_sepL_cons /=.
      iDestruct "Hloc" as "(_ & Htail_loc)".
      iMod ("Htail_close" with "[Htail_loc]") as "(Htail & HR)".
      { rewrite /struct_read_padding_locs_at.
        iApply (big_sepL_mono with "Htail_loc").
        iIntros (i pad' Hlook) "Hpad". simpl.
        replace (i0 + S i) with (S (i0 + i)) by lia. done. }
      iModIntro. iFrame "HR".
      rewrite /struct_read_padding_source_at big_sepL_cons /=.
      iSplit; first done.
      rewrite /struct_read_padding_source_at.
      iApply (big_sepL_mono with "Htail").
      iIntros (i pad' Hlook) "Hpad". simpl.
      replace (i0 + S i) with (S i0 + i) by lia. done.
  Qed.

  Local Lemma struct_read_padding_open_shared π F l fields pads κ q R :
    lftE ∪ ↑shrN ⊆ F →
    rrust_ctx -∗ q.[κ] -∗ (q.[κ] ={F}=∗ R) -∗
    struct_read_padding_source π (Shared κ) l fields pads ={F}=∗
    ∃ qread,
      struct_read_padding_locs_later π l fields pads qread ∗
      logical_step F
        (struct_read_padding_locs π l fields pads qread -∗ |={F}=>
          struct_read_padding_source π (Shared κ) l fields pads ∗ R).
  Proof.
    apply struct_read_padding_open_shared_at.
  Qed.

  Local Lemma struct_read_named_fraction_le_one qs :
    (foldr Qp.min 1 qs ≤ 1)%Qp.
  Proof.
    induction qs as [|q qs IH]; simpl; first done.
    etrans; [apply Qp.le_min_r | done].
  Qed.

  Local Definition struct_read_named_physical_any (π : thread_id) (l : loc)
      (fields : field_list) (sls : struct_layout_spec) (outs : list struct_read_out)
      (q : Qp) (qs : list Qp) (vs : list val) : iProp Σ :=
    [∗ list] i ↦ out; qv ∈ outs; zip qs vs,
      ∃ j ly name, ⌜fields !! j = Some (Some name, ly)⌝ ∗
        ⌜named_fields fields !! i = Some (name, ly)⌝ ∗
        ∃ v, struct_own_el_loc π q v j fields l (projT2 out).2 (projT2 out).1.

  Local Lemma field_named_lookup_inj fields i j name ly ly' :
    NoDup (field_names fields) →
    fields !! i = Some (Some name, ly) →
    fields !! j = Some (Some name, ly') →
    i = j.
  Proof.
    induction fields as [|[name0 ly0] fields IH] in i, j |-*; first done.
    destruct name0 as [name0|].
    - simpl. intros Hnd. inversion Hnd as [|? ? Hnot Hnd']; subst.
      destruct i as [|i], j as [|j]; simpl.
      + done.
      + intros [= <- _] Hlook. exfalso. apply Hnot.
        apply named_fields_lookup_2 in Hlook as [k Hlook].
        eapply (elem_of_named_fields_field_names fields name0 ly').
        eapply list_elem_of_lookup_2. exact Hlook.
      + intros Hlook [= <- _]. exfalso. apply Hnot.
        apply named_fields_lookup_2 in Hlook as [k Hlook].
        eapply (elem_of_named_fields_field_names fields name0 ly).
        eapply list_elem_of_lookup_2. exact Hlook.
      + intros Hlook1 Hlook2. f_equal. by eapply IH.
    - simpl. intros Hnd. destruct i as [|i], j as [|j]; simpl; try done.
      intros Hlook1 Hlook2. f_equal. by eapply IH.
  Qed.

  Local Lemma struct_read_named_fraction π l fields sls outs qs vs q q' :
    NoDup (field_names fields) →
    (q' < q)%Qp →
    struct_read_named_physical_later π l fields sls outs q qs vs -∗
      struct_read_named_physical_later π l fields sls outs q' qs vs ∗
      (struct_read_named_physical_any π l fields sls outs q' qs vs -∗
        struct_read_named_physical π l fields sls outs q qs vs).
  Proof.
    iIntros (Hnd Hlt) "Hnamed".
    set (qr := Qp_total_sub q q' Hlt).
    have Hsum : (qr + q' = q)%Qp by apply Qp_total_sub_eq.
    rewrite /struct_read_named_physical_later /struct_read_named_physical.
    iPoseProof (big_sepL2_length with "Hnamed") as "%Hlen".
    iAssert ([∗ list] i ↦ out; qv ∈ outs; zip qs vs,
      (∃ j ly name, ⌜fields !! j = Some (Some name, ly)⌝ ∗
        ⌜named_fields fields !! i = Some (name, ly)⌝ ∗
        struct_own_el_loc_later π q' qv.2 j fields l
          (projT2 out).2 (projT2 out).1) ∗
      ((∃ j ly name, ⌜fields !! j = Some (Some name, ly)⌝ ∗
        ⌜named_fields fields !! i = Some (name, ly)⌝ ∗
        ∃ v, struct_own_el_loc π q' v j fields l
          (projT2 out).2 (projT2 out).1) -∗
       ∃ j ly name, ⌜fields !! j = Some (Some name, ly)⌝ ∗
        ⌜named_fields fields !! i = Some (name, ly)⌝ ∗
        struct_own_el_loc π q qv.2 j fields l
          (projT2 out).2 (projT2 out).1))%I with "[Hnamed]" as "Hnamed".
    { iApply (big_sepL2_wand with "Hnamed"). iApply big_sepL2_intro; first exact Hlen.
      iModIntro. iIntros (i out [qi vi] Hout Hqv)
        "(%j & %ly & %name & %Hmem & %Hnamed & %r & %ly' & Hrfn & %Hfield & %Hst & Hsc & Hpt & %Hly & Hv)".
      rewrite -Hsum.
      iDestruct (fractional (Φ := λ q0,
        (l +ₗ offset_of_idx fields j) ↦{q0} vi)%I qr q' with "Hpt")
        as "(Hrest & Hpt)".
      iSplitL "Hrfn Hsc Hpt Hv".
      { iExists j, ly, name. do 2 (iSplit; first done).
        iExists r, ly'. iFrame. done. }
      iIntros "(%j2 & %ly2 & %name2 & %Hmem2 & %Hnamed2 & %w & %r2 & %ly2' & Hrfn & %Hfield2 & %Hst2 & Hsc & Hpt & %Hly2v & Hv)".
      rewrite Hnamed in Hnamed2. injection Hnamed2 as [= <- <-].
      have -> : j2 = j by eapply field_named_lookup_inj.
      rewrite Hmem in Hfield. injection Hfield as <-.
      rewrite Hmem2 in Hfield2. injection Hfield2 as <-.
      iPoseProof (heap_pointsto_agree with "Hrest Hpt") as "%Heq".
      { rewrite /has_layout_val Hly Hly2v. done. }
      subst w. iExists j, ly, name. do 2 (iSplit; first done).
      iExists r2, ly. iFrame.
      rewrite (fractional (Φ := λ q0,
        (l +ₗ offset_of_idx fields j) ↦{q0} vi)%I qr q').
      iFrame. repeat iSplit; iPureIntro; try done. by rewrite Hmem. }
    rewrite big_sepL2_sep. iDestruct "Hnamed" as "($ & Hclose)".
    iIntros "Hnamed".
    rewrite /struct_read_named_physical_any.
    iPoseProof (big_sepL2_sep_2 with "Hclose Hnamed") as "Hnamed".
    iApply (big_sepL2_wand with "Hnamed"). iApply big_sepL2_intro; first done.
    iModIntro. iIntros (i out qv Hout Hqv) "(Hclose & Hnamed)".
    iApply ("Hclose" with "Hnamed").
  Qed.

  Local Lemma struct_read_components {rts} (lts : hlist ltype rts) rs
      π E L l sls sl k qpad Rpad bmin T F :
    lftE ⊆ F → ↑rrustN ⊆ F → lft_userE ⊆ F → shrE ⊆ F →
    use_struct_layout_alg sls = Some sl →
    l `has_layout_loc` sl → length sls.(sls_fields) = length rts →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
    ltype_read_as_struct_iter π E L l sls (hpzipl rts lts rs)
      sls.(sls_fields) k bmin T -∗
    loc_in_bounds l 0 sl.(ly_size) -∗
    struct_read_named_source_k π k sls l 0 (hpzipl rts lts rs) -∗
    struct_read_padding_locs_later π l (sl_members sl)
      (pad_struct (sl_members sl)
        (replicate (length (hpzipl rts lts rs)) None) Some) qpad -∗
    logical_step F
      (struct_read_padding_locs π l (sl_members sl)
        (pad_struct (sl_members sl)
          (replicate (length (hpzipl rts lts rs)) None) Some) qpad -∗ |={F}=>
       struct_read_padding_source π k l (sl_members sl)
      (pad_struct (sl_members sl)
        (replicate (length (hpzipl rts lts rs)) None) Some) ∗ Rpad) ={F}=∗
    ∃ (L' : llctx) (R : iProp Σ) (tys : list struct_read_value)
      (qs : list Qp) (vs : list val) (upd : place_update_kind) (q : Qp)
      (v : val),
      llctx_interp L' ∗ l ↦{q} v ∗
      ▷ v ◁ᵥ{π, MetaNone} struct_read_value_rfns tys @
        struct_t sls (struct_read_value_types tys) ∗
      upd ⪯ₚ bmin ∗ struct_read_conds upd (hpzipl rts lts rs) ∗
      ⌜l `has_layout_loc` ot_layout (use_op_alg' sls)⌝ ∗
      ⌜v `has_layout_val` ot_layout (use_op_alg' sls)⌝ ∗
      ⌜∀ st, ∃ ov, decode_op_val v (use_op_alg' sls) st = Some ov⌝ ∗
      ⌜ty_has_op_type (struct_t sls (struct_read_value_types tys))
        (use_op_alg' sls)⌝ ∗
      ⌜Copyable (struct_t sls (struct_read_value_types tys))⌝ ∗
      logical_step F (∀ st ov,
        ⌜decode_op_val v (use_op_alg' sls) st = Some ov⌝ -∗
        l ↦{q} v -∗
        v ◁ᵥ{π, MetaNone} struct_read_value_rfns tys @
          struct_t sls (struct_read_value_types tys) ={F}=∗
        encode_op_val ov ◁ᵥ{π, MetaNone} struct_read_value_rfns tys @
          struct_t sls (struct_read_value_types tys) ∗
        struct_read_named_source_k π k sls l 0 (hpzipl rts lts rs) ∗
        struct_read_padding_source π k l (sl_members sl)
          (pad_struct (sl_members sl)
            (replicate (length (hpzipl rts lts rs)) None) Some) ∗ Rpad ∗ R) ∗
      T L' R tys vs upd.
  Proof.
    iIntros (Hlft Hrrust Huser Hshr Halg Hly Hlen)
      "#CTX #HE HL HT #Hlb Hnamed Hpadding Hpadding_close".
    have Hsl : struct_layout_spec_has_layout sls sl := Halg.
    have Hnd : NoDup (field_names (sl_members sl)).
    { specialize (sl_nodup sl). by rewrite bool_decide_spec. }
    set (pads := pad_struct (sl_members sl)
      (replicate (length (hpzipl rts lts rs)) None) Some).
    iMod (ltype_read_as_struct_iter_elim with
      "CTX HE HL HT Hnamed") as (L' R tys qs vs upd)
      "(HL & Hconds & Hincl & %Hhot & %Hcopy & %Hlens & Hnamed & Hnamed_close & HT)";
      [done.. |].
    pose proof Hhot as Htyfields. apply Forall2_length in Htyfields.
    destruct Hlens as [Htysqs Hqsvs].
    iPoseProof (struct_read_named_physical_open π F l sls sl
      (struct_read_value_out <$> tys) qs vs with "Hnamed") as
      "(Hnamed & Hnamed_phys_close)".
    { exact Hsl. }
    { rewrite length_fmap. exact Htysqs. }
    { exact Hqsvs. }
    set (q0 := foldr Qp.min 1%Qp qs).
    set (qbase := Qp.min q0 qpad).
    set (q := (qbase / 2)%Qp).
    have Hqbase : (q < qbase)%Qp.
    { apply Qp.div_lt. done. }
    have Hqq0 : (q < q0)%Qp.
    { eapply Qp.lt_le_trans; first exact Hqbase. apply Qp.le_min_l. }
    iPoseProof (struct_read_named_fraction π l (sl_members sl) sls
      (struct_read_value_out <$> tys) qs vs q0 q Hnd Hqq0 with "Hnamed") as
      "(Hnamed & Hnamed_frac_close)".
    have Hqpad : (q ≤ qpad)%Qp.
    { etrans; first exact (Qp.lt_le_incl _ _ Hqbase). apply Qp.le_min_r. }
    iPoseProof (struct_read_padding_fraction _ _ _ _ qpad q
      Hqpad with "Hpadding") as
      "(Hpadding & Hpadding_frac_close)".
    iAssert ([∗ list] i ↦ ty ∈
        pad_struct (sl_members sl) (struct_read_value_out <$> tys)
          struct_make_uninit_type,
        ∃ v, struct_own_el_loc_later π q v i (sl_members sl) l
          (projT2 ty).2 (projT2 ty).1)%I
      with "[Hnamed Hpadding]" as "Hout".
    { iApply (pad_struct_unfocus (struct_read_value_out <$> tys)
        (sl_members sl) struct_make_uninit_type
        (λ i ty, ∃ v, struct_own_el_loc_later π q v i (sl_members sl) l
          (projT2 ty).2 (projT2 ty).1)%I with "[Hnamed] [Hpadding]").
      - rewrite length_fmap. etrans; first exact Htyfields.
        apply struct_layout_spec_has_layout_fields_length'. done.
      - done.
      - rewrite /struct_read_named_physical_later.
        iPoseProof (big_sepL2_to_big_sepL_lookup_r with "Hnamed") as "Hnamed".
        iApply (big_sepL_impl with "Hnamed").
        iModIntro. iIntros (i ty Hlook)
          "(%qv & %Hlookqv & %j & %ly & %name & %Hmem & %Hnamed & Hty)".
        destruct qv as [qi vi].
        iExists j, ly, name. iFrame. done.
      - rewrite /struct_read_padding_locs_later /pads length_fmap
          Htyfields Hlen length_hpzipl. done. }
    iPoseProof (struct_own_val_extract_pointsto_later π q sls sl l
      (struct_read_value_out <$> tys) Halg with "Hlb Hout") as
      (v) "(Hpt & %Hlyv & Hv)".
    { rewrite length_fmap. exact Htyfields. }
    have Hsyn : syn_type_has_layout sls sl.
    { rewrite /syn_type_has_layout.
      by eapply use_struct_layout_alg_Some_inv. }
    have Hwhole_hot : ty_has_op_type
        (struct_t sls (struct_read_value_types tys)) (use_op_alg' sls).
    { eapply ty_has_op_type_struct_canonical'; first exact Hsyn.
      by apply struct_read_value_types_hot. }
    have Hwhole_copy : Copyable
        (struct_t sls (struct_read_value_types tys)).
    { apply struct_t_copy. by apply struct_read_value_types_copy. }
    have Hoply : ot_layout (use_op_alg' sls) = sl.
    { eapply syn_type_has_layout_inj.
      - exact (ty_op_type_stable
          (struct_t sls (struct_read_value_types tys)) _ Hwhole_hot).
      - exact Hsyn. }
    iAssert (▷ v ◁ᵥ{π, MetaNone} struct_read_value_rfns tys @
        struct_t sls (struct_read_value_types tys))%I with "[Hv]" as "Hv".
    { iNext. rewrite /ty_own_val /= struct_t_own_val_unfold
        /struct_t_own_val_def.
      iExists sl. iSplit; first done. iSplit; first done.
      iSplit; first by rewrite struct_read_value_rts_length.
      iSplit; first done. by rewrite struct_read_value_hpzipl. }
    iAssert (▷ ⌜∀ st, ∃ ov,
        decode_op_val v (use_op_alg' sls) st = Some ov⌝)%I
      with "[Hv]" as "#Hdec".
    { iNext. iIntros (st).
      iPoseProof (ty_decodable _ (struct_t sls (struct_read_value_types tys))
        (use_op_alg' sls) st π (struct_read_value_rfns tys) v with "Hv")
        as (ov) "%Hov"; first exact Hwhole_hot.
      iPureIntro. eauto. }
    iMod "Hdec" as "%Hdec".
    iModIntro.
    iExists L', R, tys, qs, vs, upd, q, v.
    iFrame "HL Hpt Hv Hincl Hconds HT".
    iSplit; first by rewrite Hoply.
    iSplit; first by rewrite Hoply.
    do 3 (iSplit; first done).
    { iPoseProof (logical_step_sep with "Hnamed_phys_close Hnamed_close") as "Hsteps".
      iPoseProof (logical_step_sep with "Hsteps Hpadding_close") as "Hsteps".
      iApply (logical_step_wand with "Hsteps").
      iIntros "((Hnamed_phys_close & Hnamed_close) & Hpadding_close)".
      iIntros (st ov) "%Hdecode Hpt Hv".
      pose (Hcopy_inst := Hwhole_copy).
      iDestruct "Hv" as "#Hv".
      iPoseProof "Hv" as "Hv'".
      iPoseProof (ty_encode_compat _
        (struct_t sls (struct_read_value_types tys))
        (use_op_alg' sls) st π (struct_read_value_rfns tys) v ov
        Hwhole_hot Hdecode with "Hv'") as "Henc".
      rewrite /ty_own_val /= struct_t_own_val_unfold /struct_t_own_val_def.
      iDestruct "Hv" as (sl')
        "(%Hmeta & %Halg' & %Hlen' & %Hlyv' & Hv)".
      rewrite Halg in Halg'. injection Halg' as <-.
      iEval (rewrite struct_read_value_hpzipl) in "Hv".
      iPoseProof (struct_own_val_join_pointsto π q sls sl l v
        (struct_read_value_out <$> tys) Halg with "Hpt Hv") as "Hout".
      { rewrite length_fmap. exact Htyfields. }
      { exact Hlyv'. }
      iPoseProof (pad_struct_focus (struct_read_value_out <$> tys)
        (sl_members sl) struct_make_uninit_type
        (λ i ty, ∃ v, struct_own_el_loc π q v i (sl_members sl) l
          (projT2 ty).2 (projT2 ty).1)%I with "Hout") as
        "(Hnamed & Hpadding)".
      { rewrite length_fmap. etrans; first exact Htyfields.
        apply struct_layout_spec_has_layout_fields_length'. done. }
      { done. }
      iAssert (struct_read_named_physical_any π l (sl_members sl) sls
          (struct_read_value_out <$> tys) q qs vs)%I
        with "[Hnamed]" as "Hnamed".
      { rewrite /struct_read_named_physical_any.
        iApply big_sepL2_from_big_sepL_lookup_r.
        { rewrite length_fmap length_zip Htysqs Hqsvs Nat.min_id. done. }
        iApply (big_sepL_impl with "Hnamed").
        iModIntro. iIntros (i out Hlook)
          "(%j & %ly & %name & %Hmem & %Hnamed & %w & Hcell)".
        have Hi : i < length tys.
        { have Hi' := lookup_lt_Some _ _ _ Hlook.
          by rewrite length_fmap in Hi'. }
        destruct (lookup_lt_is_Some_2 qs i) as [qi Hqi]; first lia.
        destruct (lookup_lt_is_Some_2 vs i) as [vi Hvi]; first lia.
        iExists (qi, vi). iSplit.
        { iPureIntro. apply lookup_zip_Some. done. }
        iExists j, ly, name. iFrame. done. }
      iPoseProof ("Hnamed_frac_close" with "Hnamed") as "Hnamed".
      iPoseProof ("Hnamed_phys_close" with "Hnamed") as "Hnamed".
      iMod ("Hnamed_close" with "Hnamed") as "(Hnamed & HR)".
      iEval (rewrite length_fmap Htyfields Hlen) in "Hpadding".
      iEval (rewrite /struct_read_padding_locs /pads length_hpzipl) in
        "Hpadding_frac_close".
      iPoseProof ("Hpadding_frac_close" with "Hpadding") as "Hpadding".
      iEval (rewrite /struct_read_padding_locs /struct_read_padding_source
        /pads length_hpzipl) in "Hpadding_close".
      iMod ("Hpadding_close" with "Hpadding") as "(Hpadding & HRpad)".
      rewrite /pads length_hpzipl.
      iModIntro. iFrame "Henc Hnamed Hpadding HRpad HR". }
  Qed.

  Lemma ltype_read_as_struct_owned {rts} (lts : hlist ltype rts) rs
      π E L l sls bmin T :
    ltype_read_as_struct_iter π E L l sls (hpzipl rts lts rs) sls.(sls_fields) Owned bmin 
      (λ L' R tys vs upd,
        ∀ v,
          T L' R v (plistRT (struct_read_value_rts tys))
            (struct_t sls (struct_read_value_types tys))
            (struct_read_value_rfns tys)
            (mkPUKRes upd opt_place_update_eq_refl opt_place_update_eq_refl)) ⊢
    ltype_read_as π E L l (StructLtype lts sls) (#rs) Owned bmin
      (use_op_alg' sls) T.
  Proof.
    iIntros "HT" (F Hlft Hrrust Huser Hshr) "#CTX #HE HL Hl".
    iPoseProof (struct_ltype_acc_owned F with "Hl") as
      "(%sl & %Halg & %Hly & %Hlen & #Hlb & >(Hl & Hstruct_close))";
      first done.
    have Hsl : struct_layout_spec_has_layout sls sl := Halg.
    iPoseProof (struct_ltype_focus_components_with_padding π lts rs sls sl
      Owned l with "Hl") as "(Hnamed & Hpadding & Hunfocus)"; [lia | done |].
    iEval (rewrite -/struct_read_named_source_k) in "Hnamed".
    iEval (rewrite -/struct_read_named_source_k) in "Hunfocus".
    iAssert (struct_read_padding_source π Owned l (sl_members sl)
      (pad_struct (sl_members sl)
        (replicate (length (hpzipl rts lts rs)) None) Some))%I
      with "[Hpadding]" as "Hpadding".
    { rewrite /struct_read_padding_source /struct_ltype_padding_own
        length_hpzipl. done. }
    iMod (struct_read_padding_open with "Hpadding") as
      "(Hpadding & Hpadding_close)"; first done.
    iAssert (logical_step F
        (struct_read_padding_locs π l (sl_members sl)
          (pad_struct (sl_members sl)
            (replicate (length (hpzipl rts lts rs)) None) Some) 1 -∗ |={F}=>
         struct_read_padding_source π Owned l (sl_members sl)
          (pad_struct (sl_members sl)
            (replicate (length (hpzipl rts lts rs)) None) Some) ∗ True))%I
      with "[Hpadding_close]" as "Hpadding_close".
    { iApply (logical_step_wand with "Hpadding_close").
      iIntros "Hpadding_close Hpadding".
      iMod ("Hpadding_close" with "Hpadding") as "Hpadding".
      iModIntro. iFrame. }
    iMod (struct_read_components with
      "CTX HE HL HT Hlb Hnamed Hpadding Hpadding_close") as
      (L' R tys qs vs upd q v)
      "(HL & Hpt & Hv & Hincl & Hconds & %Hloc & %Hlyv & %Hdec & %Hhot & %Hcopy & Hclose & HT)";
      [done.. |].
    iModIntro. iExists L', R, q, v,
      (plistRT (struct_read_value_rts tys)),
      (struct_t sls (struct_read_value_types tys)),
      (struct_read_value_rfns tys),
      (mkPUKRes upd opt_place_update_eq_refl opt_place_update_eq_refl).
    do 5 (iSplitR; first done). iFrame "HL Hpt Hv Hincl".
    iSplitL "Hconds"; first iApply (struct_read_conds_place with "Hconds").
    iSplitL "Hclose Hstruct_close Hunfocus".
    { iPoseProof (logical_step_sep with "Hclose Hstruct_close") as "Hsteps".
      iPoseProof (logical_step_frame_r with "Hsteps Hunfocus") as "Hsteps".
      iApply (logical_step_wand with "Hsteps").
      iIntros "((Hclose & Hstruct_close) & Hunfocus)".
      iIntros (st ov) "%Hdecode Hpt Hv".
      iMod ("Hclose" $! st ov with "[] Hpt Hv") as
        "(Henc & Hnamed & Hpadding & _ & HR)"; first done.
      iAssert (struct_ltype_padding_own π Owned l (sl_members sl)
          (length rts))%I with "[Hpadding]" as "Hpadding".
      { rewrite /struct_ltype_padding_own /struct_read_padding_source
          length_hpzipl. done. }
      iPoseProof ("Hunfocus" with "Hnamed Hpadding") as "Hsource".
      iMod ("Hstruct_close" $! rts lts rs with "[] Hsource") as "Hstruct";
        first done.
      iModIntro. iFrame. }
    iApply "HT".
  Qed.

  Definition ltype_read_as_struct_owned_inst :=
    [instance @ltype_read_as_struct_owned].
  Global Existing Instance ltype_read_as_struct_owned_inst | 20.

  Lemma ltype_read_as_struct_shared {rts} (lts : hlist ltype rts) rs
      π E L l sls κ bmin T :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L1),
      ltype_read_as_struct_iter π E L1 l sls
        (hpzipl rts lts rs) sls.(sls_fields) (Shared κ) bmin
        (λ L2 R tys vs upd,
          ∀ v,
            T L2 (llft_elt_toks κs ∗ R) v
              (plistRT (struct_read_value_rts tys))
              (struct_t sls (struct_read_value_types tys))
              (struct_read_value_rfns tys)
              (mkPUKRes upd opt_place_update_eq_refl
                opt_place_update_eq_refl))) ⊢
    ltype_read_as π E L l (StructLtype lts sls) (#rs) (Shared κ) bmin
      (use_op_alg' sls) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L1 & %Hal & HT)" (F Hlft Hrrust Huser Hshr)
      "#CTX #HE HL Hl".
    iMod (lctx_lft_alive_count_tok with "HE HL") as
      (qtok) "(Htok & Hcltok & HL)"; [done.. |].
    iPoseProof (struct_ltype_acc_shared F with "Hl") as
      "(%sl & %Halg & %Hly & %Hlen & #Hlb & Hacc)"; first done.
    iMod "Hacc" as "(%Hxr & Hl & Hstruct_close)".
    have Hsl : struct_layout_spec_has_layout sls sl := Halg.
    iPoseProof (struct_ltype_focus_components_with_padding π lts rs sls sl
      (Shared κ) l with "Hl") as "(Hnamed & Hpadding & Hunfocus)".
    { lia. }
    { exact Hsl. }
    iEval (rewrite -/struct_read_named_source_k) in "Hnamed".
    iEval (rewrite -/struct_read_named_source_k) in "Hunfocus".
    iAssert (struct_read_padding_source π (Shared κ) l (sl_members sl)
      (pad_struct (sl_members sl)
        (replicate (length (hpzipl rts lts rs)) None) Some))%I
      with "[Hpadding]" as "Hpadding".
    { rewrite /struct_read_padding_source /struct_ltype_padding_own
        length_hpzipl. done. }
    iMod (struct_read_padding_open_shared with
      "CTX Htok Hcltok Hpadding") as (qpad)
      "(Hpadding & Hpadding_close)".
    { set_solver. }
    iMod (struct_read_components with
      "CTX HE HL HT Hlb Hnamed Hpadding Hpadding_close") as
      (L2 R tys qs vs upd qread v)
      "(HL & Hpt & Hv & Hincl & Hconds & %Hloc & %Hlyv & %Hdec & %Hhot & %Hcopy & Hclose & HT)";
      [done.. |].
    iModIntro.
    iExists L2, (llft_elt_toks κs ∗ R)%I, qread, v,
      (plistRT (struct_read_value_rts tys)),
      (struct_t sls (struct_read_value_types tys)),
      (struct_read_value_rfns tys),
      (mkPUKRes upd opt_place_update_eq_refl opt_place_update_eq_refl).
    do 5 (iSplitR; first done). iFrame "HL Hpt Hv Hincl".
    iSplitL "Hconds"; first iApply (struct_read_conds_place with "Hconds").
    iSplitL "Hclose Hunfocus Hstruct_close".
    { iPoseProof (logical_step_frame_r with "Hclose Hunfocus") as "Hclose".
      iPoseProof (logical_step_frame_r with "Hclose Hstruct_close") as "Hclose".
      iApply (logical_step_wand with "Hclose").
      iIntros "((Hclose & Hunfocus) & Hstruct_close)".
      iIntros (st ov) "%Hdecode Hpt Hv".
      iMod ("Hclose" $! st ov with "[] Hpt Hv") as
        "(Henc & Hnamed & Hpadding & Htoks & HR)"; first done.
      iAssert (struct_ltype_padding_own π (Shared κ) l (sl_members sl)
          (length rts))%I with "[Hpadding]" as "Hpadding".
      { rewrite /struct_ltype_padding_own /struct_read_padding_source
          length_hpzipl. done. }
      iPoseProof ("Hunfocus" with "Hnamed Hpadding") as "Hsource".
      iMod ("Hstruct_close" $! rts lts rs with "[] [$Hsource]") as "Hstruct";
        first done.
      { done. }
      iModIntro. iFrame. }
    iApply "HT".
  Qed.

  Definition ltype_read_as_struct_shared_inst :=
    [instance @ltype_read_as_struct_shared].
  Global Existing Instance ltype_read_as_struct_shared_inst | 20.

  Lemma ltype_read_as_struct_uniq {rts} (lts : hlist ltype rts) rs
      π E L l sls κ γ bmin T :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L1),
      ltype_read_as_struct_iter π E L1 l sls
        (hpzipl rts lts rs) sls.(sls_fields) Owned bmin
        (λ L2 R tys vs upd,
          li_tactic
            (check_llctx_place_update_kind_incl_goal E L2 upd (UpdUniq [κ]))
            (λ b, if b then
              ∀ v,
                T L2 (llft_elt_toks κs ∗ R) v
                  (plistRT (struct_read_value_rts tys))
                  (struct_t sls (struct_read_value_types tys))
                  (struct_read_value_rfns tys)
                  (mkPUKRes upd opt_place_update_eq_refl
                    opt_place_update_eq_refl)
              else False))) ⊢
    ltype_read_as π E L l (StructLtype lts sls) (#rs) (Uniq κ γ) bmin
      (use_op_alg' sls) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L1 & %Hal & HT)" (F Hlft Hrrust Huser Hshr)
      "#CTX #HE HL Hl".
    iMod (fupd_mask_subseteq lftE) as "HF"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as
      (q) "(Htok & Hcltok & HL)"; [done.. |].
    iPoseProof (struct_ltype_acc_uniq with "CTX Htok Hcltok Hl") as
      "(%sl & %Halg & %Hly & %Hlen & #Hlb & >(Hl & Hstruct_close))";
      first done.
    iMod "HF" as "_".
    have Hsl : struct_layout_spec_has_layout sls sl := Halg.
    iPoseProof (struct_ltype_focus_components_with_padding π lts rs sls sl
      Owned l with "Hl") as "(Hnamed & Hpadding & Hunfocus)".
    { lia. }
    { exact Hsl. }
    iEval (rewrite -/struct_read_named_source_k) in "Hnamed".
    iEval (rewrite -/struct_read_named_source_k) in "Hunfocus".
    iAssert (struct_read_padding_source π Owned l (sl_members sl)
      (pad_struct (sl_members sl)
        (replicate (length (hpzipl rts lts rs)) None) Some))%I
      with "[Hpadding]" as "Hpadding".
    { rewrite /struct_read_padding_source /struct_ltype_padding_own
        length_hpzipl. done. }
    iMod (struct_read_padding_open with "Hpadding") as
      "(Hpadding & Hpadding_close)"; first done.
    iAssert (logical_step F
        (struct_read_padding_locs π l (sl_members sl)
          (pad_struct (sl_members sl)
            (replicate (length (hpzipl rts lts rs)) None) Some) 1 -∗ |={F}=>
         struct_read_padding_source π Owned l (sl_members sl)
          (pad_struct (sl_members sl)
            (replicate (length (hpzipl rts lts rs)) None) Some) ∗ True))%I
      with "[Hpadding_close]" as "Hpadding_close".
    { iApply (logical_step_wand with "Hpadding_close").
      iIntros "Hpadding_close Hpadding".
      iMod ("Hpadding_close" with "Hpadding") as "Hpadding".
      iModIntro. iFrame. }
    iMod (struct_read_components with
      "CTX HE HL HT Hlb Hnamed Hpadding Hpadding_close") as
      (L2 R tys qs vs upd qread v)
      "(HL & Hpt & Hv & Hincl & Hconds & %Hloc & %Hlyv & %Hdec & %Hhot & %Hcopy & Hclose & HT)";
      [done.. |].
    iEval (rewrite /check_llctx_place_update_kind_incl_goal) in "HT".
    iDestruct "HT" as "(%b & %Hb & HT)".
    destruct b; iEval (simpl) in "HT"; last done.
    simpl in Hb.
    iPoseProof (lctx_place_update_kind_incl_acc with "HE HL") as "#Hupd";
      first exact Hb.
    iPoseProof (struct_read_conds_raw upd lts rs with "Hconds") as
      "(Hconds & #Hfield_conds)".
    iPoseProof (struct_read_conds_place upd lts rs sls with "Hconds") as
      "Hwhole_cond".
    iModIntro.
    iExists L2, (llft_elt_toks κs ∗ R)%I, qread, v,
      (plistRT (struct_read_value_rts tys)),
      (struct_t sls (struct_read_value_types tys)),
      (struct_read_value_rfns tys),
      (mkPUKRes upd opt_place_update_eq_refl opt_place_update_eq_refl).
    do 5 (iSplitR; first done). iFrame "HL Hpt Hv".
    iSplitL "Hincl"; first done.
    iSplitL "Hwhole_cond"; first iExact "Hwhole_cond".
    iSplitL "Hstruct_close Hclose Hunfocus".
    { iPoseProof (logical_step_mask_mono lftE F with "Hstruct_close") as
        "Hstruct_close"; first done.
      iPoseProof (logical_step_sep with "Hclose Hstruct_close") as "Hsteps".
      iPoseProof (logical_step_frame_r with "Hsteps Hunfocus") as "Hsteps".
      iApply (logical_step_wand with "Hsteps").
      iIntros "((Hclose & Hstruct_close) & Hunfocus)".
      iIntros (st ov) "%Hdecode Hpt Hv".
      iMod ("Hclose" $! st ov with "[] Hpt Hv") as
        "(Henc & Hnamed & Hpadding & _ & HR)"; first done.
      iAssert (struct_ltype_padding_own π Owned l (sl_members sl)
          (length rts))%I with "[Hpadding]" as "Hpadding".
      { rewrite /struct_ltype_padding_own /struct_read_padding_source
          length_hpzipl. done. }
      iPoseProof ("Hunfocus" with "Hnamed Hpadding") as "Hsource".
      iDestruct "Hstruct_close" as "[Hstruct_close _]".
      iMod (fupd_mask_subseteq lftE) as "HF"; first done.
      iMod ("Hstruct_close" $! upd lts rs with
        "Hupd Hsource Hfield_conds") as "(Hstruct & Htoks & _)".
      iMod "HF" as "_".
      iFrame "Hstruct Htoks HR". iExact "Henc". }
    iApply "HT".
  Qed.

  Definition ltype_read_as_struct_uniq_inst :=
    [instance @ltype_read_as_struct_uniq].
  Global Existing Instance ltype_read_as_struct_uniq_inst | 20.

End read.
