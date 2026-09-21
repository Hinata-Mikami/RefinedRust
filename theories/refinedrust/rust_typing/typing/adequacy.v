From radium.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap.
From iris.base_logic.lib Require Import ghost_map.
From radium Require Import ghost_state.
From refinedrust Require Export type.
From refinedrust Require Import programs functions struct.struct unit static automation.
From refinedrust Require Import typing.
From iris.program_logic Require Export language. (* must be last to get the correct nsteps *)
Set Default Proof Using "Type".

(** * RefinedRust's adequacy proof *)

Class typePreG Σ := PreTypeG {
  type_invG                      :: invGpreS Σ;
  type_na_invG                   :: na_invG Σ;
  type_lftG                      :: lftGpreS Σ;
  type_frac_borrowG              :: frac_borG Σ;
  type_lctxG                     :: lctxGPreS Σ;
  type_ghost_varG                :: ghost_varG Σ gvar_refinement.RT;
  type_pinnedBorG                :: pinnedBorG Σ;
  type_trG                       :: trGpreS Σ;
  type_heap_heap_inG             :: inG Σ (authR heapUR);
  type_heap_alloc_meta_map_inG   :: ghost_mapG Σ alloc_id (Z * nat * alloc_kind);
  type_heap_alloc_alive_map_inG  :: ghost_mapG Σ alloc_id bool;
  type_heap_fntbl_inG            :: ghost_mapG Σ addr function;
  type_thread_current_frame_inG  :: ghost_mapG Σ nat nat;
  type_thread_local_vars_inG     :: ghost_mapG Σ (nat * nat) (list string);
  type_thread_local_var_loc_inG  :: ghost_mapG Σ (nat * nat * string) (loc * syn_type);
  type_na_map_inG                :: ghost_mapG Σ nat na_inv_pool_name;
}.

Definition typeΣ : gFunctors :=
  #[invΣ;
    na_invΣ;
    lftΣ;
    GFunctor (constRF fracR);
    lctxΣ;
    ghost_varΣ gvar_refinement.RT;
    pinnedBorΣ;
    trΣ;
    GFunctor (constRF (authR heapUR));
    ghost_mapΣ alloc_id (Z * nat * alloc_kind);
    ghost_mapΣ alloc_id bool;
    ghost_mapΣ addr function;
    ghost_mapΣ nat nat;
    ghost_mapΣ (nat * nat) (list string);
    ghost_mapΣ (nat * nat * string) (loc * syn_type);
    ghost_mapΣ nat na_inv_pool_name ].
Global Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

Definition initial_return_local : var_name := "__refinedrust_main_return".

Inductive unwind_policy :=
  | AllowUnwind
  | ForbidUnwind.

Definition policy_unwind_condition (policy : unwind_policy) : Prop :=
  match policy with
  | AllowUnwind => True
  | ForbidUnwind => False
  end.

Definition initial_unwind_handler (policy : unwind_policy) : stmt :=
  match policy with
  | AllowUnwind => UnwindTerminate
  | ForbidUnwind => StuckS
  end.

Program Definition initial_caller : function :=
  {| f_args := [];
     f_code := ∅;
     f_init := "";
  |}.
Next Obligation. constructor. Qed.

Definition initial_stmt `{!LayoutAlg} (policy : unwind_policy) (main : loc) : stmt :=
  LocalLiveSt initial_return_local UnitSynType
    (CallS (Val (l2v main)) [] [] []
      (Some (Na1Ord, UntypedOp unit_sl, Var initial_return_local))
      (LocalDeadSt initial_return_local (return (Val []))%E)
      (initial_unwind_handler policy)).

Definition initial_prog `{!LayoutAlg} (policy : unwind_policy)
    (main : thread_id * loc) : runtime_expr :=
  to_rtstmt main.1 initial_caller (initial_stmt policy main.2).

Definition initial_heap_state :=
  {| hs_heap := ∅; hs_allocs := ∅; |}.

Definition initial_thread_state : thread_state :=
  {| ts_frames := [empty_frame] |}.

Definition initial_state (hs : heap_state) (num_threads : nat) (fns : gmap addr function) :=
  {| st_heap := hs;
     st_fntbl := fns;
     st_thread := list_to_map (zip (seq 0 num_threads) (replicate num_threads initial_thread_state));
  |}.

Lemma initial_state_thread_empty hs num_threads fns ts π :
  st_thread (initial_state hs num_threads fns) !! π = Some ts →
  ts = initial_thread_state.
Proof.
  intros Hlook1.
  apply elem_of_list_to_map_2 in Hlook1.
  apply list_elem_of_lookup_1 in Hlook1 as (j & Hlook1).
  apply lookup_zip in Hlook1 as (Hlook1 & Hlook2).
  apply lookup_seq in Hlook1. simpl in Hlook1. destruct Hlook1 as (<- &?).
  apply lookup_replicate in Hlook2. simpl in Hlook2. destruct Hlook2 as (-> & ?).
  done.
Qed.

Lemma initial_state_thread_invariant hs n fns :
  thread_states_invariant (initial_state hs n fns).(st_thread).
Proof.
  intros ?? ->%initial_state_thread_empty.
  intros [|j] cf; simpl; last done.
  intros [= <-]. rewrite /call_frame_invariant/empty_frame. intros ???. done.
Qed.

Lemma initial_state_thread_lookup_lt hs n fns π ts :
  (initial_state hs n fns).(st_thread) !! π = Some ts → π < n.
Proof.
  intros Hlook. apply elem_of_list_to_map_2 in Hlook.
  apply list_elem_of_lookup_1 in Hlook as (j & Hlook).
  apply lookup_zip in Hlook as (Hπ & _).
  apply lookup_seq in Hπ as [Hπ Hj]. simpl in Hπ. lia.
Qed.

Definition initial_frame_map (num_threads : nat) : gmap thread_id frame_id :=
  list_to_map (zip (seq 0 num_threads) (replicate num_threads 1)).

Definition initial_local_list_map (num_threads : nat) : gmap frame_path (list var_name) :=
  list_to_map (zip ((λ π, (π, 1)) <$> seq 0 num_threads)
    (replicate num_threads [])).

Lemma initial_local_list_map_lookup n π :
  π < n → initial_local_list_map n !! (π, 1) = Some [].
Proof.
  intros Hπ. apply elem_of_list_to_map_1.
  - rewrite fst_zip; last by rewrite length_fmap length_seq length_replicate.
    apply NoDup_fmap_2, NoDup_seq. intros ?? [=]. done.
  - apply list_elem_of_lookup_2 with π.
    apply lookup_zip_Some. split.
    + rewrite list_lookup_fmap.
      have Hlook : seq 0 n !! π = Some π by (apply lookup_seq; lia).
      rewrite Hlook. done.
    + apply lookup_replicate_2. lia.
Qed.

Lemma initial_local_list_inv_1 hs n fns :
  thread_local_vars_inv_1 (initial_state hs n fns).(st_thread) (initial_local_list_map n).
Proof.
  intros π i ts cf Hi Hts Hcf.
  have Hπ := initial_state_thread_lookup_lt _ _ _ _ _ Hts.
  apply initial_state_thread_empty in Hts. subst ts.
  simpl in Hi, Hcf. assert (i = 1)%nat as -> by lia.
  simpl in Hcf. injection Hcf as <-.
  exists []. split.
  - by apply initial_local_list_map_lookup.
  - rewrite /call_frame_has_locals/empty_frame map_to_list_empty. done.
Qed.

Lemma initial_local_list_inv_2 hs n fns :
  thread_local_vars_inv_2 (initial_state hs n fns).(st_thread) (initial_local_list_map n).
Proof.
  intros π i names Hlook.
  apply elem_of_list_to_map_2 in Hlook.
  apply list_elem_of_lookup_1 in Hlook as (k & Hlook).
  apply lookup_zip in Hlook as (Hkey & Hnames).
  rewrite list_lookup_fmap in Hkey.
  destruct (seq 0 n !! k) as [π'|] eqn:Hπ'; simpl in Hkey; last done.
  injection Hkey as <- <-.
  apply lookup_seq in Hπ' as (-> & Hπ).
  simpl in Hnames. apply lookup_replicate in Hnames as (-> & _).
  exists initial_thread_state, empty_frame. split_and!; simpl.
  - apply elem_of_list_to_map_1.
    + rewrite fst_zip; last by rewrite length_seq length_replicate.
      apply NoDup_seq.
    + apply list_elem_of_lookup_2 with k.
      apply lookup_zip_Some. split.
      * apply lookup_seq. lia.
      * apply lookup_replicate_2. lia.
  - lia.
  - done.
  - done.
  - rewrite /call_frame_has_locals/empty_frame map_to_list_empty. done.
Qed.

Definition main_type `{!typeGS Σ} (policy : unwind_policy) (P : iProp Σ) :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : (), λ ϝ, []; λ π, P) → ∃ () : (), () @ unit_t; λ π, True | policy_unwind_condition policy.

Definition initial_prog_wp `{!refinedcG Σ} (policy : unwind_policy)
    (main : thread_id * loc)
    (Φ : radium.val.val → iProp Σ) : iProp Σ :=
  WP initial_prog policy main {{ runtime_post Φ False }}.

Definition initial_return_wp `{!refinedcG Σ} π (Φ : radium.val.val → iProp Σ) : iProp Σ :=
  WP to_rtstmt π initial_caller (Return (Val [])) {{ runtime_post Φ False }}.

Lemma wp_initial_return `{!refinedrustGS Σ} π locals :
  current_frame π 1 -∗
  allocated_locals (π, 1) locals -∗
  ([∗ list] x ∈ locals,
    ∃ ly l st, ⌜syn_type_has_layout st ly⌝ ∗ x is_live{(π, 1), st} l ∗ l ↦|ly|) -∗
  initial_return_wp π (λ v, ⌜v = []⌝)%I.
Proof.
  iIntros "Hframe Hlocals Hxs".
  rewrite /initial_return_wp.
  iApply wp_lift_stmt_step.
  iIntros (σ) "((%Hinv & Hhctx) & Hfctx & Htctx)".
  rewrite big_sepL_exists. iDestruct "Hxs" as (lys) "Hxs".
  iPoseProof (big_sepL2_length with "Hxs") as "%Hlen1".
  iPoseProof (big_sepL2_exists_r with "Hxs") as (ls Hls) "Hxs".
  iPoseProof (big_sepL2_exists_r with "Hxs") as (sts Hsts) "Hxs".
  rewrite length_zip Hls Nat.min_idempotent in Hsts.
  iPoseProof (big_sepL2_sep with "Hxs") as "(Hsts & Hxs)".
  iPoseProof (big_sepL2_sep with "Hxs") as "(Hxs & Hls)".
  iPoseProof (big_sepL2_elim_l with "Hsts") as "Hsts".
  iPoseProof (big_sepL2_elim_l with "Hls") as "Hls".

  iAssert ([∗ list] st; ly ∈ sts; lys, ⌜syn_type_has_layout st ly⌝)%I
    with "[Hsts]" as "Hsts".
  { rewrite zip_assoc_l big_sepL_fmap.
    iApply big_sepL2_from_zip. { lia. }
    iApply big_sepL2_elim_l.
    rewrite zip_assoc_r (zip_flip lys ls) zip_fmap_l.
    rewrite zip_assoc_l (zip_flip lys sts) zip_fmap_r !big_sepL_fmap.
    iApply big_sepL2_from_zip; first last.
    { iApply (big_sepL_impl with "Hsts").
      iModIntro. iIntros (? [? []] ?). simpl. done. }
    rewrite length_zip. lia. }
  iPoseProof (big_sepL2_Forall2 with "Hsts") as "%Hsts'".
  iClear "Hsts".

  iAssert ([∗ list] l ∈ zip ls lys, l.1 ↦|l.2|)%I with "[Hls]" as "Hxs2".
  { rewrite (zip_flip lys ls) zip_fmap_l big_sepL_fmap.
    iApply big_sepL2_elim_r. iApply big_sepL2_from_zip; first last.
    { iApply (big_sepL_impl with "Hls").
      iModIntro. iIntros (? ([] & ?) ?). simpl. eauto. }
    rewrite !length_zip. lia. }
  iAssert ([∗ list] x; lsynty ∈ locals; zip ls sts,
      x is_live{(π, 1), lsynty.2} lsynty.1)%I with "[Hxs]" as "Hxs1".
  { iPoseProof (big_sepL2_to_zip with "Hxs") as "Hxs1".
    rewrite (zip_flip lys ls) zip_fmap_l zip_fmap_r.
    rewrite (zip_assoc_l ls lys sts) (zip_flip lys sts) ?zip_fmap_l ?zip_fmap_r.
    rewrite (zip_assoc_r ls sts lys) zip_fmap_r (zip_assoc_r locals _ lys).
    iApply big_sepL2_from_zip. { rewrite length_zip. lia. }
    iApply big_sepL2_elim_r.
    iApply big_sepL2_from_zip; first last.
    { rewrite !big_sepL_fmap. iApply (big_sepL_impl with "Hxs1").
      iModIntro. iIntros (? ([? []] & []) ?). simpl. eauto. }
    rewrite !length_zip. lia. }

  iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as
    "(%ts & %cf & %Hthread & %Hframe & %Hlocals & %Hlen)".
  apply call_frame_has_locals_nodup in Hlocals.
  iPoseProof (state_lookup_vars with "Htctx Hframe Hxs1 Hlocals") as
    "(%Hlook & %Hst & %Hlive & %Hbounds & %Hperm)"; [done | lia |].
  unfold thread_get_frame in *. simplify_eq.
  iMod (thread_frame_deallocate_vars _ _ _ _ _ locals _ _ _ sts ls with
    "Htctx Hframe Hlocals Hxs1") as "(Hframe & Hlocals & Hfree & Htctx)";
    [done | done | done | done | | |].
  { lia. }
  { lia. }
  iMod (heap_free_blocks_upd (zip ls lys) with "[Hxs2 Hfree] [$Hhctx //]")
    as (hs Hfree) "Hhctx".
  { rewrite !big_sepL_sep. iFrame.
    iPoseProof (big_sepL2_to_zip with "Hfree") as "Hfree".
    iApply (big_sepL2_elim_r sts).
    iApply big_sepL2_from_zip. { rewrite length_zip. lia. }
    iPoseProof (big_sepL_extend_r lys with "Hfree") as "Hfree".
    { rewrite length_zip. lia. }
    iPoseProof (big_sepL2_to_zip with "Hfree") as "Hfree".
    rewrite zip_assoc_l (zip_flip sts _) zip_fmap_r zip_assoc_r !big_sepL_fmap.
    iApply (big_sepL_impl with "Hfree").
    iModIntro. iIntros (? [[] ?] Hlook'). simpl.
    apply lookup_zip_Some in Hlook' as (Hlook1 & Hlook3).
    apply lookup_zip_Some in Hlook1 as (Hlook1 & Hlook2).
    opose proof (Forall2_lookup_lr _ _ _ _ _ _ Hsts' _ _) as Ha; [done.. |].
    rewrite /use_layout_alg' Ha /=. eauto. }
  eapply free_blocks_perm in Hfree; last done; first last.
  { symmetry. done. }
  iEval (rewrite list_difference_diag) in "Hlocals".
  iMod (thread_pop_frame_empty π 1
    (<[π := thread_update_frame ts (frame_dealloc_vars cf locals)]> σ.(st_thread))
    (<[π := thread_pop_frame ts]> σ.(st_thread))
    (thread_update_frame ts (frame_dealloc_vars cf locals)) []
    with "Htctx Hframe Hlocals") as "(Hframe & Htctx)".
  { rewrite lookup_insert_eq. done. }
  { rewrite insert_insert decide_True; last done.
    unfold thread_pop_frame, thread_update_frame. simpl. done. }
  { done. }
  iModIntro. iSplit.
  { iPureIntro. eexists [], (RTVal []),
      ({| st_heap := hs; st_fntbl := σ.(st_fntbl);
          st_thread := <[π := thread_pop_frame ts]> σ.(st_thread) |}), [].
    eapply ReturnS; [done | done | done]. }
  iIntros (os e2 σ2 efs Hstep Hinv2). inv_stmt_step.
  unfold state_get_thread, thread_get_frame in *. simplify_eq.
  have -> : hs0 = hs by apply: free_blocks_inj.
  iApply physical_step_intro. iNext.
  rewrite /state_ctx. simpl. iFrame.
  iSplit; first done.
  iApply wp_value. done.
Qed.

Ltac solve_initial_return_value :=
  iApply type_val; iApply type_val_unit;
  rewrite /introduce_with_hooks;
  iIntros (F HF) "#CTX' #HE HL Hv"; iModIntro;
  iExists []; iFrame "HL";
  iApply find_in_context_frame_locals; iExists []; iFrame;
  rewrite /trigger_tc; iExists [], _;
  iApply typed_context_fold_nil;
  iIntros (F0 HF0) "#CTX0 #HE0 HL Hacc"; iModIntro;
  iExists []; iFrame "HL";
  iApply prove_with_subtype_pure; iSplit; first done;
  iIntros (F1 HF1) "#CTX1 #HE1 HL _"; iModIntro;
  iExists []; iFrame "HL"; done.

Lemma wp_initial_prog `{!refinedrustGS Σ} policy π main (P : iProp Σ) :
  rrust_ctx -∗
  current_frame π 1 -∗
  allocated_locals (π, 1) [] -∗
  na_own π ⊤ -∗
  (l2v main) ◁ᵥ{π, MetaNone} main @ function_ptr [] (@eq_refl _ [], main_type policy P) -∗
  P -∗
  initial_prog_wp policy (π, main) (λ v, ⌜v = []⌝)%I.
Proof.
  iIntros "#CTX Hframe Hlocals Hna Hmain HP".
  rewrite /initial_prog_wp /initial_prog /initial_stmt /initial_return_local.
  set (Ψ := (λ v : radium.val.val,
    ∃ locals, ⌜v = ([] : radium.val.val)⌝ ∗ current_frame π 1 ∗
      allocated_locals (π, 1) locals ∗
      ([∗ list] x ∈ locals,
        ∃ ly l st, ⌜syn_type_has_layout st ly⌝ ∗ x is_live{(π, 1), st} l ∗ l ↦|ly|))%I).
  have Hunit : syn_type_has_layout UnitSynType unit_sl.
  { apply syn_type_has_layout_unit. done. }
  have Hfresh : "__refinedrust_main_return" ∉ ([] : list var_name).
  { apply not_elem_of_nil. }
  iPoseProof (wps_local_live π UnitSynType "__refinedrust_main_return"
    (CallS (Val (l2v main)) [] [] []
      (Some (Na1Ord, UntypedOp unit_sl, Var "__refinedrust_main_return"))
      (LocalDeadSt "__refinedrust_main_return" (return (Val []))%E)
      (initial_unwind_handler policy))
    unit_sl [] 1 ∅ Ψ False%I Hunit Hfresh with "Hframe Hlocals") as "Hlive".
  iMod (tr_zero) as "Htr".
  iSpecialize ("Hlive" with "[-]").
  { iApply (physical_step_intro_tr with "Htr").
    iNext. iIntros "Htr Hcred". iModIntro.
    iIntros (l) "Hlive Hframe Hlocals Hl %Hly".
    iAssert (credit_store 0 0) with "[Hcred Htr]" as "Hstore".
    { rewrite credit_store_eq /credit_store_def. iSplitL "Hcred".
      - iApply (lc_weaken with "Hcred"). simpl. unfold num_laters_per_step. lia.
      - iApply (tr_weaken with "Htr"). simpl. unfold num_laters_per_step. lia. }
    iAssert (l ◁ₗ[π, Owned] .@ (◁ uninit UnitSynType))%I with "[Hl]" as "Hl".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists unit_sl. iSplitR.
      { iPureIntro. cbn. exact (syn_type_has_layout_untyped UnitSynType unit_sl Hunit). }
      iR. iR.
      iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#$".
      rewrite length_replicate. iExists (). iR. iModIntro.
      iExists _. iFrame. rewrite uninit_own_spec. iR.
      iExists _. iR. rewrite /has_layout_val length_replicate. done. }
    iPoseProof (named_lfts_init (π, 1) []) as "Hnamed".
    iAssert (typed_stmt [] [] (π, 1)
      (CallS (Val (l2v main)) [] [] []
        (Some (Na1Ord, UntypedOp unit_sl, Var "__refinedrust_main_return"))
        (LocalDeadSt "__refinedrust_main_return" (return (Val []))%E)
        (initial_unwind_handler policy))
       initial_caller (λ v _, ⌜v = []⌝)%I (λ _, False%I) static)
      with "[Hstore Hna Hmain HP Hlocals Hlive Hl Hnamed]" as "Hs".
    { destruct policy; simpl.
      all: rep <-? 1 liRStep; liShow.
      all: try iFrame. all: try done.
       Unshelve. all: rep <-? 1 liRStep.
      all: try iFrame. all: try done.
       all: try (rep <-? 1 liRStep; liShow).
      all: try iFrame. all: try done.
      1: solve_initial_return_value.
      1: solve_initial_return_value.
      1: {
        iIntros (κ q) "HL"; iModIntro; iIntros "#HE".
        have Hwf : ty_wf_E unit_t = [] by
          (rewrite ty_wf_E_unfold /unit_t /=; done).
        have Hout : ty_outlives_E unit_t κ = [] by
          (apply tac_unfold_ty_outlives_E;
           rewrite ty_lfts_unfold /unit_t /=;
           apply tac_lfts_outlives_E_nil).
        rewrite Hwf Hout /elctx_interp /=. done. }
       Unshelve. all: sidecond_solver. }
    iEval (rewrite /typed_stmt /typed_stmt_post_cond /typed_stmt_unwind_post_cond) in "Hs".
    iSpecialize ("Hs" $! Ψ False%I with "CTX [] [] Hframe").
    { rewrite elctx_interp_nil. done. }
    { rewrite /llctx_interp /llctx_interp_noend. done. }
    iApply "Hs". iSplit.
    - iIntros (L v locals) "_ Hframe Hlocals Hlive ->".
      iApply logical_step_intro. unfold Ψ. iExists locals. iFrame. done.
    - iIntros (L locals) "_ _ _ _ []". }
  iEval (rewrite stmt_wp_unfold /stmt_wp_def) in "Hlive".
  iApply ("Hlive" $! (λ v, ⌜v = []⌝)%I False%I initial_caller with "[]").
  { done. }
  iSplit; last by iIntros "[]".
  iIntros (v) "Hr".
  iDestruct "Hr" as "(%locals & -> & Hframe & Hlocals & Hlive)".
  iApply (wp_initial_return with "Hframe Hlocals Hlive").
Qed.

(*Lemma na_alloc Σ `{!refinedcG Σ} `{!na_invG Σ} (num_threads : nat) :*)
  (*⊢ (|==> (∃ γ (M : gmap thread_id na_inv_pool_name), *)
      (*ghost_map_auth γ 1 M ∗ [∗ list] π ∈ seq 0 num_threads, ∃ γ' : na_inv_pool_name, ghost_map_elem γ π DfracDiscarded γ' ∗ na_invariants.na_own γ' ⊤))%I.*)

(** * The main adequacy lemma *)
(** [config] fixes link-time abstract-machine behavior. In particular, abort is
    trusted as terminal divergence; this theorem does not execute or verify the
    platform's panic handler or abort runtime. [policy] separately controls
    whether an unwind that escapes the initial function is accepted. *)
Lemma refinedrust_adequacy (config : RadiumConfig) (policy : unwind_policy) Σ `{!typePreG Σ} `{A : LayoutAlg}
    (thread_mains : list loc) (fns : gmap addr function)
    (static_ls : list loc) (static_vals : list val.val)
    n t2 σ2 obs hs σ:
  alloc_new_blocks initial_heap_state GlobalAlloc static_ls static_vals hs →
  σ = initial_state hs (length thread_mains) fns →
  Forall (λ l, l.(loc_a) ∈ USize) thread_mains →
  (* show that the main functions for the individual threads are well-typed for a provable precondition [P] *)
  (∀ {HtypeG : typeGS Σ},
    ALG = A →
    ∃ static_locs static_tys,
    let Hstatics : staticGS Σ := {| static_locs:=static_locs; static_types := static_tys |} in
    ([∗ list] l; v ∈ static_ls; static_vals, l ↦ v) -∗
    ([∗ map] k↦qs∈fns, fntbl_entry (fn_loc k) qs) ={⊤}=∗
      [∗ list] π ↦ main ∈ thread_mains, ∃ P, (l2v main) ◁ᵥ{π, MetaNone} main @ function_ptr [] (@eq_refl _ [], main_type policy P) ∗ P) →
  (* if the whole thread pool steps for [n] steps *)
  nsteps (Λ := @c_lang config) n (initial_prog policy <$> (zip (seq 0 (length thread_mains)) thread_mains), σ) obs (t2, σ2) →
  (* then it has not gotten stuck *)
  ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
Proof.
  move => Halloc -> Hran Hwp. apply: (wp_strong_adequacy _ _ refinedc_trgen NotStuck) . move => ? ?.
  (* heap/Caesium stuff *)
  set h := to_heapUR ∅.
  iMod (own_alloc (● h ⋅ ◯ h)) as (γh) "[Hh _]" => //.
  { apply auth_both_valid_discrete. split => //. }
  iMod(ghost_map_alloc fns) as (γf) "[Hf Hfm]".
  iMod (ghost_map_alloc_empty (V:=(Z * nat * alloc_kind))) as (γr) "Hr".
  iMod (ghost_map_alloc_empty (V:=bool)) as (γs) "Hs".
  set (HheapG := HeapG _ _ γh _ γr _ γs _ γf).

  set (num_threads := length thread_mains).
  set (initial_thread_map := initial_frame_map num_threads).
  iMod (ghost_map_alloc initial_thread_map) as (γcur) "(Hcur & Hcur_thread)".
  iMod (ghost_map_alloc (initial_local_list_map num_threads)) as (γlocals) "(Hall_locals & Halloc_thread)".
  iMod (ghost_map_alloc_empty (K:= nat * nat * string) (V:= loc * syn_type)) as (γloc) "Hlocals".
  set (HthreadG := ThreadG _ _ γcur _ γlocals _ γloc).

  set (HrefinedCG := RefinedCG _ config _ HheapG HthreadG _ A).

  (* lifetime logic stuff *)
  iMod (lft_init _ lft_userE) as "(%Hlft & #LFT)"; [solve_ndisj.. | ].
  iMod (lctx_init) as "(%Hlctx & #LCTX & _)"; [solve_ndisj.. | ].

  (* Na mapping from thread ids *)
  iAssert (|==> [∗ list] i ∈ seq 0 num_threads, ∃ γ, na_invariants.na_own γ ⊤)%I as ">Ha".
  { iApply big_sepL_bupd.
    iApply big_sepL_intro. iModIntro. iIntros (k x Hlook).
    iApply na_alloc. }
  iPoseProof (big_sepL_exists with "Ha") as "(%γnas & Hna)".
  iPoseProof (big_sepL2_length with "Hna") as "%Hna_len".
  iMod (ghost_map_alloc (list_to_map (zip (seq 0 num_threads) γnas))) as "(%γna & Hna_auth & Hna_map)".
  rewrite big_sepM_list_to_map; first last.
  { rewrite fst_zip; first apply NoDup_seq. lia. }

  set (HtypeG := TypeG _ HrefinedCG Hlft _ γna _ _ Hlctx _ _).

  iAssert (|==> [∗ list] π ∈ seq 0 num_threads, na_own π ⊤)%I with "[Hna_map Hna]" as ">Hna".
  { iApply big_sepL_bupd.
    iApply big_sepL2_elim_r. iApply (big_sepL2_wand with "Hna").
    iApply big_sepL2_from_zip. { lia. }
    iApply (big_sepL_impl with "Hna_map").
    iModIntro. iIntros (? [] Hlook).
    simpl. rewrite na_own_unfold /na_own_def.
    iIntros "Hna $". iApply (ghost_map_elem_persist with "Hna"). }

  iAssert ([∗ list] π ∈ seq 0 num_threads, current_frame π 1)%I with "[Hcur_thread]" as "Hframe".
  { rewrite big_sepM_list_to_map; first last.
    { rewrite fst_zip; first apply NoDup_seq. rewrite length_seq length_replicate. lia. }
    iPoseProof (big_sepL2_from_zip _ _  (λ _ a b, a ↪[γcur] b)%I with "Hcur_thread") as "Ha".
    { rewrite length_seq length_replicate. done. }
    rewrite big_sepL2_replicate_r; last by rewrite length_seq.
    iApply (big_sepL_impl with "Ha"). iModIntro.
    iIntros (???). rewrite current_frame_unfold. eauto. }

  iAssert ([∗ list] π ∈ seq 0 num_threads, allocated_locals (π, 1) [])%I with "[Halloc_thread]" as "Halloc".
  { rewrite /initial_local_list_map big_sepM_list_to_map; first last.
    { rewrite fst_zip; last by rewrite length_fmap length_seq length_replicate.
      apply NoDup_fmap_2, NoDup_seq. intros ?? [=]. done. }
    iPoseProof (big_sepL2_from_zip _ _ (λ _ (a : frame_path) (b : list var_name), a ↪[γlocals] b)%I with "Halloc_thread") as "Ha".
    { rewrite length_fmap length_seq length_replicate. done. }
    rewrite big_sepL2_replicate_r; last by rewrite length_fmap length_seq.
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "Ha"). iModIntro.
    iIntros (???). rewrite allocated_locals_unfold. eauto. }

  move: (Hwp HtypeG eq_refl) => {Hwp} [static_locs [static_tys]].
  set (Hstatics := {| static_locs := static_locs; static_types := static_tys |}).

  move => Hwp.
  iMod (heap_alloc_new_blocks_upd with "[Hh Hr Hs]") as "[Hctx Hmt]" => //. {
    rewrite /heap_state_ctx /alloc_meta_ctx /to_alloc_meta_map /alloc_alive_ctx /to_alloc_alive_map !fmap_empty.
    iFrame. done.
  }
  rewrite big_sepL2_sep. iDestruct "Hmt" as "[Hmt Hfree]".

  iAssert (|==> [∗ map] k↦qs ∈ fns, fntbl_entry (fn_loc k) qs)%I with "[Hfm]" as ">Hfm". {
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Hfm").
    iIntros "!>" (???) "Hm". rewrite fntbl_entry_eq.
    iExists _. iSplitR; [done|].
    iApply (ghost_map_elem_persist with "Hm"). }
  iMod (Hwp with "Hmt Hfm") as "Hmains".

  iModIntro. iExists c_irisG.(state_interp), (replicate (length thread_mains) (λ _, True%I)), c_irisG.(fork_post), c_irisG.(state_interp_mono).
  iSplitL "Hf Hctx Hcur Hall_locals Hlocals"; last first. 1: iSplitL "Hmains Hna Hframe Halloc".
  (*iSplitL "Hf Hctx Hcur Hall_locals Hlocals"; last first. 1: iSplitL "Hmains Hna Hframe".*)
  Unshelve.
  - rewrite big_sepL2_fmap_l. iApply big_sepL2_replicate_r.
    { rewrite length_zip length_seq. unfold num_threads. lia. }
    iApply (big_sepL2_to_zip _ _ (λ _ a b, WP initial_prog policy (a, b) {{ _, True }})%I).
    rewrite -(big_sepL_zip_seq (λ (imain : nat * loc), ∃ P : iProp Σ, (imain.2 ◁ᵥ{imain.1, MetaNone} imain.2 @ function_ptr [] (eq_refl, main_type policy P)) ∗ P)%I 0%nat num_threads); last lia.
    iPoseProof (big_sepL2_from_zip _ _ (λ _ a (b : loc), ∃ P : iProp Σ, (b ◁ᵥ{a, MetaNone} b @ function_ptr [] (eq_refl, main_type policy P)) ∗ P)%I with "Hmains") as "Hmains".
    { rewrite length_seq. lia. }
    iApply (big_sepL2_wand with "Hmains").
    iPoseProof (big_sepL_extend_r with "Hna") as "Hna"; last iApply (big_sepL2_wand with "Hna").
    { rewrite length_seq. lia. }
    iPoseProof (big_sepL_extend_r with "Hframe") as "Hframe"; last iApply (big_sepL2_wand with "Hframe").
    { rewrite length_seq. lia. }
    iPoseProof (big_sepL_extend_r with "Halloc") as "Halloc"; last iApply (big_sepL2_wand with "Halloc").
    { rewrite length_seq. lia. }
    iApply big_sepL2_intro. { rewrite length_seq. lia. }

    iIntros "!#" (π ? main Hlook1 ?) "Halloc Hframe Hna Hfn".
    apply lookup_seq in Hlook1 as (-> & ?).
    iDestruct ("Hfn") as (P) "[Hmain HP]".
    pose ({| refinedrust_typeGS := HtypeG; refinedrust_staticGS := Hstatics |} : refinedrustGS Σ) as Hrr.
    iPoseProof (wp_initial_prog policy (0 + π) main P
      with "[] Hframe Halloc Hna Hmain HP") as "Hprog".
    { rewrite /rrust_ctx. iFrame "#". }
    iEval (rewrite /initial_prog_wp) in "Hprog".
    iApply (wp_wand with "Hprog"). iIntros (v) "_". done.
  - iFrame. iIntros (?? _ _ ?) "_ _ _". iApply fupd_mask_intro_discard => //. iPureIntro. by eauto.
  - rewrite /state_ctx /heap_state_ctx /thread_ctx /alloc_meta_ctx /to_alloc_meta_map /alloc_alive_ctx /to_alloc_alive_map.
    iFrame.
    iSplitR.
    { iPureIntro. apply initial_state_thread_invariant. }
    iSplitL.
    { unfold thread_current_frame_auth.
      iApply (ghost_map_auth_prove_eq with "Hcur").
       rewrite /to_current_frame /initial_thread_map /initial_frame_map /=.
      rewrite -list_to_map_fmap prod_map_zip.
      rewrite list_fmap_id.
      f_equiv. f_equiv.
       rewrite fmap_replicate//. }
    iSplitR; first iSplit; last iSplitL; [ | | by iApply big_sepM_empty | iSplit]; iPureIntro.
    + apply initial_local_list_inv_1.
    + apply initial_local_list_inv_2.
    + intros ???????? Hlook1 ?.
      apply initial_state_thread_empty in Hlook1.
      subst. simpl in *. assert (i = 1)%nat as -> by lia.
      simpl in H0. injection H0 as <-. done.
    + done.
Qed.

Definition refinedrust_adequacy_allow_unwind config := refinedrust_adequacy config AllowUnwind.
Definition refinedrust_adequacy_unwind_free config := refinedrust_adequacy config ForbidUnwind.

(*Print Assumptions refinedrust_adequacy.*)

(* clients of this:
    - create a function map with monomorphized entries of all the functions they need
        -> this we need to know upfront.
    - from the fntbl_entry we get, build the function_ptr types.
        we use Löb induction as part of that (have a later in the function_ptr type to enable that)
          the induction assumes that we already have fn_ptrs for all the functions we build, at the types that they should have.


  clients of this may also instantiate it with concrete layouts, if they can provide a layout algorithm that computes them.
 *)



(** * Helper functions for using the adequacy lemma *)
Definition fn_lists_to_fns (addrs : list addr) (fns : list function) : gmap addr function :=
  list_to_map (zip addrs fns).

Lemma fn_lists_to_fns_cons `{!refinedcG Σ} addr fn addrs fns :
  length addrs = length fns →
  addr ∉ addrs →
  ([∗ map] k↦qs ∈ fn_lists_to_fns (addr :: addrs) (fn :: fns), fntbl_entry (fn_loc k) qs) -∗
  fntbl_entry (Loc ProvFnPtr addr) fn ∗ ([∗ map] k↦qs ∈ fn_lists_to_fns addrs fns, fntbl_entry (fn_loc k) qs).
Proof.
  move => Hnotin ?.
  rewrite /fn_lists_to_fns /= big_sepM_insert //; auto.
  apply not_elem_of_list_to_map_1. rewrite fst_zip => //; lia.
Qed.

(** * Tactics for solving conditions in an adequacy proof *)

Ltac adequacy_intro_parameter :=
  repeat lazymatch goal with
         | |- ∀ _ : (), _ => case
         | |- ∀ _ : (_ * _), _ => case
         | |- ∀ _ : _, _ => move => ?
         end.

Ltac adequacy_invert_forall H :=
  repeat match type of H with
  | Forall _ [] =>
    clear H
  | Forall _ _ =>
    apply Forall_cons in H;
    destruct H as [? H]
  end.
Ltac adequacy_split_forall :=
  repeat first [apply Forall_cons; split | by apply Forall_nil].

Ltac adequacy_solve_typed_function lemma :=
  iApply typed_function_equiv; iSplit;
    [ iApply (lemma ) => //
      (*; iExists _; repeat iSplit => //*)
    | rep liRStep
    ].

Ltac adequacy_solve_function_ptr :=
  rewrite /ty_own_val/=; iR;
  iExists _;
  iSplitR; [ iPureIntro; by apply val_to_loc_Some_l2v| ];
  iSplitR; [ done | ];
  iSplitR; [ iPureIntro; simpl; repeat first [by apply Forall2_nil | apply Forall2_cons; split; [shelve_sidecond | ]] | ];
  iNext; simpl;
  iApply typed_function_equiv; iSplit; first done;
  rep liRStep.
