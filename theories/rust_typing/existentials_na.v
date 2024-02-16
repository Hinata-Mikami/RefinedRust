From refinedrust Require Export type ltypes programs.
From refinedrust Require Import uninit int ltype_rules.
From lrust.lifetime Require Import na_borrow.
Set Default Proof Using "Type".

Record na_ex_inv_def `{!typeGS Σ} (X : Type) (Y : Type) : Type := na_mk_ex_inv_def' {
  na_inv_xr : Type;
  na_inv_xr_inh : Inhabited na_inv_xr;
  na_inv_xrt : na_inv_xr → Y;

  (* NOTE: Make persistent part (Timeless) + non-persistent part inside &na *)
  na_inv_P : thread_id → X → Y → iProp Σ;

  na_inv_P_lfts : list lft;
  na_inv_P_wf_E : elctx;
  na_inv_P_pers : ∀ π x y, Persistent (na_inv_P π x y);
  na_inv_P_timeless : ∀ π x y, Timeless (na_inv_P π x y);
}.

(* Stop Typeclass resolution for the [inv_P_pers] argument, to make it more deterministic. *)
Definition na_mk_ex_inv_def `{!typeGS Σ} {X Y : Type} (YR : Type) `{!Inhabited YR}
  (inv_xrt : YR → Y)

  (inv_P : thread_id → X → Y → iProp Σ)

  inv_P_lfts
  (inv_P_wf_E : elctx)
  (inv_P_pers : TCNoResolve (∀ (π : thread_id) (x : X) (y : Y), Persistent (inv_P π x y)))
  (inv_P_timeless: TCNoResolve (∀ (π : thread_id) (x : X) (y : Y), Timeless (inv_P π x y)))

  := na_mk_ex_inv_def' _ _ _ _ _ _
       inv_xrt inv_P inv_P_lfts inv_P_wf_E inv_P_pers inv_P_timeless.

Global Arguments na_inv_xr {_ _ _ _ _}.
Global Arguments na_inv_xrt {_ _ _ _ _}.
Global Arguments na_inv_P {_ _ _ _}.
Global Arguments na_inv_P_lfts {_ _ _ _}.
Global Arguments na_inv_P_wf_E {_ _ _ _}.
Global Arguments na_inv_P_pers {_ _ _ _}.
Global Arguments na_inv_P_timeless {_ _ _ _}.
Global Existing Instance na_inv_P_pers.
Global Existing Instance na_inv_P_timeless.

(** Smart constructor for persistent and timeless [P] *)
Program Definition na_mk_pers_ex_inv_def
  `{!typeGS Σ} {X : Type} {Y : Type}
  (YR : Type) `{!Inhabited YR} (xtr : YR → Y)
  (P : X → Y → iProp Σ)
  (_: TCNoResolve (∀ x y, Persistent (P x y)))
  (_: TCNoResolve (∀ x y, Timeless (P x y))): na_ex_inv_def X Y :=
    na_mk_ex_inv_def YR xtr (λ _, P) [] [] _ _.
Next Obligation.
  by rewrite /TCNoResolve.
Qed.
Next Obligation.
  by rewrite /TCNoResolve.
Qed.



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
    ty_shr κ π r l := ∃ x : X,
      P.(na_inv_P) π x r ∗
      ty.(ty_sidecond) ∗
      &na{κ, π, shrN.@l}(∃ v, l ↦ v ∗ ty.(ty_own_val) π x v) ∗
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
    iIntros (?????) "(% & (_ & $ & _))".
  Qed.

  (* ty_shr_aligned *)
  Next Obligation.
    iIntros (?????) "(% & _ & _ & _ & $)".
  Qed.

  (* ty_share *)
  Next Obligation.
    iIntros (ty E κ l ly π r q ?) "#(LFT & TIME & LLCTX) Htok %Halg %Hly Hlb Hb".
    setoid_rewrite bi.sep_exist_l at 1.
    setoid_rewrite bi_exist_comm at 1.

    rewrite lft_intersect_list_app -!lft_tok_sep.
    iDestruct "Htok" as "(Htok & ? & ?)".

    iApply fupd_logical_step.
    iMod (bor_exists_tok with "LFT Hb Htok") as "(%x & Hb & Htok)"; first solve_ndisj.

    iPoseProof (bor_iff _ _ (P.(na_inv_P) π x r ∗ (∃ a : val, l ↦ a ∗ a ◁ᵥ{ π} x @ ty)) with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit; [iIntros "(% & ? & ? & ?)" | iIntros "(? & (% & ? & ?))"]; eauto with iFrame. }

    iMod (bor_sep with "LFT Hb") as "(HP & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT HP Htok") as "(>HP & Htok)"; first solve_ndisj.

    iMod (bor_get_persistent _ (ty_sidecond ty) with "LFT [] Hb Htok") as "(Hty & Hb & Htok)"; first solve_ndisj.
    { iIntros "Hv".
      (* NOTE: Use ty_own_val_sidecond *)
      admit. }

    iMod (bor_na with "Hb") as "Hb"; first solve_ndisj.
    iModIntro.

    iApply logical_step_intro; iFrame.
    iExists x; eauto with iFrame.
  Admitted.

  (* ty_shr_mono *)
  Next Obligation.
    iIntros (ty κ κ' π r l) "#Hincl (%x & HP & Hty & Hshr& Hly)".
    iExists x. iFrame.
    iApply (na_bor_shorten with "Hincl Hshr").
  Qed.

  (* _ty_memcast_compat *)
  Next Obligation.
    iIntros (ty ot mt st π r v Hot) "(%x & HP & Hv)".
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
  Admitted.

  Global Instance na_ex_inv_def_ne {rt X Y : Type}
    (P : type rt → na_ex_inv_def X Y)
    (F : type rt → type X)
    :
    NaExInvDefNonExpansive P →
    TypeNonExpansive F →
    TypeNonExpansive (λ ty, na_ex_plain_t X Y (P ty) (F ty)).
  Proof.
  Admitted.
End contr.

Notation "'∃na;' P ',' τ" := (na_ex_plain_t _ _ P τ) (at level 40) : stdpp_scope.

Section generated_code.
  From refinedrust Require Import typing shims.

  Section Cell_sls.
    Context `{!refinedrustGS Σ}.

    Definition Cell_sls  : struct_layout_spec := mk_sls "Cell" [
      ("value", IntSynType I32)] StructReprRust.
  End Cell_sls.

  Section code.
  Context `{!typeGS Σ}.
  Open Scope printing_sugar.

  Definition Cell_new_def : function := {|
  f_args := [
    ("value", (it_layout I32) : layout)
  ];
  f_local_vars := [
    ("__0", (use_layout_alg' (syn_type_of_sls (Cell_sls))) : layout);
    ("__2", (it_layout I32) : layout)
  ];
  f_code :=
    <[
    "_bb0" :=
    "__2" <-{ IntOp I32 } use{ IntOp I32 } ("value");
    "__0" <-{ (use_op_alg' (syn_type_of_sls (Cell_sls))) } StructInit (Cell_sls) [("value", use{ IntOp I32 } ("__2") : expr)];
    return (use{ (use_op_alg' (syn_type_of_sls (Cell_sls))) } ("__0"))
    ]>%E $
    ∅;
  f_init := "_bb0";
  |}.

  End code.

  Section Cell_ty.
    Context `{!refinedrustGS Σ}.

    Definition Cell_ty : type (plist place_rfn [Z : Type]).
    Proof using . exact (struct_t Cell_sls +[(int I32)]). Defined.

    Definition Cell_rt : Type.
    Proof using . let __a := eval hnf in (rt_of Cell_ty) in exact __a. Defined.

    Global Typeclasses Transparent Cell_ty.
    Global Typeclasses Transparent Cell_rt.
  End Cell_ty.
  Global Arguments Cell_rt : clear implicits.

  Section Cell_inv_t.
    Context `{!refinedrustGS Σ}.

    Program Definition Cell_inv_t_inv_spec : na_ex_inv_def (Cell_rt) (Z) :=
      na_mk_ex_inv_def
        ((Z)%type)
        (xmap)
        (λ π inner_rfn 'x, ⌜inner_rfn = -[#(x)]⌝ ∗ ⌜Zeven x⌝ ∗ True)%I
        []
        [] _ _.
    Next Obligation. ex_t_solve_persistent. Qed.
    Next Obligation. ex_t_solve_timeless. Qed.

    Definition Cell_inv_t : type (Z) :=
      na_ex_plain_t _ _ Cell_inv_t_inv_spec Cell_ty.
    Global Typeclasses Transparent Cell_inv_t.

    Definition Cell_inv_t_rt : Type.
    Proof using. let __a := eval hnf in (rt_of Cell_inv_t) in exact __a. Defined.
    Global Typeclasses Transparent Cell_inv_t_rt.
  End Cell_inv_t.
  Global Arguments Cell_inv_t_rt : clear implicits.

  Section specs.
    Context `{!refinedrustGS Σ}.

    Definition type_of_Cell_new  :=
      fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (Type * syn_type)%type) | (x) : (Z), (λ ϝ, []); x :@: (int I32); (λ π : thread_id, (⌜Zeven x⌝)))
        → ∃ _ : unit, x @ Cell_inv_t; (λ π : thread_id, True).
  End specs.

  Section proof.
    Context `{!refinedrustGS Σ}.

    Definition Cell_new_lemma  (π : thread_id) : Prop :=
      syn_type_is_layoutable ((syn_type_of_sls (Cell_sls))) →
      ⊢ typed_function π (Cell_new_def ) [(syn_type_of_sls (Cell_sls)); IntSynType I32] (<tag_type> type_of_Cell_new ).
  End proof.

  Ltac Cell_new_prelude :=
    unfold Cell_new_lemma;
    set (FN_NAME := FUNCTION_NAME "Cell_new");
    intros;
    iStartProof;
    let ϝ := fresh "ϝ" in
    start_function "Cell_new" ϝ ( [] ) ( [] ) (  x ) (  x );
    set (loop_map := BB_INV_MAP (PolyNil));
    intros arg_value local___0 local___2;
    init_lfts (∅ );
    init_tyvars ( ∅ ).

  Section na_subtype.
    Context `{!refinedrustGS Σ}.
    Context {rt X : Type} (P : na_ex_inv_def rt X).

    Lemma na_owned_subtype_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
      (prove_with_subtype E L false ProveDirect (P.(na_inv_P) π r r') (λ L1 _ R, R -∗ T L1))
      ⊢ owned_subtype π E L false r r' ty (∃na; P, ty) T.
    Proof.
      unfold owned_subtype, prove_with_subtype.

      iIntros "HT".
      iIntros (???) "#CTX #HE HL".
      iMod ("HT" with "[//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
      iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
      iSplitR; last iSplitR.
      - simpl. iPureIntro.
        intros ly1 ly2 Hly1 HLy2. f_equiv. by eapply syn_type_has_layout_inj.
      - simpl. eauto.
      - iIntros (v) "Hv0".
        iEval (rewrite /ty_own_val/=).
        eauto with iFrame.
    Qed.
    Global Instance owned_subtype_ex_plain_t_inst π E L (ty : type rt) (r : rt) (r' : X) :
      OwnedSubtype π E L false r r' ty (∃na; P, ty) :=
      λ T, i2p (na_owned_subtype_ex_plain_t π E L ty r r' T).
  End na_subtype.

  Section proof.
    Context `{!refinedrustGS Σ}.
    Lemma Cell_T_new_proof (π : thread_id) :
      Cell_new_lemma π.
    Proof.
      Cell_new_prelude.

      repeat liRStep; liShow.

      all: print_remaining_goal.
      Unshelve. all: sidecond_solver.
      Unshelve. all: sidecond_hammer.
      Unshelve. all: print_remaining_sidecond.
    Qed.
  End proof.
End generated_code.
