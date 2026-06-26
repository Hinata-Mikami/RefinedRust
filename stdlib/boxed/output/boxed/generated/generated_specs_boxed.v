From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.boxed.boxed Require Export generated_code_boxed.

Section Box_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (A_rt : RT).


Definition Box_ty (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(T_rt); (A_rt)] ((type (plist place_rfnRT [((((unique_Unique_inv_t_rt)) ((T_rt)))) : RT; (A_rt) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((struct_t (Box_sls ((T_ty.(ty_syn_type) (MetaNone))) ((A_ty.(ty_syn_type) (MetaNone)))) +[((unique_Unique_inv_t ((T_rt)) -[] -[T_ty])); (A_ty)]))).
Defined.

Definition Box_rt  : RT.
Proof using T_rt A_rt .
  let __a := (normalized_rt_of_spec_ty (Box_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Box_ty.
#[global] Typeclasses Transparent Box_rt.
End Box_ty.
Global Arguments Box_rt : clear implicits.
Section Box_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (A_rt : RT).

  Program Definition Box_inv_t_inv_spec (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [T_rt; A_rt] (ex_inv_def ((Box_rt (T_rt) (A_rt)))%type ((place_rfn (T_rt)))%type) := spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), mk_ex_inv_def_auto_shr
    (λ π inner_rfn (_ty_rfn : RT_rt ((place_rfn (T_rt))%type : RT)),
            let 'x := _ty_rfn in ∃ (l: name_hint_ty "l" ((loc))%Z) (a: name_hint_ty "a" (((RT_xt (A_rt))))%Z), ⌜inner_rfn = -[#(l); #($# a)]⌝ ∗ guarded true (l ◁ₗ[π, Owned] x @ ◁ T_ty) ∗ Allocator_A_spec_attrs.(Allocator_FreeablePerm) a l (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) ∗ True)%I
    (λ π _ (_rfn_binder : RT_rt ((place_rfn (T_rt))%type : RT)),
            let 'x := _rfn_binder in (∃ r, place_rfn_interp_owned x r ∗ ty_ghost_drop T_ty π r) ∗ True)%I
    (false)
    ([] ++ ty_lfts T_ty)
    ([] ++ ty_wf_E T_ty)
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. intros ?; ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. intros ?; ex_plain_t_solve_ghost_drop. Qed.

  Definition Box_inv_t (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [T_rt; A_rt] (type ((place_rfn (T_rt)))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ex_plain_t _ _ (Box_inv_t_inv_spec Allocator_A_spec_attrs -[] -[T_ty; A_ty]) (((Box_ty (T_rt) (A_rt)) (Allocator_A_spec_attrs)) -[] -[T_ty; A_ty]).
Global Arguments Box_inv_t_inv_spec : simpl never.
Global Arguments Box_inv_t : simpl never.
  Global Typeclasses Transparent Box_inv_t.
  Definition Box_inv_t_rt : RT.
  Proof using T_rt A_rt . let __a := normalized_rt_of_spec_ty Box_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Box_inv_t_rt.
End Box_inv_t.
Global Arguments Box_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition BoxTAasstd_ops_Drop_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (A_rt: RT) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((Drop_spec_attrs (((Box_inv_t_rt ((T_rt)) ((A_rt))))))) :=
  mk_Drop_spec_attrs.


End attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section contractive.
  Context `{!refinedrustGS Σ}.

  Global Instance Box_inv_t_contr {rt1 T_rt A_rt : RT} (T : type rt1 → type T_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, Box_inv_t T_rt A_rt A_attrs <TY> (T ty) <TY> A_ty <INST!>).
  Proof.
    intros X.
    apply ex_inv_def_contractive.
    - constructor.
      + simpl. apply ty_lft_morphism_to_direct.
        apply X.
      + solve_proper_prepare.
        repeat solve_proper_step.
      + solve_proper_prepare.
        repeat solve_proper_step.
    - cbn; apply _.
  Qed.
  Global Instance Box_inv_t_ne {rt1 T_rt A_rt : RT} (T : type rt1 → type T_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, Box_inv_t T_rt A_rt A_attrs <TY> (T ty) <TY> A_ty <INST!>).
  Proof. apply _. Qed.

  (** Resolve ghost: Resolve observations on the contained value. *)
  Lemma resolve_ghost_box {T_rt A_rt} A_attrs (T_ty : type T_rt) (A_ty : type A_rt) π E L r rm T :
    (∀ l', resolve_ghost π E L rm true l' (◁ T_ty) Owned r T)
    ⊢ resolve_ghost_adt π E L rm r (Box_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>) T.
  Proof.
    rewrite /resolve_ghost_adt /resolve_ghost.
    iIntros "HT" (????) "#CTX #HE HL Hv".
    rewrite ex_plain_t_unfold_val.
    iDestruct "Hv" as ((l' & a & [])) "(Hinv & Hv)". simpl in *.
    iDestruct "Hinv" as "(%l'' & %a'' & %Heq & Hl' & Halloc & _)".
    inversion Heq. subst.
    unfold guarded. iDestruct "Hl'" as "(Hc & Hl')".
    iDestruct "Hc" as "((Hc1 & Hc) & Ht)".
    iApply (lc_fupd_add_later with "Hc1"). iNext.
    iMod ("HT" with "[] [] CTX HE HL Hl'") as "(%L2 & %r' & %R & %progress & Hstep & HL & HT)"; [done.. | ].
    iFrame.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_tr with "Ht").
    iModIntro. iIntros "Ht Hcreds' !> (Hl' & $)".
    rewrite ex_plain_t_unfold_val.
    iFrame. iR.
    rewrite /guarded. iFrame.
    iDestruct "Ht" as "(_ & $)".
  Qed.

  (* Box is covariant in T and A *)
  Lemma subtype_box {T_rt A_rt} A_attrs (T_ty_1 T_ty_2 : type T_rt) (A_ty_1 A_ty_2 : type A_rt) E L T :
    mut_subtype E L T_ty_1 T_ty_2 (mut_subtype E L A_ty_1 A_ty_2 T)
    ⊢ subtype_adt E L (Box_inv_t_inv_spec T_rt A_rt A_attrs <TY> T_ty_1 <TY> A_ty_1 <INST!>) (Box_inv_t_inv_spec T_rt A_rt A_attrs <TY> T_ty_2 <TY> A_ty_2 <INST!>) T.
  Proof.
    rewrite /mut_subtype /subtype_adt.
    iIntros "(%HsubT & %HsubA & $)". iPureIntro.
    iIntros (?) "HL HE".
    iPoseProof (full_subtype_acc_noend with "HE HL") as "(%HstT & #HinclT)"; first apply HsubT.
    iPoseProof (full_subtype_acc_noend with "HE HL") as "(%HstA & #HinclA)"; first apply HsubA.
    iSplit; iModIntro.
    - iIntros (? x r). simpl.
      iIntros "(%l & %a & -> & Hl & Hperm)".
      iExists _, _. iR.
      rewrite HstT. iFrame.
      iApply (guarded_mono with "[] Hl").
      iIntros "Hl". iApply type_incl_ltype_owned_wand; [ | done..].
      rewrite HstT//.
    - iIntros (? ? x r). simpl.
      iIntros "(%l & %a & -> & Hl & Hperm)".
      iExists _, _. iR. iL.
      iApply (guarded_mono with "[] Hl").
      iIntros "Hl". iApply type_incl_ltype_shared_wand; [ | done..].
      rewrite HstT//.
  Qed.
  Definition subtype_box_inst := [instance @subtype_box].
  Global Existing Instance subtype_box_inst.
End contractive.
Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_box_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_box_new (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x @ (Box_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_Box_T_from_raw (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_Box_T_from_raw (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b, raw) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) raw :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (raw ◁ₗ[π, Owned] #(($#@{ (T_rt) } b)) @ (◁ T_ty))
        ∗ (freeable_nz raw (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) 1 HeapAlloc)
        ∗ (⌜(raw.(loc_a) ≠ 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, b @ (Box_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_Box_TA_from_raw_in (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_A_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt)))) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st-[] -[A_ty]))) ∧ (trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Box_TA_from_raw_in (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b, raw, alloc) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) raw :@: alias_ptr_t, alloc :@: A_ty;
      (* precondition. *) (λ π : thread_id, (raw ◁ₗ[π, Owned] #(($#@{ (T_rt) } b)) @ (◁ T_ty))
        ∗ (Allocator_A_spec_attrs.(Allocator_FreeablePerm) alloc raw (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))))
        ∗ (⌜(raw.(loc_a) ≠ 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, b @ (Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_Box_T_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_Box_T_new (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x @ (Box_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_drop_glue_Box (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_A_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st-[] -[A_ty])))).

Definition type_of_drop_glue_Box (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; A_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec (((Box_inv_t_rt ((T_rt)) ((A_rt))))) ((Box_st (T_st) (A_st))))
    -[] -[(Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])]).(DropGlue_drop_glue_spec)   a b))) <MERGE!>.


Definition trait_incl_of_BoxTAasstd_ops_Drop_drop (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_A_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st-[] -[A_ty])))).

Definition type_of_BoxTAasstd_ops_Drop_drop (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, lmem, a) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) l :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(-[#lmem; #($# a)]) @ (◁ Box_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]))
        ∗ (lmem ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))
        ∗ (Allocator_A_spec_attrs.(Allocator_FreeablePerm) a lmem (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(-[#lmem; #($# a)]) @ (◁ Box_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]))).

Definition trait_incl_of_Box_T_into_raw (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_Box_T_into_raw (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) b :@: (Box_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : (((loc))), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(($#@{ (T_rt) } b)) @ (◁ T_ty))
      ∗ (freeable_nz l (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) 1 HeapAlloc)
      ∗ (⌜(l.(loc_a) ≠ 0)%Z⌝)).

Definition trait_incl_of_Box_TA_into_raw_with_allocator (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_A_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt)))) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st-[] -[A_ty]))) ∧ (trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Box_TA_into_raw_with_allocator (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) b :@: (Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l, a) : (((loc) * _)), *[l; a] @ (tuple2_ty (loc) ((A_rt)) -[] -[alias_ptr_t; A_ty]);
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(($#@{ (T_rt) } b)) @ (◁ T_ty))
      ∗ (Allocator_A_spec_attrs.(Allocator_FreeablePerm) a l (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))))
      ∗ (⌜(l.(loc_a) ≠ 0)%Z⌝)).



End specs.
Section BoxTAasstd_ops_Drop_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition BoxTAasstd_ops_Drop_spec (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (Drop_spec (((Box_inv_t_rt ((T_rt)) ((A_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), {|
        Drop_drop_spec  :=
          (type_of_BoxTAasstd_ops_Drop_drop ((T_rt)) ((A_rt)) (T_st) (A_st)) Allocator_A_spec_attrs 
             <TY> T_ty <TY> A_ty : (spec_with 1 [] fn_spec);
      |}
  .
  Definition BoxTAasstd_ops_Drop_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl Drop_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (BoxTAasstd_ops_Drop_spec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs))-[] -[T_ty; A_ty]) (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), scope_add_typarams _ -[T_ty; A_ty] ((Drop_base_spec ((Box_inv_t_rt ((T_rt)) ((A_rt)))) (Box_st (T_st) (A_st)) (BoxTAasstd_ops_Drop_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs))-[] -[(Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])])))).
End BoxTAasstd_ops_Drop_spec.

Section drop_glue_Box_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition drop_glue_Box_spec (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (DropGlue_spec (((Box_inv_t_rt ((T_rt)) ((A_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), {|
        DropGlue_drop_glue_spec  :=
          (type_of_drop_glue_Box ((T_rt)) ((A_rt)) (T_st) (A_st)) Allocator_A_spec_attrs 
             <TY> T_ty <TY> A_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition drop_glue_Box_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (drop_glue_Box_spec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs))-[] -[T_ty; A_ty]) (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), scope_add_typarams _ -[T_ty; A_ty] ((DropGlue_base_spec ((Box_inv_t_rt ((T_rt)) ((A_rt)))) (Box_st (T_st) (A_st))-[] -[(Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])])))).
End drop_glue_Box_spec.

