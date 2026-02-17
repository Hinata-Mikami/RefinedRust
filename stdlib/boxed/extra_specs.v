Section box.
  Context `{!LayoutAlg}.

  (* Notation used for Rust's magic box deref *)
  Definition magic_box_deref (T_st A_st : syn_type) (e : expr) : expr :=
    (*b.0.pointer.pointer*)
    (!{PtrOp} (((e at{Box_sls T_st A_st} "0") at{unique_Unique_sls T_st} "ptr") at{nonnull_NonNull_sls T_st} "pointer"))%E
  .
End box.
#[export] Hint Unfold magic_box_deref : solve_into_place_unfold.
Notation "'!box{' T_st ',' A_st '}' e" := (magic_box_deref T_st A_st e) (at level 9, format "!box{ T_st , A_st } e") : expr_scope.

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
End contractive.
