From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced Require Export generated_code_ptr_advanced.

Section nonnull_NonNull_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).


Definition nonnull_NonNull_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [loc : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (nonnull_NonNull_sls ((T_ty.(ty_syn_type) (MetaNone)))) +[(alias_ptr_t)]))).
Defined.

Definition nonnull_NonNull_rt  : RT.
Proof using T_rt .
  let __a := (normalized_rt_of_spec_ty (nonnull_NonNull_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent nonnull_NonNull_ty.
#[global] Typeclasses Transparent nonnull_NonNull_rt.
End nonnull_NonNull_ty.
Global Arguments nonnull_NonNull_rt : clear implicits.
Section nonnull_NonNull_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).

  Program Definition nonnull_NonNull_inv_t_inv_spec  : spec_with 0 [T_rt] (ex_inv_def ((nonnull_NonNull_rt (T_rt)))%type ((loc))%type) := spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((loc)%type : RT)),
            let 'l := _ty_rfn in ⌜inner_rfn = -[#(l)]⌝ ∗ ⌜(l.(loc_a) ≠ 0)%Z⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition nonnull_NonNull_inv_t  : spec_with 0 [T_rt] (type ((loc))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (nonnull_NonNull_inv_t_inv_spec   <TY> T_ty <INST!>) ((nonnull_NonNull_ty (T_rt))  <TY> T_ty <INST!>).
  Global Typeclasses Transparent nonnull_NonNull_inv_t.
  Definition nonnull_NonNull_inv_t_rt : RT.
  Proof using T_rt . let __a := normalized_rt_of_spec_ty nonnull_NonNull_inv_t in exact __a. Defined.
  Global Typeclasses Transparent nonnull_NonNull_inv_t_rt.
End nonnull_NonNull_inv_t.
Global Arguments nonnull_NonNull_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition nonnull_NonNullTasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Clone_spec_attrs (((nonnull_NonNull_inv_t_rt ((T_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section unique_Unique_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).


Definition unique_Unique_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [((nonnull_NonNull_inv_t_rt ((T_rt)))) : RT; (((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (unique_Unique_sls ((T_ty.(ty_syn_type) (MetaNone)))) +[((nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>)); ((core_marker_PhantomData_ty ((T_rt))  <TY> T_ty <INST!>))]))).
Defined.

Definition unique_Unique_rt  : RT.
Proof using T_rt .
  let __a := (normalized_rt_of_spec_ty (unique_Unique_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent unique_Unique_ty.
#[global] Typeclasses Transparent unique_Unique_rt.
End unique_Unique_ty.
Global Arguments unique_Unique_rt : clear implicits.
Section unique_Unique_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).

  Program Definition unique_Unique_inv_t_inv_spec  : spec_with 0 [T_rt] (ex_inv_def ((unique_Unique_rt (T_rt)))%type ((loc))%type) := spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((loc)%type : RT)),
            let 'l := _ty_rfn in ⌜inner_rfn = -[#(l); #(tt)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition unique_Unique_inv_t  : spec_with 0 [T_rt] (type ((loc))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (unique_Unique_inv_t_inv_spec   <TY> T_ty <INST!>) ((unique_Unique_ty (T_rt))  <TY> T_ty <INST!>).
  Global Typeclasses Transparent unique_Unique_inv_t.
  Definition unique_Unique_inv_t_rt : RT.
  Proof using T_rt . let __a := normalized_rt_of_spec_ty unique_Unique_inv_t in exact __a. Defined.
  Global Typeclasses Transparent unique_Unique_inv_t_rt.
End unique_Unique_inv_t.
Global Arguments unique_Unique_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition nonnull_NonNullTasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Copy_spec_attrs (((nonnull_NonNull_inv_t_rt ((T_rt))))) ((nonnull_NonNullTasstd_clone_Clone_spec_attrs ((T_rt)))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition unique_UniqueTasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Clone_spec_attrs (((unique_Unique_inv_t_rt ((T_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition unique_UniqueTasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Copy_spec_attrs (((unique_Unique_inv_t_rt ((T_rt))))) ((unique_UniqueTasstd_clone_Clone_spec_attrs ((T_rt)))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section contractive.
  Context `{!refinedrustGS Σ}.

  Global Instance NonNull_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, nonnull_NonNull_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_inv_def_contractive.
    - constructor.
      + simpl. apply _.
      + solve_proper.
      + solve_proper.
    - cbn. apply _.
  Qed.
  Global Instance NonNull_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, nonnull_NonNull_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.
  Global Instance Unique_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, unique_Unique_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_inv_def_contractive.
    - constructor.
      + simpl. apply _.
      + solve_proper.
      + solve_proper.
    - cbn; apply _.
  Qed.
  Global Instance Unique_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, unique_Unique_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.
End contractive.
Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_nonnull_NonNullTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNullTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),((Clone_base_spec (((nonnull_NonNull_inv_t_rt ((T_rt))))) ((nonnull_NonNull_st (T_st))) ((nonnull_NonNullTasstd_clone_Clone_spec_attrs (T_rt))))
     <TY> (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_unique_UniqueTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_unique_UniqueTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),((Clone_base_spec (((unique_Unique_inv_t_rt ((T_rt))))) ((unique_Unique_st (T_st))) ((unique_UniqueTasstd_clone_Clone_spec_attrs (T_rt))))
     <TY> (unique_Unique_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_nonnull_NonNull_T_as_ptr (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_as_ptr (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; U_ty]) : ([(T_rt, T_st); (U_rt, U_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ (nonnull_NonNull_inv_t ((U_rt))   <TY> U_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_is_aligned (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_is_aligned (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (self `aligned_to` (ly_align (use_layout_alg' (ty_syn_type T_ty MetaNone)))) @ bool_t;
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_is_aligned_to (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_is_aligned_to (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, align) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>), align :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(is_power_of_two (Z.to_nat align))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (self `aligned_to` Z.to_nat align) @ bool_t;
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_new (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_new (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if decide (ptr.(loc_a) = 0) then None else Some ptr @ (Option_ty (((nonnull_NonNull_inv_t_rt ((T_rt)))))  <TY> (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_new_unchecked (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_new_unchecked (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (⌜(ptr.(loc_a) ≠ 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ptr @ (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_read (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_read (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, self) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_reads ty.(xtype_ty))%Z⌝)
        ∗ (⌜(ty_allows_writes ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))).

Definition trait_incl_of_nonnull_NonNull_T_read_volatile (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_read_volatile (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, self) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_reads ty.(xtype_ty))%Z⌝)
        ∗ (⌜(ty_allows_writes ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))).

Definition trait_incl_of_nonnull_NonNull_T_write (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_write (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, val) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>), val :@: T_ty;
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, Owned] #($# val) @ (◁ T_ty))).

Definition trait_incl_of_nonnull_NonNull_T_write_volatile (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_nonnull_NonNull_T_write_volatile (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, val) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>), val :@: T_ty;
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, Owned] #($# val) @ (◁ T_ty))).

Definition trait_incl_of_unique_Unique_T_as_ptr (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_unique_Unique_T_as_ptr (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (unique_Unique_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_unique_Unique_T_dangling (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_unique_Unique_T_dangling (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ (unique_Unique_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit UnitSynType))
      ∗ (freeable_nz l 0 1 HeapAlloc)).

Definition trait_incl_of_unique_Unique_T_new_unchecked (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_unique_Unique_T_new_unchecked (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (⌜(ptr.(loc_a) ≠ 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ptr @ (unique_Unique_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).




End specs.
Section nonnull_NonNullTasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition nonnull_NonNullTasstd_clone_Clone_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Clone_spec (((nonnull_NonNull_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_nonnull_NonNullTasstd_clone_Clone_clone ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (((nonnull_NonNull_inv_t_rt ((T_rt))))) ((nonnull_NonNull_st (T_st)))) (nonnull_NonNullTasstd_clone_Clone_spec_attrs (T_rt)) 
             <TY> (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition nonnull_NonNullTasstd_clone_Clone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (nonnull_NonNullTasstd_clone_Clone_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Clone_base_spec ((nonnull_NonNull_inv_t_rt ((T_rt)))) (nonnull_NonNull_st (T_st)) (nonnull_NonNullTasstd_clone_Clone_spec_attrs (T_rt))<TY> (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>))).
End nonnull_NonNullTasstd_clone_Clone_spec.

Section nonnull_NonNullTasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition nonnull_NonNullTasstd_marker_Copy_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Copy_spec (((nonnull_NonNull_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (((nonnull_NonNull_inv_t_rt ((T_rt)))))).
  Definition nonnull_NonNullTasstd_marker_Copy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (nonnull_NonNullTasstd_marker_Copy_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Copy_base_spec ((nonnull_NonNull_inv_t_rt ((T_rt)))) (nonnull_NonNull_st (T_st)) (nonnull_NonNullTasstd_clone_Clone_spec_attrs ((T_rt))) (nonnull_NonNullTasstd_marker_Copy_spec_attrs (T_rt))<TY> (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>))).
  Lemma nonnull_NonNullTasstd_marker_Copy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp ((nonnull_NonNull_inv_t_rt ((T_rt)))) (nonnull_NonNull_inv_t ((T_rt))   <TY> T_ty <INST!>)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End nonnull_NonNullTasstd_marker_Copy_spec.

Section unique_UniqueTasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition unique_UniqueTasstd_clone_Clone_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Clone_spec (((unique_Unique_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_unique_UniqueTasstd_clone_Clone_clone ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (((unique_Unique_inv_t_rt ((T_rt))))) ((unique_Unique_st (T_st)))) (unique_UniqueTasstd_clone_Clone_spec_attrs (T_rt)) 
             <TY> (unique_Unique_inv_t ((T_rt))   <TY> T_ty <INST!>) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition unique_UniqueTasstd_clone_Clone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (unique_UniqueTasstd_clone_Clone_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Clone_base_spec ((unique_Unique_inv_t_rt ((T_rt)))) (unique_Unique_st (T_st)) (unique_UniqueTasstd_clone_Clone_spec_attrs (T_rt))<TY> (unique_Unique_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>))).
End unique_UniqueTasstd_clone_Clone_spec.

Section unique_UniqueTasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition unique_UniqueTasstd_marker_Copy_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Copy_spec (((unique_Unique_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (((unique_Unique_inv_t_rt ((T_rt)))))).
  Definition unique_UniqueTasstd_marker_Copy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (unique_UniqueTasstd_marker_Copy_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Copy_base_spec ((unique_Unique_inv_t_rt ((T_rt)))) (unique_Unique_st (T_st)) (unique_UniqueTasstd_clone_Clone_spec_attrs ((T_rt))) (unique_UniqueTasstd_marker_Copy_spec_attrs (T_rt))<TY> (unique_Unique_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>))).
  Lemma unique_UniqueTasstd_marker_Copy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp ((unique_Unique_inv_t_rt ((T_rt)))) (unique_Unique_inv_t ((T_rt))   <TY> T_ty <INST!>)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End unique_UniqueTasstd_marker_Copy_spec.

