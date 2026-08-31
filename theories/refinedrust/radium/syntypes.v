From radium Require Import lang.

(** * Syntactic types *)
(** Syntactic types determine abstract layout information (i.e. that a struct has certain fields), but do not determine a concrete data layout yet.
  For generic code, they capture all the operational layout information that the generic type needs to satisfy, i.e. we can verify generic code by parameterizing it over the syntactic type of the type parameters.
*)


(* TODO move *)
Lemma Nat_pow_max x n1 n2 :
  (1 ≤ x)%nat →
  (x ^ Nat.max n1 n2 = Nat.max (x ^ n1) (x ^ n2))%nat.
Proof.
  intros ?.
  destruct (Nat.max_spec n1 n2) as [[Hle ->] | [Hle ->]].
  - rewrite Nat.max_r; first lia. apply Nat.pow_le_mono_r; lia.
  - rewrite Nat.max_l; first lia. apply Nat.pow_le_mono_r; lia.
Qed.
(* TODO move *)
Lemma Nat_Z_in_bounds_max (l h : Z) (n1 n2 : nat) :
  (l ≤ n1 ≤ h) →
  (l ≤ n2 ≤ h) →
  (l ≤ (n1 `max` n2)%nat ≤ h).
Proof.
  intros Ha Hb. destruct (Nat.max_spec n1 n2) as [[Hle ->] | [Hle ->]]; lia.
Qed.
Lemma Nat_Z_in_bounds_max_1 (h : Z) (n1 n2 : nat) :
  (n1 ≤ h) →
  (n2 ≤ h) →
  ((n1 `max` n2)%nat ≤ h).
Proof.
  intros Ha Hb. destruct (Nat.max_spec n1 n2) as [[Hle ->] | [Hle ->]]; lia.
Qed.

Lemma max_list_pow (n : nat) l :
  1 ≤ n →
  n ^ (max_list l) = max 1 (max_list ((λ x, (n ^ x)%nat) <$> l)).
Proof.
  intros ?.
  induction l as [ | x l IH]; simpl; first done.
  change (n ^ max_list l = (1 `max` max_list (list_fmap nat nat (λ x0 : nat, (n ^ x0)%nat) l))%nat) in IH.
  destruct (Nat.max_spec x (max_list l)) as [[Hle Hmax] | [Hle Hmax]]; rewrite Hmax.
  - rewrite IH.
    assert (Hpow : (n ^ x ≤ n ^ max_list l)%nat) by (apply Nat.pow_le_mono_r; lia).
    set (M := max_list (list_fmap nat nat (λ x0 : nat, (n ^ x0)%nat) l)).
    destruct (Nat.max_spec (n ^ x) M) as [[Hxm Hin] | [Hmx Hin]]; rewrite Hin; subst M; first done.
    destruct (Nat.max_spec 1 (max_list (list_fmap nat nat (λ x0 : nat, (n ^ x0)%nat) l))) as [[H1M H1max] | [HM1 H1max]]; rewrite H1max; lia.
  - assert (Hpow : (n ^ max_list l ≤ n ^ x)%nat) by (apply Nat.pow_le_mono_r; lia).
    assert (HM : (max_list (list_fmap nat nat (λ x0 : nat, (n ^ x0)%nat) l) ≤ n ^ x)%nat).
    { lia. }
    assert (Hone : (1 ≤ n ^ x)%nat).
    { rewrite -(Nat.pow_1_l x).
      apply Nat.pow_le_mono_l; lia. }
    rewrite Nat.max_r; last lia.
    rewrite Nat.max_l; first lia.
    lia.
Qed.

(* TODO move *)
Lemma max_alloc_end_le_usize :
  (max_alloc_end ≤ max_int USize)%Z.
Proof.
  unfold_common_radium_defs. simpl. lia.
Qed.

Lemma mjoin_has_struct_layout sl vs :
  Forall2 (λ v ly, v `has_layout_val` ly) vs sl.(sl_members).*2 →
  mjoin vs `has_layout_val` sl.
Proof.
  rewrite /has_layout_val/layout_of{2}/ly_size/=.
  generalize (sl_members sl) => fields. clear sl.
  induction fields as [ | [n field] fields IH] in vs |-*; simpl; intros Hf.
  - apply Forall2_nil_inv_r in Hf as ->. done.
  - destruct vs as [ | v vs].
    { apply Forall2_nil_inv_l in Hf. naive_solver. }
    apply Forall2_cons_inv in Hf as (Hlen & Hf).
    simpl. rewrite length_app Hlen.
    rewrite IH; done.
Qed.

Lemma mjoin_pad_struct_layout sl els f :
  Forall2 (λ '(n, ly) v, v `has_layout_val` ly) (named_fields sl.(sl_members)) els →
  (∀ ly, length (f ly) = ly_size ly) →
  mjoin (pad_struct sl.(sl_members) els f) `has_layout_val` sl.
Proof.
  intros Ha Hb. apply mjoin_has_struct_layout.
  move: Ha. generalize (sl_members sl) => fields. clear sl.
  induction fields as [ | [[name | ] field] fields IH] in els |-*; simpl; first done.
  - destruct els as [ | v els]; simpl; first inversion 1.
    intros [Ha Hf]%Forall2_cons_inv. econstructor; first done. by apply IH.
  - intros Hf. econstructor; first apply Hb. by apply IH.
Qed.

Ltac unsafe_unfold_common_radium_defs :=
  rewrite ?MaxInt_eq ?MinInt_eq;
  repeat match goal with
  | H : context[MaxInt ?it] |- _ => rewrite !MaxInt_eq in H
  | H : context[MinInt ?it] |- _ => rewrite !MinInt_eq in H
  end;
  unfold_common_radium_defs.

(** Rust repr options *)
Inductive struct_repr :=
  (** repr(rust) *)
  | StructReprRust
  (** repr(C) *)
  | StructReprC
  (** repr(transparent) *)
  | StructReprTransparent.
Global Instance struct_repr_eqdec : EqDecision struct_repr.
Proof. solve_decision. Defined.
Global Instance struct_repr_inhabited : Inhabited struct_repr.
Proof. exact (populate StructReprRust). Qed.

Inductive union_repr :=
  (** repr(rust) *)
  | UnionReprRust
  (** repr(C) *)
  | UnionReprC.
Global Instance union_repr_eqdec : EqDecision union_repr.
Proof. solve_decision. Defined.
Global Instance union_repr_inhabited : Inhabited union_repr.
Proof. exact (populate UnionReprRust). Qed.

(** Rust already picks a representation for the tag at the MIR level, so we do not include this part. *)
Inductive enum_repr :=
  (** repr(rust) *)
  | EnumReprRust
  (** repr(C) *)
  | EnumReprC
  (** repr(transparent) *)
  | EnumReprTransparent.
Global Instance enum_repr_eqdec : EqDecision enum_repr.
Proof. solve_decision. Defined.
Global Instance enum_repr_inhabited : Inhabited enum_repr.
Proof. exact (populate EnumReprRust). Qed.

Record enum_layout_spec_raw_gen (A : Set) : Set := mk_els_raw
  { raw_els_name : string;
    (* This is fixed (and not something chooseable by the layout algorithm), because Rust's MIR already has this type fixed. *)
    raw_els_tag_it : int_type;
    raw_els_variants : list (string * A);
    raw_els_repr : enum_repr;
    (* This is additional information that doesn't affect the layout algorithm, but just the operational behavior of enum operations *)
    raw_els_tag_int : list (var_name * Z);
  }.
Global Arguments raw_els_name {_} _.
Global Arguments raw_els_tag_it {_} _.
Global Arguments raw_els_variants {_} _.
Global Arguments raw_els_repr {_} _.
Global Arguments raw_els_tag_int {_} _.

(** ** Syntactic types *)
(** Syntactic types describe primitive types relevant to the operational semantics *before* layouting.
  They are not to be confused with proper semantic types.
 *)
#[warnings="-register-all"]
Inductive syn_type : Set :=
  (* integers *)
  | IntSynType (it : int_type)
  (* booleans *)
  | BoolSynType
  (* pointers. currently no distinction in terms of aliasing or so *)
  | PtrSynType
  (* function pointers *)
  | FnPtrSynType
  (* structs *)
  | StructSynType (sn : string) (field_list : list (string * syn_type)) (repr : struct_repr)
  (* unit *)
  | UnitSynType
  (* never *)
  | NeverSynType
  (* arrays of a specific length *)
  | ArraySynType (st : syn_type) (len : nat)
  (* UnsafeCell. Currently, it does not do anything exciting, but some day.. *)
  | UnsafeCell (st : syn_type)
  (* Untyped wrapper *)
  | UntypedSynType (st : syn_type)
  (* no type, using a literal layout *)
  (* we use this mostly to refer to untyped chunks of memory at runtime *)
  | LiteralSynType (ly : layout)
  (* enums *)
  | EnumSynType (els : enum_layout_spec_raw_gen syn_type)
  (* unions *)
  | UnionSynType (un : string) (variant_list : list (string * syn_type)) (repr : union_repr)
  (* char *)
  | CharSynType
  (* Rust references *)
  | RefSynType
.
Canonical Structure syn_typeO := leibnizO syn_type.
Global Instance syn_type_eq_dec : EqDecision syn_type.
Proof.
  refine (fix go (st1 st2 : syn_type) {struct st1} : Decision (st1 = st2) :=
    match st1, st2 with
    | IntSynType it1, IntSynType it2 => cast_if (decide (it1 = it2))
    | BoolSynType, BoolSynType => left _
    | PtrSynType, PtrSynType => left _
    | FnPtrSynType, FnPtrSynType => left _
    | StructSynType n1 fields1 repr1, StructSynType n2 fields2 repr2 =>
        if (decide (repr1 = repr2)) then
          cast_if_and (decide (n1 = n2))
            (List.list_eq_dec _ fields1 fields2)
          else right _
    | UnitSynType, UnitSynType => left _
    | ArraySynType st len, ArraySynType st' len' =>
        if (decide (len = len')) then
          cast_if (go st st')
        else right _
    | UntypedSynType st1, UntypedSynType st2 => cast_if (decide (st1 = st2))
    | LiteralSynType ly1, LiteralSynType ly2 => cast_if (decide (ly1 = ly2))
    | UnsafeCell st1, UnsafeCell st2 =>
        cast_if (go st1 st2)
    | EnumSynType els1, EnumSynType els2 =>
        if decide (els1.(raw_els_repr) = els2.(raw_els_repr)) then
        if decide (els1.(raw_els_name) = els2.(raw_els_name)) then
        if decide (els1.(raw_els_tag_it) = els2.(raw_els_tag_it)) then
        if List.list_eq_dec _ els1.(raw_els_variants) els2.(raw_els_variants) then
        if List.list_eq_dec _ els1.(raw_els_tag_int) els2.(raw_els_tag_int) then left _ else right _
        else right _ else right _ else right _ else right _
    | UnionSynType un1 vars1 repr1, UnionSynType un2 vars2 repr2 =>
        if decide (repr1 = repr2) then
        cast_if_and (decide (un1 = un2))
          (List.list_eq_dec _ vars1 vars2)
        else right _
    | CharSynType, CharSynType =>
        left _
    | RefSynType, RefSynType => left _
    | NeverSynType, NeverSynType => left _
    | _, _ => right _
    end);
    try (clear go; abstract intuition congruence).
    all: try (destruct els1, els2; simpl in *; subst; reflexivity).
    all: try solve_decision.
    all: unshelve eapply prod_eq_dec; [solve_decision | exact go].
Defined.

Lemma syn_type_strong_ind (P : syn_type → Prop) :
  (∀ it : int_type, P (IntSynType it)) →
  P BoolSynType →
  P PtrSynType →
  P FnPtrSynType →
  (∀ (sn : string) (field_list : list (string * syn_type)) repr,
    Forall (λ '(_, st), P st) field_list →
    P (StructSynType sn field_list repr)) →
  P UnitSynType →
  P NeverSynType →
  (∀ st : syn_type, P st → ∀ len : nat, P (ArraySynType st len)) →
  (∀ st : syn_type, P st → P (UnsafeCell st)) →
  (∀ st : syn_type, P st → P (UntypedSynType st)) →
  (∀ ly : layout, P (LiteralSynType ly)) →
  (∀ (els : enum_layout_spec_raw_gen syn_type),
    Forall (λ '(_, st), P st) els.(raw_els_variants) →
    P (EnumSynType els)) →
  (∀ (un : string) (variant_list : list (string * syn_type)) repr,
    Forall (λ '(_, st), P st) variant_list →
    P (UnionSynType un variant_list repr)) →
  P CharSynType →
  P RefSynType →
  ∀ s : syn_type, P s.
Proof.
  intros Hint Hbool Hptr Hfptr Hstruct Hunit Hnever Harray Huc Huntyped Hlayout Henum Hunion Hchar Href.
  refine (fix F (s : syn_type) : P s := _).
  destruct s.
  - apply Hint.
  - apply Hbool.
  - apply Hptr.
  - apply Hfptr.
  - apply Hstruct.
    induction field_list as [ | [f st] H IH]; first done.
    econstructor; first apply F. apply IH.
  - apply Hunit.
  - apply Hnever.
  - apply Harray. apply F.
  - apply Huc. apply F.
  - by apply Huntyped.
  - apply Hlayout.
  - apply Henum.
    induction (raw_els_variants els) as [ | [f st] H IH]; first done.
    econstructor; first apply F. apply IH.
  - apply Hunion.
    induction variant_list as [ | [f st] H IH]; first done.
    econstructor; first apply F. apply IH.
  - apply Hchar.
  - apply Href.
Qed.

Record struct_layout_spec : Set := mk_sls
  { sls_name : string; sls_fields : list (string * syn_type); sls_repr : struct_repr }.
Global Instance struct_layout_spec_eq_dec : EqDecision struct_layout_spec.
Proof. solve_decision. Defined.

Definition syn_type_of_sls (sls : struct_layout_spec) : syn_type :=
  StructSynType sls.(sls_name) sls.(sls_fields) sls.(sls_repr).
Coercion syn_type_of_sls : struct_layout_spec >-> syn_type.

Record union_layout_spec : Set := mk_uls
  { uls_name : string; uls_variants : list (string * syn_type); uls_repr : union_repr }.
Global Instance union_layout_spec_eq_dec : EqDecision union_layout_spec.
Proof. solve_decision. Defined.

Definition syn_type_of_uls (uls : union_layout_spec) : syn_type :=
  UnionSynType uls.(uls_name) uls.(uls_variants) uls.(uls_repr).
Coercion syn_type_of_uls : union_layout_spec >-> syn_type.

Record enum_layout_spec : Set := mk_els
  { els_name : string;
    (* This is fixed (and not something chooseable by the layout algorithm), because Rust's MIR already has this type fixed. *)
    els_tag_it : int_type;
    els_variants : list (string * syn_type);
    els_repr : enum_repr;
    (* This is additional information that doesn't affect the layout algorithm, but just the operational behavior of enum operations *)
    els_tag_int : list (var_name * Z);
    (* The variant list should have no duplicates *)
    els_variants_nodup :
      NoDup (fmap fst els_variants);
    (* The variant lists should agree *)
    els_tag_int_agree :
      fmap fst els_tag_int = fmap fst els_variants;
    (* the tags should have no duplicates *)
    els_tag_int_nodup:
      NoDup (fmap snd els_tag_int);
    (* the tags should be in range of the integer type for the tags *)
    els_tag_int_wf3 :
      Forall (λ '(_, tag), int_elem_of_it tag (els_tag_it : int_type)) els_tag_int;
  }.

Definition enum_layout_spec_raw (els : enum_layout_spec) : enum_layout_spec_raw_gen syn_type :=
  @mk_els_raw syn_type els.(els_name) els.(els_tag_it) els.(els_variants) els.(els_repr) els.(els_tag_int).

Definition syn_type_of_els (els : enum_layout_spec) : syn_type :=
    EnumSynType (enum_layout_spec_raw els).
Coercion syn_type_of_els : enum_layout_spec >-> syn_type.

Definition els_lookup_tag (els : enum_layout_spec) (f : string) : Z :=
  let discriminant_map : gmap _ _ := list_to_map (els.(els_tag_int)) in
  default 0%Z (discriminant_map !! f).

Definition enum_tag_int_wf (it : int_type) (variants : list (string * syn_type)) (tag_int : list (var_name * Z)) : Prop :=
  tag_int.*1 = variants.*1 ∧
  NoDup tag_int.*1 ∧
  NoDup tag_int.*2 ∧
  Forall (λ '(_, tag), int_elem_of_it tag it) tag_int.

(* TODO: generalize to permutations + subset? (it should work even when we ignore some named fields, I think, and reordering is allowed) *)
Definition sl_has_members (sl : struct_layout) (fields : list (var_name * layout)) :=
  fields = named_fields (sl.(sl_members)).

(* TODO: union layouts should be allowed to have trailing padding -- this is not accomodated by radium currently.
    Can we simulate that by adding a "__padding" variant?
*)
Definition ul_has_variants (ul : union_layout) (variants : list (var_name * layout)) :=
  variants = ul.(ul_members).

Definition el_has_variants (el : enum_layout) (tag_it : int_type) (variants : list (var_name * layout)) :=
  el.(el_tag_it) = tag_it ∧ variants = el.(el_variants).


Section C_alg.
  (** Defining the C struct layout algorithm for repr(C) *)
  Definition padding_needed (off a : nat) : nat :=
    (a - (off mod a)) mod a.
  Definition pad_layout (pad_bytes : nat) : layout := Layout pad_bytes 0.

  Fixpoint C_struct_layout_alg_raw_go (off a : nat) (fields : list (string * layout)) : list (option string * layout) :=
    match fields with
    | [] =>
        let pad := padding_needed off a in
        if decide (pad = 0%nat) then [] else [(None, pad_layout pad)]
    | (name, ly) :: fields' =>
        let a' := ly_align ly in
        let pad := padding_needed off a' in
        let off' := (off + pad)%nat in
        let a'' := Nat.max a a' in
        let this := (Some name, ly) in
        let rest := C_struct_layout_alg_raw_go (off' + ly_size ly)%nat a'' fields' in
        if decide (pad = 0%nat) then
          this :: rest
        else
          (None, pad_layout pad) :: this :: rest
    end.

  Local Lemma ly_align_nonzero ly :
    ly_align ly <> 0%nat.
  Proof.
    unfold ly_align. apply Nat.pow_nonzero. lia.
  Qed.

  Local Lemma padding_needed_zero_inv off a :
    a <> 0%nat →
    padding_needed off a = 0%nat →
    off mod a = 0%nat.
  Proof.
    intros Ha Hpad.
    unfold padding_needed in Hpad.
    destruct (off mod a)%nat eqn:Hmod.
    - lia.
    - simpl in Hpad.
      rewrite Nat.mod_small in Hpad; last lia.
      lia.
  Qed.

  Local Lemma padding_needed_zero_inv_nat off a :
    a <> 0%nat →
    padding_needed off a = 0%nat →
    ((off mod a)%nat = 0%nat).
  Proof.
    intros Ha Hpad.
    unfold padding_needed in Hpad.
    destruct (off mod a)%nat eqn:Hmod; first done.
    simpl in Hpad.
    rewrite Nat.mod_small in Hpad; last lia.
    lia.
  Qed.

  Local Lemma padding_needed_mod_zero (off a : nat) :
    a <> 0%nat →
    ((off + padding_needed off a) mod a)%nat = 0%nat.
  Proof.
    intros Ha.
    unfold padding_needed.
    rewrite Nat.Div0.add_mod.
    destruct (off mod a)%nat eqn:Hmod.
    - rewrite Nat.sub_0_r.
      rewrite Nat.Div0.mod_same.
      simpl. rewrite !Nat.Div0.mod_0_l; lia.
    - simpl. rewrite Nat.Div0.mod_mod.
      rewrite (Nat.mod_small (a - S n)%nat); last lia.
      assert (Hsum : (S (n + (a - S n)) = a)%nat) by lia.
      rewrite Hsum.
      rewrite Nat.Div0.mod_same; lia.
  Qed.

  Local Lemma C_struct_layout_alg_raw_go_aligned fields off a :
    check_fields_aligned (C_struct_layout_alg_raw_go off a fields) off = true.
  Proof.
    revert off a.
    induction fields as [|field fields IH]; intros off a; simpl.
    - destruct (decide (padding_needed off a = 0%nat)).
      + done.
      + simpl.
        rewrite /pad_layout/ly_align/=.
        rewrite Z.mod_1_r. done.
    - destruct field as [name ly].
      set (a' := ly_align ly).
      destruct (decide (padding_needed off a' = 0%nat)) as [Hpad|Hpad].
      + simpl.
        rewrite (padding_needed_zero_inv off a' (ly_align_nonzero ly) Hpad).
        rewrite Hpad Nat.add_0_r.
        simpl. by rewrite IH.
      + simpl.
        rewrite /pad_layout/ly_align/=.
        rewrite Z.mod_1_r.
        simpl.
        apply andb_true_intro.
        split; last apply IH.
        (* padding field is aligned *)
        apply bool_decide_true.
        subst a'. unfold ly_size.
        opose proof (padding_needed_mod_zero off (ly_align ly) _) as Ha.
        { apply ly_align_nonzero. }
        rewrite -Nat2Z.inj_mod.
        rewrite Ha. done.
  Qed.

  Definition C_struct_layout_alg_raw (fields : list (string * layout)) : list (option string * layout) :=
    C_struct_layout_alg_raw_go 0 1 fields.

  Program Definition C_struct_layout_alg (fields : list (string * layout)) : option struct_layout :=
    let fields' := C_struct_layout_alg_raw fields in
    if decide (NoDup (field_names fields')) then
      if decide (sum_list (ly_size <$> fields'.*2) ≤ max_int ISize) then
        Some {| sl_members := fields' |}
      else
        None
    else None
    .
  Next Obligation.
    intros fields fields' Hnd Hle.
    by rewrite bool_decide_true.
  Qed.
  Next Obligation.
    intros. lia.
  Qed.
  Next Obligation.
    intros. apply C_struct_layout_alg_raw_go_aligned.
  Qed.

  Local Lemma C_struct_layout_alg_raw_go_has_fields fields off a :
    named_fields (C_struct_layout_alg_raw_go off a fields) = fields.
  Proof.
    revert off a.
    induction fields as [|[name ly] fields IH]; intros off a; simpl.
    - destruct (decide (padding_needed off a = 0%nat)); done.
    - set (a' := ly_align ly).
      destruct (decide (padding_needed off a' = 0%nat)); simpl; by rewrite IH.
  Qed.

  Lemma C_struct_layout_alg_raw_has_fields fields :
    named_fields (C_struct_layout_alg_raw fields) = fields.
  Proof.
    unfold C_struct_layout_alg_raw.
    apply C_struct_layout_alg_raw_go_has_fields.
  Qed.

  Lemma C_struct_layout_alg_has_fields fields sl :
    C_struct_layout_alg fields = Some sl →
    named_fields sl.(sl_members) = fields.
  Proof.
    intros Halg.
    unfold C_struct_layout_alg in Halg.
    destruct (decide (NoDup (field_names (C_struct_layout_alg_raw fields)))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (sum_list (ly_size <$> (C_struct_layout_alg_raw fields).*2) ≤ max_int ISize)) as [Hle|Hle]; last discriminate.
    inversion Halg; subst sl; clear Halg.
    simpl.
    apply C_struct_layout_alg_raw_has_fields.
  Qed.

  Fixpoint C_struct_layout_alg_align_go (a : nat) (fields : list (string * layout)) : nat :=
    match fields with
    | [] => a
    | (_, ly) :: fields' => C_struct_layout_alg_align_go (Nat.max a (ly_align ly)) fields'
    end.

  Local Lemma C_struct_layout_alg_align_go_nonzero a fields :
    a <> 0%nat →
    C_struct_layout_alg_align_go a fields <> 0%nat.
  Proof.
    revert a.
    induction fields as [|[name ly] fields IH]; intros a Ha; simpl.
    - done.
    - apply IH. assert (Nat.max a (ly_align ly) <> 0%nat) by lia. done.
  Qed.

  Local Lemma C_struct_layout_alg_align_go_eq_max a fields :
    C_struct_layout_alg_align_go a fields = max a (max_list (ly_align <$> fields.*2)).
  Proof.
    revert a.
    induction fields as [|[name ly] fields IH]; intros a; simpl.
    - unfold fmap. simpl. lia.
    - rewrite IH. unfold fmap. lia.
  Qed.

  Local Lemma C_struct_layout_alg_align_go_1_eq_max fields :
    C_struct_layout_alg_align_go 1 fields = max 1 (max_list (ly_align <$> fields.*2)).
  Proof. apply C_struct_layout_alg_align_go_eq_max. Qed.

  Local Lemma C_struct_layout_alg_raw_go_max_align_preserve fields off a :
    max 1 (max_list (ly_align <$> (C_struct_layout_alg_raw_go off a fields).*2)) =
    max 1 (max_list (ly_align <$> fields.*2)).
  Proof.
    revert off a.
    induction fields as [|[name ly] fields IH]; intros off a; simpl.
    - destruct (decide (padding_needed off a = 0%nat)); simpl; done.
    - set (a' := ly_align ly).
      destruct (decide (padding_needed off a' = 0%nat)) as [Hpad|Hpad]; simpl.
      + rewrite Hpad Nat.add_0_r.
        pose proof (IH (off + ly_size ly)%nat (Nat.max a a')) as Hrec.
        unfold fmap in *. lia.
      + pose proof (IH (off + padding_needed off a' + ly_size ly)%nat (Nat.max a a')) as Hrec.
        rewrite /pad_layout/ly_align/=.
        subst a'. simpl in Hrec.
        pose proof (ly_align_ge_1 ly) as Hly.
        set (X := max_list (ly_align <$> (C_struct_layout_alg_raw_go (off + padding_needed off (ly_align ly) + ly_size ly) (Nat.max a (ly_align ly)) fields).*2)).
        set (Y := max_list (ly_align <$> fields.*2)).

        assert (HX : (1 `max` (1 `max` (ly_align ly `max` X)))%nat = (ly_align ly `max` (1 `max` X))%nat) by lia.
        assert (HY : (1 `max` (ly_align ly `max` Y))%nat = (ly_align ly `max` (1 `max` Y))%nat).
        (* TODO: without the clear, coqlsp crashes lol *)
        { clear X HX. lia. }
        rewrite HX HY.
        apply (f_equal (Nat.max (ly_align ly))) in Hrec.
        exact Hrec.
  Qed.

  Local Lemma C_struct_layout_alg_raw_go_size_mod fields off a :
    a <> 0%nat →
    ((off + sum_list (ly_size <$> (C_struct_layout_alg_raw_go off a fields).*2)) mod (C_struct_layout_alg_align_go a fields))%nat = 0%nat.
  Proof.
    revert off a.
    induction fields as [|[name ly] fields IH]; intros off a Ha; simpl.
    - destruct (decide (padding_needed off a = 0%nat)) as [Hpad|Hpad].
      + rewrite Nat.add_0_r.
        unfold padding_needed in Hpad.
        destruct ((off `mod` a)%nat) eqn:Hm; first done.
        simpl in Hpad.
        rewrite Nat.mod_small in Hpad; last lia.
        lia.
      + rewrite /pad_layout /=.
        replace (off + (padding_needed off a + 0))%nat with (off + padding_needed off a)%nat by lia.
        apply (padding_needed_mod_zero off a Ha).
    - set (a' := ly_align ly).
      set (pad := padding_needed off a').
      set (off' := (off + pad)%nat).
      set (a'' := Nat.max a a').
      destruct (decide (pad = 0%nat)) as [Hpad|Hpad].
      + subst pad off'. simpl.
        rewrite Hpad Nat.add_0_r.
        rewrite Nat.add_assoc.
        apply IH.
        assert (a'' <> 0%nat) by (subst a'' a'; lia).
        done.
      + subst off'. simpl.
        rewrite !Nat.add_assoc.
        apply IH.
        assert (a'' <> 0%nat) by (subst a'' a'; lia).
        done.
  Qed.

  Local Lemma sl_align_eq_local (sl : struct_layout) :
    ly_align sl = max 1 (max_list (ly_align <$> (sl_members sl).*2)).
  Proof.
    rewrite /ly_align{1}/ly_align_log/=.
    generalize (sl_members sl).*2 => lys.
    clear sl. induction lys as [ | ly lys IH]; simpl; first done.
    rewrite Nat_pow_max; last lia. rewrite IH.
      unfold fmap. lia.
  Qed.

  Local Lemma struct_layout_named_field_align_le sl name ly :
    (name, ly) ∈ named_fields sl.(sl_members) →
    ly_align ly ≤ ly_align sl.
  Proof.
    rewrite sl_align_eq_local elem_of_named_fields.
    intros Hin.
    assert (ly_align ly ≤ max_list (ly_align <$> sl.(sl_members).*2))%nat as Hmax.
    { eapply max_list_elem_of_le.
      apply list_elem_of_fmap.
      exists ly. split; first done.
      apply list_elem_of_fmap.
      exists (Some name, ly). done. }
    destruct (Nat.max_spec 1 (max_list (ly_align <$> sl.(sl_members).*2))) as [[? ->] | [? ->]]; lia.
  Qed.

  Lemma C_struct_layout_alg_wf fields sl :
    C_struct_layout_alg fields = Some sl →
    layout_wf sl.
  Proof.
    intros Halg.
    unfold C_struct_layout_alg in Halg.
    destruct (decide (NoDup (field_names (C_struct_layout_alg_raw fields)))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (sum_list (ly_size <$> (C_struct_layout_alg_raw fields).*2) ≤ max_int ISize)) as [Hle|Hle]; last discriminate.
    inversion Halg; subst sl; clear Halg.
    apply layout_wf_mod.
    simpl.
    rewrite sl_align_eq_local.
    simpl.
    rewrite C_struct_layout_alg_raw_go_max_align_preserve.
    rewrite -C_struct_layout_alg_align_go_1_eq_max.
    pose proof (C_struct_layout_alg_raw_go_size_mod fields 0 1 ltac:(lia)) as Hmod.
    rewrite /ly_size /=.
    simpl in Hmod.
    rewrite -Nat2Z.inj_mod.
    rewrite Hmod. done.
  Qed.

  Local Lemma C_struct_layout_alg_raw_go_pad_align off a fields :
    Forall (λ '(named, ly), if named is None then ly_align_log ly = 0%nat else True)
      (C_struct_layout_alg_raw_go off a fields).
  Proof.
    revert off a.
    induction fields as [|[name ly] fields IH]; intros off a; simpl.
    - destruct (decide (padding_needed off a = 0%nat)); constructor; simpl; done.
    - set (a' := ly_align ly).
      destruct (decide (padding_needed off a' = 0%nat)); simpl.
      + constructor; first done. apply IH.
      + constructor.
        * reflexivity.
        * constructor; first done. apply IH.
  Qed.

  Lemma C_struct_layout_alg_pad_align fields sl :
    C_struct_layout_alg fields = Some sl →
    Forall (λ '(named, ly), if named is None then ly_align_log ly = 0%nat else True) (sl_members sl).
  Proof.
    intros Halg.
    unfold C_struct_layout_alg in Halg.
    destruct (decide (NoDup (field_names (C_struct_layout_alg_raw fields)))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (sum_list (ly_size <$> (C_struct_layout_alg_raw fields).*2) ≤ max_int ISize)) as [Hle|Hle]; last discriminate.
    inversion Halg; subst sl; clear Halg.
    simpl.
    unfold C_struct_layout_alg_raw.
    apply C_struct_layout_alg_raw_go_pad_align.
  Qed.

  Local Lemma max_list_ly_align_le (variants : list (var_name * layout)) (n : nat) :
    Forall (λ '(_, ly), ly_align ly ≤ n) variants →
    (1 ≤ n)%nat →
    max_list (ly_align <$> variants.*2) ≤ n.
  Proof.
    intros Hn Hnz.
    induction Hn as [ | [name ly] variants Hly Hvariants IH]; simpl; first lia.
    unfold fmap in *. lia.
  Qed.
  Lemma C_struct_layout_alg_align_le fields sl (n : nat) :
    C_struct_layout_alg fields = Some sl →
    Forall (λ '(_, ly), ly_align ly ≤ n) fields →
    (1 ≤ n)%nat →
    ly_align sl ≤ n.
  Proof.
    intros Halg Hfields Hn.
    unfold C_struct_layout_alg in Halg.
    destruct (decide (NoDup (field_names (C_struct_layout_alg_raw fields)))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (sum_list (ly_size <$> (C_struct_layout_alg_raw fields).*2) ≤ max_int ISize)) as [Hle|Hle]; last discriminate.
    inversion Halg; subst sl; clear Halg.
    rewrite sl_align_eq_local /=.
    unfold C_struct_layout_alg_raw.
    rewrite C_struct_layout_alg_raw_go_max_align_preserve.
    pose proof (max_list_ly_align_le fields n Hfields Hn) as Hmax.
    lia.
  Qed.

  (** Unions *)
  Definition C_union_layout_alg_raw (variants : list (var_name * layout)) : nat :=
    let max_sz := max_list (ly_size <$> variants.*2) in
    let max_al := (2 ^ (max_list (ly_align_log <$> variants.*2)))%nat in
    (max_sz + padding_needed max_sz max_al)%nat.

  Program Definition C_union_layout_alg (variants : list (var_name * layout)) : option union_layout :=
    let sz := C_union_layout_alg_raw variants in
    if decide (NoDup (variants.*1)) then
      if decide (max_list (ly_size <$> variants.*2) ≤ sz) then
        if decide (sz ≤ max_int ISize) then
          Some {| ul_members := variants; ul_size := sz |}
        else
          None
      else
        None
    else None
    .
  Next Obligation.
    intros fields fields' Hnd Hle.
    by rewrite bool_decide_true.
  Qed.
  Next Obligation.
    intros. lia.
  Qed.
  Next Obligation.
    intros. lia.
  Qed.

  Lemma C_union_layout_alg_has_variants variants ul :
    C_union_layout_alg variants = Some ul →
    ul_has_variants ul variants.
  Proof.
    intros Halg.
    unfold C_union_layout_alg in Halg.
    destruct (decide (NoDup (variants.*1))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (max_list (ly_size <$> variants.*2) ≤ C_union_layout_alg_raw variants)) as [Hle|Hle]; last discriminate.
    destruct (decide (C_union_layout_alg_raw variants ≤ max_int ISize)) as [Hsz|Hsz]; last discriminate.
    inversion Halg; subst ul; clear Halg.
    done.
  Qed.

  Lemma C_union_layout_alg_wf variants ul :
    C_union_layout_alg variants = Some ul →
    layout_wf ul.
  Proof.
    intros Halg.
    unfold C_union_layout_alg in Halg.
    destruct (decide (NoDup (variants.*1))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (max_list (ly_size <$> variants.*2) ≤ C_union_layout_alg_raw variants)) as [Hle|Hle]; last discriminate.
    destruct (decide (C_union_layout_alg_raw variants ≤ max_int ISize)) as [Hsz|Hsz]; last discriminate.
    inversion Halg; subst ul; clear Halg.
    rewrite /layout_wf /C_union_layout_alg_raw /ly_size /ly_align /=.
    set (k := max_list (ly_align_log <$> variants.*2)).
    apply Z.mod_divide.
    { intro Hk.
      assert ((2 ^ k)%nat = 0%nat) as Hk' by (apply Nat2Z.inj; exact Hk).
      pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hnz.
      rewrite Hk' in Hnz. done. }
    set (m := max_list ((λ l : layout, let (ly_size, _) := l in ly_size) <$> variants.*2)).
    set (a := (2 ^ k)%nat).
    pose proof (padding_needed_mod_zero m a ltac:(subst a; apply Nat.pow_nonzero; lia)) as Hmod.
    lia.
  Qed.

  Lemma C_union_layout_alg_nodup variants ul :
    C_union_layout_alg variants = Some ul →
    NoDup variants.*1.
  Proof.
    intros Halg.
    unfold C_union_layout_alg in Halg.
    destruct (decide (NoDup variants.*1)) as [Hnd|Hnd]; last discriminate.
    done.
  Qed.

  Lemma C_union_layout_alg_variant_size_le variants ul :
    C_union_layout_alg variants = Some ul →
    Forall (λ '(_, ly), Nat.le (ly_size ly) (ly_size ul)) variants.
  Proof.
    intros Halg.
    unfold C_union_layout_alg in Halg.
    destruct (decide (NoDup variants.*1)) as [Hnd|Hnd]; last discriminate.
    destruct (decide (max_list (ly_size <$> variants.*2) ≤ C_union_layout_alg_raw variants)) as [Hle|Hle]; last discriminate.
    destruct (decide (C_union_layout_alg_raw variants ≤ max_int ISize)) as [Hsz|Hsz]; last discriminate.
    inversion Halg; subst ul; clear Halg.
    rewrite Forall_forall.
    intros [name [sz al]] Hel.
    rewrite /ly_size/ul_layout /=.
    assert (sz ≤ max_list (ly_size <$> variants.*2))%nat as Hmax.
    { eapply max_list_elem_of_le.
      apply list_elem_of_fmap.
      exists {| ly_size := sz; ly_align_log := al |}. split; first done.
      apply list_elem_of_fmap.
      exists (name, {| ly_size := sz; ly_align_log := al |}). done. }
    lia.
  Qed.

  Lemma C_union_layout_alg_variant_align_log_le variants ul :
    C_union_layout_alg variants = Some ul →
    Forall (λ '(_, ly), Nat.le (ly_align_log ly) (ly_align_log ul)) variants.
  Proof.
    intros Halg.
    unfold C_union_layout_alg in Halg.
    destruct (decide (NoDup variants.*1)) as [Hnd|Hnd]; last discriminate.
    destruct (decide (max_list (ly_size <$> variants.*2) ≤ C_union_layout_alg_raw variants)) as [Hle|Hle]; last discriminate.
    destruct (decide (C_union_layout_alg_raw variants ≤ max_int ISize)) as [Hsz|Hsz]; last discriminate.
    inversion Halg; subst ul; clear Halg.
    rewrite Forall_forall.
    intros [name [sz al]] Hel.
    rewrite /ly_align_log/ul_layout /=.
    change (al ≤ max_list (ly_align_log <$> variants.*2))%nat.
    assert (al ≤ max_list (ly_align_log <$> variants.*2))%nat as Hmax.
    { eapply max_list_elem_of_le.
      apply list_elem_of_fmap.
      exists {| ly_size := sz; ly_align_log := al |}. split; first done.
      apply list_elem_of_fmap.
      exists (name, {| ly_size := sz; ly_align_log := al |}). done. }
    exact Hmax.
  Qed.

  Lemma C_union_layout_alg_align_le variants ul (n : nat) :
    C_union_layout_alg variants = Some ul →
    Forall (λ '(_, ly), ly_align ly ≤ n) variants →
    (1 ≤ n)%nat →
    ly_align ul ≤ n.
  Proof.
    intros Halg Hvariants Hn.
    apply C_union_layout_alg_has_variants in Halg as Hmembers.
    rewrite /ul_has_variants in Hmembers. subst variants.
    rewrite /ly_align/ul_layout/ly_align_log /=.
    change ((2 ^ max_list (ly_align_log <$> (ul_members ul).*2))%nat ≤ n).
    pose proof (max_list_pow 2 (ly_align_log <$> (ul_members ul).*2) ltac:(lia)) as Hpow.
    rewrite -list_fmap_compose list_fmap_compose.
    pose proof (max_list_ly_align_le ul.(ul_members) n Hvariants Hn) as Hmax.
    rewrite /ly_align in Hmax.
    simpl in Hmax.
    assert (Hmax' : (max_list ((λ x : nat, (2 ^ x)%nat) <$> (ly_align_log <$> (ul_members ul).*2)) ≤ n)%nat).
    { rewrite -list_fmap_compose.
      change (max_list ((λ ly : layout, (2 ^ ly_align_log ly)%nat) <$> (ul_members ul).*2) ≤ n)%nat.
      lia. }
    lia.
  Qed.

  (** Enums *)
  Local Lemma padding_needed_0 a :
    a <> 0%nat →
    padding_needed 0 a = 0%nat.
  Proof.
    intros Ha.
    rewrite /padding_needed Nat.Div0.mod_0_l Nat.sub_0_r Nat.Div0.mod_same; lia.
  Qed.

  Local Lemma C_struct_layout_alg_raw_enum_data_after_tag tag_it ul :
    ly_size (it_layout tag_it) ≤
    default 0%nat (offset_of (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)]) "data").
  Proof.
    rewrite /C_struct_layout_alg_raw /C_struct_layout_alg_raw_go.
    destruct (decide (padding_needed 0 (ly_align (it_layout tag_it)) = 0%nat)) as [Htag|Htag]; last first.
    { rewrite padding_needed_0 in Htag; [done | apply ly_align_nonzero]. }
    rewrite Htag.
    repeat match goal with | |- context[(0 + 0 + ?n)%nat] => replace (0 + 0 + n)%nat with n by lia end.
    simpl.
    destruct (decide (padding_needed (ly_size (it_layout tag_it)) (ly_align ul) = 0%nat)) as [Hpad|Hpad]; simpl.
    - rewrite Hpad /= /offset_of_idx /=. lia.
    - rewrite /offset_of_idx /pad_layout /=. lia.
  Qed.

  Local Lemma C_struct_layout_alg_raw_enum_data_aligned tag_it ul :
    (default 0%nat (offset_of (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)]) "data") `mod` ly_align ul)%nat = 0%nat.
  Proof.
    rewrite /C_struct_layout_alg_raw /C_struct_layout_alg_raw_go.
    destruct (decide (padding_needed 0 (ly_align (it_layout tag_it)) = 0%nat)) as [Htag|Htag]; last first.
    { rewrite padding_needed_0 in Htag; [done | apply ly_align_nonzero]. }
    rewrite Htag.
    repeat match goal with | |- context[(0 + 0 + ?n)%nat] => replace (0 + 0 + n)%nat with n by lia end.
    simpl.
    destruct (decide (padding_needed (ly_size (it_layout tag_it)) (ly_align ul) = 0%nat)) as [Hpad|Hpad]; simpl.
    - rewrite Hpad /= /offset_of_idx /=.
      replace (ly_size (it_layout tag_it) + 0)%nat with (ly_size (it_layout tag_it)) by lia.
      assert (Hmod : ((ly_size (it_layout tag_it) `mod` ly_align ul)%nat = 0%nat)).
      { apply padding_needed_zero_inv_nat; [apply ly_align_nonzero | done]. }
      exact Hmod.
    - rewrite /offset_of_idx /pad_layout /=.
      repeat match goal with
      | |- context[ly_size {| ly_size := ?sz; ly_align_log := ?al |}] =>
          replace (ly_size {| ly_size := sz; ly_align_log := al |}) with sz by done
      end.
      replace (ly_size (it_layout tag_it) + (padding_needed (ly_size (it_layout tag_it)) (ly_align ul) + 0))%nat with
        (ly_size (it_layout tag_it) + padding_needed (ly_size (it_layout tag_it)) (ly_align ul))%nat by lia.
      apply padding_needed_mod_zero. apply ly_align_nonzero.
  Qed.

  Local Lemma C_struct_layout_alg_raw_enum_data_in_bounds tag_it ul :
    (default 0%nat (offset_of (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)]) "data") + ly_size ul ≤
     sum_list (ly_size <$> (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)]).*2))%nat.
  Proof.
    rewrite /C_struct_layout_alg_raw /C_struct_layout_alg_raw_go.
    destruct (decide (padding_needed 0 (ly_align (it_layout tag_it)) = 0%nat)) as [Htag|Htag]; last first.
    { rewrite padding_needed_0 in Htag; [done | apply ly_align_nonzero]. }
    rewrite Htag.
    repeat match goal with | |- context[(0 + 0 + ?n)%nat] => replace (0 + 0 + n)%nat with n by lia end.
    simpl.
    destruct (decide (padding_needed (ly_size (it_layout tag_it)) (ly_align ul) = 0%nat)) as [Hpad|Hpad]; simpl.
    - rewrite Hpad /= /offset_of_idx /=.
      destruct (decide (padding_needed (ly_size (it_layout tag_it) + 0 + ly_size ul)
        ((1 `max` ly_align (it_layout tag_it)) `max` ly_align ul) = 0%nat)); simpl; rewrite /pad_layout /=; lia.
    - rewrite /offset_of_idx /pad_layout /=.
      destruct (decide (padding_needed (ly_size (it_layout tag_it) + padding_needed (ly_size (it_layout tag_it)) (ly_align ul) + ly_size ul)
        ((1 `max` ly_align (it_layout tag_it)) `max` ly_align ul) = 0%nat)); simpl; rewrite /pad_layout /=; lia.
  Qed.

  Local Lemma C_struct_layout_alg_enum_data_after_tag tag_it ul sl :
    C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] = Some sl →
    ly_size (it_layout tag_it) ≤ default 0%nat (offset_of sl.(sl_members) "data").
  Proof.
    intros Halg.
    unfold C_struct_layout_alg in Halg.
    destruct (decide (NoDup (field_names (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)])))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (sum_list (ly_size <$> (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)]).*2) ≤ max_int ISize)) as [Hle|Hle]; last discriminate.
    inversion Halg; subst sl; clear Halg. simpl.
    apply C_struct_layout_alg_raw_enum_data_after_tag.
  Qed.

  Local Lemma C_struct_layout_alg_enum_data_aligned tag_it ul sl :
    C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] = Some sl →
    (default 0%nat (offset_of sl.(sl_members) "data") `mod` ly_align ul)%nat = 0%nat.
  Proof.
    intros Halg.
    unfold C_struct_layout_alg in Halg.
    destruct (decide (NoDup (field_names (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)])))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (sum_list (ly_size <$> (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)]).*2) ≤ max_int ISize)) as [Hle|Hle]; last discriminate.
    inversion Halg; subst sl; clear Halg. simpl.
    apply C_struct_layout_alg_raw_enum_data_aligned.
  Qed.

  Local Lemma C_struct_layout_alg_enum_data_in_bounds tag_it ul sl :
    C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] = Some sl →
    (default 0%nat (offset_of sl.(sl_members) "data") + ly_size ul ≤ ly_size sl)%nat.
  Proof.
    intros Halg.
    unfold C_struct_layout_alg in Halg.
    destruct (decide (NoDup (field_names (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)])))) as [Hnd|Hnd]; last discriminate.
    destruct (decide (sum_list (ly_size <$> (C_struct_layout_alg_raw [("discriminant", it_layout tag_it); ("data", ul_layout ul)]).*2) ≤ max_int ISize)) as [Hle|Hle]; last discriminate.
    inversion Halg; subst sl; clear Halg. simpl.
    apply C_struct_layout_alg_raw_enum_data_in_bounds.
  Qed.

  Local Lemma C_struct_layout_alg_enum_tag_align_le tag_it ul sl :
    C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] = Some sl →
    ly_align (it_layout tag_it) ≤ ly_align sl.
  Proof.
    intros Halg.
    pose proof (C_struct_layout_alg_has_fields _ _ Halg) as Hfields.
    eapply struct_layout_named_field_align_le.
    rewrite Hfields. simpl. by left.
  Qed.

  Local Lemma C_struct_layout_alg_enum_data_align_le tag_it ul sl :
    C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] = Some sl →
    ly_align ul ≤ ly_align sl.
  Proof.
    intros Halg.
    pose proof (C_struct_layout_alg_has_fields _ _ Halg) as Hfields.
    eapply struct_layout_named_field_align_le.
    rewrite Hfields. simpl. by right; left.
  Qed.

  Local Lemma pow_align_log_dvd a b :
    (a ≤ b)%nat →
    (2 ^ a | 2 ^ b)%nat.
  Proof.
    intros Hle.
    exists (2 ^ (b - a))%nat.
    rewrite -Nat.pow_add_r.
    f_equal. lia.
  Qed.

  Local Lemma mod_pow_align_log a b (n : nat) :
    (a ≤ b)%nat →
    (n mod (2 ^ b))%nat = 0%nat →
    (n mod (2 ^ a))%nat = 0%nat.
  Proof.
    intros Hle Hmod.
    apply Nat.Lcm0.mod_divide.
    apply Nat.Lcm0.mod_divide in Hmod.
    destruct Hmod as [k ->].
    destruct (pow_align_log_dvd a b Hle) as [k' ->].
    exists (k' * k)%nat. lia.
  Qed.

  Program Definition C_enum_layout_from_alg_results
      (tag_it : int_type) (variants : list (var_name * layout))
      (ul : union_layout) (sl : struct_layout)
      (Hul : C_union_layout_alg variants = Some ul)
      (Hsl : C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] = Some sl)
      (Hwf : Forall (λ '(_, ly), layout_wf ly) variants) : enum_layout :=
    let data_offset := default 0%nat (offset_of sl.(sl_members) "data") in
    {| el_size := ly_size sl;
       el_align_log := ly_align_log sl;
       el_tag_it := tag_it;
       el_data_offset := data_offset;
       el_variants := variants |}.
  Next Obligation.
    intros. rewrite bool_decide_true; first done.
    by eapply C_union_layout_alg_nodup.
  Qed.
  Next Obligation.
    intros. apply sl_size.
  Qed.
  Next Obligation.
    intros. eapply C_struct_layout_alg_wf. done.
  Qed.
  Next Obligation.
    intros. subst data_offset. by eapply C_struct_layout_alg_enum_tag_align_le.
  Qed.
  Next Obligation.
    intros tag_it variants ul sl Hul Hsl Hwf data_offset.
    apply Forall_forall.
    intros [name ly] Hel.
    trans (ly_align ul).
    - rewrite /ly_align.
      pose proof (proj1 (Forall_forall _ _) (C_union_layout_alg_variant_align_log_le _ _ Hul) (name, ly) Hel) as Hle.
      assert (Nat.le (2 ^ ly_align_log (name, ly).2) (2 ^ ly_align_log ul)) as Hpow.
      { simpl in Hle. rewrite /ly_align_log/ul_layout /=.
        change (Nat.le (2 ^ ly_align_log ly) (2 ^ max_list (ly_align_log <$> (ul_members ul).*2))).
        apply Nat.pow_le_mono_r; lia. }
      lia.
    - subst data_offset. by eapply C_struct_layout_alg_enum_data_align_le.
  Qed.
  Next Obligation.
    intros.
    subst data_offset. by eapply C_struct_layout_alg_enum_data_after_tag.
  Qed.
  Next Obligation.
    intros tag_it variants ul sl Hul Hsl Hwf data_offset.
    apply Forall_forall.
    intros [name [sz al]] Hel.
    split; first exact (proj1 (Forall_forall _ _) Hwf (name, {| ly_size := sz; ly_align_log := al |}) Hel).
    subst data_offset.
    pose proof (C_struct_layout_alg_enum_data_aligned _ _ _ Hsl) as Hul_align.
    rewrite /ly_align in Hul_align |- *.
    replace (ly_align_log (name, {| ly_size := sz; ly_align_log := al |}).2) with al by done.
    assert (Hdata : ((default 0 (offset_of (sl_members sl) "data") mod (2 ^ al))%nat = 0%nat)).
    { eapply mod_pow_align_log; last exact Hul_align.
      pose proof (proj1 (Forall_forall _ _) (C_union_layout_alg_variant_align_log_le _ _ Hul) (name, {| ly_size := sz; ly_align_log := al |}) Hel) as Hle.
      exact Hle. }
    rewrite -Nat2Z.inj_mod.
    rewrite Hdata. done.
  Qed.
  Next Obligation.
    intros tag_it variants ul sl Hul Hsl Hwf data_offset.
    pose proof (C_union_layout_alg_variant_size_le _ _ Hul) as Hsize.
    apply Forall_forall.
    intros [name [sz al]] Hel.
    pose proof (proj1 (Forall_forall _ _) Hsize (name, {| ly_size := sz; ly_align_log := al |}) Hel) as Hsize'.
    subst data_offset.
    pose proof (C_struct_layout_alg_enum_data_in_bounds _ _ _ Hsl) as Hbounds.
    replace (ly_size (name, {| ly_size := sz; ly_align_log := al |}).2) with sz by done.
    change (Nat.le sz (ly_size ul)) in Hsize'.
    lia.
  Qed.

  Definition C_enum_layout_alg (tag_it : int_type) (variants : list (var_name * layout)) : option enum_layout :=
    match C_union_layout_alg variants as x return C_union_layout_alg variants = x → option enum_layout with
    | Some ul =>
      fun Hul =>
      match C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] as x
          return C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] = x → option enum_layout with
      | Some sl =>
        fun Hsl =>
          match decide (Forall (λ '(_, ly), layout_wf ly) variants) with
          | left Hwf => Some (C_enum_layout_from_alg_results tag_it variants ul sl Hul Hsl Hwf)
          | right _ => None
          end
      | None => fun _ => None
      end eq_refl
    | None => fun _ => None
    end eq_refl.

  Lemma C_enum_layout_from_alg_results_has_variants tag_it variants ul sl Hul Hsl Hwf :
    el_has_variants (C_enum_layout_from_alg_results tag_it variants ul sl Hul Hsl Hwf) tag_it variants.
  Proof.
    split; done.
  Qed.

  Lemma C_enum_layout_alg_Some_inv tag_it variants el :
    C_enum_layout_alg tag_it variants = Some el →
    ∃ ul sl Hul Hsl Hwf,
      el = C_enum_layout_from_alg_results tag_it variants ul sl Hul Hsl Hwf.
  Proof.
    unfold C_enum_layout_alg.
    refine ((match C_union_layout_alg variants as ou return ∀ Hul : C_union_layout_alg variants = ou,
      ((match ou as x return C_union_layout_alg variants = x → option enum_layout with
        | Some ul =>
          fun Hul =>
          match C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] as x
              return C_struct_layout_alg _ = x → option enum_layout with
          | Some sl =>
            fun Hsl =>
              match decide (Forall (λ '(_, ly), layout_wf ly) variants) with
              | left Hwf => Some (C_enum_layout_from_alg_results tag_it variants ul sl Hul Hsl Hwf)
              | right _ => None
              end
          | None => fun _ => None
          end eq_refl
        | None => fun _ => None
        end Hul) = Some el →
        ∃ ul sl Hul Hsl Hwf, el = C_enum_layout_from_alg_results tag_it variants ul sl Hul Hsl Hwf) with
      | Some ul => fun Hul => _
      | None => fun _ => _
      end) eq_refl).
    - refine ((match C_struct_layout_alg [("discriminant", it_layout tag_it); ("data", ul_layout ul)] as os
          return ∀ Hsl : C_struct_layout_alg _ = os,
        ((match os as x return C_struct_layout_alg _ = x → option enum_layout with
          | Some sl =>
            fun Hsl =>
              match decide (Forall (λ '(_, ly), layout_wf ly) variants) with
              | left Hwf => Some (C_enum_layout_from_alg_results tag_it variants ul sl Hul Hsl Hwf)
              | right _ => None
              end
          | None => fun _ => None
          end Hsl) = Some el →
          ∃ ul sl Hul Hsl Hwf, el = C_enum_layout_from_alg_results tag_it variants ul sl Hul Hsl Hwf) with
        | Some sl => fun Hsl => _
        | None => fun _ => _
        end) eq_refl).
      + destruct (decide (Forall (λ '(_, ly), layout_wf ly) variants)) as [Hwf|]; simpl; last done.
        intros [= <-]. eexists _, _, _, _, _. done.
      + done.
    - done.
  Qed.

  Lemma C_enum_layout_alg_has_variants tag_it variants el :
    C_enum_layout_alg tag_it variants = Some el →
    el_has_variants el tag_it variants.
  Proof.
    intros (ul & sl & Hul & Hsl & Hwf & ->)%C_enum_layout_alg_Some_inv.
    apply C_enum_layout_from_alg_results_has_variants.
  Qed.

  Lemma C_enum_layout_alg_align_in_bounds tag_it variants el :
    Forall (λ '(_, ly), ly_align ly ≤ max_alloc_end_zero) variants →
    C_enum_layout_alg tag_it variants = Some el →
    ly_align el ≤ max_alloc_end_zero.
  Proof.
    intros Hvariants.
    intros (ul & sl & Hul & Hsl & Hwf & ->)%C_enum_layout_alg_Some_inv.
    simpl.
    assert (Hvariants_nat : Forall (λ '(_, ly), ly_align ly ≤ Z.to_nat max_alloc_end_zero) variants).
    { eapply Forall_impl; first exact Hvariants.
      intros [name ly] Hly.
      lia. }
    assert (Hul_align : ly_align ul ≤ Z.to_nat max_alloc_end_zero).
    { eapply (C_union_layout_alg_align_le variants ul (Z.to_nat max_alloc_end_zero)); [done | done |].
      unfold_common_radium_defs. simpl. lia. }
    assert (Htag : ly_align (it_layout tag_it) ≤ Z.to_nat max_alloc_end_zero).
    { etrans; first apply IntType_align_le.
      unfold_common_radium_defs; simpl. lia. }
    assert (Hsl_align : ly_align sl ≤ Z.to_nat max_alloc_end_zero).
    { eapply (C_struct_layout_alg_align_le _ sl (Z.to_nat max_alloc_end_zero)); first done.
      - repeat constructor; done.
      - unfold_common_radium_defs. simpl. lia. }
    move: Hsl_align.
    rewrite /ly_align/=.
    lia.
  Qed.
End C_alg.

(** A layout algorithm takes a syn_type and produces a layout for it, if possible.
  The string arguments models that the algorithm may produce different layouts even for the same syn_type, in some case (e.g. structs).
 *)
Class LayoutAlg : Type := {
  (* Note that we assume that fields have already been layouted: this encodes a kind of coherence requirement on the fields, i.e. that the algorithm really first layouts the fields according to their layout rules. *)
  struct_layout_alg : string → list (string * layout) → struct_repr → option struct_layout;
  union_layout_alg : string → list (string * layout) → union_repr → option union_layout;
  enum_layout_alg : string → int_type → list (string * layout) → enum_repr → option enum_layout;
  (* the named (= non-padding) fields should be exactly the input fields *)
  struct_layout_alg_has_fields sn fields repr sl :
    struct_layout_alg sn fields repr = Some sl →
    sl_has_members sl fields;
  (* the total size should be divisible by the alignment *)
  struct_layout_alg_wf sn fields repr sl :
    struct_layout_alg sn fields repr = Some sl →
    layout_wf sl;
  (* the padding fields should pose no alignment requirements *)
  struct_layout_alg_pad_align sn fields repr sl :
    struct_layout_alg sn fields repr = Some sl →
    Forall (λ '(named, ly), if named is None then ly_align_log ly = 0%nat else True) (sl_members sl);
  (* For repr(C), the algorithm computes the same layout as the C layout algorithm. *)
  strruct_layout_alg_repr_C sn fields :
    struct_layout_alg sn fields StructReprC = C_struct_layout_alg fields;
  (* TODO: add requirements on repr(transparent) *)

  (* the variants should be exactly as given *)
  union_layout_alg_has_variants un variants repr ul :
    union_layout_alg un variants repr = Some ul →
    ul_has_variants ul variants;
  (* the total size should be divisible by the alignment *)
  union_layout_alg_wf un variants repr ul :
    union_layout_alg un variants repr = Some ul →
    layout_wf ul;
  union_layout_alg_repr_C un variants :
    union_layout_alg un variants UnionReprC = C_union_layout_alg variants;

  (* the variants and tag integer type should be exactly as given *)
  enum_layout_alg_has_variants en tag_it variants repr el :
    enum_layout_alg en tag_it variants repr = Some el →
    el_has_variants el tag_it variants;
  enum_layout_alg_align_in_bounds en tag_it variants repr el :
    Forall (λ '(_, ly), ly_align ly ≤ max_alloc_end_zero) variants →
    enum_layout_alg en tag_it variants repr = Some el →
    ly_align el ≤ max_alloc_end_zero;
  enum_layout_alg_repr_C en it variants :
    enum_layout_alg en it variants EnumReprC = C_enum_layout_alg it variants;
}.

Program Definition LayoutAlg_C : LayoutAlg := {|
  struct_layout_alg _ fields _ := C_struct_layout_alg fields;
  union_layout_alg _ variants _ := C_union_layout_alg variants;
  enum_layout_alg _ tag_it variants _ := C_enum_layout_alg tag_it variants; |}.
Next Obligation.
  intros.
  unfold sl_has_members. symmetry.
  by apply C_struct_layout_alg_has_fields.
Qed.
Next Obligation.
  simpl. intros. by eapply C_struct_layout_alg_wf.
Qed.
Next Obligation.
  simpl. intros. by eapply C_struct_layout_alg_pad_align.
Qed.
Next Obligation.
  simpl. done.
Qed.
Next Obligation.
  simpl. intros. by eapply C_union_layout_alg_has_variants.
Qed.
Next Obligation.
  simpl. intros. by eapply C_union_layout_alg_wf.
Qed.
Next Obligation.
  simpl. done.
Qed.
Next Obligation.
  intros. by apply C_enum_layout_alg_has_variants.
Qed.
Next Obligation.
  simpl.
  intros. by eapply C_enum_layout_alg_align_in_bounds.
Qed.
Next Obligation.
  done.
Qed.
Global Instance LayoutAlg_inhabited : Inhabited LayoutAlg :=
  {| inhabitant := LayoutAlg_C |}.

(** We fix a specific layout for the unit type, since Rust gives layout guarantees for it. *)
Program Definition unit_sl : struct_layout := {|
  sl_members := [];
|}.
Solve Obligations with done.
(** A union layout that would be a valid layout for the never type (although Rust does not specify that it is the only possible one). *)
Program Definition neverlike_ul : union_layout := {|
  ul_members := [];
  ul_size := 0;
|}.
Solve Obligations with done.

Definition empty_el : enum_layout.
Proof.
  refine {| el_size := 1%nat;
            el_align_log := 0%nat;
            el_tag_it := U8;
            el_data_offset := 1%nat;
            el_variants := [] |}; simpl; try done; try lia.
  rewrite /layout_wf /ly_size /ly_align /=. exists 1. lia.
Defined.

(** The alignment has to fit in [usize].
   More restrictively, in order to make [NonNull::dangling] work, the alignment also needs to be a valid address. *)
Definition ly_align_in_bounds (ly : layout) :=
  ly_align ly ≤ max_alloc_end_zero.
Lemma ly_align_in_bounds_1 ly :
  ly_align_log ly = 0%nat → ly_align_in_bounds ly.
Proof.
  rewrite /ly_align_in_bounds/ly_align => ->.
  unfold_common_radium_defs. simpl. nia.
Qed.

Lemma ly_align_log_in_U8 ly :
  ly_align_in_bounds ly → (Z.of_nat (ly_align_log ly)) ∈ U8.
Proof.
  rewrite /ly_align_in_bounds/min_alloc_start/max_alloc_end/=/ly_align/bytes_per_addr/bytes_per_addr_log/=.
  rewrite /bits_per_byte/=.
  intros Ha.
  split. { unsafe_unfold_common_radium_defs. simpl in *. lia. }
  assert ((2 ^ ly_align_log ly) ≤ 2 ^ (8%nat * 8))%nat as Hle.
  { apply Nat2Z.inj_le. etrans; first apply Ha.
    rewrite Nat2Z.inj_pow.
    unsafe_unfold_common_radium_defs; simpl.
    nia.
  }
  apply PeanoNat.Nat.pow_le_mono_r_iff in Hle; last lia.
  unsafe_unfold_common_radium_defs. simpl in *. lia.
Qed.
Lemma ly_align_log_in_usize ly :
  ly_align_in_bounds ly → (Z.of_nat (ly_align_log ly)) ∈ USize.
Proof.
  intros [_ Ha]%ly_align_log_in_U8.
  split. { unsafe_unfold_common_radium_defs. simpl in *. lia. }
  unsafe_unfold_common_radium_defs. simpl in *. lia.
Qed.
Lemma ly_align_in_usize ly :
  ly_align_in_bounds ly → (Z.of_nat (ly_align ly)) ∈ USize.
Proof.
  unfold ly_align_in_bounds.
  intros Ha.
  split; unsafe_unfold_common_radium_defs; simpl in *; lia.
Qed.

Lemma ly_align_in_bounds_mono ly1 ly2 :
  (ly_align_log ly2 ≤ ly_align_log ly1)%nat →
  ly_align_in_bounds ly1 →
  ly_align_in_bounds ly2.
Proof.
  rewrite /ly_align_in_bounds.
  intros Hle. rewrite /ly_align/min_alloc_start. intros Ha.
  etrans; last apply Ha.
  apply inj_le. apply Nat.pow_le_mono_r; last lia. done.
Qed.

(** Use a layout algorithm recursively on a layout spec. *)
(* NOTE on size limits from https://doc.rust-lang.org/stable/reference/types/numeric.html#machine-dependent-integer-types:
    "The isize type is a signed integer type with the same number of bits as the platform's pointer type. The theoretical upper bound on object and array size is the maximum isize value. This ensures that isize can be used to calculate differences between pointers into an object or array and can address every byte within an object along with one byte past the end." *)
Fixpoint use_layout_alg_def `{!LayoutAlg} (synty : syn_type) : option layout :=
  match synty with
  | IntSynType it =>
      (* make sure that we respect limits on object size *)
      if decide (ly_size (it_layout it) ≤ MaxInt ISize) then
        Some (it_layout it)
      else None
  | BoolSynType => Some (it_layout U8)
  | CharSynType => Some (char_layout)
  | PtrSynType => Some void*
  | FnPtrSynType => Some void*
  | StructSynType sn fields repr =>
      field_lys ← list_map_option (λ '(field_name, field_spec),
        ly ← use_layout_alg_def field_spec;
        Some (field_name, ly)) fields;
      sl ← struct_layout_alg sn field_lys repr;
      Some (layout_of sl)
  | UnitSynType => Some (layout_of unit_sl)
  | NeverSynType => Some (zst_layout)
  | ArraySynType st len =>
      ly ← use_layout_alg_def st;
      (* check that this is within the size limits *)
      if decide (ly_size (mk_array_layout ly len) ≤ MaxInt ISize) then
        Some (mk_array_layout ly len)
      else None
  | UnsafeCell st => use_layout_alg_def st
  | UnionSynType un variants repr =>
      variant_lys ← list_map_option (λ '(variant_name, variant_spec),
        ly ← use_layout_alg_def variant_spec;
        Some (variant_name, ly)) variants;
      ul ← union_layout_alg un variant_lys repr;
      Some (ul_layout ul)
  | EnumSynType els =>
      variant_lys ← list_map_option (λ '(variant_name, variant_spec),
        ly ← use_layout_alg_def variant_spec;
        Some (variant_name, ly)) els.(raw_els_variants);
      el ← enum_layout_alg els.(raw_els_name) els.(raw_els_tag_it) variant_lys els.(raw_els_repr);
      if decide (enum_tag_int_wf els.(raw_els_tag_it) els.(raw_els_variants) els.(raw_els_tag_int)) then Some (layout_of_enum el) else None
  | UntypedSynType st =>
      use_layout_alg_def st
  | LiteralSynType ly =>
      if decide (layout_wf ly ∧ ly_size ly ≤ MaxInt ISize ∧ ly_align_in_bounds ly) then Some ly else None
  | RefSynType => Some void*
  end.
Definition use_layout_alg_aux `{!LayoutAlg} : seal (use_layout_alg_def). Proof. by eexists. Qed.
Definition use_layout_alg `{!LayoutAlg} := use_layout_alg_aux.(unseal).
Definition use_layout_alg_unfold `{!LayoutAlg} : use_layout_alg = use_layout_alg_def := use_layout_alg_aux.(seal_eq).

Ltac unfold_layout_alg :=
  rewrite -> use_layout_alg_unfold in *.

(** Under our current layout environment, [ly] is a valid layout for [synty]. *)
Definition syn_type_has_layout `{!LayoutAlg} (synty : syn_type) (ly : layout) : Prop :=
  use_layout_alg synty = Some ly.
Lemma syn_type_has_layout_inj `{!LayoutAlg} synty ly1 ly2 :
  syn_type_has_layout synty ly1 → syn_type_has_layout synty ly2 → ly1 = ly2.
Proof. rewrite /syn_type_has_layout => ??. simplify_option_eq => //. Qed.
Lemma Forall2_syn_type_has_layout_inj `{!LayoutAlg} synty lys1 lys2 :
  Forall2 syn_type_has_layout synty lys1 → Forall2 syn_type_has_layout synty lys2 → lys1 = lys2.
Proof.
  induction 1 as [ | st ly ? ? ? Ha IH] in lys2 |-*; simpl.
  { intros Ha. apply Forall2_nil_inv_l in Ha. done. }
  intros Hb. apply Forall2_cons_inv_l in Hb as (ly' & lys' & ? & Hb & ->).
  opose proof (syn_type_has_layout_inj st ly ly' _ _) as <-; [done.. | ].
  f_equiv. by apply IH.
Qed.

(** Use a layout algorithm on a struct_layout_spec *)
Definition use_struct_layout_alg `{!LayoutAlg} (sl_spec : struct_layout_spec) : option struct_layout :=
  field_lys ← list_map_option (λ '(field_name, field_spec),
    ly ← use_layout_alg field_spec;
    Some (field_name, ly)) sl_spec.(sls_fields);
  struct_layout_alg sl_spec.(sls_name) field_lys (sl_spec.(sls_repr)).
Arguments use_struct_layout_alg : simpl never.

Lemma use_struct_layout_alg_Some_inv `{!LayoutAlg} (sls : struct_layout_spec) sl :
  use_struct_layout_alg sls = Some sl →
  use_layout_alg sls = Some (layout_of sl).
Proof.
  intros Hly.
  unfold use_struct_layout_alg in Hly. simplify_option_eq.
  unfold_layout_alg. rewrite /use_layout_alg_def.
  simpl. fold use_layout_alg_def.
  simplify_option_eq; eauto.
Qed.
Lemma use_layout_alg_struct_Some_inv `{!LayoutAlg} (sls : struct_layout_spec) ly :
  use_layout_alg sls = Some ly →
  ∃ sl, use_struct_layout_alg sls = Some sl ∧ ly = layout_of sl.
Proof.
  intros Hly.
  unfold_layout_alg.
  simpl in Hly. simplify_option_eq.
  eexists _. unfold use_struct_layout_alg.
  unfold_layout_alg.
  simplify_option_eq; eauto.
Qed.

Lemma use_struct_layout_alg_Some `{!LayoutAlg} sls sl fields' :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ use_layout_alg fst = Some fly) sls.(sls_fields) fields' →
  struct_layout_alg sls.(sls_name) fields' sls.(sls_repr) = Some sl →
  use_struct_layout_alg sls = Some sl.
Proof.
  intros Ha Hb. rewrite /use_struct_layout_alg.
  apply bind_Some. exists fields'.
  split; last done.
  clear Hb. move: Ha. generalize (sls_fields sls) as fields. clear sls.
  induction fields as [ | [name st] fields IH] in fields' |-*; simpl.
  - by intros []%Forall2_nil_inv_l.
  - intros ([name' ly] & fields'' & [<- Hst] & Ha & ->)%Forall2_cons_inv_l.
    erewrite IH; last done. simpl. rewrite Hst//.
Qed.

Local Arguments use_layout_alg : simpl nomatch.
Lemma use_struct_layout_alg_inv `{!LayoutAlg} sls sl :
  use_struct_layout_alg sls = Some sl →
  ∃ (field_lys : list (string * layout)),
    struct_layout_alg sls.(sls_name) field_lys sls.(sls_repr) = Some sl ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) sls.(sls_fields) field_lys.
Proof.
  intros (field_lys & Hfields%list_map_option_alt & Halg)%bind_Some.
  exists field_lys. split_and!; [done.. | ].
  eapply Forall2_impl; first done.
  intros [] []. intros (fly & ? & [= <- <-])%bind_Some. done.
Qed.
Lemma syn_type_has_layout_struct_inv `{!LayoutAlg} name fields repr ly :
  syn_type_has_layout (StructSynType name fields repr) ly →
  ∃ (field_lys : list (string * layout)) (sl : struct_layout),
    ly = layout_of sl ∧
    struct_layout_alg name field_lys repr = Some sl ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) fields field_lys.
Proof.
  set (sls := mk_sls name fields repr).
  intros Ha. apply (use_layout_alg_struct_Some_inv sls) in Ha as (sl & Ha & ?).
  apply use_struct_layout_alg_inv in Ha as (? & ? & ?).
  naive_solver.
Qed.
Lemma syn_type_has_layout_struct `{!LayoutAlg} name fields fields' repr ly :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) fields fields' →
  struct_layout_alg name fields' repr = Some ly →
  syn_type_has_layout (StructSynType name fields repr) ly.
Proof.
  intros Ha Hb. rewrite /syn_type_has_layout /=;
  unfold_layout_alg; simpl;
  fold use_layout_alg_def.
  rewrite bind_Some. exists fields'.
  split.
  { rewrite list_map_option_alt.
    eapply Forall2_impl; first apply Ha.
    rewrite /syn_type_has_layout; unfold_layout_alg.
    intros [] [] [-> ->] => //. }
  rewrite Hb. done.
Qed.

Lemma use_struct_layout_alg_fields_layoutable `{!LayoutAlg} sls sl :
  use_struct_layout_alg sls = Some sl →
  Forall (λ fst, ∃ ly, syn_type_has_layout fst ly) (sls.(sls_fields).*2).
Proof.
  intros (fields & _ & Hf)%use_struct_layout_alg_inv.
  rewrite Forall_fmap.
  eapply Forall2_Forall_impl; first last.
  { apply Forall2_flip. done. }
  intros [] []; simpl.
  intros [-> ?]. eauto.
Qed.

(** Union *)
Definition use_union_layout_alg `{!LayoutAlg} (uls : union_layout_spec) : option union_layout :=
  variant_lys ← list_map_option (λ '(variant_name, variant_spec),
    ly ← use_layout_alg variant_spec;
    Some (variant_name, ly)) uls.(uls_variants);
  union_layout_alg uls.(uls_name) variant_lys uls.(uls_repr).
Arguments use_union_layout_alg : simpl never.

Lemma use_union_layout_alg_Some_inv `{!LayoutAlg} (uls : union_layout_spec) ul :
  use_union_layout_alg uls = Some ul →
  use_layout_alg uls = Some (ul_layout ul).
Proof.
  intros Hly.
  unfold use_union_layout_alg in Hly. simplify_option_eq.
  unfold_layout_alg. simpl. fold use_layout_alg.
  simplify_option_eq; eauto.
Qed.
Lemma use_layout_alg_union_Some_inv `{!LayoutAlg} (uls : union_layout_spec) ly :
  use_layout_alg uls = Some ly →
  ∃ ul, use_union_layout_alg uls = Some ul ∧ ly = ul_layout ul.
Proof.
  intros Hly.
  unfold_layout_alg. simpl in Hly. simplify_option_eq.
  eexists _. unfold use_union_layout_alg.
  unfold_layout_alg. simplify_option_eq; eauto.
Qed.
Lemma use_union_layout_alg_Some `{!LayoutAlg} uls ul variants' :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ use_layout_alg fst = Some fly) uls.(uls_variants) variants' →
  union_layout_alg uls.(uls_name) variants' uls.(uls_repr) = Some ul →
  use_union_layout_alg uls = Some ul.
Proof.
  intros Ha Hb. rewrite /use_union_layout_alg.
  apply bind_Some. exists variants'.
  split; last done.
  clear Hb. move: Ha. generalize (uls_variants uls) as variants. clear uls.
  induction variants as [ | [name st] variants IH] in variants' |-*; simpl.
  - by intros []%Forall2_nil_inv_l.
  - intros ([name' ly] & variants'' & [<- Hst] & Ha & ->)%Forall2_cons_inv_l.
    erewrite IH; last done. simpl. rewrite Hst//.
Qed.
Lemma syn_type_has_layout_union `{!LayoutAlg} name variants variants' repr ly :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) variants variants' →
  union_layout_alg name variants' repr = Some ly →
  syn_type_has_layout (UnionSynType name variants repr) ly.
Proof.
  intros Ha Hb. rewrite /syn_type_has_layout /=;
  unfold_layout_alg.
  rewrite bind_Some. exists variants'.
  split.
  { fold use_layout_alg_def.
    rewrite list_map_option_alt.
    eapply Forall2_impl; first apply Ha.
    rewrite /syn_type_has_layout.
    unfold_layout_alg.
    intros [] [] [-> ->] => //. }
  rewrite Hb. done.
Qed.
Lemma use_union_layout_alg_inv `{!LayoutAlg} uls ul :
  use_union_layout_alg uls = Some ul →
  ∃ (variant_lys : list (string * layout)),
    union_layout_alg uls.(uls_name) variant_lys uls.(uls_repr) = Some ul ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) uls.(uls_variants) variant_lys.
Proof.
  intros (variant_lys & Hvars%list_map_option_alt & Halg)%bind_Some.
  exists variant_lys. split_and!; [done.. | ].
  eapply Forall2_impl; first done.
  intros [] []. intros (fly & ? & [= <- <-])%bind_Some. done.
Qed.
Lemma syn_type_has_layout_union_inv `{!LayoutAlg} name variants repr ly :
  syn_type_has_layout (UnionSynType name variants repr) ly →
  ∃ (variant_lys : list (string * layout)) (ul : union_layout),
  ly = ul_layout ul ∧
    union_layout_alg name variant_lys repr = Some ul ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) variants variant_lys.
Proof.
  set (uls := mk_uls name variants repr).
  intros Ha. apply (use_layout_alg_union_Some_inv uls) in Ha as (ul & Ha & ?).
  apply use_union_layout_alg_inv in Ha as (? & ? & ?).
  naive_solver.
Qed.

(** Enum *)
Definition use_enum_layout_alg `{!LayoutAlg} (els : enum_layout_spec) : option enum_layout :=
  variant_lys ← list_map_option (λ '(variant_name, variant_spec),
    ly ← use_layout_alg variant_spec;
    Some (variant_name, ly)) els.(els_variants);
  enum_layout_alg els.(els_name) els.(els_tag_it) variant_lys els.(els_repr).
Arguments use_enum_layout_alg : simpl never.

Lemma els_tag_it_size (els : enum_layout_spec) :
  ly_size (it_layout $ els_tag_it els) ≤ MaxInt ISize.
Proof.
  specialize (IntType_size_le els.(els_tag_it)).
  rewrite MaxInt_eq /max_int /int_half_modulus/bits_per_int/bytes_per_int/bits_per_byte/=. lia.
Qed.

Lemma use_enum_layout_alg_Some_inv `{!LayoutAlg} (els : enum_layout_spec) el :
  use_enum_layout_alg els = Some el →
  use_layout_alg els = Some (layout_of_enum el).
Proof.
  intros Hly.
  unfold use_enum_layout_alg in Hly. simplify_option_eq.
  unfold_layout_alg. simpl. fold use_layout_alg_def.
  rewrite Heqo /= Hly /= decide_True //.
  rewrite /enum_tag_int_wf /=. split_and!.
  - apply els_tag_int_agree.
  - rewrite (els_tag_int_agree els). apply els_variants_nodup.
  - apply els_tag_int_nodup.
  - apply els_tag_int_wf3.
Qed.
Lemma use_layout_alg_enum_Some_inv `{!LayoutAlg} (els : enum_layout_spec) ly :
  use_layout_alg els = Some ly →
  ∃ el, use_enum_layout_alg els = Some el ∧ ly = layout_of_enum el.
Proof.
  intros Hly.
  unfold_layout_alg. simpl in Hly.
  apply bind_Some in Hly as (vars & Hvars & Hul).
  apply bind_Some in Hul as (el & Hel & Hul).
  case_decide; last done.
  injection Hul as <-.
  eexists _. unfold use_enum_layout_alg. simpl.
  unfold_layout_alg; simpl.
  rewrite Hvars /= Hel //.
Qed.
Lemma use_enum_layout_alg_Some `{!LayoutAlg} els el variants' :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ use_layout_alg fst = Some fly) els.(els_variants) variants' →
  enum_layout_alg els.(els_name) els.(els_tag_it) variants' els.(els_repr) = Some el →
  use_enum_layout_alg els = Some el.
Proof.
  intros Ha Hb. rewrite /use_enum_layout_alg.
  apply bind_Some. exists variants'.
  split; last done.
  clear Hb. move: Ha. generalize (els_variants els) as variants. clear els.
  induction variants as [ | [name st] variants IH] in variants' |-*; simpl.
  - by intros []%Forall2_nil_inv_l.
  - intros ([name' ly] & variants'' & [<- Hst] & Ha & ->)%Forall2_cons_inv_l.
    erewrite IH; last done. simpl. rewrite Hst//.
Qed.

Lemma syn_type_has_layout_array `{!LayoutAlg} st (len : nat) ly ly' :
  ly' = (mk_array_layout ly len) →
  syn_type_has_layout st ly →
  (ly_size ly * len) ≤ MaxInt ISize →
  syn_type_has_layout (ArraySynType st len) ly'.
Proof.
  rewrite /syn_type_has_layout. intros -> Hst Hsize.
  unfold_layout_alg. rewrite /use_layout_alg_def/=.
  fold use_layout_alg_def.
  rewrite Hst //. simpl. rewrite decide_True; first done.
  rewrite /ly_size /=. lia.
Qed.

Lemma syn_type_has_layout_array_inv `{!LayoutAlg} st len ly :
  syn_type_has_layout (ArraySynType st len) ly →
  ∃ ly', syn_type_has_layout st ly' ∧ ly = mk_array_layout ly' len ∧ ly_size ly ≤ MaxInt ISize.
Proof.
  rewrite /syn_type_has_layout.
  unfold_layout_alg. rewrite /use_layout_alg_def/=.
  fold use_layout_alg_def.
  destruct (use_layout_alg_def st) as [ ly' | ]; last done.
  simpl. case_decide; last done.
  intros [= <-]. eauto.
Qed.

Lemma syn_type_has_layout_untyped_inv `{!LayoutAlg} st ly :
  use_layout_alg (UntypedSynType st) = Some ly →
  syn_type_has_layout st ly.
Proof.
  rewrite /syn_type_has_layout.
  unfold_layout_alg. done.
Qed.
Lemma syn_type_has_layout_untyped `{!LayoutAlg} st ly :
  syn_type_has_layout st ly →
  syn_type_has_layout (UntypedSynType st) ly.
Proof.
  rewrite /syn_type_has_layout.
  unfold_layout_alg. done.
Qed.

Lemma syn_type_has_layout_literal_inv `{!LayoutAlg} ly ly' :
  use_layout_alg (LiteralSynType ly) = Some ly' →
  ly' = ly ∧ layout_wf ly ∧ (ly_size ly ≤ MaxInt ISize)%Z ∧ ly_align_in_bounds ly.
Proof.
  unfold_layout_alg.
  rewrite /use_layout_alg_def /=.
  case_decide; last done.
  intros [= <-]. naive_solver.
Qed.
Lemma syn_type_has_layout_literal `{!LayoutAlg} ly ly' :
  ly = ly' →
  layout_wf ly →
  (ly_size ly ≤ MaxInt ISize)%Z →
  ly_align_in_bounds ly →
  use_layout_alg (LiteralSynType ly) = Some ly'.
Proof.
  intros -> ???.
  unfold_layout_alg.
  rewrite /use_layout_alg_def decide_True; done.
Qed.

Lemma syn_type_has_layout_int `{!LayoutAlg} (it : int_type) (ly : layout) :
  ly = it_layout it →
  syn_type_has_layout (IntSynType it) ly.
Proof.
  intros; subst.
  rewrite /syn_type_has_layout.
  unfold_layout_alg.
  rewrite /use_layout_alg_def decide_True; first done.
  apply it_size_bounded.
Qed.
Lemma syn_type_has_layout_int_inv `{!LayoutAlg} (it : int_type) (ly : layout) :
  syn_type_has_layout (IntSynType it) ly →
  ly = it_layout it.
Proof.
  rewrite /syn_type_has_layout.
  unfold_layout_alg.
  rewrite /use_layout_alg_def.
  case_decide; naive_solver.
Qed.

Lemma syn_type_has_layout_bool_inv `{!LayoutAlg} ly :
  syn_type_has_layout BoolSynType ly → ly = it_layout U8.
Proof.
  rewrite /syn_type_has_layout.
  unfold_layout_alg.
  rewrite /use_layout_alg => [= <-] //.
Qed.
Lemma syn_type_has_layout_bool `{!LayoutAlg} ly :
  ly = it_layout U8 → syn_type_has_layout BoolSynType ly.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  intros -> => //.
Qed.

Lemma syn_type_has_layout_char_inv `{!LayoutAlg} ly :
  syn_type_has_layout CharSynType ly → ly = char_layout.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg => [= <-] //.
Qed.
Lemma syn_type_has_layout_char `{!LayoutAlg} ly :
  ly = char_layout → syn_type_has_layout CharSynType ly.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  intros -> => //.
Qed.

Lemma syn_type_has_layout_ptr_inv `{!LayoutAlg} ly :
  syn_type_has_layout PtrSynType ly → ly = void*.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  move => [= <-] //.
Qed.
Lemma syn_type_has_layout_ptr `{!LayoutAlg} ly :
  ly = void* → syn_type_has_layout PtrSynType ly.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  intros -> => //.
Qed.

Lemma syn_type_has_layout_fnptr_inv `{!LayoutAlg} ly :
  syn_type_has_layout FnPtrSynType ly → ly = void*.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  move => [= <-] //.
Qed.
Lemma syn_type_has_layout_fnptr `{!LayoutAlg} ly :
  ly = void* → syn_type_has_layout FnPtrSynType ly.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  intros -> => //.
Qed.

Lemma syn_type_has_layout_ref_inv `{!LayoutAlg} ly :
  syn_type_has_layout RefSynType ly →
  ly = void*.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg. rewrite /use_layout_alg_def.
  intros [= <-]. done.
Qed.
Lemma syn_type_has_layout_ref `{!LayoutAlg} :
  syn_type_has_layout RefSynType void*.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg. rewrite /use_layout_alg_def. done.
Qed.

Lemma syn_type_has_layout_unit_inv `{!LayoutAlg} ly :
  syn_type_has_layout UnitSynType ly → ly = unit_sl.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  move => [= <-] //.
Qed.
Lemma syn_type_has_layout_unit `{!LayoutAlg} ly :
  ly = unit_sl → syn_type_has_layout UnitSynType ly.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  intros -> => //.
Qed.

Lemma syn_type_has_layout_never_inv `{!LayoutAlg} ly :
  syn_type_has_layout NeverSynType ly → ly = zst_layout.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  move => [= <-] //.
Qed.
Lemma syn_type_has_layout_never `{!LayoutAlg} ly :
  ly = zst_layout → syn_type_has_layout NeverSynType ly.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  intros -> => //.
Qed.

Lemma syn_type_has_layout_unsafecell_inv `{!LayoutAlg} st ly :
  syn_type_has_layout (UnsafeCell st) ly → syn_type_has_layout st ly.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  done.
Qed.
Lemma syn_type_has_layout_unsafecell `{!LayoutAlg} st ly :
  syn_type_has_layout st ly → syn_type_has_layout (UnsafeCell st) ly.
Proof.
  rewrite /syn_type_has_layout. unfold_layout_alg.
  done.
Qed.

(* More on structs *)
Definition struct_layout_spec_has_layout `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout) : Prop :=
  use_struct_layout_alg sls = Some sl.
Lemma struct_layout_spec_has_layout_inj `{!LayoutAlg} sls sl1 sl2 :
  struct_layout_spec_has_layout sls sl1 → struct_layout_spec_has_layout sls sl2 → sl1 = sl2.
Proof. rewrite /struct_layout_spec_has_layout => ??. simplify_option_eq => //. Qed.


Lemma struct_layout_spec_has_layout_lookup `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout) (x : var_name) (st : syn_type) i :
  struct_layout_spec_has_layout sls sl →
  sls.(sls_fields) !! i = Some (x, st) →
  field_index_of sl.(sl_members) x = Some i.
Proof.
  rewrite /struct_layout_spec_has_layout /use_struct_layout_alg. intros Halg.
  apply bind_Some in Halg as (fields & Heq1 & Heq2).
  apply struct_layout_alg_has_fields in Heq2. rewrite /sl_has_members in Heq2.
  intros Hlook. eapply list_map_option_lookup in Heq1; last apply Hlook.
  destruct Heq1 as ([n ly] & Heq1 & Heq3).
  symmetry in Heq3. apply bind_Some in Heq3 as (ly' & ? & [= -> ->]).
  rewrite Heq2 in Heq1.
  eapply named_fields_lookup_field_index_of; last done.
  specialize (sl_nodup sl). apply bool_decide_unpack.
Qed.

Lemma struct_layout_spec_has_layout_alt_1 `{!LayoutAlg} sls sl :
  struct_layout_spec_has_layout sls sl →
  ∃ fields, Forall2 (λ '(name, st) '(name2, ly), use_layout_alg st = Some ly ∧ name2 = name) sls.(sls_fields) fields ∧
    struct_layout_alg sls.(sls_name) fields sls.(sls_repr) = Some sl.
Proof.
  rewrite /struct_layout_spec_has_layout /use_struct_layout_alg.
  intros (fields & Ha1 & Ha2)%bind_Some.
  eapply list_map_option_alt in Ha1.
  exists fields. split; last done.
  eapply Forall2_impl; first done.
  intros [name st] [name2 ly].
  intros (ly' & ? & [= <- <-])%bind_Some. done.
Qed.
Lemma struct_layout_spec_has_layout_alt_2 `{!LayoutAlg} sls sl :
  struct_layout_spec_has_layout sls sl →
  Forall2 (λ '(name, st) '(name2, ly), use_layout_alg st = Some ly ∧ name2 = name) sls.(sls_fields) (named_fields sl.(sl_members)).
Proof.
  intros (fields & Hf & Halg%struct_layout_alg_has_fields)%struct_layout_spec_has_layout_alt_1.
  rewrite -Halg. done.
Qed.
Lemma struct_layout_spec_has_layout_fields_length' `{!LayoutAlg} sls sl :
  struct_layout_spec_has_layout sls sl →
  length (sls.(sls_fields)) = length (named_fields sl.(sl_members)).
Proof.
  intros Ha%struct_layout_spec_has_layout_alt_2. by eapply Forall2_length.
Qed.
Lemma struct_layout_spec_has_layout_fields_length `{!LayoutAlg} sls sl :
  struct_layout_spec_has_layout sls sl →
  length (field_names (sl_members sl)) = length (sls_fields sls).
Proof.
  rewrite -named_fields_field_names_length.
  intros ?. erewrite struct_layout_spec_has_layout_fields_length'; done.
Qed.

Lemma struct_layout_spec_has_layout_members_lookup_1 `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout) :
  struct_layout_spec_has_layout sls sl →
  ∀ x st i,
  sls.(sls_fields) !! i = Some (x, st) →
  ∃ ly j, sl.(sl_members) !! j = Some (Some x, ly) ∧ syn_type_has_layout st ly.
Proof.
  intros Ha%struct_layout_spec_has_layout_alt_2 ???.
  intros Hlook.
  eapply Forall2_lookup_l in Ha; last done.
  destruct Ha as ([name ly] & Hlook2 & [Halg ->]).
  eapply named_fields_lookup_1 in Hlook2 as (j & Hlook2).
  exists ly, j. done.
Qed.
Lemma struct_layout_spec_has_layout_members_lookup_2 `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout)  :
  struct_layout_spec_has_layout sls sl →
  ∀ i ly x,
  sl.(sl_members) !! i = Some (Some x, ly) →
  ∃ st j, sls.(sls_fields) !! j = Some (x, st) ∧ syn_type_has_layout st ly.
Proof.
  intros Ha%struct_layout_spec_has_layout_alt_2 ???.
  intros (j & Hlook)%named_fields_lookup_2.
  eapply Forall2_lookup_r in Ha; last done.
  destruct Ha as ([name st] & Hlook2 & [Halg ->]).
  eauto.
Qed.

Lemma struct_layout_spec_has_layout_members `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout) (x : var_name) (st : syn_type) :
  struct_layout_spec_has_layout sls sl →
  (x, st) ∈ sls.(sls_fields) →
  ∃ ly, (Some x, ly) ∈ sl.(sl_members) ∧ syn_type_has_layout st ly.
Proof.
  intros Ha%struct_layout_spec_has_layout_alt_2.
  intros (i & Hlook)%list_elem_of_lookup_1.
  eapply Forall2_lookup_l in Ha; last done.
  destruct Ha as ([name ly] & Hlook2 & [Halg ->]).
  exists ly. split; last done.
  eapply elem_of_named_fields.
  by eapply list_elem_of_lookup_2.
Qed.


(** [field_index_of]: version for struct_layout_spec *)
Fixpoint sls_field_index_of (fields : list (string * syn_type)) (x : string) : option nat :=
  match fields with
  | [] => None
  | (n', _) :: s =>
      if bool_decide (n' = x) then Some 0%nat
      else S <$> sls_field_index_of s x
  end.

Lemma sls_field_index_of_fmap fields x (f : nat → nat) i :
  f <$> (sls_field_index_of fields x) = Some i →
  ∃ j, sls_field_index_of fields x = Some j ∧ i = f j.
Proof.
  induction fields as [ | [y ly] fields IH] in i, f |-*; simpl; first done.
  case_bool_decide as Ha; subst.
  - intros [= <-]. eauto.
  - rewrite -option_fmap_compose. intros (j & Hlook & ->)%IH.
    rewrite Hlook. eauto.
Qed.
Lemma sls_field_index_of_lookup fields f i :
  sls_field_index_of fields f = Some i →
  ∃ ly, fields !! i = Some (f, ly).
Proof.
  induction fields as [ | [f0 ly] fields IH] in i |-*; simpl; first done.
  case_bool_decide as Ha; subst.
  - intros [= <-]. eauto.
  - intros (j & Hlook & ->)%sls_field_index_of_fmap. eauto.
Qed.

(** More on unions *)
Definition union_layout_spec_has_layout `{!LayoutAlg} (uls : union_layout_spec) (ul : union_layout) : Prop :=
  use_union_layout_alg uls = Some ul.
Lemma union_layout_spec_has_layout_inj `{!LayoutAlg} uls ul1 ul2 :
  union_layout_spec_has_layout uls ul1 → union_layout_spec_has_layout uls ul2 → ul1 = ul2.
Proof. rewrite /union_layout_spec_has_layout => ??. simplify_option_eq => //. Qed.


(** More on enums *)
Definition enum_layout_spec_has_layout `{!LayoutAlg} (els : enum_layout_spec) (el : enum_layout) : Prop :=
  use_enum_layout_alg els = Some el.
Lemma enum_layout_spec_has_layout_inj `{!LayoutAlg} els el1 el2 :
  enum_layout_spec_has_layout els el1 → enum_layout_spec_has_layout els el2 → el1 = el2.
Proof. rewrite /enum_layout_spec_has_layout => ??. simplify_option_eq => //. Qed.

Lemma use_enum_layout_alg_inv `{!LayoutAlg} els el :
  use_enum_layout_alg els = Some el →
  ∃ (variant_lys : list (string * layout)),
    enum_layout_alg els.(els_name) els.(els_tag_it) variant_lys els.(els_repr) = Some el ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) els.(els_variants) variant_lys.
Proof.
  intros (variant_lys & Hvars%list_map_option_alt & Halg)%bind_Some.
  exists variant_lys. split_and!; [done.. | ].
  eapply Forall2_impl; first done.
  intros [] []. intros (fly & ? & [= <- <-])%bind_Some. done.
Qed.
Lemma syn_type_has_layout_enum_inv `{!LayoutAlg} ly (els : enum_layout_spec_raw_gen syn_type) :
  syn_type_has_layout (EnumSynType els) ly →
  ∃ el (variant_lys : list (string * layout)),
    enum_layout_alg els.(raw_els_name) els.(raw_els_tag_it) variant_lys els.(raw_els_repr) = Some el ∧
    ly = layout_of_enum el ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) els.(raw_els_variants) variant_lys ∧
    enum_tag_int_wf els.(raw_els_tag_it) els.(raw_els_variants) els.(raw_els_tag_int).
Proof.
  simpl. rewrite /syn_type_has_layout/=.
  unfold_layout_alg.
  intros (variant_lys & Hvariants & Ha)%bind_Some.
  apply list_map_option_alt in Hvariants.
  apply bind_Some in Ha as (el & Hel & Ha).
  case_decide as Htag; last done.
  injection Ha as <-.
  exists el, variant_lys. split_and!; try done.
  eapply Forall2_impl; first done.
  intros [] [].
  intros (ly & Halg & [= -> ->])%bind_Some.
  eauto.
Qed.
Lemma syn_type_has_layout_enum `{!LayoutAlg} (els : enum_layout_spec_raw_gen syn_type) variants' ly el :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) els.(raw_els_variants) variants' →
  enum_layout_alg els.(raw_els_name) els.(raw_els_tag_it) variants' els.(raw_els_repr) = Some el →
  enum_tag_int_wf els.(raw_els_tag_it) els.(raw_els_variants) els.(raw_els_tag_int) →
  ly = layout_of_enum el →
  syn_type_has_layout (EnumSynType els) ly.
Proof.
  intros Ha Hb Htag ->.
  rewrite /syn_type_has_layout.
  unfold_layout_alg.
  eapply bind_Some. exists variants'.
  split. { apply list_map_option_alt. eapply Forall2_impl; first done.
    rewrite /syn_type_has_layout.
     unfold_layout_alg.
     fold use_layout_alg_def.
     intros [] [] [-> ->]. done. }
  rewrite Hb/=//. by rewrite decide_True.
Qed.

(** Well-formedness: the size is divisible by the alignment *)
Lemma use_struct_layout_alg_wf `{!LayoutAlg} sls sl :
  use_struct_layout_alg sls = Some sl →
  layout_wf sl.
Proof.
  rewrite /use_struct_layout_alg => Ha.
  apply bind_Some in Ha as (lys & Ha & Halg).
  by apply struct_layout_alg_wf in Halg.
Qed.
Lemma use_union_layout_alg_wf `{!LayoutAlg} uls ul :
  use_union_layout_alg uls = Some ul →
  layout_wf ul.
Proof.
  rewrite /use_struct_layout_alg => Ha.
  apply bind_Some in Ha as (lys & Ha & Halg).
  by apply union_layout_alg_wf in Halg.
Qed.
Lemma use_enum_layout_alg_wf `{!LayoutAlg} els el :
  use_enum_layout_alg els = Some el →
  layout_wf el.
Proof.
  intros _. apply enum_layout_wf.
Qed.
Lemma use_layout_alg_wf `{!LayoutAlg} st ly :
  use_layout_alg st = Some ly →
  layout_wf ly.
Proof.
  unfold_layout_alg.
  induction st in ly |-*; move => ?; simplify_option_eq; fold use_layout_alg_def in *.
  - apply int_type_layout_wf.
  - apply int_type_layout_wf.
  - apply ptr_layout_wf.
  - apply ptr_layout_wf.
  - by eapply struct_layout_alg_wf.
  - rewrite /layout_wf /unit_sl /layout_of /=.
    rewrite /ly_align /ly_size /=.
    apply Z.divide_0_r.
  - rewrite /layout_wf /zst_layout/=.
    rewrite /ly_align /ly_size /=.
    apply Z.divide_0_r.
  - eapply array_layout_wf. eauto.
  - eauto.
  - naive_solver.
  - naive_solver.
  - apply enum_layout_wf.
  - by eapply union_layout_alg_wf.
  - apply char_layout_wf.
  - apply ptr_layout_wf.
Qed.

(** Size limits: object size should be limited by isize *)
Lemma use_layout_alg_size `{!LayoutAlg} st ly :
  use_layout_alg st = Some ly →
  ly_size ly ≤ MaxInt ISize.
Proof.
  unfold_layout_alg.
  induction st in ly |-*; move => ?; simplify_option_eq; fold use_layout_alg_def in *.
  - done.
  - rewrite MaxInt_eq. done.
  - rewrite MaxInt_eq. done.
  - rewrite MaxInt_eq. done.
  - rewrite /ly_size /=.
    match goal with | H : struct_layout |- _ => specialize (sl_size H) end.
    rewrite MaxInt_eq. lia.
  - rewrite MaxInt_eq. done.
  - rewrite MaxInt_eq. done.
  - done.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - rewrite /ly_size /=.
    match goal with | H : enum_layout |- _ => pose proof (el_size_bounded H) end.
    rewrite MaxInt_eq. lia.
  - match goal with | H : union_layout |- _ => rename H into ul end.
    specialize (ul_size_bound_1 ul) as Hsz.
    rewrite /ly_size /= MaxInt_eq. lia.
  - rewrite MaxInt_eq. done.
  - rewrite MaxInt_eq. done.
Qed.

Lemma use_struct_layout_alg_size `{!LayoutAlg} sls sl :
  use_struct_layout_alg sls = Some sl →
  ly_size sl ≤ MaxInt ISize.
Proof.
  intros _.
  rewrite /ly_size /=.
  pose (sl_size sl) as Ha. rewrite MaxInt_eq. lia.
Qed.
Lemma use_union_layout_alg_size `{!LayoutAlg} uls ul :
  use_union_layout_alg uls = Some ul →
  ly_size ul ≤ MaxInt ISize.
Proof.
  intros _. rewrite /ly_size /=.
  pose (ul_size_bound_1 ul) as Ha. rewrite MaxInt_eq. lia.
Qed.
Lemma use_enum_layout_alg_size `{!LayoutAlg} els el :
  use_enum_layout_alg els = Some el →
  ly_size el ≤ MaxInt ISize.
Proof.
  intros _. rewrite /ly_size /=.
  pose proof (el_size_bounded el) as Ha. rewrite MaxInt_eq. lia.
Qed.

(** Alignment limits *)


Lemma sl_align_eq (sl : struct_layout) :
  ly_align sl = max 1 (max_list (ly_align <$> (sl_members sl).*2)).
Proof.
  rewrite /ly_align{1}/ly_align_log/=.
  generalize (sl_members sl).*2 => lys.
  clear sl. induction lys as [ | ly lys IH]; simpl; first done.
  rewrite Nat_pow_max; last lia. rewrite IH.
  unfold fmap. lia.
Qed.
Lemma ul_align_eq (ul : union_layout) :
  ly_align ul = max 1 (max_list (ly_align <$> (ul_members ul).*2)).
Proof.
  rewrite /ly_align{1}/ly_align_log/=.
  generalize (ul_members ul).*2 => lys.
  clear ul. induction lys as [ | ly lys IH]; simpl; first done.
  rewrite Nat_pow_max; last lia. rewrite IH.
  unfold fmap. lia.
Qed.

Lemma struct_layout_alg_align_in_bounds `{!LayoutAlg} sn fields repr sl :
  Forall (λ '(_, ly), ly_align_in_bounds ly) fields →
  struct_layout_alg sn fields repr = Some sl →
  ly_align_in_bounds sl.
Proof.
  rewrite /ly_align_in_bounds.
  intros Hfields Halg.
  rewrite sl_align_eq.
  specialize (struct_layout_alg_has_fields _ _ _ _ Halg) as ->.
  specialize (struct_layout_alg_pad_align _ _ _ _ Halg) as Hpad.
  clear Halg.
  move: Hfields Hpad.
  generalize (sl_members sl) => mems. intros Halgs Hpad.
  clear sl. induction mems as [ | [n ly] mems IH'] in Halgs, Hpad |-*; simpl in *.
  { unsafe_unfold_common_radium_defs. simpl. lia. }
  rewrite Nat.max_assoc. rewrite [(1 `max` _)%nat]Nat.max_comm. rewrite -Nat.max_assoc.
  destruct n as [ n | ].
  + (* named *)
    inversion Hpad; subst.
    inversion Halgs as [ | ? ? Hx Halgs']; subst.
    eapply Nat_Z_in_bounds_max_1. { apply Hx. }
    eapply IH'; done.
  + (* unnamed *)
    inversion Hpad; subst.
    rename select (ly_align_log ly = _) into Hly.
    eapply Nat_Z_in_bounds_max_1. {
      rewrite /ly_align Hly.
      unsafe_unfold_common_radium_defs.
      simpl. lia. }
    eapply IH'; done.
Qed.
Lemma union_layout_alg_align_in_bounds `{!LayoutAlg} sn variants repr ul :
  Forall (λ '(_, ly), ly_align_in_bounds ly) variants →
  union_layout_alg sn variants repr = Some ul →
  ly_align_in_bounds ul.
Proof.
  rewrite /ly_align_in_bounds.
  intros Hfields Halg.
  rewrite ul_align_eq.
  specialize (union_layout_alg_has_variants _ _ _ _ Halg) as ->.
  clear Halg.
  move: Hfields.
  generalize (ul_members ul) => mems. intros Halgs.
  clear ul. induction mems as [ | [n ly] mems IH'] in Halgs |-*; simpl in *.
  { unsafe_unfold_common_radium_defs. simpl. lia. }
  rewrite Nat.max_assoc. rewrite [(1 `max` _)%nat]Nat.max_comm. rewrite -Nat.max_assoc.
  inversion Halgs as [ | ? ? Hx Halgs']; subst.
  eapply Nat_Z_in_bounds_max_1. { apply Hx. }
  eapply IH'; done.
Qed.

Lemma use_layout_alg_align `{!LayoutAlg} st ly :
  use_layout_alg st = Some ly →
  ly_align_in_bounds ly.
Proof.
  unfold_layout_alg.
  induction st as [ it | | | | sn fields repr IH | | | st IH len | st IH | st IH | ly' | en tag_it | un variant_list repr IH | | ] using syn_type_strong_ind in ly |-*; move => ?; simplify_option_eq; fold use_layout_alg_def in *;
      rewrite /ly_align_in_bounds.
  - rewrite /ly_align/it_layout/=.
    revert select (ly_size _ ≤ _). rewrite /ly_size/=/bytes_per_int => Ha.
    etrans; first apply Ha.
    specialize MaxInt_isize_lt_usize.
    rewrite !MaxInt_eq. lia.
  - done.
  - done.
  - done.
  - (* struct *)
    rename select (list_map_option _ _ = Some _) into Halgs.
    match type of Halgs with list_map_option _ _ = Some ?Ha => rename Ha into mems end.
    apply list_map_option_alt in Halgs.
    eapply struct_layout_alg_align_in_bounds; last done.
    clear -IH Halgs.
    induction mems as [ | [n ly] mems IH'] in fields, IH, Halgs |-*; simpl in *.
    { econstructor. }
    apply Forall2_cons_inv_r in Halgs as ([n' st] & fields' & Ha & Hb & ->).
    apply bind_Some in Ha as (ly' & Halg & [= -> ->]).
    inversion IH as [ | ? ? Hx IH1]; subst.
    specialize (Hx _ Halg).
    econstructor; first done. eapply IH'; done.
  - done.
  - done.
  - rewrite /mk_array_layout/=/ly_mult/ly_align/=.
    apply IH. done.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* enum *)
    rename select (list_map_option _ _ = Some _) into Halgs.
    match type of Halgs with list_map_option _ _ = Some ?Ha => rename Ha into mems end.
    apply list_map_option_alt in Halgs.
    rename select (enum_layout_alg _ _ _ _ = _) into Henum.
    eapply enum_layout_alg_align_in_bounds; last done.
    move: tag_it Halgs. generalize (raw_els_variants en) as variants.
    intros variants IH Halgs.
    induction mems as [ | [n ly] mems IH'] in variants, IH, Halgs |-*; simpl in *.
    { econstructor. }
    apply Forall2_cons_inv_r in Halgs as ([n' st] & fields' & Ha & Hb & ->).
    apply bind_Some in Ha as (ly' & Halg & [= -> ->]).
    inversion IH as [ | ? ? Hx IH1]; subst.
    specialize (Hx _ Halg).
    econstructor; first done. eapply IH'; done.
  - (* union *)
    rename select (list_map_option _ _ = Some _) into Halgs.
    match type of Halgs with list_map_option _ _ = Some ?Ha => rename Ha into mems end.
    apply list_map_option_alt in Halgs.
    rename select (union_layout_alg _ _ _ = _) into Hunion.
    eapply union_layout_alg_align_in_bounds; last done.
    clear -IH Halgs.
    induction mems as [ | [n ly] mems IH'] in variant_list, IH, Halgs |-*; simpl in *.
    { econstructor. }
    apply Forall2_cons_inv_r in Halgs as ([n' st] & fields' & Ha & Hb & ->).
    apply bind_Some in Ha as (ly' & Halg & [= -> ->]).
    inversion IH as [ | ? ? Hx IH1]; subst.
    specialize (Hx _ Halg).
    econstructor; first done. eapply IH'; done.
  - (* char *)
    done.
  - done.
Qed.

Lemma syn_type_has_layout_make_literal `{!LayoutAlg} st ly ly' :
  ly = ly' →
  syn_type_has_layout st ly →
  syn_type_has_layout (LiteralSynType ly) ly'.
Proof.
  intros <- Hst.
  apply syn_type_has_layout_literal.
  - done.
  - eapply use_layout_alg_wf; done.
  - eapply use_layout_alg_size; done.
  - by eapply use_layout_alg_align.
Qed.

Lemma syn_type_has_layout_literal_mono `{!LayoutAlg} ly1 ly2 :
  ly_align_log ly2 ≤ ly_align_log ly1 →
  ly_size ly1 = ly_size ly2 →
  syn_type_has_layout (LiteralSynType ly1) ly1 →
  syn_type_has_layout (LiteralSynType ly2) ly2.
Proof.
  intros ?? Hut. apply syn_type_has_layout_literal_inv in Hut as (_ & Hwf & Hsz & Hal).
  apply syn_type_has_layout_literal; first done.
  - eapply layout_wf_mono; last apply Hwf.
    all: lia.
  - lia.
  - eapply ly_align_in_bounds_mono; last apply Hal.
    lia.
Qed.

(** Infallible versions *)
Definition use_layout_alg' `{!LayoutAlg} (st : syn_type) : layout :=
  default inhabitant (use_layout_alg st).
(*Coercion use_layout_alg' : syn_type >-> layout.*)

Lemma use_layout_alg_eq' `{!LayoutAlg} st ly :
  use_layout_alg st = Some ly →
  use_layout_alg' st = ly.
Proof.
  rewrite /use_layout_alg' => -> //.
Qed.

Global Instance struct_layout_inhabited : Inhabited struct_layout := populate unit_sl.
Definition use_struct_layout_alg' `{!LayoutAlg} (sls : struct_layout_spec) : struct_layout :=
  default inhabitant (use_struct_layout_alg sls).

Global Instance union_layout_inhabited : Inhabited union_layout := populate neverlike_ul.
Definition use_union_layout_alg' `{!LayoutAlg} (uls : union_layout_spec) : union_layout :=
  default inhabitant (use_union_layout_alg uls).

Global Instance enum_layout_inhabited : Inhabited enum_layout := populate empty_el.
Definition use_enum_layout_alg' `{!LayoutAlg} (els : enum_layout_spec) : enum_layout :=
  default inhabitant (use_enum_layout_alg els).

(** Size of syn_types *)
Definition size_of_st `{!LayoutAlg} (st : syn_type) : nat :=
  ly_size (use_layout_alg' st).

Section size_of.
  Context `{!LayoutAlg}.

  Ltac unfold_st := rewrite /size_of_st /use_layout_alg'/syn_type_has_layout; unfold_layout_alg; rewrite /use_layout_alg_def.

  Lemma size_of_st_ptr :
    size_of_st PtrSynType = ly_size void*.
  Proof. unfold_st. done. Qed.
  Lemma size_of_st_int (it : int_type) :
    (ly_size (it_layout it) ≤ MaxInt ISize)%Z → size_of_st (IntSynType it) = ly_size (it_layout it).
  Proof.
    intros. unfold_st. rewrite decide_True; done.
  Qed.
  Lemma size_of_st_Int (it : int_type) :
    size_of_st (IntSynType it) = ly_size (it_layout it).
  Proof.
    apply size_of_st_int. apply it_size_bounded.
  Qed.
  Lemma size_of_st_bool :
    size_of_st BoolSynType = 1%nat.
  Proof. unfold_st. done. Qed.
  Lemma size_of_st_unit :
    size_of_st UnitSynType = 0%nat.
  Proof. unfold_st. done. Qed.
  Lemma size_of_st_never :
    size_of_st NeverSynType = 0%nat.
  Proof. unfold_st. done. Qed.
  Lemma size_of_st_array st sz n ly :
    syn_type_has_layout (ArraySynType st n) ly →
    size_of_st st = sz →
    size_of_st (ArraySynType st n) = (n * sz)%nat.
  Proof.
    intros Halg.
    apply syn_type_has_layout_array_inv in Halg as (ly' & Hst & -> & Hsz).
    move: Hst.
    unfold_st; fold use_layout_alg_def.
    intros Hst <-.
    rewrite Hst. simpl.
    rewrite decide_True; last done.
    simpl. rewrite /mk_array_layout /ly_mult /ly_size; destruct ly'; lia.
  Qed.

  (* For struct, enum, and union, we will have to treat this opaquely, since it is the layout algorithm's choice. *)
End size_of.

(** We can compute a canonical optype for every syntype that should be used when accessing an element of this syntype in a safe read/write *)
Fixpoint use_op_alg `{!LayoutAlg} (st : syn_type) : option op_type :=
  match st with
  | IntSynType it => Some $ IntOp it
  | BoolSynType => Some BoolOp
  | CharSynType => Some CharOp
  | PtrSynType => Some PtrOp
  | FnPtrSynType => Some FnPtrOp
  | StructSynType name fields repr =>
    sl ← use_struct_layout_alg (mk_sls name fields repr);
    ots ← list_map_option (λ '(name, st), use_op_alg st) fields;
    Some $ StructOp sl ots
  | UnitSynType => Some $ StructOp unit_sl []
  | NeverSynType => Some $ NeverOp
  | ArraySynType st n =>
    _ ← use_layout_alg (ArraySynType st n);
    ot ← use_op_alg st;
    Some $ ArrayOp ot n
  | UnsafeCell st =>
      use_op_alg st
  | UntypedSynType st =>
      ly ← use_layout_alg (UntypedSynType st);
      Some $ UntypedOp ly
  | LiteralSynType ly =>
      ly ← use_layout_alg (LiteralSynType ly);
      Some $ UntypedOp ly
  | EnumSynType els =>
      variant_lys ← list_map_option (λ '(name, st), ly ← use_layout_alg st; Some (name, ly)) els.(raw_els_variants);
      el ← enum_layout_alg els.(raw_els_name) els.(raw_els_tag_it) variant_lys els.(raw_els_repr);
      variant_ots ← list_map_option (λ '(name, st), ot ← use_op_alg st; Some (name, ot)) els.(raw_els_variants);
      if decide (enum_tag_int_wf els.(raw_els_tag_it) els.(raw_els_variants) els.(raw_els_tag_int)) then Some $ EnumOp el variant_ots els.(raw_els_tag_int) else None
  | UnionSynType _ _ _ =>
      ly ← use_layout_alg st;
      Some $ UntypedOp ly
  | RefSynType => Some RefOp
  end.
Definition use_op_alg' `{!LayoutAlg} (st : syn_type) : op_type :=
  default (UntypedOp unit_sl) (use_op_alg st).

Lemma use_op_alg_inj `{!LayoutAlg} st ot ot' :
  use_op_alg st = Some ot →
  use_op_alg st = Some ot' →
  ot' = ot.
Proof.
  congruence.
Qed.

Definition use_op_alg_struct_pred `{!LayoutAlg} : (string * syn_type) → op_type → Prop := (λ '(_, fst) (fop : op_type), use_op_alg fst = Some fop).
Lemma use_op_alg_struct `{!LayoutAlg} name fields sl ots ot repr :
  Forall2 use_op_alg_struct_pred (fields) ots →
  use_struct_layout_alg (mk_sls name fields repr) = Some sl →
  ot = StructOp sl ots →
  use_op_alg (StructSynType name fields repr) = Some ot.
Proof.
  intros Ha Hb ->. rewrite /use_op_alg Hb /=. fold (use_op_alg).
  apply bind_Some. exists ots.
  split; last done.
  apply list_map_option_alt.
  eapply Forall2_impl; first done.
  intros [] ?; done.
Qed.
Lemma use_op_alg_sls `{!LayoutAlg} sls sl ots ot :
  Forall2 use_op_alg_struct_pred (sls.(sls_fields)) ots →
  use_struct_layout_alg sls = Some sl →
  ot = StructOp sl ots →
  use_op_alg (syn_type_of_sls sls) = Some ot.
Proof.
  intros. by eapply use_op_alg_struct.
Qed.
Lemma use_op_alg_struct_inv `{!LayoutAlg} name fields repr op :
  use_op_alg (StructSynType name fields repr) = Some op →
  ∃ sl ots,
    use_struct_layout_alg (mk_sls name fields repr) = Some sl ∧
    Forall2 (λ field ot, use_op_alg field.2 = Some ot) fields ots ∧
    op = StructOp sl ots.
Proof.
  intros Ha. apply bind_Some in Ha as (sl & Hsl & Hots).
  apply bind_Some in Hots as (ots & Hots & [= <-]).
  exists sl, ots. split_and!; try done.
  apply list_map_option_alt in Hots.
  eapply Forall2_impl; first done.
  intros [] ?. done.
Qed.

Definition use_op_alg_enum_pred `{!LayoutAlg} : (string * syn_type) → (string * op_type) → Prop :=
  (λ '(name, fst) fop, name=fop.1 ∧ use_op_alg fst = Some fop.2).
Lemma use_op_alg_enum `{!LayoutAlg} (els : enum_layout_spec_raw_gen syn_type) variant_lys el variant_ots ot :
  list_map_option (λ '(name, st), ly ← use_layout_alg st; Some (name, ly)) els.(raw_els_variants) = Some variant_lys →
  enum_layout_alg els.(raw_els_name) els.(raw_els_tag_it) variant_lys els.(raw_els_repr) = Some el →
  list_map_option (λ '(name, st), ot ← use_op_alg st; Some (name, ot)) els.(raw_els_variants) = Some variant_ots →
  enum_tag_int_wf els.(raw_els_tag_it) els.(raw_els_variants) els.(raw_els_tag_int) →
  ot = EnumOp el variant_ots els.(raw_els_tag_int) →
  use_op_alg (EnumSynType els) = Some ot.
Proof.
  intros Hlys Hel Hots Htag ->.
  rewrite /use_op_alg Hlys /= Hel /= Hots /= decide_True //.
Qed.
Lemma use_op_alg_els `{!LayoutAlg} els sl ots ot :
  use_enum_layout_alg els = Some sl →
  Forall2 use_op_alg_enum_pred (els.(els_variants)) ots →
  ot = EnumOp sl ots els.(els_tag_int) →
  use_op_alg (syn_type_of_els els) = Some ot.
Proof.
  intros (variant_lys & Halg & Hlys)%use_enum_layout_alg_inv Hots ->.
  rewrite /syn_type_of_els /enum_layout_spec_raw /use_op_alg /=. fold use_op_alg.
  assert (list_map_option (λ '(name, st), use_layout_alg st ≫= λ ly : layout, Some (name, ly)) (els_variants els) = Some variant_lys) as ->.
  { apply list_map_option_alt. eapply Forall2_impl; first done.
    intros [] [] [-> Hst]. rewrite /syn_type_has_layout in Hst. by rewrite Hst. }
  rewrite /= Halg /=.
  assert (list_map_option (λ '(name, st), use_op_alg st ≫= λ ot : op_type, Some (name, ot)) (els_variants els) = Some ots) as ->.
  { apply list_map_option_alt. eapply Forall2_impl; first done.
    intros [] [] [-> Hst]. rewrite /syn_type_has_layout in Hst. by rewrite Hst. }
  rewrite /= decide_True //.
  rewrite /enum_tag_int_wf /=. split_and!.
  - apply els_tag_int_agree.
  - rewrite (els_tag_int_agree els). apply els_variants_nodup.
  - apply els_tag_int_nodup.
  - apply els_tag_int_wf3.
Qed.

Lemma use_op_alg_union `{!LayoutAlg} name variants ly ot repr :
  use_layout_alg (UnionSynType name variants repr) = Some ly →
  ot = (UntypedOp ly) →
  use_op_alg (UnionSynType name variants repr) = Some ot.
Proof.
  intros Halg ->.
  rewrite /use_op_alg Halg//.
Qed.
Lemma use_op_alg_uls `{!LayoutAlg} uls ul ot :
  use_union_layout_alg uls = Some ul →
  ot = (UntypedOp ul) →
  use_op_alg (syn_type_of_uls uls) = Some ot.
Proof.
  intros Halg ->.
  eapply use_op_alg_union; last done.
  by eapply use_union_layout_alg_Some_inv.
Qed.

Lemma use_op_alg_int `{!LayoutAlg} it ot:
  ot = IntOp it →
  use_op_alg (IntSynType it) = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_bool `{!LayoutAlg} ot :
  ot = BoolOp →
  use_op_alg BoolSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_char `{!LayoutAlg} ot :
  ot = CharOp →
  use_op_alg CharSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_ptr `{!LayoutAlg} ot :
  ot = PtrOp →
  use_op_alg PtrSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_fnptr `{!LayoutAlg} ot :
  ot = FnPtrOp →
  use_op_alg FnPtrSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_ref `{!LayoutAlg} :
  use_op_alg RefSynType = Some RefOp.
Proof. done. Qed.
Lemma use_op_alg_unit `{!LayoutAlg} ot :
  ot = (StructOp unit_sl []) →
  use_op_alg UnitSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_never `{!LayoutAlg} ot :
  ot = NeverOp →
  use_op_alg NeverSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_array `{!LayoutAlg} st n ly ot :
  use_layout_alg (ArraySynType st n) = Some ly →
  use_op_alg st = Some ot →
  use_op_alg (ArraySynType st n) = Some (ArrayOp ot n).
Proof. intros Hly Hot. rewrite /use_op_alg Hly /=. fold use_op_alg. by rewrite Hot. Qed.
Lemma use_op_alg_array_inv `{!LayoutAlg} st n op :
  use_op_alg (ArraySynType st n) = Some op →
  ∃ ly ot,
    use_layout_alg (ArraySynType st n) = Some ly ∧
    use_op_alg st = Some ot ∧
    op = ArrayOp ot n.
Proof.
  rewrite /use_op_alg. fold use_op_alg.
  intros Hop. apply bind_Some in Hop as (ly & Hly & Hop).
  apply bind_Some in Hop as (ot & Hot & [= <-]).
  eauto.
Qed.
Lemma use_op_alg_unsafecell `{!LayoutAlg} st op :
  use_op_alg st = Some op →
  use_op_alg (UnsafeCell st) = Some op.
Proof. simpl. done. Qed.


Lemma use_op_alg_untyped `{!LayoutAlg} st ot ly :
  ot = (UntypedOp ly) →
  use_layout_alg (UntypedSynType st) = Some ly →
  use_op_alg (UntypedSynType st) = Some ot.
Proof.
  intros -> Hly. rewrite /use_op_alg Hly //.
Qed.
Lemma use_op_alg_untyped_inv `{!LayoutAlg} st ot :
  use_op_alg (UntypedSynType st) = Some ot →
  ∃ ly, use_layout_alg (UntypedSynType st) = Some ly ∧ ot = (UntypedOp ly).
Proof.
  rewrite /use_op_alg.
  intros (ly & Hly & [= <-])%bind_Some.
  eauto.
Qed.

Lemma use_op_alg_literal `{!LayoutAlg} ly ot :
  ot = (UntypedOp ly) →
  use_layout_alg (LiteralSynType ly) = Some ly →
  use_op_alg (LiteralSynType ly) = Some ot.
Proof. intros -> Hly. rewrite /use_op_alg Hly //. Qed.
Lemma use_op_alg_literal_inv `{!LayoutAlg} ly ot :
  use_op_alg (LiteralSynType ly) = Some ot →
  use_layout_alg (LiteralSynType ly) = Some ly ∧ ot = (UntypedOp ly).
Proof.
  rewrite /use_op_alg.
  intros (ly' & Hly & [= <-])%bind_Some.
  apply syn_type_has_layout_literal_inv in Hly as (<- & ? & ? & ?).
  split; last done.
  by apply syn_type_has_layout_literal.
Qed.



(** Prevent simplification from unfolding it too eagerly. *)
Arguments use_op_alg : simpl never.


Lemma use_op_alg_layout_alg `{!LayoutAlg} st op :
  use_op_alg st = Some op →
  use_layout_alg st = Some (ot_layout op).
Proof.
  induction st in op |-* using syn_type_strong_ind; rewrite /use_op_alg; simpl; fold use_op_alg; intros Ha; simplify_option_eq.
  - unfold_layout_alg. rewrite /use_layout_alg_def decide_True; first done.
    apply it_size_bounded.
  - unfold_layout_alg. rewrite /use_layout_alg_def /bool_layout /it_layout /bytes_per_int /=. done.
  - unfold_layout_alg. done.
  - unfold_layout_alg. done.
  - change (use_layout_alg (syn_type_of_sls (mk_sls sn field_list repr)) = Some (layout_of H1)).
    by eapply use_struct_layout_alg_Some_inv.
  - unfold_layout_alg. done.
  - unfold_layout_alg. done.
  - move: Heqo. unfold_layout_alg.
    rewrite /use_layout_alg_def /=. fold use_layout_alg_def.
    rewrite (IHst _ eq_refl) /=.
    case_decide; simplify_eq; done.
  - unfold_layout_alg. by apply IHst.
  - done.
  - unfold_layout_alg. done.
  - unfold_layout_alg. rewrite /use_layout_alg_def /=. rewrite Heqo /= Heqo0 /= decide_True //.
  - done.
  - unfold_layout_alg. rewrite /use_layout_alg_def. done.
  - unfold_layout_alg. rewrite /use_layout_alg_def. done.
Qed.

Lemma use_struct_layout_alg_op_alg `{!LayoutAlg} (sls : struct_layout_spec) (sl: struct_layout) :
  use_struct_layout_alg sls = Some sl →
  Forall (λ '(_, st), ∀ ly, syn_type_has_layout st ly → ∃ ot : op_type, use_op_alg st = Some ot ∧ ot_layout ot = ly) (sls_fields sls) →
  ∃ ot, use_op_alg sls = Some ot ∧ ot_layout ot = layout_of sl.
Proof.
  intros (field_lys & Halg & Hfields)%use_struct_layout_alg_inv.
  destruct sls as [sn fields].
  rewrite {2}/use_op_alg/=. fold use_op_alg.
  move: Hfields Halg. simpl. intros Hfields Halg IH.
  assert (∃ ots : list op_type, Forall3 (λ '(_, ly) '(_, st) ot, use_op_alg st = Some ot ∧ ot_layout ot = ly) field_lys fields ots) as (ots & Hots).
  {
    clear -IH Hfields.
    induction fields as [ | [n st] fields IH'] in field_lys, IH, Hfields |-*; simpl.
    { exists []. apply Forall2_nil_inv_l in Hfields. subst. econstructor. }
    inversion IH as [ | ?? Hst IH1]; subst.
    apply Forall2_cons_inv_l in Hfields as ([n' ly] & fields' & [<- Hst'] & Hfields & ->).
    apply Hst in Hst' as (ot & Hot & <-).
    opose proof* (IH') as Ha; [done.. | ].
    destruct Ha as (ots & Hots').
    exists (ot :: ots). econstructor; done.
  }
  exists (StructOp sl ots). split; last done.
  rewrite /use_op_alg. fold use_op_alg.
  erewrite use_struct_layout_alg_Some; [ | done..].
  simpl.
  apply bind_Some. exists ots. split; last done.
  apply list_map_option_alt.
  clear -Hots.
  eapply Forall3_Forall2_impl; last done.
  intros [] [] ? []. done.
Qed.
Lemma use_union_layout_alg_op_alg `{!LayoutAlg} (uls : union_layout_spec) (ul: union_layout) :
  use_union_layout_alg uls = Some ul →
  ∃ ot, use_op_alg uls = Some ot ∧ ot_layout ot = ul_layout ul.
Proof.
  intros (variant_lys & Halg & Hvariants)%use_union_layout_alg_inv.
  destruct uls as [un variants].
  exists (UntypedOp ul). split; last done.
  rewrite /use_op_alg. simpl. fold use_op_alg.
  apply bind_Some. exists ul. split; last done.
  unfold_layout_alg.
  apply bind_Some. fold use_layout_alg_def. exists variant_lys.
  split. { apply list_map_option_alt. eapply Forall2_impl; first done.
    rewrite /syn_type_has_layout. unfold_layout_alg.
    intros [] [] [-> ->]. done. }
  rewrite Halg. done.
Qed.

Lemma syn_type_has_layout_op_alg `{!LayoutAlg} st ly :
  syn_type_has_layout st ly →
  ∃ ot, use_op_alg st = Some ot ∧ ot_layout ot = ly.
Proof.
  induction st as [ it | | | | sn fields IH | | | st IH len | st IH | st IH | ly' | en IH | un variant_list IH | | ] using syn_type_strong_ind in ly |-*.
  - intros ->%syn_type_has_layout_int_inv.
    exists (IntOp it). split; last done. done.
  - intros ->%syn_type_has_layout_bool_inv.
    exists BoolOp. split; last done. done.
  - intros ->%syn_type_has_layout_ptr_inv.
    exists PtrOp. split; last done. done.
  - intros ->%syn_type_has_layout_fnptr_inv.
    exists FnPtrOp. split; last done. done.
  - intros Hsl.
    specialize (syn_type_has_layout_struct_inv _ _ _ _ Hsl) as (field_lys & sl & -> & Halg & Hfields).
    eapply (use_struct_layout_alg_op_alg (mk_sls _ _ _)); last done.
    eapply use_struct_layout_alg_Some; done.
  - intros ->%syn_type_has_layout_unit_inv. exists (StructOp unit_sl []). done.
  - intros ->%syn_type_has_layout_never_inv. exists NeverOp. done.
  - intros (ly' & Ha & -> & Hb)%syn_type_has_layout_array_inv.
    pose proof Ha as Ha_layout.
    apply IH in Ha as (ot & Hot & Hot_layout).
    exists (ArrayOp ot len). split; last by simpl; rewrite Hot_layout.
    apply use_op_alg_array with (ly := mk_array_layout ly' len); last done.
    rewrite /syn_type_has_layout in Ha_layout.
    unfold_layout_alg. rewrite /use_layout_alg_def/=. fold use_layout_alg_def.
    rewrite Ha_layout. simpl. rewrite decide_True; done.
  - intros Ha%syn_type_has_layout_unsafecell_inv. by apply IH.
  - intros Ha%syn_type_has_layout_untyped_inv.
    exists (UntypedOp ly). split; last done.
    rewrite /use_op_alg.
    apply bind_Some. eexists. split; last done.
    by apply syn_type_has_layout_untyped.
  - intros (<- & ? & ? & ?)%syn_type_has_layout_literal_inv.
    exists (UntypedOp ly). split; last done.
    rewrite /use_op_alg.
    apply bind_Some. eexists. split; last done.
    by apply syn_type_has_layout_literal.
  - intros (el & variant_lys & Halg & -> & Hvariants & Htag)%syn_type_has_layout_enum_inv.
    assert (∃ variant_ots, Forall2 (λ '(name, st) '(name', ot), name = name' ∧ use_op_alg st = Some ot) (raw_els_variants en) variant_ots) as (variant_ots & Hots).
    { clear -IH Hvariants.
      induction Hvariants as [|[name st] [name' ly] variants variant_lys [<- Hst] Hvariants IHvars] in IH |-*.
      { exists []. constructor. }
      inversion IH as [|?? Hst_IH IH']; subst.
      apply Hst_IH in Hst as (ot & Hot & <-).
      destruct (IHvars IH') as (ots & Hots).
      exists ((name, ot) :: ots). constructor; done. }
    exists (EnumOp el variant_ots (raw_els_tag_int en)). split; last done.
    rewrite /use_op_alg. fold use_op_alg.
    apply bind_Some. exists variant_lys. split.
    { apply list_map_option_alt. eapply Forall2_impl; first done.
      intros [] [] [-> Hst]. rewrite /syn_type_has_layout in Hst. by rewrite Hst. }
    rewrite Halg /=.
    apply bind_Some. exists variant_ots. split; last by rewrite decide_True.
    apply list_map_option_alt. eapply Forall2_impl; first done.
    intros [] [] [-> Hot]. by rewrite Hot.
    (* TODO: maybe we should at least make the read of the top-level struct typed? *)
    (*
    intros Halg%syn_type_has_layout_enum_inv.
    destruct Halg as (el & ul & variants & Hunion & Hstruct & -> & Hvariants).
    efeed pose proof (use_union_layout_alg_op_alg) as Ha.
    { eapply (use_union_layout_alg_Some (mk_uls _ _)); done. }
    destruct Ha as (ot & Hot & ?).
    efeed pose proof (use_struct_layout_alg_op_alg) as Ha.
    { eapply (use_struct_layout_alg_Some (mk_sls _ [(_, IntSynType tag_it); (_, UnionSynType _ _)])); last done.
      econstructor; simpl.
      { split; first done. eapply syn_type_has_layout_int; [done | apply it_size_bounded]. }
      econstructor; last constructor.
      split; first done.
      eapply syn_type_has_layout_union; done. }
    { simpl. econstructor.
      { intros ly (-> & Ha)%syn_type_has_layout_int_inv. eauto. }
      econstructor; last constructor.
      intros ly Hly.
      exists (UntypedOp ly). split; last done.
      rewrite /use_op_alg. apply bind_Some. rewrite Hly. eauto. }
    destruct Ha as (ot' & Hot' & <-).
    exists ot'. split; last done.
    simpl in Hot'.
    rewrite /use_op_alg.
     *)
  - intros (variant_lys & ul & -> & Halg & Hvariants)%syn_type_has_layout_union_inv.
    eapply (use_union_layout_alg_op_alg (mk_uls _ _ _)).
    eapply use_union_layout_alg_Some; done.
  - intros ->%syn_type_has_layout_char_inv.
    exists CharOp. split; last done. done.
  - intros ->%syn_type_has_layout_ref_inv.
    exists RefOp. split; last done. apply use_op_alg_ref.
Qed.

Lemma use_op_alg_wf `{!LayoutAlg} st ot :
  use_op_alg st = Some ot →
  op_type_wf ot.
Proof.
  induction st as [ | | | | sn fields repr IH | | | | | | | en IH | un variants repr IH | | ] in ot |-* using syn_type_strong_ind; rewrite /use_op_alg; simpl; fold use_op_alg; try naive_solver.
  - intros (sl & Halg & Hfields)%bind_Some.
    apply bind_Some in Hfields as (ots & Hots & [= <-]). simpl.
    apply use_struct_layout_alg_inv in Halg as (field_lys & Halg & Hfields).
    simpl in *. apply struct_layout_alg_has_fields in Halg.
    move : Halg. rewrite /sl_has_members. generalize (sl_members sl) as members => members. clear sl.
    intros ->.
    move: Hfields. generalize (named_fields members) as named => named Hfields.

    induction fields as [ | [name st] fields IH2] in named, ots, Hots, Hfields, IH |-*; simpl in *.
    { injection Hots as <-. apply Forall2_nil_inv_l in Hfields as ->. done. }
    simpl in IH. apply Forall_cons in IH as (Hot & IH).
    apply Forall2_cons_inv_l in Hfields as ([n' ly] & named' & [<- Hst] & Hfields & ->).
    apply bind_Some in Hots as (ots' & Hots & Hot1).
    apply bind_Some in Hot1 as (ot1 & Hot1 & [= <-]).
    simpl.
    split.
    + split; first by apply Hot.
      apply syn_type_has_layout_op_alg in Hst as (ot' & Hot' & <-).
      f_equiv. by eapply use_op_alg_inj.
    + apply IH2; done.
  - intros (ly0 & Halg & Hop)%bind_Some.
    apply bind_Some in Hop as (ot' & Hot & [= <-]). simpl.
    by eapply IHst.
  - intros (ly0 & Halg & [= <-])%bind_Some. done.
  - intros (ly0 & Halg & [= <-])%bind_Some. done.
  - intros (variant_lys & Hlys & Henum)%bind_Some.
    apply bind_Some in Henum as (el & Hel & Hots_tag).
    apply bind_Some in Hots_tag as (variant_ots & Hots & Htag_eq).
    case_decide as Htag; last done.
    injection Htag_eq as <-. simpl.
    rewrite /enum_tag_int_wf in Htag. destruct Htag as (Hnames & Hnodup_names & Hnodup_tags & Hrange).
    apply enum_layout_alg_has_variants in Hel as [Hel_tag Hvariants].
    apply list_map_option_alt in Hlys.
    apply list_map_option_alt in Hots.
    assert (Hlys_names : variant_lys.*1 = (raw_els_variants en).*1).
    { clear -Hlys. induction Hlys as [|[name st] [name' ly] variants variant_lys Hly Hlys IHlys]; simpl; first done.
      apply bind_Some in Hly as (ly' & Hly & [= <- <-]). by f_equal. }
    assert (Hots_names : variant_ots.*1 = (raw_els_variants en).*1).
    { clear -Hots. induction Hots as [|[name st] [name' ot'] variants variant_ots Hot Hots IHots]; simpl; first done.
      apply bind_Some in Hot as (ot'' & Hot & [= <- <-]). by f_equal. }
    split_and!.
    + rewrite /enum_variant_names -Hvariants Hots_names Hlys_names //.
    + rewrite /enum_variant_names -Hvariants Hnames Hlys_names //.
    + done.
    + change (Forall (λ tag : string * Z, int_elem_of_it tag.2 el.(el_tag_it)) (raw_els_tag_int en)).
      rewrite Hel_tag. eapply Forall_impl; first exact Hrange.
      intros [name tag] Htag'. exact Htag'.
    + rewrite -Forall_Forall_cb Forall_forall.
      intros [name ot'] Hin.
      apply list_elem_of_lookup_1 in Hin as [i Hot_lookup].
      eapply Forall2_lookup_r in Hots as ([name0 st] & Hraw_lookup & Hot); last done.
      apply bind_Some in Hot as (ot'' & Hot & [= <- <-]).
      eapply Forall2_lookup_l in Hlys as ([name1 ly] & Hvariant_lookup & Hly); last done.
      apply bind_Some in Hly as (ly' & Hly & [= <- <-]).
      exists ly'. split.
      { apply enum_variant_lookup_is_Some. rewrite -Hvariants. by eapply list_elem_of_lookup_2. }
      split.
      * rewrite Forall_forall in IH.
        exact (IH (name0, st) (list_elem_of_lookup_2 _ _ _ Hraw_lookup) ot'' Hot).
      * pose proof (use_op_alg_layout_alg _ _ Hot) as Hot_layout.
        rewrite /syn_type_has_layout in Hly. congruence.
  - intros (ly0 & Halg & [= <-])%bind_Some. done.
Qed.

Lemma use_struct_layout_alg_op_type_wf `{!LayoutAlg} sls sl ots :
  use_struct_layout_alg sls = Some sl →
  Forall2 (λ field ot, use_op_alg field.2 = Some ot) sls.(sls_fields) ots →
  op_type_wf (StructOp sl ots).
Proof.
  intros Hsl Hots. simpl. rewrite -Forall2_Forall2_cb.
  pose proof (struct_layout_spec_has_layout_alt_2 sls sl Hsl) as Hlys.
  induction Hlys as [| [name st] [name' ly] fields nfields [Hly <-] Hlys IH] in ots, Hots |-*.
  - apply Forall2_nil_inv_l in Hots as ->. constructor.
  - apply Forall2_cons_inv_l in Hots as (ot & ots' & Hot & Hots & ->).
    constructor; last by apply IH.
    split; first by eapply use_op_alg_wf.
    pose proof (use_op_alg_layout_alg _ _ Hot) as Hly'. simpl in Hly'. congruence.
Qed.

(** A relation requirement size equality, without caring about the alignment. *)
Definition syn_type_size_eq `{!LayoutAlg} st1 st2 :=
  ∀ ly1, syn_type_has_layout st1 ly1 → ∃ ly2, syn_type_has_layout st2 ly2 ∧ ly_size ly1 = ly_size ly2.
Global Instance syn_type_size_eq_refl `{!LayoutAlg} :
  Reflexive syn_type_size_eq.
Proof.
  intros st ly1 Hst. exists ly1. done.
Qed.
Global Instance syn_type_size_eq_trans `{!LayoutAlg} :
  Transitive syn_type_size_eq.
Proof.
  intros st1 st2 st3 Heq1 Heq2.
  intros ly1 Hst1.
  apply Heq1 in Hst1 as (ly2 & Hst2 & ?).
  apply Heq2 in Hst2 as (ly3 & Hst3 & ?).
  eexists. split; first done. lia.
Qed.
(*
Global Instance syn_type_size_eq_sym `{!LayoutAlg} : Symmetric syn_type_size_eq.
Proof.
  intros st1 st2 Hsz ly1 Halg1.

  exists
  symmetry. by eapply Hsz.
Qed.
 *)

Lemma syn_type_size_eq_untyped_r `{!LayoutAlg} st1 :
  syn_type_size_eq st1 (UntypedSynType st1).
Proof.
  intros ly1 Hst1.
  exists ly1. split; last done.
  by apply syn_type_has_layout_untyped.
Qed.
Lemma syn_type_size_eq_untyped_l `{!LayoutAlg} st1 :
  syn_type_size_eq (UntypedSynType st1) st1.
Proof.
  intros ly1 Hst1.
  apply syn_type_has_layout_untyped_inv in Hst1.
  eauto.
Qed.

Lemma syn_type_size_eq_use `{!LayoutAlg} st1 st2 ly1 ly2 :
  syn_type_size_eq st1 st2 →
  syn_type_has_layout st1 ly1 →
  syn_type_has_layout st2 ly2 →
  ly_size ly1 = ly_size ly2.
Proof.
  intros Heq Hst1 Hst2. apply Heq in Hst1 as (ly3 & Hst1 & ->).
  f_equiv. by eapply syn_type_has_layout_inj.
Qed.
Lemma syn_type_size_eq_prove `{!LayoutAlg} st1 st2 ly1 ly2 :
  syn_type_has_layout st1 ly1 →
  syn_type_has_layout st2 ly2 →
  ly_size ly1 = ly_size ly2 →
  syn_type_size_eq st1 st2.
Proof.
  intros ???.
  intros ly3 ?. assert (ly3 = ly1) as -> by by eapply syn_type_has_layout_inj.
  eauto.
Qed.

(** A stronger relation requiring layout equality *)
Definition syn_type_compat `{!LayoutAlg} (st1 st2 : syn_type) :=
  ∀ ly,
  syn_type_has_layout st1 ly →
  syn_type_has_layout st2 ly.

Global Instance syn_type_compat_refl `{!LayoutAlg} :
  Reflexive syn_type_compat.
Proof.
  intros ? ??. done.
Qed.

Global Instance syn_type_compat_trans `{!LayoutAlg} : Transitive syn_type_compat.
Proof.
  intros st1 st2 st3.
  intros Hcompat1 Hcompat2 ly Hst1.
  apply Hcompat1 in Hst1. apply Hcompat2 in Hst1.
  done.
Qed.

Lemma syn_type_compat_use `{!LayoutAlg} st1 st2 ly1 ly2 :
  syn_type_compat st1 st2 →
  syn_type_has_layout st1 ly1 →
  syn_type_has_layout st2 ly2 →
  ly1 = ly2.
Proof.
  intros Hcompat Hst1 Hst2.
  apply Hcompat in Hst1.
  assert (ly1 = ly2) as <- by by eapply syn_type_has_layout_inj.
  done.
Qed.

Lemma syn_type_compat_untyped_l `{!LayoutAlg} st1 st2 :
  syn_type_compat st1 st2 →
  syn_type_compat (UntypedSynType st1) st2.
Proof.
  intros Hcomp ly Hst.
  apply syn_type_has_layout_untyped_inv in Hst.
  by apply Hcomp in Hst.
Qed.
Lemma syn_type_compat_untyped_r `{!LayoutAlg} st1 st2 :
  syn_type_compat st1 st2 →
  syn_type_compat st1 (UntypedSynType st2).
Proof.
  intros Hcomp ly Hst.
  apply Hcomp in Hst.
  by apply syn_type_has_layout_untyped.
Qed.

Lemma syn_type_compat_array `{!LayoutAlg} st1 st2 n1 n2 :
  n1 = n2 →
  syn_type_compat st1 st2 →
  syn_type_compat (ArraySynType st1 n1) (ArraySynType st2 n2).
Proof.
  intros -> Hcomp.
  intros ly Halg. apply syn_type_has_layout_array_inv in Halg as (ly' & Halg1 & -> & Hsz).
  apply Hcomp in Halg1.
  eapply syn_type_has_layout_array; first done; first done.
  move: Hsz. rewrite ly_size_mk_array_layout.
  lia.
Qed.


Lemma syn_type_compat_size_eq `{!LayoutAlg} st1 st2 :
  syn_type_compat st1 st2 →
  syn_type_size_eq st1 st2.
Proof.
  intros Hcomp.
  intros ly1' Hly1'.
  apply Hcomp in Hly1'.
  eauto.
Qed.

(** Existential versions *)
Definition syn_type_is_layoutable `{!LayoutAlg} (st : syn_type) : Prop :=
  is_Some (use_layout_alg st).
Definition struct_layout_spec_is_layoutable `{!LayoutAlg} (sls : struct_layout_spec) : Prop :=
  is_Some (use_struct_layout_alg sls).
Definition union_layout_spec_is_layoutable `{!LayoutAlg} (uls : union_layout_spec) : Prop :=
  is_Some (use_union_layout_alg uls).
Definition enum_layout_spec_is_layoutable `{!LayoutAlg} (els : enum_layout_spec) : Prop :=
  is_Some (use_enum_layout_alg els).
