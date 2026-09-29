From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops.

Definition Add_AddOpDefined_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → Prop).
Definition Add_AddOp_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Add_AddOpDefined: (Add_AddOpDefined_sig (Self_rt) (Rhs_rt) (Output_rt))) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → (RT_xt (Output_rt))).
Record Add_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : Type := mk_Add_spec_attrs {
  Add_AddOpDefined  : (Add_AddOpDefined_sig (Self_rt) (Rhs_rt) (Output_rt));
  Add_AddOp  : (Add_AddOp_sig (Self_rt) (Rhs_rt) (Output_rt) (Add_AddOpDefined));
}.
#[global] Arguments Add_spec_attrs : clear implicits.

#[global] Arguments Add_spec_attrs {_ _}.

#[global] Arguments mk_Add_spec_attrs  {_} {_} {_} {_} {_}.


Definition AddAssign_AddAssignOpDefined_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → Prop).
Definition AddAssign_AddAssignOp_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (AddAssign_AddAssignOpDefined: (AddAssign_AddAssignOpDefined_sig (Self_rt) (Rhs_rt))) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → (RT_xt (Self_rt))).
Record AddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_AddAssign_spec_attrs {
  AddAssign_AddAssignOpDefined  : (AddAssign_AddAssignOpDefined_sig (Self_rt) (Rhs_rt));
  AddAssign_AddAssignOp  : (AddAssign_AddAssignOp_sig (Self_rt) (Rhs_rt) (AddAssign_AddAssignOpDefined));
}.
#[global] Arguments AddAssign_spec_attrs : clear implicits.

#[global] Arguments AddAssign_spec_attrs {_ _}.

#[global] Arguments mk_AddAssign_spec_attrs  {_} {_} {_} {_}.


Definition Deref_DerefInto_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Target_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Target_rt))).
Record Deref_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Target_rt : !RT} : Type := mk_Deref_spec_attrs {
  Deref_DerefInto  : (Deref_DerefInto_sig (Self_rt) (Target_rt));
}.
#[global] Arguments Deref_spec_attrs : clear implicits.

#[global] Arguments Deref_spec_attrs {_ _}.

#[global] Arguments mk_Deref_spec_attrs  {_} {_} {_} {_}.


Definition Mul_MulOpDefined_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → Prop).
Definition Mul_MulOp_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Mul_MulOpDefined: (Mul_MulOpDefined_sig (Self_rt) (Rhs_rt) (Output_rt))) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → (RT_xt (Output_rt))).
Record Mul_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : Type := mk_Mul_spec_attrs {
  Mul_MulOpDefined  : (Mul_MulOpDefined_sig (Self_rt) (Rhs_rt) (Output_rt));
  Mul_MulOp  : (Mul_MulOp_sig (Self_rt) (Rhs_rt) (Output_rt) (Mul_MulOpDefined));
}.
#[global] Arguments Mul_spec_attrs : clear implicits.

#[global] Arguments Mul_spec_attrs {_ _}.

#[global] Arguments mk_Mul_spec_attrs  {_} {_} {_} {_} {_}.


Definition MulAssign_MulAssignOpDefined_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → Prop).
Definition MulAssign_MulAssignOp_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (MulAssign_MulAssignOpDefined: (MulAssign_MulAssignOpDefined_sig (Self_rt) (Rhs_rt))) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → (RT_xt (Self_rt))).
Record MulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_MulAssign_spec_attrs {
  MulAssign_MulAssignOpDefined  : (MulAssign_MulAssignOpDefined_sig (Self_rt) (Rhs_rt));
  MulAssign_MulAssignOp  : (MulAssign_MulAssignOp_sig (Self_rt) (Rhs_rt) (MulAssign_MulAssignOpDefined));
}.
#[global] Arguments MulAssign_spec_attrs : clear implicits.

#[global] Arguments MulAssign_spec_attrs {_ _}.

#[global] Arguments mk_MulAssign_spec_attrs  {_} {_} {_} {_}.


Definition Sub_SubOpDefined_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → Prop).
Definition Sub_SubOp_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Sub_SubOpDefined: (Sub_SubOpDefined_sig (Self_rt) (Rhs_rt) (Output_rt))) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → (RT_xt (Output_rt))).
Record Sub_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : Type := mk_Sub_spec_attrs {
  Sub_SubOpDefined  : (Sub_SubOpDefined_sig (Self_rt) (Rhs_rt) (Output_rt));
  Sub_SubOp  : (Sub_SubOp_sig (Self_rt) (Rhs_rt) (Output_rt) (Sub_SubOpDefined));
}.
#[global] Arguments Sub_spec_attrs : clear implicits.

#[global] Arguments Sub_spec_attrs {_ _}.

#[global] Arguments mk_Sub_spec_attrs  {_} {_} {_} {_} {_}.


Definition SubAssign_SubAssignOpDefined_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → Prop).
Definition SubAssign_SubAssignOp_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (SubAssign_SubAssignOpDefined: (SubAssign_SubAssignOpDefined_sig (Self_rt) (Rhs_rt))) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → (RT_xt (Self_rt))).
Record SubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_SubAssign_spec_attrs {
  SubAssign_SubAssignOpDefined  : (SubAssign_SubAssignOpDefined_sig (Self_rt) (Rhs_rt));
  SubAssign_SubAssignOp  : (SubAssign_SubAssignOp_sig (Self_rt) (Rhs_rt) (SubAssign_SubAssignOpDefined));
}.
#[global] Arguments SubAssign_spec_attrs : clear implicits.

#[global] Arguments SubAssign_spec_attrs {_ _}.

#[global] Arguments mk_SubAssign_spec_attrs  {_} {_} {_} {_}.


Definition DerefMut_DerefMutInject_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Deref_Self_Target_rt: RT) (Deref_Self_spec_attrs: (Deref_spec_attrs (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt) )) :=
  ((RT_xt (Self_rt)) → gname → (Self_rt)).
Record DerefMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Deref_Self_Target_rt : !RT} `{Deref_Self_spec_attrs : !(Deref_spec_attrs (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt) )} : Type := mk_DerefMut_spec_attrs {
  DerefMut_DerefMutInject  : (DerefMut_DerefMutInject_sig (Self_rt) (Deref_Self_Target_rt) (Deref_Self_spec_attrs));
}.
#[global] Arguments DerefMut_spec_attrs : clear implicits.

#[global] Arguments DerefMut_spec_attrs {_ _}.

#[global] Arguments mk_DerefMut_spec_attrs  {_} {_} {_} {_} {_}.


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFTasDeref_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Deref_spec_attrs ((place_rfnRT (T_rt))) ((T_rt)))) :=
  {|
    Deref_DerefInto  :=
      (id) : ((Deref_DerefInto_sig ((place_rfnRT (T_rt))) ((T_rt))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi128asAddREFai128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i128) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi128asAddi128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i128) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi128asMulREFai128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i128) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi128asMuli128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i128) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi128asSubREFai128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i128) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi128asSubi128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i128) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi16asAddREFai16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i16) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi16asAddi16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i16) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi16asMulREFai16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i16) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi16asMuli16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i16) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi16asSubREFai16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i16) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi16asSubi16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i16) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi32asAddREFai32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i32) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi32asAddi32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i32) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi32asMulREFai32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i32) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi32asMuli32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i32) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi32asSubREFai32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i32) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi32asSubi32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i32) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi64asAddREFai64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i64) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi64asAddi64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i64) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi64asMulREFai64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i64) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi64asMuli64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i64) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi64asSubREFai64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i64) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi64asSubi64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i64) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi8asAddREFai8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i8) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi8asAddi8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i8) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi8asMulREFai8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i8) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi8asMuli8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i8) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi8asSubREFai8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i8) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFi8asSubi8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i8) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFisizeasAddREFaisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ isize) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFisizeasAddisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ isize) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFisizeasMulREFaisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ isize) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFisizeasMulisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ isize) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFisizeasSubREFaisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ isize) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFisizeasSubisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ isize) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFmutTasDeref_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Deref_spec_attrs (((place_rfnRT (T_rt)) * gname)%type) ((T_rt)))) :=
  {|
    Deref_DerefInto  :=
      (λ x, x.cur) : ((Deref_DerefInto_sig (((place_rfnRT (T_rt)) * gname)%type) ((T_rt))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu128asAddREFau128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u128) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu128asAddu128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u128) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu128asMulREFau128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u128) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu128asMulu128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u128) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu128asSubREFau128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u128) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu128asSubu128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u128) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu16asAddREFau16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u16) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu16asAddu16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u16) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu16asMulREFau16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u16) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu16asMulu16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u16) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu16asSubREFau16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u16) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu16asSubu16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u16) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu32asAddREFau32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u32) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu32asAddu32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u32) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu32asMulREFau32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u32) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu32asMulu32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u32) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu32asSubREFau32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u32) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu32asSubu32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u32) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu64asAddREFau64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u64) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu64asAddu64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u64) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu64asMulREFau64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u64) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu64asMulu64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u64) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu64asSubREFau64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u64) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu64asSubu64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u64) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu8asAddREFau8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u8) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu8asAddu8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u8) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu8asMulREFau8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u8) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu8asMulu8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u8) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu8asSubREFau8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u8) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFu8asSubu8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u8) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFusizeasAddREFausize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ usize) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFusizeasAddusize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ usize) : ((Add_AddOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFusizeasMulREFausize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ usize) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFusizeasMulusize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ usize) : ((Mul_MulOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFusizeasSubREFausize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ usize) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFusizeasSubusize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs ((place_rfnRT Z)) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ usize) : ((Sub_SubOpDefined_sig ((place_rfnRT Z)) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig ((place_rfnRT Z)) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asAddREFai128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i128) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i128) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asAddAssignREFi128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i128) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i128) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asMulREFai128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i128) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i128) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asMulAssignREFi128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i128) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i128) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asSubREFai128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i128) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i128) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asSubAssignREFi128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i128) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i128) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asAddREFai16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i16) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i16) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asAddAssignREFi16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i16) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i16) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asMulREFai16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i16) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i16) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asMulAssignREFi16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i16) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i16) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asSubREFai16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i16) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i16) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asSubAssignREFi16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i16) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i16) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asAddREFai32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i32) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i32) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asAddAssignREFi32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i32) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i32) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asMulREFai32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i32) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i32) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asMulAssignREFi32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i32) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i32) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asSubREFai32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i32) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i32) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asSubAssignREFi32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i32) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i32) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asAddREFai64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i64) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i64) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asAddAssignREFi64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i64) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i64) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asMulREFai64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i64) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i64) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asMulAssignREFi64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i64) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i64) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asSubREFai64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i64) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i64) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asSubAssignREFi64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i64) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i64) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asAddREFai8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i8) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ i8) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asAddAssignREFi8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i8) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ i8) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asMulREFai8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i8) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ i8) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asMulAssignREFi8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i8) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ i8) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asSubREFai8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i8) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ i8) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asSubAssignREFi8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i8) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ i8) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasAddREFaisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ isize) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ isize) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasAddAssignREFisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ isize) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ isize) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasMulREFaisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ isize) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ isize) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasMulAssignREFisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ isize) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ isize) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasSubREFaisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ isize) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ isize) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasSubAssignREFisize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ isize) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ isize) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asAddREFau128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u128) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u128) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asAddAssignREFu128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u128) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u128) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asMulREFau128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u128) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u128) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asMulAssignREFu128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u128) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u128) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asSubREFau128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u128) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u128) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asSubAssignREFu128_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u128) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u128) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asAddREFau16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u16) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u16) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asAddAssignREFu16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u16) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u16) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asMulREFau16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u16) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u16) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asMulAssignREFu16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u16) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u16) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asSubREFau16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u16) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u16) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asSubAssignREFu16_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u16) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u16) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asAddREFau32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u32) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u32) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asAddAssignREFu32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u32) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u32) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asMulREFau32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u32) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u32) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asMulAssignREFu32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u32) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u32) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asSubREFau32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u32) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u32) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asSubAssignREFu32_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u32) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u32) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asAddREFau64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u64) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u64) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asAddAssignREFu64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u64) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u64) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asMulREFau64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u64) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u64) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asMulAssignREFu64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u64) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u64) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asSubREFau64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u64) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u64) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asSubAssignREFu64_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u64) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u64) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asAddREFau8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u8) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ u8) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asAddAssignREFu8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u8) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ u8) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asMulREFau8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u8) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ u8) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asMulAssignREFu8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u8) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ u8) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asSubREFau8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u8) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ u8) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asSubAssignREFu8_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u8) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ u8) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasAddREFausize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ usize) : ((Add_AddOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasAdd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Add_spec_attrs (Z) (Z) (Z))) :=
  {|
    Add_AddOpDefined  :=
      (λ a b, (a + b) ∈ usize) : ((Add_AddOpDefined_sig (Z) (Z) (Z)));
    Add_AddOp  :=
      (λ a b : Z, a + b) : ((Add_AddOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasAddAssignREFusize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ usize) : ((AddAssign_AddAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasAddAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((AddAssign_spec_attrs (Z) (Z))) :=
  {|
    AddAssign_AddAssignOpDefined  :=
      (λ a b, (a + b) ∈ usize) : ((AddAssign_AddAssignOpDefined_sig (Z) (Z)));
    AddAssign_AddAssignOp  :=
      (λ a b : Z, a + b) : ((AddAssign_AddAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasMulREFausize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ usize) : ((Mul_MulOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasMul_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Mul_spec_attrs (Z) (Z) (Z))) :=
  {|
    Mul_MulOpDefined  :=
      (λ a b, (a * b) ∈ usize) : ((Mul_MulOpDefined_sig (Z) (Z) (Z)));
    Mul_MulOp  :=
      (λ a b : Z, a * b) : ((Mul_MulOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasMulAssignREFusize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ usize) : ((MulAssign_MulAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasMulAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((MulAssign_spec_attrs (Z) (Z))) :=
  {|
    MulAssign_MulAssignOpDefined  :=
      (λ a b, (a * b) ∈ usize) : ((MulAssign_MulAssignOpDefined_sig (Z) (Z)));
    MulAssign_MulAssignOp  :=
      (λ a b : Z, a * b) : ((MulAssign_MulAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasSubREFausize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) ((place_rfnRT Z)) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ usize) : ((Sub_SubOpDefined_sig (Z) ((place_rfnRT Z)) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) ((place_rfnRT Z)) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasSub_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Sub_spec_attrs (Z) (Z) (Z))) :=
  {|
    Sub_SubOpDefined  :=
      (λ a b, (a - b) ∈ usize) : ((Sub_SubOpDefined_sig (Z) (Z) (Z)));
    Sub_SubOp  :=
      (λ a b : Z, a - b) : ((Sub_SubOp_sig (Z) (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasSubAssignREFusize_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) ((place_rfnRT Z)))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ usize) : ((SubAssign_SubAssignOpDefined_sig (Z) ((place_rfnRT Z))));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) ((place_rfnRT Z)) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasSubAssign_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((SubAssign_spec_attrs (Z) (Z))) :=
  {|
    SubAssign_SubAssignOpDefined  :=
      (λ a b, (a - b) ∈ usize) : ((SubAssign_SubAssignOpDefined_sig (Z) (Z)));
    SubAssign_SubAssignOp  :=
      (λ a b : Z, a - b) : ((SubAssign_SubAssignOp_sig (Z) (Z) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFmutTasDerefMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((DerefMut_spec_attrs (((place_rfnRT (T_rt)) * gname)%type) ((T_rt)) ((REFmutTasDeref_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))))) :=
  {|
    DerefMut_DerefMutInject  :=
      (λ old x, (👻 x, old.ghost)) : ((DerefMut_DerefMutInject_sig (((place_rfnRT (T_rt)) * gname)%type) ((T_rt)) ((REFmutTasDeref_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)))));
  |}
.


End attrs.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Record Add_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : Type := mk_Add_spec {
  Add_add_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments Add_spec : clear implicits.

#[global] Arguments Add_spec {_ _}.


Record AddAssign_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_AddAssign_spec {
  AddAssign_add_assign_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments AddAssign_spec : clear implicits.

#[global] Arguments AddAssign_spec {_ _}.


Record Deref_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Target_rt : !RT} : Type := mk_Deref_spec {
  Deref_deref_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments Deref_spec : clear implicits.

#[global] Arguments Deref_spec {_ _}.


Record Mul_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : Type := mk_Mul_spec {
  Mul_mul_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments Mul_spec : clear implicits.

#[global] Arguments Mul_spec {_ _}.


Record MulAssign_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_MulAssign_spec {
  MulAssign_mul_assign_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments MulAssign_spec : clear implicits.

#[global] Arguments MulAssign_spec {_ _}.


Record Sub_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : Type := mk_Sub_spec {
  Sub_sub_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments Sub_spec : clear implicits.

#[global] Arguments Sub_spec {_ _}.


Record SubAssign_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_SubAssign_spec {
  SubAssign_sub_assign_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments SubAssign_spec : clear implicits.

#[global] Arguments SubAssign_spec {_ _}.


Record DerefMut_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Deref_Self_Target_rt : !RT} : Type := mk_DerefMut_spec {
  DerefMut_deref_mut_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments DerefMut_spec : clear implicits.

#[global] Arguments DerefMut_spec {_ _}.


Section Add.
Context `{RRGS : !refinedrustGS Σ}.
Definition Add_spec_incl `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} (spec1: ((Add_spec (Self_rt) (Rhs_rt) (Output_rt)))) (spec2: ((Add_spec (Self_rt) (Rhs_rt) (Output_rt)))) : Prop :=
  ((function_subtype (spec1.(Add_add_spec)) (spec2.(Add_add_spec)))).
Instance Add_spec_incl_preorder `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : (PreOrder (Add_spec_incl (Self_rt := Self_rt) (Rhs_rt := Rhs_rt) (Output_rt := Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Add_spec `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : (ScopeBindable ((Add_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Add_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
      {|
        Add_add_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Add_add_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Add_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
      {|
        Add_add_spec  :=
          (scope_add_elctx (E) (s.(Add_add_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Add_spec.

Definition Add_add_base_spec (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_SelfasAddRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (Add_Self_Rhs_spec_attrs: (Add_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, rhs :@: Rhs_ty;
      (* precondition. *) (λ π : thread_id, (⌜(Add_Self_Rhs_spec_attrs.(Add_AddOpDefined) self rhs)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Add_Self_Rhs_spec_attrs.(Add_AddOp) self rhs @ Output_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Add_base_spec (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_SelfasAddRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (_ATTRS: ((Add_spec_attrs ((Self_rt)) ((Rhs_rt)) ((Output_rt))))) : (spec_with _ _ (Add_spec ((Self_rt)) ((Rhs_rt)) ((Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([Self_rt; Rhs_rt; Output_rt] : list RT), {|
      Add_add_spec  :=
        (Add_add_base_spec ((Self_rt)) ((Rhs_rt)) ((Output_rt)) (Self_st) (Rhs_st) (Output_st)) DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs DropGlue_SelfasAddRhs_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty <TY> Output_ty : (spec_with 0 [] fn_spec);
    |}
.

End Add.

Section AddAssign.
Context `{RRGS : !refinedrustGS Σ}.
Definition AddAssign_spec_incl `{Self_rt : !RT} `{Rhs_rt : !RT} (spec1: ((AddAssign_spec (Self_rt) (Rhs_rt)))) (spec2: ((AddAssign_spec (Self_rt) (Rhs_rt)))) : Prop :=
  ((function_subtype (spec1.(AddAssign_add_assign_spec)) (spec2.(AddAssign_add_assign_spec)))).
Instance AddAssign_spec_incl_preorder `{Self_rt : !RT} `{Rhs_rt : !RT} : (PreOrder (AddAssign_spec_incl (Self_rt := Self_rt) (Rhs_rt := Rhs_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_AddAssign_spec `{Self_rt : !RT} `{Rhs_rt : !RT} : (ScopeBindable ((AddAssign_spec (Self_rt) (Rhs_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((AddAssign_spec (Self_rt) (Rhs_rt)))) :=
      {|
        AddAssign_add_assign_spec  :=
          (scope_add_typarams (rts) (tys) (s.(AddAssign_add_assign_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((AddAssign_spec (Self_rt) (Rhs_rt)))) :=
      {|
        AddAssign_add_assign_spec  :=
          (scope_add_elctx (E) (s.(AddAssign_add_assign_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_AddAssign_spec.

Definition AddAssign_add_assign_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (AddAssign_Self_Rhs_spec_attrs: (AddAssign_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), rhs :@: Rhs_ty;
      (* precondition. *) (λ π : thread_id, (⌜(AddAssign_Self_Rhs_spec_attrs.(AddAssign_AddAssignOpDefined) self.cur rhs)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost (AddAssign_Self_Rhs_spec_attrs.(AddAssign_AddAssignOp) self.cur rhs))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition AddAssign_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (_ATTRS: ((AddAssign_spec_attrs ((Self_rt)) ((Rhs_rt))))) : (spec_with _ _ (AddAssign_spec ((Self_rt)) ((Rhs_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), {|
      AddAssign_add_assign_spec  :=
        (AddAssign_add_assign_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 1 [] fn_spec);
    |}
.

End AddAssign.

Section Deref.
Context `{RRGS : !refinedrustGS Σ}.
Definition Deref_spec_incl `{Self_rt : !RT} `{Target_rt : !RT} (spec1: ((Deref_spec (Self_rt) (Target_rt)))) (spec2: ((Deref_spec (Self_rt) (Target_rt)))) : Prop :=
  ((function_subtype (spec1.(Deref_deref_spec)) (spec2.(Deref_deref_spec)))).
Instance Deref_spec_incl_preorder `{Self_rt : !RT} `{Target_rt : !RT} : (PreOrder (Deref_spec_incl (Self_rt := Self_rt) (Target_rt := Target_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Deref_spec `{Self_rt : !RT} `{Target_rt : !RT} : (ScopeBindable ((Deref_spec (Self_rt) (Target_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Deref_spec (Self_rt) (Target_rt)))) :=
      {|
        Deref_deref_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Deref_deref_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Deref_spec (Self_rt) (Target_rt)))) :=
      {|
        Deref_deref_spec  :=
          (scope_add_elctx (E) (s.(Deref_deref_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Deref_spec.

Definition Deref_deref_base_spec (Self_rt: RT) (Target_rt: RT) (Self_st: syn_type) (Target_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_SelfasDeref_Target_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Target_rt) )) (Deref_Self_spec_attrs: (Deref_spec_attrs (RRGS:=RRGS) (Self_rt) (Target_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Target_ty]) : ([(Self_rt, Self_st); (Target_rt, Target_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Deref_Self_spec_attrs.(Deref_DerefInto) self @ (shr_ref ulft_1 Target_ty);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Deref_base_spec (Self_rt: RT) (Target_rt: RT) (Self_st: syn_type) (Target_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_SelfasDeref_Target_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Target_rt) )) (_ATTRS: ((Deref_spec_attrs ((Self_rt)) ((Target_rt))))) : (spec_with _ _ (Deref_spec ((Self_rt)) ((Target_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Target_ty]) : ([Self_rt; Target_rt] : list RT), {|
      Deref_deref_spec  :=
        (Deref_deref_base_spec ((Self_rt)) ((Target_rt)) (Self_st) (Target_st)) DropGlue_Self_spec_attrs DropGlue_SelfasDeref_Target_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Target_ty : (spec_with 1 [] fn_spec);
    |}
.

End Deref.

Section Mul.
Context `{RRGS : !refinedrustGS Σ}.
Definition Mul_spec_incl `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} (spec1: ((Mul_spec (Self_rt) (Rhs_rt) (Output_rt)))) (spec2: ((Mul_spec (Self_rt) (Rhs_rt) (Output_rt)))) : Prop :=
  ((function_subtype (spec1.(Mul_mul_spec)) (spec2.(Mul_mul_spec)))).
Instance Mul_spec_incl_preorder `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : (PreOrder (Mul_spec_incl (Self_rt := Self_rt) (Rhs_rt := Rhs_rt) (Output_rt := Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Mul_spec `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : (ScopeBindable ((Mul_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Mul_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
      {|
        Mul_mul_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Mul_mul_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Mul_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
      {|
        Mul_mul_spec  :=
          (scope_add_elctx (E) (s.(Mul_mul_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Mul_spec.

Definition Mul_mul_base_spec (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_SelfasMulRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (Mul_Self_Rhs_spec_attrs: (Mul_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, rhs :@: Rhs_ty;
      (* precondition. *) (λ π : thread_id, (⌜(Mul_Self_Rhs_spec_attrs.(Mul_MulOpDefined) self rhs)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Mul_Self_Rhs_spec_attrs.(Mul_MulOp) self rhs @ Output_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Mul_base_spec (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_SelfasMulRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (_ATTRS: ((Mul_spec_attrs ((Self_rt)) ((Rhs_rt)) ((Output_rt))))) : (spec_with _ _ (Mul_spec ((Self_rt)) ((Rhs_rt)) ((Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([Self_rt; Rhs_rt; Output_rt] : list RT), {|
      Mul_mul_spec  :=
        (Mul_mul_base_spec ((Self_rt)) ((Rhs_rt)) ((Output_rt)) (Self_st) (Rhs_st) (Output_st)) DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs DropGlue_SelfasMulRhs_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty <TY> Output_ty : (spec_with 0 [] fn_spec);
    |}
.

End Mul.

Section MulAssign.
Context `{RRGS : !refinedrustGS Σ}.
Definition MulAssign_spec_incl `{Self_rt : !RT} `{Rhs_rt : !RT} (spec1: ((MulAssign_spec (Self_rt) (Rhs_rt)))) (spec2: ((MulAssign_spec (Self_rt) (Rhs_rt)))) : Prop :=
  ((function_subtype (spec1.(MulAssign_mul_assign_spec)) (spec2.(MulAssign_mul_assign_spec)))).
Instance MulAssign_spec_incl_preorder `{Self_rt : !RT} `{Rhs_rt : !RT} : (PreOrder (MulAssign_spec_incl (Self_rt := Self_rt) (Rhs_rt := Rhs_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_MulAssign_spec `{Self_rt : !RT} `{Rhs_rt : !RT} : (ScopeBindable ((MulAssign_spec (Self_rt) (Rhs_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((MulAssign_spec (Self_rt) (Rhs_rt)))) :=
      {|
        MulAssign_mul_assign_spec  :=
          (scope_add_typarams (rts) (tys) (s.(MulAssign_mul_assign_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((MulAssign_spec (Self_rt) (Rhs_rt)))) :=
      {|
        MulAssign_mul_assign_spec  :=
          (scope_add_elctx (E) (s.(MulAssign_mul_assign_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_MulAssign_spec.

Definition MulAssign_mul_assign_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (MulAssign_Self_Rhs_spec_attrs: (MulAssign_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), rhs :@: Rhs_ty;
      (* precondition. *) (λ π : thread_id, (⌜(MulAssign_Self_Rhs_spec_attrs.(MulAssign_MulAssignOpDefined) self.cur rhs)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost (MulAssign_Self_Rhs_spec_attrs.(MulAssign_MulAssignOp) self.cur rhs))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition MulAssign_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (_ATTRS: ((MulAssign_spec_attrs ((Self_rt)) ((Rhs_rt))))) : (spec_with _ _ (MulAssign_spec ((Self_rt)) ((Rhs_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), {|
      MulAssign_mul_assign_spec  :=
        (MulAssign_mul_assign_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 1 [] fn_spec);
    |}
.

End MulAssign.

Section Sub.
Context `{RRGS : !refinedrustGS Σ}.
Definition Sub_spec_incl `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} (spec1: ((Sub_spec (Self_rt) (Rhs_rt) (Output_rt)))) (spec2: ((Sub_spec (Self_rt) (Rhs_rt) (Output_rt)))) : Prop :=
  ((function_subtype (spec1.(Sub_sub_spec)) (spec2.(Sub_sub_spec)))).
Instance Sub_spec_incl_preorder `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : (PreOrder (Sub_spec_incl (Self_rt := Self_rt) (Rhs_rt := Rhs_rt) (Output_rt := Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Sub_spec `{Self_rt : !RT} `{Rhs_rt : !RT} `{Output_rt : !RT} : (ScopeBindable ((Sub_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Sub_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
      {|
        Sub_sub_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Sub_sub_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Sub_spec (Self_rt) (Rhs_rt) (Output_rt)))) :=
      {|
        Sub_sub_spec  :=
          (scope_add_elctx (E) (s.(Sub_sub_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Sub_spec.

Definition Sub_sub_base_spec (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_SelfasSubRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (Sub_Self_Rhs_spec_attrs: (Sub_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, rhs :@: Rhs_ty;
      (* precondition. *) (λ π : thread_id, (⌜(Sub_Self_Rhs_spec_attrs.(Sub_SubOpDefined) self rhs)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Sub_Self_Rhs_spec_attrs.(Sub_SubOp) self rhs @ Output_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Sub_base_spec (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_SelfasSubRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (_ATTRS: ((Sub_spec_attrs ((Self_rt)) ((Rhs_rt)) ((Output_rt))))) : (spec_with _ _ (Sub_spec ((Self_rt)) ((Rhs_rt)) ((Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([Self_rt; Rhs_rt; Output_rt] : list RT), {|
      Sub_sub_spec  :=
        (Sub_sub_base_spec ((Self_rt)) ((Rhs_rt)) ((Output_rt)) (Self_st) (Rhs_st) (Output_st)) DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs DropGlue_SelfasSubRhs_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty <TY> Output_ty : (spec_with 0 [] fn_spec);
    |}
.

End Sub.

Section SubAssign.
Context `{RRGS : !refinedrustGS Σ}.
Definition SubAssign_spec_incl `{Self_rt : !RT} `{Rhs_rt : !RT} (spec1: ((SubAssign_spec (Self_rt) (Rhs_rt)))) (spec2: ((SubAssign_spec (Self_rt) (Rhs_rt)))) : Prop :=
  ((function_subtype (spec1.(SubAssign_sub_assign_spec)) (spec2.(SubAssign_sub_assign_spec)))).
Instance SubAssign_spec_incl_preorder `{Self_rt : !RT} `{Rhs_rt : !RT} : (PreOrder (SubAssign_spec_incl (Self_rt := Self_rt) (Rhs_rt := Rhs_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_SubAssign_spec `{Self_rt : !RT} `{Rhs_rt : !RT} : (ScopeBindable ((SubAssign_spec (Self_rt) (Rhs_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((SubAssign_spec (Self_rt) (Rhs_rt)))) :=
      {|
        SubAssign_sub_assign_spec  :=
          (scope_add_typarams (rts) (tys) (s.(SubAssign_sub_assign_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((SubAssign_spec (Self_rt) (Rhs_rt)))) :=
      {|
        SubAssign_sub_assign_spec  :=
          (scope_add_elctx (E) (s.(SubAssign_sub_assign_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_SubAssign_spec.

Definition SubAssign_sub_assign_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (SubAssign_Self_Rhs_spec_attrs: (SubAssign_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), rhs :@: Rhs_ty;
      (* precondition. *) (λ π : thread_id, (⌜(SubAssign_Self_Rhs_spec_attrs.(SubAssign_SubAssignOpDefined) self.cur rhs)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost (SubAssign_Self_Rhs_spec_attrs.(SubAssign_SubAssignOp) self.cur rhs))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition SubAssign_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (_ATTRS: ((SubAssign_spec_attrs ((Self_rt)) ((Rhs_rt))))) : (spec_with _ _ (SubAssign_spec ((Self_rt)) ((Rhs_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), {|
      SubAssign_sub_assign_spec  :=
        (SubAssign_sub_assign_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 1 [] fn_spec);
    |}
.

End SubAssign.

Section DerefMut.
Context `{RRGS : !refinedrustGS Σ}.
Definition DerefMut_spec_incl `{Self_rt : !RT} `{Deref_Self_Target_rt : !RT} (spec1: ((DerefMut_spec (Self_rt) (Deref_Self_Target_rt)))) (spec2: ((DerefMut_spec (Self_rt) (Deref_Self_Target_rt)))) : Prop :=
  ((function_subtype (spec1.(DerefMut_deref_mut_spec)) (spec2.(DerefMut_deref_mut_spec)))).
Instance DerefMut_spec_incl_preorder `{Self_rt : !RT} `{Deref_Self_Target_rt : !RT} : (PreOrder (DerefMut_spec_incl (Self_rt := Self_rt) (Deref_Self_Target_rt := Deref_Self_Target_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_DerefMut_spec `{Self_rt : !RT} `{Deref_Self_Target_rt : !RT} : (ScopeBindable ((DerefMut_spec (Self_rt) (Deref_Self_Target_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((DerefMut_spec (Self_rt) (Deref_Self_Target_rt)))) :=
      {|
        DerefMut_deref_mut_spec  :=
          (scope_add_typarams (rts) (tys) (s.(DerefMut_deref_mut_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((DerefMut_spec (Self_rt) (Deref_Self_Target_rt)))) :=
      {|
        DerefMut_deref_mut_spec  :=
          (scope_add_elctx (E) (s.(DerefMut_deref_mut_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_DerefMut_spec.

Definition DerefMut_deref_mut_base_spec (Self_rt: RT) (Deref_Self_Target_rt: RT) (Self_st: syn_type) (Deref_Self_Target_st: syn_type) (Deref_Self_spec_attrs: (Deref_spec_attrs (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_SelfasDeref_Target_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Deref_Self_Target_rt) )) (DerefMut_Self_spec_attrs: (DerefMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt) Deref_Self_spec_attrs)) :=
  fn(∀ ( *[ulft_a]) : 1 | ( *[Self_ty; Deref_Self_Target_ty]) : ([(Self_rt, Self_st); (Deref_Self_Target_rt, Deref_Self_Target_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_a)]);
      (* args......... *) self :@: (mut_ref ulft_a Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (γi) : ((_)), (Deref_Self_spec_attrs.(Deref_DerefInto) self.cur, γi) @ (mut_ref ulft_a Deref_Self_Target_ty);
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost (DerefMut_Self_spec_attrs.(DerefMut_DerefMutInject) self.cur γi))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition DerefMut_base_spec (Self_rt: RT) (Deref_Self_Target_rt: RT) (Self_st: syn_type) (Deref_Self_Target_st: syn_type) (Deref_Self_spec_attrs: (Deref_spec_attrs (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_SelfasDeref_Target_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Deref_Self_Target_rt) )) (_ATTRS: ((DerefMut_spec_attrs ((Self_rt)) ((Deref_Self_Target_rt)) (Deref_Self_spec_attrs)))) : (spec_with _ _ (DerefMut_spec ((Self_rt)) ((Deref_Self_Target_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Deref_Self_Target_ty]) : ([Self_rt; Deref_Self_Target_rt] : list RT), {|
      DerefMut_deref_mut_spec  :=
        (DerefMut_deref_mut_base_spec ((Self_rt)) ((Deref_Self_Target_rt)) (Self_st) (Deref_Self_Target_st)) Deref_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_SelfasDeref_Target_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Deref_Self_Target_ty : (spec_with 1 [] fn_spec);
    |}
.

End DerefMut.

Section Add_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Add_add (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt)))) (DropGlue_SelfasAddRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (DropGlue_SelfasAddRhs_Output_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Output_rt)))) (Add_Self_Rhs_spec_attrs: (Add_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt) )) (Add_Self_Rhs_spec: (spec_with 0 [] (Add_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([Self_rt; Rhs_rt; Output_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasAddRhs_Output_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Output_rt) Output_st DropGlue_SelfasAddRhs_Output_spec_attrs-[] -[Output_ty]))) ∧ (trait_incl_marker (lift_trait_incl Add_spec_incl Add_Self_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Add_base_spec (Self_rt) (Rhs_rt) (Output_rt) Self_st Rhs_st Output_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs DropGlue_SelfasAddRhs_Output_spec_attrs Add_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty; Output_ty])))).
End Add_trait_req_incls.

Section AddAssign_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_AddAssign_add_assign (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt)))) (AddAssign_Self_Rhs_spec_attrs: (AddAssign_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (AddAssign_Self_Rhs_spec: (spec_with 0 [] (AddAssign_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))) ∧ (trait_incl_marker (lift_trait_incl AddAssign_spec_incl AddAssign_Self_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), AddAssign_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs AddAssign_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty])))).
End AddAssign_trait_req_incls.

Section Deref_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Deref_deref (Self_rt: RT) (Target_rt: RT) (Self_st: syn_type) (Target_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_SelfasDeref_Target_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Target_rt) )) (DropGlue_SelfasDeref_Target_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Target_rt)))) (Deref_Self_spec_attrs: (Deref_spec_attrs (RRGS:=RRGS) (Self_rt) (Target_rt) )) (Deref_Self_spec: (spec_with 0 [] (Deref_spec (RRGS:=RRGS) (Self_rt) (Target_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Target_ty]) : ([Self_rt; Target_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasDeref_Target_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Target_rt) Target_st DropGlue_SelfasDeref_Target_spec_attrs-[] -[Target_ty]))) ∧ (trait_incl_marker (lift_trait_incl Deref_spec_incl Deref_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Deref_base_spec (Self_rt) (Target_rt) Self_st Target_st DropGlue_Self_spec_attrs DropGlue_SelfasDeref_Target_spec_attrs Deref_Self_spec_attrs-[] -[Self_ty; Target_ty])))).
End Deref_trait_req_incls.

Section Mul_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Mul_mul (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt)))) (DropGlue_SelfasMulRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (DropGlue_SelfasMulRhs_Output_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Output_rt)))) (Mul_Self_Rhs_spec_attrs: (Mul_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt) )) (Mul_Self_Rhs_spec: (spec_with 0 [] (Mul_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([Self_rt; Rhs_rt; Output_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasMulRhs_Output_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Output_rt) Output_st DropGlue_SelfasMulRhs_Output_spec_attrs-[] -[Output_ty]))) ∧ (trait_incl_marker (lift_trait_incl Mul_spec_incl Mul_Self_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Mul_base_spec (Self_rt) (Rhs_rt) (Output_rt) Self_st Rhs_st Output_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs DropGlue_SelfasMulRhs_Output_spec_attrs Mul_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty; Output_ty])))).
End Mul_trait_req_incls.

Section MulAssign_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_MulAssign_mul_assign (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt)))) (MulAssign_Self_Rhs_spec_attrs: (MulAssign_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (MulAssign_Self_Rhs_spec: (spec_with 0 [] (MulAssign_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))) ∧ (trait_incl_marker (lift_trait_incl MulAssign_spec_incl MulAssign_Self_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), MulAssign_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs MulAssign_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty])))).
End MulAssign_trait_req_incls.

Section Sub_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Sub_sub (Self_rt: RT) (Rhs_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt)))) (DropGlue_SelfasSubRhs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (DropGlue_SelfasSubRhs_Output_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Output_rt)))) (Sub_Self_Rhs_spec_attrs: (Sub_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt) )) (Sub_Self_Rhs_spec: (spec_with 0 [] (Sub_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt) (Output_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty; Output_ty]) : ([Self_rt; Rhs_rt; Output_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasSubRhs_Output_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Output_rt) Output_st DropGlue_SelfasSubRhs_Output_spec_attrs-[] -[Output_ty]))) ∧ (trait_incl_marker (lift_trait_incl Sub_spec_incl Sub_Self_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Sub_base_spec (Self_rt) (Rhs_rt) (Output_rt) Self_st Rhs_st Output_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs DropGlue_SelfasSubRhs_Output_spec_attrs Sub_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty; Output_ty])))).
End Sub_trait_req_incls.

Section SubAssign_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_SubAssign_sub_assign (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt)))) (SubAssign_Self_Rhs_spec_attrs: (SubAssign_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (SubAssign_Self_Rhs_spec: (spec_with 0 [] (SubAssign_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))) ∧ (trait_incl_marker (lift_trait_incl SubAssign_spec_incl SubAssign_Self_Rhs_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), SubAssign_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs SubAssign_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty])))).
End SubAssign_trait_req_incls.

Section DerefMut_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_DerefMut_deref_mut (Self_rt: RT) (Deref_Self_Target_rt: RT) (Self_st: syn_type) (Deref_Self_Target_st: syn_type) (Deref_Self_spec_attrs: (Deref_spec_attrs (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt) )) (Deref_Self_spec: (spec_with 0 [] (Deref_spec (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt)))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_SelfasDeref_Target_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Deref_Self_Target_rt) )) (DropGlue_SelfasDeref_Target_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Deref_Self_Target_rt)))) (DerefMut_Self_spec_attrs: (DerefMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt) Deref_Self_spec_attrs)) (DerefMut_Self_spec: (spec_with 0 [] (DerefMut_spec (RRGS:=RRGS) (Self_rt) (Deref_Self_Target_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_a]) : 1 | ( *[Self_ty; Deref_Self_Target_ty]) : ([Self_rt; Deref_Self_Target_rt] : list RT), ((trait_incl_marker (lift_trait_incl Deref_spec_incl Deref_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Deref_base_spec (Self_rt) (Deref_Self_Target_rt) Self_st Deref_Self_Target_st DropGlue_Self_spec_attrs DropGlue_SelfasDeref_Target_spec_attrs Deref_Self_spec_attrs-[] -[Self_ty; Deref_Self_Target_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasDeref_Target_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Deref_Self_Target_rt) Deref_Self_Target_st DropGlue_SelfasDeref_Target_spec_attrs-[] -[Deref_Self_Target_ty]))) ∧ (trait_incl_marker (lift_trait_incl DerefMut_spec_incl DerefMut_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DerefMut_base_spec (Self_rt) (Deref_Self_Target_rt) Self_st Deref_Self_Target_st Deref_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_SelfasDeref_Target_spec_attrs DerefMut_Self_spec_attrs-[] -[Self_ty; Deref_Self_Target_ty])))).
End DerefMut_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_REFi128asAddREFai128_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi128asAddREFai128_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi128asAddREFai128_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I128)); (shr_ref ulft_a (int I128)); (int I128)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi128asAddi128_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi128asAddi128_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi128asAddi128_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I128)); (int I128); (int I128)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi16asAddREFai16_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi16asAddREFai16_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi16asAddREFai16_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I16)); (shr_ref ulft_a (int I16)); (int I16)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi16asAddi16_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi16asAddi16_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi16asAddi16_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I16)); (int I16); (int I16)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi32asAddREFai32_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi32asAddREFai32_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi32asAddREFai32_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I32)); (shr_ref ulft_a (int I32)); (int I32)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi32asAddi32_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi32asAddi32_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi32asAddi32_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I32)); (int I32); (int I32)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi64asAddREFai64_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi64asAddREFai64_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi64asAddREFai64_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I64)); (shr_ref ulft_a (int I64)); (int I64)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi64asAddi64_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi64asAddi64_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi64asAddi64_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I64)); (int I64); (int I64)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi8asAddREFai8_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi8asAddREFai8_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi8asAddREFai8_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I8)); (shr_ref ulft_a (int I8)); (int I8)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi8asAddi8_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi8asAddi8_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi8asAddi8_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I8)); (int I8); (int I8)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFisizeasAddREFaisize_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFisizeasAddREFaisize_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFisizeasAddREFaisize_spec_attrs))
    -[] -[(shr_ref ulft_1 (int ISize)); (shr_ref ulft_a (int ISize)); (int ISize)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFisizeasAddisize_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFisizeasAddisize_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFisizeasAddisize_spec_attrs))
    -[] -[(shr_ref ulft_0 (int ISize)); (int ISize); (int ISize)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu128asAddREFau128_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu128asAddREFau128_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu128asAddREFau128_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U128)); (shr_ref ulft_a (int U128)); (int U128)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu128asAddu128_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu128asAddu128_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu128asAddu128_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U128)); (int U128); (int U128)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu16asAddREFau16_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu16asAddREFau16_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu16asAddREFau16_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U16)); (shr_ref ulft_a (int U16)); (int U16)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu16asAddu16_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu16asAddu16_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu16asAddu16_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U16)); (int U16); (int U16)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu32asAddREFau32_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu32asAddREFau32_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu32asAddREFau32_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U32)); (shr_ref ulft_a (int U32)); (int U32)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu32asAddu32_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu32asAddu32_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu32asAddu32_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U32)); (int U32); (int U32)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu64asAddREFau64_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu64asAddREFau64_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu64asAddREFau64_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U64)); (shr_ref ulft_a (int U64)); (int U64)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu64asAddu64_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu64asAddu64_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu64asAddu64_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U64)); (int U64); (int U64)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu8asAddREFau8_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu8asAddREFau8_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu8asAddREFau8_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U8)); (shr_ref ulft_a (int U8)); (int U8)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu8asAddu8_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu8asAddu8_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu8asAddu8_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U8)); (int U8); (int U8)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFusizeasAddREFausize_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFusizeasAddREFausize_add  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Add_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFusizeasAddREFausize_spec_attrs))
    -[] -[(shr_ref ulft_1 (int USize)); (shr_ref ulft_a (int USize)); (int USize)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFusizeasAddusize_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFusizeasAddusize_add  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Add_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFusizeasAddusize_spec_attrs))
    -[] -[(shr_ref ulft_0 (int USize)); (int USize); (int USize)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asAddREFai128_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asAddREFai128_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I128)) (RefSynType) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i128asAddREFai128_spec_attrs))
    -[] -[(int I128); (shr_ref ulft_a (int I128)); (int I128)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asAdd_spec_attrs))
    -[] -[(int I128); (int I128); (int I128)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asAddREFai16_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asAddREFai16_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I16)) (RefSynType) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i16asAddREFai16_spec_attrs))
    -[] -[(int I16); (shr_ref ulft_a (int I16)); (int I16)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asAdd_spec_attrs))
    -[] -[(int I16); (int I16); (int I16)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asAddREFai32_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asAddREFai32_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I32)) (RefSynType) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i32asAddREFai32_spec_attrs))
    -[] -[(int I32); (shr_ref ulft_a (int I32)); (int I32)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asAdd_spec_attrs))
    -[] -[(int I32); (int I32); (int I32)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asAddREFai64_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asAddREFai64_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I64)) (RefSynType) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i64asAddREFai64_spec_attrs))
    -[] -[(int I64); (shr_ref ulft_a (int I64)); (int I64)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asAdd_spec_attrs))
    -[] -[(int I64); (int I64); (int I64)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asAddREFai8_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asAddREFai8_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I8)) (RefSynType) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i8asAddREFai8_spec_attrs))
    -[] -[(int I8); (shr_ref ulft_a (int I8)); (int I8)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asAdd_spec_attrs))
    -[] -[(int I8); (int I8); (int I8)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasAddREFaisize_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasAddREFaisize_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType ISize)) (RefSynType) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasAddREFaisize_spec_attrs))
    -[] -[(int ISize); (shr_ref ulft_a (int ISize)); (int ISize)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasAdd_spec_attrs))
    -[] -[(int ISize); (int ISize); (int ISize)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asAddREFau128_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asAddREFau128_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U128)) (RefSynType) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u128asAddREFau128_spec_attrs))
    -[] -[(int U128); (shr_ref ulft_a (int U128)); (int U128)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asAdd_spec_attrs))
    -[] -[(int U128); (int U128); (int U128)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asAddREFau16_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asAddREFau16_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U16)) (RefSynType) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u16asAddREFau16_spec_attrs))
    -[] -[(int U16); (shr_ref ulft_a (int U16)); (int U16)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asAdd_spec_attrs))
    -[] -[(int U16); (int U16); (int U16)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asAddREFau32_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asAddREFau32_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U32)) (RefSynType) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u32asAddREFau32_spec_attrs))
    -[] -[(int U32); (shr_ref ulft_a (int U32)); (int U32)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asAdd_spec_attrs))
    -[] -[(int U32); (int U32); (int U32)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asAddREFau64_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asAddREFau64_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U64)) (RefSynType) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u64asAddREFau64_spec_attrs))
    -[] -[(int U64); (shr_ref ulft_a (int U64)); (int U64)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asAdd_spec_attrs))
    -[] -[(int U64); (int U64); (int U64)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asAddREFau8_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asAddREFau8_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U8)) (RefSynType) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u8asAddREFau8_spec_attrs))
    -[] -[(int U8); (shr_ref ulft_a (int U8)); (int U8)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asAdd_spec_attrs))
    -[] -[(int U8); (int U8); (int U8)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasAddREFausize_add  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasAddREFausize_add  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Add_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType USize)) (RefSynType) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasAddREFausize_spec_attrs))
    -[] -[(int USize); (shr_ref ulft_a (int USize)); (int USize)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasAdd_add  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasAdd_add  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Add_base_spec (Z) (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasAdd_spec_attrs))
    -[] -[(int USize); (int USize); (int USize)]).(Add_add_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asAddAssignREFi128_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asAddAssignREFi128_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I128)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i128asAddAssignREFi128_spec_attrs))
    -[] -[(int I128); (shr_ref ulft_0 (int I128))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asAddAssign_spec_attrs))
    -[] -[(int I128); (int I128)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asAddAssignREFi16_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asAddAssignREFi16_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I16)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i16asAddAssignREFi16_spec_attrs))
    -[] -[(int I16); (shr_ref ulft_0 (int I16))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asAddAssign_spec_attrs))
    -[] -[(int I16); (int I16)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asAddAssignREFi32_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asAddAssignREFi32_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I32)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i32asAddAssignREFi32_spec_attrs))
    -[] -[(int I32); (shr_ref ulft_0 (int I32))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asAddAssign_spec_attrs))
    -[] -[(int I32); (int I32)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asAddAssignREFi64_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asAddAssignREFi64_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I64)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i64asAddAssignREFi64_spec_attrs))
    -[] -[(int I64); (shr_ref ulft_0 (int I64))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asAddAssign_spec_attrs))
    -[] -[(int I64); (int I64)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asAddAssignREFi8_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asAddAssignREFi8_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I8)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i8asAddAssignREFi8_spec_attrs))
    -[] -[(int I8); (shr_ref ulft_0 (int I8))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asAddAssign_spec_attrs))
    -[] -[(int I8); (int I8)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasAddAssignREFisize_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasAddAssignREFisize_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType ISize)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (isizeasAddAssignREFisize_spec_attrs))
    -[] -[(int ISize); (shr_ref ulft_0 (int ISize))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasAddAssign_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asAddAssignREFu128_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asAddAssignREFu128_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U128)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u128asAddAssignREFu128_spec_attrs))
    -[] -[(int U128); (shr_ref ulft_0 (int U128))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asAddAssign_spec_attrs))
    -[] -[(int U128); (int U128)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asAddAssignREFu16_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asAddAssignREFu16_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U16)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u16asAddAssignREFu16_spec_attrs))
    -[] -[(int U16); (shr_ref ulft_0 (int U16))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asAddAssign_spec_attrs))
    -[] -[(int U16); (int U16)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asAddAssignREFu32_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asAddAssignREFu32_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U32)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u32asAddAssignREFu32_spec_attrs))
    -[] -[(int U32); (shr_ref ulft_0 (int U32))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asAddAssign_spec_attrs))
    -[] -[(int U32); (int U32)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asAddAssignREFu64_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asAddAssignREFu64_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U64)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u64asAddAssignREFu64_spec_attrs))
    -[] -[(int U64); (shr_ref ulft_0 (int U64))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asAddAssign_spec_attrs))
    -[] -[(int U64); (int U64)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asAddAssignREFu8_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asAddAssignREFu8_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U8)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u8asAddAssignREFu8_spec_attrs))
    -[] -[(int U8); (shr_ref ulft_0 (int U8))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asAddAssign_spec_attrs))
    -[] -[(int U8); (int U8)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasAddAssignREFusize_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasAddAssignREFusize_add_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((AddAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType USize)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (usizeasAddAssignREFusize_spec_attrs))
    -[] -[(int USize); (shr_ref ulft_0 (int USize))]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasAddAssign_add_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasAddAssign_add_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((AddAssign_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasAddAssign_spec_attrs))
    -[] -[(int USize); (int USize)]).(AddAssign_add_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFTasDeref_deref (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_REFTasDeref_deref (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Deref_base_spec ((place_rfnRT (T_rt))) ((T_rt)) (RefSynType) (T_st) ((drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt))))) (DropGlue_T_spec_attrs) ((REFTasDeref_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(shr_ref ulft_0 T_ty); T_ty]).(Deref_deref_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFmutTasDeref_deref (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_REFmutTasDeref_deref (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Deref_base_spec (((place_rfnRT (T_rt)) * gname)%type) ((T_rt)) (RefSynType) (T_st) ((drop_glue_trivial_spec_attrs (((place_rfnRT (T_rt)) * gname)%type))) (DropGlue_T_spec_attrs) ((REFmutTasDeref_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(mut_ref ulft_0 T_ty); T_ty]).(Deref_deref_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi128asMulREFai128_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi128asMulREFai128_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi128asMulREFai128_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I128)); (shr_ref ulft_a (int I128)); (int I128)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi128asMuli128_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi128asMuli128_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi128asMuli128_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I128)); (int I128); (int I128)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi16asMulREFai16_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi16asMulREFai16_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi16asMulREFai16_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I16)); (shr_ref ulft_a (int I16)); (int I16)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi16asMuli16_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi16asMuli16_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi16asMuli16_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I16)); (int I16); (int I16)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi32asMulREFai32_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi32asMulREFai32_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi32asMulREFai32_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I32)); (shr_ref ulft_a (int I32)); (int I32)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi32asMuli32_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi32asMuli32_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi32asMuli32_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I32)); (int I32); (int I32)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi64asMulREFai64_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi64asMulREFai64_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi64asMulREFai64_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I64)); (shr_ref ulft_a (int I64)); (int I64)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi64asMuli64_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi64asMuli64_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi64asMuli64_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I64)); (int I64); (int I64)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi8asMulREFai8_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi8asMulREFai8_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi8asMulREFai8_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I8)); (shr_ref ulft_a (int I8)); (int I8)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi8asMuli8_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi8asMuli8_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi8asMuli8_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I8)); (int I8); (int I8)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFisizeasMulREFaisize_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFisizeasMulREFaisize_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFisizeasMulREFaisize_spec_attrs))
    -[] -[(shr_ref ulft_1 (int ISize)); (shr_ref ulft_a (int ISize)); (int ISize)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFisizeasMulisize_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFisizeasMulisize_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFisizeasMulisize_spec_attrs))
    -[] -[(shr_ref ulft_0 (int ISize)); (int ISize); (int ISize)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu128asMulREFau128_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu128asMulREFau128_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu128asMulREFau128_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U128)); (shr_ref ulft_a (int U128)); (int U128)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu128asMulu128_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu128asMulu128_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu128asMulu128_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U128)); (int U128); (int U128)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu16asMulREFau16_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu16asMulREFau16_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu16asMulREFau16_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U16)); (shr_ref ulft_a (int U16)); (int U16)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu16asMulu16_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu16asMulu16_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu16asMulu16_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U16)); (int U16); (int U16)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu32asMulREFau32_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu32asMulREFau32_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu32asMulREFau32_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U32)); (shr_ref ulft_a (int U32)); (int U32)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu32asMulu32_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu32asMulu32_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu32asMulu32_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U32)); (int U32); (int U32)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu64asMulREFau64_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu64asMulREFau64_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu64asMulREFau64_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U64)); (shr_ref ulft_a (int U64)); (int U64)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu64asMulu64_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu64asMulu64_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu64asMulu64_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U64)); (int U64); (int U64)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu8asMulREFau8_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu8asMulREFau8_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu8asMulREFau8_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U8)); (shr_ref ulft_a (int U8)); (int U8)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu8asMulu8_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu8asMulu8_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu8asMulu8_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U8)); (int U8); (int U8)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFusizeasMulREFausize_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFusizeasMulREFausize_mul  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Mul_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFusizeasMulREFausize_spec_attrs))
    -[] -[(shr_ref ulft_1 (int USize)); (shr_ref ulft_a (int USize)); (int USize)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFusizeasMulusize_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFusizeasMulusize_mul  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Mul_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFusizeasMulusize_spec_attrs))
    -[] -[(shr_ref ulft_0 (int USize)); (int USize); (int USize)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asMulREFai128_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asMulREFai128_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I128)) (RefSynType) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i128asMulREFai128_spec_attrs))
    -[] -[(int I128); (shr_ref ulft_a (int I128)); (int I128)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asMul_spec_attrs))
    -[] -[(int I128); (int I128); (int I128)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asMulREFai16_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asMulREFai16_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I16)) (RefSynType) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i16asMulREFai16_spec_attrs))
    -[] -[(int I16); (shr_ref ulft_a (int I16)); (int I16)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asMul_spec_attrs))
    -[] -[(int I16); (int I16); (int I16)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asMulREFai32_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asMulREFai32_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I32)) (RefSynType) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i32asMulREFai32_spec_attrs))
    -[] -[(int I32); (shr_ref ulft_a (int I32)); (int I32)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asMul_spec_attrs))
    -[] -[(int I32); (int I32); (int I32)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asMulREFai64_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asMulREFai64_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I64)) (RefSynType) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i64asMulREFai64_spec_attrs))
    -[] -[(int I64); (shr_ref ulft_a (int I64)); (int I64)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asMul_spec_attrs))
    -[] -[(int I64); (int I64); (int I64)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asMulREFai8_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asMulREFai8_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I8)) (RefSynType) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i8asMulREFai8_spec_attrs))
    -[] -[(int I8); (shr_ref ulft_a (int I8)); (int I8)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asMul_spec_attrs))
    -[] -[(int I8); (int I8); (int I8)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasMulREFaisize_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasMulREFaisize_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType ISize)) (RefSynType) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasMulREFaisize_spec_attrs))
    -[] -[(int ISize); (shr_ref ulft_a (int ISize)); (int ISize)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasMul_spec_attrs))
    -[] -[(int ISize); (int ISize); (int ISize)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asMulREFau128_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asMulREFau128_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U128)) (RefSynType) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u128asMulREFau128_spec_attrs))
    -[] -[(int U128); (shr_ref ulft_a (int U128)); (int U128)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asMul_spec_attrs))
    -[] -[(int U128); (int U128); (int U128)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asMulREFau16_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asMulREFau16_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U16)) (RefSynType) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u16asMulREFau16_spec_attrs))
    -[] -[(int U16); (shr_ref ulft_a (int U16)); (int U16)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asMul_spec_attrs))
    -[] -[(int U16); (int U16); (int U16)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asMulREFau32_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asMulREFau32_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U32)) (RefSynType) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u32asMulREFau32_spec_attrs))
    -[] -[(int U32); (shr_ref ulft_a (int U32)); (int U32)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asMul_spec_attrs))
    -[] -[(int U32); (int U32); (int U32)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asMulREFau64_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asMulREFau64_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U64)) (RefSynType) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u64asMulREFau64_spec_attrs))
    -[] -[(int U64); (shr_ref ulft_a (int U64)); (int U64)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asMul_spec_attrs))
    -[] -[(int U64); (int U64); (int U64)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asMulREFau8_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asMulREFau8_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U8)) (RefSynType) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u8asMulREFau8_spec_attrs))
    -[] -[(int U8); (shr_ref ulft_a (int U8)); (int U8)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asMul_spec_attrs))
    -[] -[(int U8); (int U8); (int U8)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasMulREFausize_mul  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasMulREFausize_mul  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Mul_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType USize)) (RefSynType) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasMulREFausize_spec_attrs))
    -[] -[(int USize); (shr_ref ulft_a (int USize)); (int USize)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasMul_mul  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasMul_mul  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Mul_base_spec (Z) (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasMul_spec_attrs))
    -[] -[(int USize); (int USize); (int USize)]).(Mul_mul_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asMulAssignREFi128_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asMulAssignREFi128_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I128)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i128asMulAssignREFi128_spec_attrs))
    -[] -[(int I128); (shr_ref ulft_0 (int I128))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asMulAssign_spec_attrs))
    -[] -[(int I128); (int I128)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asMulAssignREFi16_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asMulAssignREFi16_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I16)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i16asMulAssignREFi16_spec_attrs))
    -[] -[(int I16); (shr_ref ulft_0 (int I16))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asMulAssign_spec_attrs))
    -[] -[(int I16); (int I16)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asMulAssignREFi32_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asMulAssignREFi32_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I32)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i32asMulAssignREFi32_spec_attrs))
    -[] -[(int I32); (shr_ref ulft_0 (int I32))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asMulAssign_spec_attrs))
    -[] -[(int I32); (int I32)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asMulAssignREFi64_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asMulAssignREFi64_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I64)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i64asMulAssignREFi64_spec_attrs))
    -[] -[(int I64); (shr_ref ulft_0 (int I64))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asMulAssign_spec_attrs))
    -[] -[(int I64); (int I64)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asMulAssignREFi8_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asMulAssignREFi8_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I8)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i8asMulAssignREFi8_spec_attrs))
    -[] -[(int I8); (shr_ref ulft_0 (int I8))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asMulAssign_spec_attrs))
    -[] -[(int I8); (int I8)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasMulAssignREFisize_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasMulAssignREFisize_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType ISize)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (isizeasMulAssignREFisize_spec_attrs))
    -[] -[(int ISize); (shr_ref ulft_0 (int ISize))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasMulAssign_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asMulAssignREFu128_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asMulAssignREFu128_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U128)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u128asMulAssignREFu128_spec_attrs))
    -[] -[(int U128); (shr_ref ulft_0 (int U128))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asMulAssign_spec_attrs))
    -[] -[(int U128); (int U128)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asMulAssignREFu16_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asMulAssignREFu16_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U16)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u16asMulAssignREFu16_spec_attrs))
    -[] -[(int U16); (shr_ref ulft_0 (int U16))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asMulAssign_spec_attrs))
    -[] -[(int U16); (int U16)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asMulAssignREFu32_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asMulAssignREFu32_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U32)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u32asMulAssignREFu32_spec_attrs))
    -[] -[(int U32); (shr_ref ulft_0 (int U32))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asMulAssign_spec_attrs))
    -[] -[(int U32); (int U32)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asMulAssignREFu64_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asMulAssignREFu64_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U64)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u64asMulAssignREFu64_spec_attrs))
    -[] -[(int U64); (shr_ref ulft_0 (int U64))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asMulAssign_spec_attrs))
    -[] -[(int U64); (int U64)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asMulAssignREFu8_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asMulAssignREFu8_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U8)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u8asMulAssignREFu8_spec_attrs))
    -[] -[(int U8); (shr_ref ulft_0 (int U8))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asMulAssign_spec_attrs))
    -[] -[(int U8); (int U8)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasMulAssignREFusize_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasMulAssignREFusize_mul_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((MulAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType USize)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (usizeasMulAssignREFusize_spec_attrs))
    -[] -[(int USize); (shr_ref ulft_0 (int USize))]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasMulAssign_mul_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasMulAssign_mul_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((MulAssign_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasMulAssign_spec_attrs))
    -[] -[(int USize); (int USize)]).(MulAssign_mul_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi128asSubREFai128_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi128asSubREFai128_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi128asSubREFai128_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I128)); (shr_ref ulft_a (int I128)); (int I128)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi128asSubi128_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi128asSubi128_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi128asSubi128_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I128)); (int I128); (int I128)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi16asSubREFai16_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi16asSubREFai16_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi16asSubREFai16_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I16)); (shr_ref ulft_a (int I16)); (int I16)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi16asSubi16_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi16asSubi16_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi16asSubi16_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I16)); (int I16); (int I16)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi32asSubREFai32_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi32asSubREFai32_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi32asSubREFai32_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I32)); (shr_ref ulft_a (int I32)); (int I32)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi32asSubi32_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi32asSubi32_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi32asSubi32_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I32)); (int I32); (int I32)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi64asSubREFai64_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi64asSubREFai64_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi64asSubREFai64_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I64)); (shr_ref ulft_a (int I64)); (int I64)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi64asSubi64_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi64asSubi64_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi64asSubi64_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I64)); (int I64); (int I64)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi8asSubREFai8_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi8asSubREFai8_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFi8asSubREFai8_spec_attrs))
    -[] -[(shr_ref ulft_1 (int I8)); (shr_ref ulft_a (int I8)); (int I8)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFi8asSubi8_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFi8asSubi8_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFi8asSubi8_spec_attrs))
    -[] -[(shr_ref ulft_0 (int I8)); (int I8); (int I8)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFisizeasSubREFaisize_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFisizeasSubREFaisize_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFisizeasSubREFaisize_spec_attrs))
    -[] -[(shr_ref ulft_1 (int ISize)); (shr_ref ulft_a (int ISize)); (int ISize)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFisizeasSubisize_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFisizeasSubisize_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFisizeasSubisize_spec_attrs))
    -[] -[(shr_ref ulft_0 (int ISize)); (int ISize); (int ISize)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu128asSubREFau128_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu128asSubREFau128_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu128asSubREFau128_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U128)); (shr_ref ulft_a (int U128)); (int U128)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu128asSubu128_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu128asSubu128_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu128asSubu128_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U128)); (int U128); (int U128)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu16asSubREFau16_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu16asSubREFau16_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu16asSubREFau16_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U16)); (shr_ref ulft_a (int U16)); (int U16)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu16asSubu16_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu16asSubu16_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu16asSubu16_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U16)); (int U16); (int U16)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu32asSubREFau32_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu32asSubREFau32_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu32asSubREFau32_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U32)); (shr_ref ulft_a (int U32)); (int U32)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu32asSubu32_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu32asSubu32_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu32asSubu32_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U32)); (int U32); (int U32)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu64asSubREFau64_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu64asSubREFau64_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu64asSubREFau64_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U64)); (shr_ref ulft_a (int U64)); (int U64)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu64asSubu64_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu64asSubu64_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu64asSubu64_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U64)); (int U64); (int U64)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu8asSubREFau8_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu8asSubREFau8_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFu8asSubREFau8_spec_attrs))
    -[] -[(shr_ref ulft_1 (int U8)); (shr_ref ulft_a (int U8)); (int U8)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFu8asSubu8_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFu8asSubu8_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFu8asSubu8_spec_attrs))
    -[] -[(shr_ref ulft_0 (int U8)); (int U8); (int U8)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFusizeasSubREFausize_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFusizeasSubREFausize_sub  :=
  spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_1)]) (((Sub_base_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z) (RefSynType) (RefSynType) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (REFusizeasSubREFausize_spec_attrs))
    -[] -[(shr_ref ulft_1 (int USize)); (shr_ref ulft_a (int USize)); (int USize)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFusizeasSubusize_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_REFusizeasSubusize_sub  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Sub_base_spec ((place_rfnRT Z)) (Z) (Z) (RefSynType) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (REFusizeasSubusize_spec_attrs))
    -[] -[(shr_ref ulft_0 (int USize)); (int USize); (int USize)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asSubREFai128_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asSubREFai128_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I128)) (RefSynType) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i128asSubREFai128_spec_attrs))
    -[] -[(int I128); (shr_ref ulft_a (int I128)); (int I128)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asSub_spec_attrs))
    -[] -[(int I128); (int I128); (int I128)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asSubREFai16_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asSubREFai16_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I16)) (RefSynType) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i16asSubREFai16_spec_attrs))
    -[] -[(int I16); (shr_ref ulft_a (int I16)); (int I16)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asSub_spec_attrs))
    -[] -[(int I16); (int I16); (int I16)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asSubREFai32_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asSubREFai32_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I32)) (RefSynType) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i32asSubREFai32_spec_attrs))
    -[] -[(int I32); (shr_ref ulft_a (int I32)); (int I32)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asSub_spec_attrs))
    -[] -[(int I32); (int I32); (int I32)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asSubREFai64_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asSubREFai64_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I64)) (RefSynType) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i64asSubREFai64_spec_attrs))
    -[] -[(int I64); (shr_ref ulft_a (int I64)); (int I64)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asSub_spec_attrs))
    -[] -[(int I64); (int I64); (int I64)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asSubREFai8_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asSubREFai8_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType I8)) (RefSynType) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (i8asSubREFai8_spec_attrs))
    -[] -[(int I8); (shr_ref ulft_a (int I8)); (int I8)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asSub_spec_attrs))
    -[] -[(int I8); (int I8); (int I8)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasSubREFaisize_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasSubREFaisize_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType ISize)) (RefSynType) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasSubREFaisize_spec_attrs))
    -[] -[(int ISize); (shr_ref ulft_a (int ISize)); (int ISize)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasSub_spec_attrs))
    -[] -[(int ISize); (int ISize); (int ISize)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asSubREFau128_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asSubREFau128_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U128)) (RefSynType) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u128asSubREFau128_spec_attrs))
    -[] -[(int U128); (shr_ref ulft_a (int U128)); (int U128)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asSub_spec_attrs))
    -[] -[(int U128); (int U128); (int U128)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asSubREFau16_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asSubREFau16_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U16)) (RefSynType) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u16asSubREFau16_spec_attrs))
    -[] -[(int U16); (shr_ref ulft_a (int U16)); (int U16)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asSub_spec_attrs))
    -[] -[(int U16); (int U16); (int U16)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asSubREFau32_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asSubREFau32_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U32)) (RefSynType) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u32asSubREFau32_spec_attrs))
    -[] -[(int U32); (shr_ref ulft_a (int U32)); (int U32)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asSub_spec_attrs))
    -[] -[(int U32); (int U32); (int U32)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asSubREFau64_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asSubREFau64_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U64)) (RefSynType) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u64asSubREFau64_spec_attrs))
    -[] -[(int U64); (shr_ref ulft_a (int U64)); (int U64)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asSub_spec_attrs))
    -[] -[(int U64); (int U64); (int U64)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asSubREFau8_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asSubREFau8_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType U8)) (RefSynType) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (u8asSubREFau8_spec_attrs))
    -[] -[(int U8); (shr_ref ulft_a (int U8)); (int U8)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asSub_spec_attrs))
    -[] -[(int U8); (int U8); (int U8)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasSubREFausize_sub  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasSubREFausize_sub  :=
  spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)]) (((Sub_base_spec (Z) ((place_rfnRT Z)) (Z) ((IntSynType USize)) (RefSynType) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasSubREFausize_spec_attrs))
    -[] -[(int USize); (shr_ref ulft_a (int USize)); (int USize)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasSub_sub  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasSub_sub  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Sub_base_spec (Z) (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasSub_spec_attrs))
    -[] -[(int USize); (int USize); (int USize)]).(Sub_sub_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asSubAssignREFi128_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asSubAssignREFi128_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I128)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i128asSubAssignREFi128_spec_attrs))
    -[] -[(int I128); (shr_ref ulft_0 (int I128))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asSubAssign_spec_attrs))
    -[] -[(int I128); (int I128)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asSubAssignREFi16_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asSubAssignREFi16_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I16)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i16asSubAssignREFi16_spec_attrs))
    -[] -[(int I16); (shr_ref ulft_0 (int I16))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asSubAssign_spec_attrs))
    -[] -[(int I16); (int I16)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asSubAssignREFi32_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asSubAssignREFi32_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I32)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i32asSubAssignREFi32_spec_attrs))
    -[] -[(int I32); (shr_ref ulft_0 (int I32))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asSubAssign_spec_attrs))
    -[] -[(int I32); (int I32)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asSubAssignREFi64_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asSubAssignREFi64_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I64)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i64asSubAssignREFi64_spec_attrs))
    -[] -[(int I64); (shr_ref ulft_0 (int I64))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asSubAssign_spec_attrs))
    -[] -[(int I64); (int I64)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asSubAssignREFi8_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asSubAssignREFi8_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType I8)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (i8asSubAssignREFi8_spec_attrs))
    -[] -[(int I8); (shr_ref ulft_0 (int I8))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asSubAssign_spec_attrs))
    -[] -[(int I8); (int I8)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasSubAssignREFisize_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasSubAssignREFisize_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType ISize)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (isizeasSubAssignREFisize_spec_attrs))
    -[] -[(int ISize); (shr_ref ulft_0 (int ISize))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasSubAssign_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asSubAssignREFu128_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asSubAssignREFu128_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U128)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u128asSubAssignREFu128_spec_attrs))
    -[] -[(int U128); (shr_ref ulft_0 (int U128))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asSubAssign_spec_attrs))
    -[] -[(int U128); (int U128)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asSubAssignREFu16_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asSubAssignREFu16_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U16)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u16asSubAssignREFu16_spec_attrs))
    -[] -[(int U16); (shr_ref ulft_0 (int U16))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asSubAssign_spec_attrs))
    -[] -[(int U16); (int U16)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asSubAssignREFu32_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asSubAssignREFu32_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U32)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u32asSubAssignREFu32_spec_attrs))
    -[] -[(int U32); (shr_ref ulft_0 (int U32))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asSubAssign_spec_attrs))
    -[] -[(int U32); (int U32)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asSubAssignREFu64_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asSubAssignREFu64_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U64)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u64asSubAssignREFu64_spec_attrs))
    -[] -[(int U64); (shr_ref ulft_0 (int U64))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asSubAssign_spec_attrs))
    -[] -[(int U64); (int U64)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asSubAssignREFu8_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asSubAssignREFu8_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType U8)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (u8asSubAssignREFu8_spec_attrs))
    -[] -[(int U8); (shr_ref ulft_0 (int U8))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asSubAssign_spec_attrs))
    -[] -[(int U8); (int U8)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasSubAssignREFusize_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasSubAssignREFusize_sub_assign  :=
  spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((SubAssign_base_spec (Z) ((place_rfnRT Z)) ((IntSynType USize)) (RefSynType) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs ((place_rfnRT Z)))) (usizeasSubAssignREFusize_spec_attrs))
    -[] -[(int USize); (shr_ref ulft_0 (int USize))]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasSubAssign_sub_assign  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasSubAssign_sub_assign  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((SubAssign_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasSubAssign_spec_attrs))
    -[] -[(int USize); (int USize)]).(SubAssign_sub_assign_spec)   a b))) <MERGE!>.


Definition trait_incl_of_REFmutTasDerefMut_deref_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_a]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_REFmutTasDerefMut_deref_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((DerefMut_base_spec (((place_rfnRT (T_rt)) * gname)%type) ((T_rt)) (RefSynType) (T_st) ((REFmutTasDeref_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))) ((drop_glue_trivial_spec_attrs (((place_rfnRT (T_rt)) * gname)%type))) (DropGlue_T_spec_attrs) ((REFmutTasDerefMut_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(mut_ref ulft_0 T_ty); T_ty]).(DerefMut_deref_mut_spec)   a b))) <MERGE!>.



End specs.
Section REFTasDeref_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFTasDeref_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Deref_spec ((place_rfnRT (T_rt))) ((T_rt)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), let Target_rt := (T_rt) in {|
        Deref_deref_spec  :=
          (type_of_REFTasDeref_deref ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition REFTasDeref_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Deref_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (REFTasDeref_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[ulft_0] -[T_ty]) (spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Deref_base_spec (place_rfnRT (T_rt)) (T_rt) RefSynType T_st (drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt)))) DropGlue_T_spec_attrs (REFTasDeref_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(shr_ref ulft_0 T_ty); T_ty])))).
End REFTasDeref_spec.

Section REFi128asAddREFai128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi128asAddREFai128_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi128asAddREFai128_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi128asAddREFai128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi128asAddREFai128_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi128asAddREFai128_spec_attrs-[] -[(shr_ref ulft_1 (int I128)); (shr_ref ulft_a (int I128)); (int I128)])))).
End REFi128asAddREFai128_spec.

Section REFi128asAddi128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi128asAddi128_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi128asAddi128_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi128asAddi128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi128asAddi128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi128asAddi128_spec_attrs-[] -[(shr_ref ulft_0 (int I128)); (int I128); (int I128)])))).
End REFi128asAddi128_spec.

Section REFi128asMulREFai128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi128asMulREFai128_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi128asMulREFai128_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi128asMulREFai128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi128asMulREFai128_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi128asMulREFai128_spec_attrs-[] -[(shr_ref ulft_1 (int I128)); (shr_ref ulft_a (int I128)); (int I128)])))).
End REFi128asMulREFai128_spec.

Section REFi128asMuli128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi128asMuli128_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi128asMuli128_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi128asMuli128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi128asMuli128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi128asMuli128_spec_attrs-[] -[(shr_ref ulft_0 (int I128)); (int I128); (int I128)])))).
End REFi128asMuli128_spec.

Section REFi128asSubREFai128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi128asSubREFai128_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi128asSubREFai128_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi128asSubREFai128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi128asSubREFai128_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi128asSubREFai128_spec_attrs-[] -[(shr_ref ulft_1 (int I128)); (shr_ref ulft_a (int I128)); (int I128)])))).
End REFi128asSubREFai128_spec.

Section REFi128asSubi128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi128asSubi128_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi128asSubi128_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi128asSubi128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi128asSubi128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi128asSubi128_spec_attrs-[] -[(shr_ref ulft_0 (int I128)); (int I128); (int I128)])))).
End REFi128asSubi128_spec.

Section REFi16asAddREFai16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi16asAddREFai16_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi16asAddREFai16_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi16asAddREFai16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi16asAddREFai16_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi16asAddREFai16_spec_attrs-[] -[(shr_ref ulft_1 (int I16)); (shr_ref ulft_a (int I16)); (int I16)])))).
End REFi16asAddREFai16_spec.

Section REFi16asAddi16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi16asAddi16_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi16asAddi16_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi16asAddi16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi16asAddi16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi16asAddi16_spec_attrs-[] -[(shr_ref ulft_0 (int I16)); (int I16); (int I16)])))).
End REFi16asAddi16_spec.

Section REFi16asMulREFai16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi16asMulREFai16_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi16asMulREFai16_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi16asMulREFai16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi16asMulREFai16_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi16asMulREFai16_spec_attrs-[] -[(shr_ref ulft_1 (int I16)); (shr_ref ulft_a (int I16)); (int I16)])))).
End REFi16asMulREFai16_spec.

Section REFi16asMuli16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi16asMuli16_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi16asMuli16_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi16asMuli16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi16asMuli16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi16asMuli16_spec_attrs-[] -[(shr_ref ulft_0 (int I16)); (int I16); (int I16)])))).
End REFi16asMuli16_spec.

Section REFi16asSubREFai16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi16asSubREFai16_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi16asSubREFai16_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi16asSubREFai16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi16asSubREFai16_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi16asSubREFai16_spec_attrs-[] -[(shr_ref ulft_1 (int I16)); (shr_ref ulft_a (int I16)); (int I16)])))).
End REFi16asSubREFai16_spec.

Section REFi16asSubi16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi16asSubi16_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi16asSubi16_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi16asSubi16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi16asSubi16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi16asSubi16_spec_attrs-[] -[(shr_ref ulft_0 (int I16)); (int I16); (int I16)])))).
End REFi16asSubi16_spec.

Section REFi32asAddREFai32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi32asAddREFai32_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi32asAddREFai32_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi32asAddREFai32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi32asAddREFai32_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi32asAddREFai32_spec_attrs-[] -[(shr_ref ulft_1 (int I32)); (shr_ref ulft_a (int I32)); (int I32)])))).
End REFi32asAddREFai32_spec.

Section REFi32asAddi32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi32asAddi32_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi32asAddi32_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi32asAddi32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi32asAddi32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi32asAddi32_spec_attrs-[] -[(shr_ref ulft_0 (int I32)); (int I32); (int I32)])))).
End REFi32asAddi32_spec.

Section REFi32asMulREFai32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi32asMulREFai32_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi32asMulREFai32_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi32asMulREFai32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi32asMulREFai32_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi32asMulREFai32_spec_attrs-[] -[(shr_ref ulft_1 (int I32)); (shr_ref ulft_a (int I32)); (int I32)])))).
End REFi32asMulREFai32_spec.

Section REFi32asMuli32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi32asMuli32_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi32asMuli32_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi32asMuli32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi32asMuli32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi32asMuli32_spec_attrs-[] -[(shr_ref ulft_0 (int I32)); (int I32); (int I32)])))).
End REFi32asMuli32_spec.

Section REFi32asSubREFai32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi32asSubREFai32_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi32asSubREFai32_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi32asSubREFai32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi32asSubREFai32_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi32asSubREFai32_spec_attrs-[] -[(shr_ref ulft_1 (int I32)); (shr_ref ulft_a (int I32)); (int I32)])))).
End REFi32asSubREFai32_spec.

Section REFi32asSubi32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi32asSubi32_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi32asSubi32_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi32asSubi32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi32asSubi32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi32asSubi32_spec_attrs-[] -[(shr_ref ulft_0 (int I32)); (int I32); (int I32)])))).
End REFi32asSubi32_spec.

Section REFi64asAddREFai64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi64asAddREFai64_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi64asAddREFai64_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi64asAddREFai64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi64asAddREFai64_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi64asAddREFai64_spec_attrs-[] -[(shr_ref ulft_1 (int I64)); (shr_ref ulft_a (int I64)); (int I64)])))).
End REFi64asAddREFai64_spec.

Section REFi64asAddi64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi64asAddi64_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi64asAddi64_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi64asAddi64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi64asAddi64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi64asAddi64_spec_attrs-[] -[(shr_ref ulft_0 (int I64)); (int I64); (int I64)])))).
End REFi64asAddi64_spec.

Section REFi64asMulREFai64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi64asMulREFai64_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi64asMulREFai64_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi64asMulREFai64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi64asMulREFai64_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi64asMulREFai64_spec_attrs-[] -[(shr_ref ulft_1 (int I64)); (shr_ref ulft_a (int I64)); (int I64)])))).
End REFi64asMulREFai64_spec.

Section REFi64asMuli64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi64asMuli64_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi64asMuli64_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi64asMuli64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi64asMuli64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi64asMuli64_spec_attrs-[] -[(shr_ref ulft_0 (int I64)); (int I64); (int I64)])))).
End REFi64asMuli64_spec.

Section REFi64asSubREFai64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi64asSubREFai64_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi64asSubREFai64_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi64asSubREFai64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi64asSubREFai64_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi64asSubREFai64_spec_attrs-[] -[(shr_ref ulft_1 (int I64)); (shr_ref ulft_a (int I64)); (int I64)])))).
End REFi64asSubREFai64_spec.

Section REFi64asSubi64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi64asSubi64_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi64asSubi64_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi64asSubi64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi64asSubi64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi64asSubi64_spec_attrs-[] -[(shr_ref ulft_0 (int I64)); (int I64); (int I64)])))).
End REFi64asSubi64_spec.

Section REFi8asAddREFai8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi8asAddREFai8_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi8asAddREFai8_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi8asAddREFai8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi8asAddREFai8_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi8asAddREFai8_spec_attrs-[] -[(shr_ref ulft_1 (int I8)); (shr_ref ulft_a (int I8)); (int I8)])))).
End REFi8asAddREFai8_spec.

Section REFi8asAddi8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi8asAddi8_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFi8asAddi8_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi8asAddi8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi8asAddi8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi8asAddi8_spec_attrs-[] -[(shr_ref ulft_0 (int I8)); (int I8); (int I8)])))).
End REFi8asAddi8_spec.

Section REFi8asMulREFai8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi8asMulREFai8_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi8asMulREFai8_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi8asMulREFai8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi8asMulREFai8_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi8asMulREFai8_spec_attrs-[] -[(shr_ref ulft_1 (int I8)); (shr_ref ulft_a (int I8)); (int I8)])))).
End REFi8asMulREFai8_spec.

Section REFi8asMuli8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi8asMuli8_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFi8asMuli8_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi8asMuli8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi8asMuli8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi8asMuli8_spec_attrs-[] -[(shr_ref ulft_0 (int I8)); (int I8); (int I8)])))).
End REFi8asMuli8_spec.

Section REFi8asSubREFai8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi8asSubREFai8_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi8asSubREFai8_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi8asSubREFai8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFi8asSubREFai8_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType I8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFi8asSubREFai8_spec_attrs-[] -[(shr_ref ulft_1 (int I8)); (shr_ref ulft_a (int I8)); (int I8)])))).
End REFi8asSubREFai8_spec.

Section REFi8asSubi8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFi8asSubi8_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFi8asSubi8_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFi8asSubi8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFi8asSubi8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFi8asSubi8_spec_attrs-[] -[(shr_ref ulft_0 (int I8)); (int I8); (int I8)])))).
End REFi8asSubi8_spec.

Section REFisizeasAddREFaisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFisizeasAddREFaisize_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFisizeasAddREFaisize_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFisizeasAddREFaisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFisizeasAddREFaisize_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType ISize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFisizeasAddREFaisize_spec_attrs-[] -[(shr_ref ulft_1 (int ISize)); (shr_ref ulft_a (int ISize)); (int ISize)])))).
End REFisizeasAddREFaisize_spec.

Section REFisizeasAddisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFisizeasAddisize_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFisizeasAddisize_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFisizeasAddisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFisizeasAddisize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFisizeasAddisize_spec_attrs-[] -[(shr_ref ulft_0 (int ISize)); (int ISize); (int ISize)])))).
End REFisizeasAddisize_spec.

Section REFisizeasMulREFaisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFisizeasMulREFaisize_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFisizeasMulREFaisize_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFisizeasMulREFaisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFisizeasMulREFaisize_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType ISize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFisizeasMulREFaisize_spec_attrs-[] -[(shr_ref ulft_1 (int ISize)); (shr_ref ulft_a (int ISize)); (int ISize)])))).
End REFisizeasMulREFaisize_spec.

Section REFisizeasMulisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFisizeasMulisize_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFisizeasMulisize_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFisizeasMulisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFisizeasMulisize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFisizeasMulisize_spec_attrs-[] -[(shr_ref ulft_0 (int ISize)); (int ISize); (int ISize)])))).
End REFisizeasMulisize_spec.

Section REFisizeasSubREFaisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFisizeasSubREFaisize_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFisizeasSubREFaisize_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFisizeasSubREFaisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFisizeasSubREFaisize_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType ISize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFisizeasSubREFaisize_spec_attrs-[] -[(shr_ref ulft_1 (int ISize)); (shr_ref ulft_a (int ISize)); (int ISize)])))).
End REFisizeasSubREFaisize_spec.

Section REFisizeasSubisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFisizeasSubisize_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFisizeasSubisize_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFisizeasSubisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFisizeasSubisize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFisizeasSubisize_spec_attrs-[] -[(shr_ref ulft_0 (int ISize)); (int ISize); (int ISize)])))).
End REFisizeasSubisize_spec.

Section REFmutTasDeref_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFmutTasDeref_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Deref_spec (((place_rfnRT (T_rt)) * gname)%type) ((T_rt)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), let Target_rt := (T_rt) in {|
        Deref_deref_spec  :=
          (type_of_REFmutTasDeref_deref ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition REFmutTasDeref_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Deref_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (REFmutTasDeref_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[ulft_0] -[T_ty]) (spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Deref_base_spec ((place_rfnRT (T_rt)) * gname)%type (T_rt) RefSynType T_st (drop_glue_trivial_spec_attrs (((place_rfnRT (T_rt)) * gname)%type)) DropGlue_T_spec_attrs (REFmutTasDeref_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(mut_ref ulft_0 T_ty); T_ty])))).
End REFmutTasDeref_spec.

Section REFmutTasDerefMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFmutTasDerefMut_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (DerefMut_spec (((place_rfnRT (T_rt)) * gname)%type) ((T_rt)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), {|
        DerefMut_deref_mut_spec  :=
          (type_of_REFmutTasDerefMut_deref_mut ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition REFmutTasDerefMut_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl DerefMut_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (REFmutTasDerefMut_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[ulft_0] -[T_ty]) (spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((DerefMut_base_spec ((place_rfnRT (T_rt)) * gname)%type (T_rt) RefSynType T_st (REFmutTasDeref_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_trivial_spec_attrs (((place_rfnRT (T_rt)) * gname)%type)) DropGlue_T_spec_attrs (REFmutTasDerefMut_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(mut_ref ulft_0 T_ty); T_ty])))).
End REFmutTasDerefMut_spec.

Section REFu128asAddREFau128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu128asAddREFau128_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu128asAddREFau128_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu128asAddREFau128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu128asAddREFau128_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu128asAddREFau128_spec_attrs-[] -[(shr_ref ulft_1 (int U128)); (shr_ref ulft_a (int U128)); (int U128)])))).
End REFu128asAddREFau128_spec.

Section REFu128asAddu128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu128asAddu128_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu128asAddu128_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu128asAddu128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu128asAddu128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu128asAddu128_spec_attrs-[] -[(shr_ref ulft_0 (int U128)); (int U128); (int U128)])))).
End REFu128asAddu128_spec.

Section REFu128asMulREFau128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu128asMulREFau128_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu128asMulREFau128_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu128asMulREFau128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu128asMulREFau128_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu128asMulREFau128_spec_attrs-[] -[(shr_ref ulft_1 (int U128)); (shr_ref ulft_a (int U128)); (int U128)])))).
End REFu128asMulREFau128_spec.

Section REFu128asMulu128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu128asMulu128_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu128asMulu128_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu128asMulu128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu128asMulu128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu128asMulu128_spec_attrs-[] -[(shr_ref ulft_0 (int U128)); (int U128); (int U128)])))).
End REFu128asMulu128_spec.

Section REFu128asSubREFau128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu128asSubREFau128_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu128asSubREFau128_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu128asSubREFau128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu128asSubREFau128_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu128asSubREFau128_spec_attrs-[] -[(shr_ref ulft_1 (int U128)); (shr_ref ulft_a (int U128)); (int U128)])))).
End REFu128asSubREFau128_spec.

Section REFu128asSubu128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu128asSubu128_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu128asSubu128_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu128asSubu128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu128asSubu128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu128asSubu128_spec_attrs-[] -[(shr_ref ulft_0 (int U128)); (int U128); (int U128)])))).
End REFu128asSubu128_spec.

Section REFu16asAddREFau16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu16asAddREFau16_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu16asAddREFau16_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu16asAddREFau16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu16asAddREFau16_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu16asAddREFau16_spec_attrs-[] -[(shr_ref ulft_1 (int U16)); (shr_ref ulft_a (int U16)); (int U16)])))).
End REFu16asAddREFau16_spec.

Section REFu16asAddu16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu16asAddu16_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu16asAddu16_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu16asAddu16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu16asAddu16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu16asAddu16_spec_attrs-[] -[(shr_ref ulft_0 (int U16)); (int U16); (int U16)])))).
End REFu16asAddu16_spec.

Section REFu16asMulREFau16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu16asMulREFau16_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu16asMulREFau16_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu16asMulREFau16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu16asMulREFau16_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu16asMulREFau16_spec_attrs-[] -[(shr_ref ulft_1 (int U16)); (shr_ref ulft_a (int U16)); (int U16)])))).
End REFu16asMulREFau16_spec.

Section REFu16asMulu16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu16asMulu16_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu16asMulu16_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu16asMulu16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu16asMulu16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu16asMulu16_spec_attrs-[] -[(shr_ref ulft_0 (int U16)); (int U16); (int U16)])))).
End REFu16asMulu16_spec.

Section REFu16asSubREFau16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu16asSubREFau16_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu16asSubREFau16_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu16asSubREFau16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu16asSubREFau16_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu16asSubREFau16_spec_attrs-[] -[(shr_ref ulft_1 (int U16)); (shr_ref ulft_a (int U16)); (int U16)])))).
End REFu16asSubREFau16_spec.

Section REFu16asSubu16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu16asSubu16_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu16asSubu16_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu16asSubu16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu16asSubu16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu16asSubu16_spec_attrs-[] -[(shr_ref ulft_0 (int U16)); (int U16); (int U16)])))).
End REFu16asSubu16_spec.

Section REFu32asAddREFau32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu32asAddREFau32_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu32asAddREFau32_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu32asAddREFau32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu32asAddREFau32_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu32asAddREFau32_spec_attrs-[] -[(shr_ref ulft_1 (int U32)); (shr_ref ulft_a (int U32)); (int U32)])))).
End REFu32asAddREFau32_spec.

Section REFu32asAddu32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu32asAddu32_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu32asAddu32_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu32asAddu32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu32asAddu32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu32asAddu32_spec_attrs-[] -[(shr_ref ulft_0 (int U32)); (int U32); (int U32)])))).
End REFu32asAddu32_spec.

Section REFu32asMulREFau32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu32asMulREFau32_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu32asMulREFau32_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu32asMulREFau32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu32asMulREFau32_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu32asMulREFau32_spec_attrs-[] -[(shr_ref ulft_1 (int U32)); (shr_ref ulft_a (int U32)); (int U32)])))).
End REFu32asMulREFau32_spec.

Section REFu32asMulu32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu32asMulu32_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu32asMulu32_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu32asMulu32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu32asMulu32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu32asMulu32_spec_attrs-[] -[(shr_ref ulft_0 (int U32)); (int U32); (int U32)])))).
End REFu32asMulu32_spec.

Section REFu32asSubREFau32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu32asSubREFau32_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu32asSubREFau32_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu32asSubREFau32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu32asSubREFau32_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu32asSubREFau32_spec_attrs-[] -[(shr_ref ulft_1 (int U32)); (shr_ref ulft_a (int U32)); (int U32)])))).
End REFu32asSubREFau32_spec.

Section REFu32asSubu32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu32asSubu32_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu32asSubu32_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu32asSubu32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu32asSubu32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu32asSubu32_spec_attrs-[] -[(shr_ref ulft_0 (int U32)); (int U32); (int U32)])))).
End REFu32asSubu32_spec.

Section REFu64asAddREFau64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu64asAddREFau64_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu64asAddREFau64_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu64asAddREFau64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu64asAddREFau64_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu64asAddREFau64_spec_attrs-[] -[(shr_ref ulft_1 (int U64)); (shr_ref ulft_a (int U64)); (int U64)])))).
End REFu64asAddREFau64_spec.

Section REFu64asAddu64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu64asAddu64_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu64asAddu64_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu64asAddu64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu64asAddu64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu64asAddu64_spec_attrs-[] -[(shr_ref ulft_0 (int U64)); (int U64); (int U64)])))).
End REFu64asAddu64_spec.

Section REFu64asMulREFau64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu64asMulREFau64_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu64asMulREFau64_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu64asMulREFau64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu64asMulREFau64_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu64asMulREFau64_spec_attrs-[] -[(shr_ref ulft_1 (int U64)); (shr_ref ulft_a (int U64)); (int U64)])))).
End REFu64asMulREFau64_spec.

Section REFu64asMulu64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu64asMulu64_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu64asMulu64_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu64asMulu64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu64asMulu64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu64asMulu64_spec_attrs-[] -[(shr_ref ulft_0 (int U64)); (int U64); (int U64)])))).
End REFu64asMulu64_spec.

Section REFu64asSubREFau64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu64asSubREFau64_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu64asSubREFau64_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu64asSubREFau64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu64asSubREFau64_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu64asSubREFau64_spec_attrs-[] -[(shr_ref ulft_1 (int U64)); (shr_ref ulft_a (int U64)); (int U64)])))).
End REFu64asSubREFau64_spec.

Section REFu64asSubu64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu64asSubu64_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu64asSubu64_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu64asSubu64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu64asSubu64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu64asSubu64_spec_attrs-[] -[(shr_ref ulft_0 (int U64)); (int U64); (int U64)])))).
End REFu64asSubu64_spec.

Section REFu8asAddREFau8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu8asAddREFau8_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu8asAddREFau8_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu8asAddREFau8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu8asAddREFau8_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu8asAddREFau8_spec_attrs-[] -[(shr_ref ulft_1 (int U8)); (shr_ref ulft_a (int U8)); (int U8)])))).
End REFu8asAddREFau8_spec.

Section REFu8asAddu8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu8asAddu8_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFu8asAddu8_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu8asAddu8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu8asAddu8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu8asAddu8_spec_attrs-[] -[(shr_ref ulft_0 (int U8)); (int U8); (int U8)])))).
End REFu8asAddu8_spec.

Section REFu8asMulREFau8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu8asMulREFau8_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu8asMulREFau8_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu8asMulREFau8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu8asMulREFau8_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu8asMulREFau8_spec_attrs-[] -[(shr_ref ulft_1 (int U8)); (shr_ref ulft_a (int U8)); (int U8)])))).
End REFu8asMulREFau8_spec.

Section REFu8asMulu8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu8asMulu8_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFu8asMulu8_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu8asMulu8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu8asMulu8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu8asMulu8_spec_attrs-[] -[(shr_ref ulft_0 (int U8)); (int U8); (int U8)])))).
End REFu8asMulu8_spec.

Section REFu8asSubREFau8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu8asSubREFau8_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu8asSubREFau8_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu8asSubREFau8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFu8asSubREFau8_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType U8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFu8asSubREFau8_spec_attrs-[] -[(shr_ref ulft_1 (int U8)); (shr_ref ulft_a (int U8)); (int U8)])))).
End REFu8asSubREFau8_spec.

Section REFu8asSubu8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFu8asSubu8_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFu8asSubu8_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFu8asSubu8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFu8asSubu8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFu8asSubu8_spec_attrs-[] -[(shr_ref ulft_0 (int U8)); (int U8); (int U8)])))).
End REFu8asSubu8_spec.

Section REFusizeasAddREFausize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFusizeasAddREFausize_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFusizeasAddREFausize_add 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFusizeasAddREFausize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFusizeasAddREFausize_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType USize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFusizeasAddREFausize_spec_attrs-[] -[(shr_ref ulft_1 (int USize)); (shr_ref ulft_a (int USize)); (int USize)])))).
End REFusizeasAddREFausize_spec.

Section REFusizeasAddusize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFusizeasAddusize_spec  : (spec_with _ _ (Add_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_REFusizeasAddusize_add 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFusizeasAddusize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFusizeasAddusize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFusizeasAddusize_spec_attrs-[] -[(shr_ref ulft_0 (int USize)); (int USize); (int USize)])))).
End REFusizeasAddusize_spec.

Section REFusizeasMulREFausize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFusizeasMulREFausize_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFusizeasMulREFausize_mul 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFusizeasMulREFausize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFusizeasMulREFausize_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType USize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFusizeasMulREFausize_spec_attrs-[] -[(shr_ref ulft_1 (int USize)); (shr_ref ulft_a (int USize)); (int USize)])))).
End REFusizeasMulREFausize_spec.

Section REFusizeasMulusize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFusizeasMulusize_spec  : (spec_with _ _ (Mul_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_REFusizeasMulusize_mul 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFusizeasMulusize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFusizeasMulusize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFusizeasMulusize_spec_attrs-[] -[(shr_ref ulft_0 (int USize)); (int USize); (int USize)])))).
End REFusizeasMulusize_spec.

Section REFusizeasSubREFausize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFusizeasSubREFausize_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFusizeasSubREFausize_sub 
             <LFT> ulft_a <LFT> ulft_1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFusizeasSubREFausize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), REFusizeasSubREFausize_spec-[ulft_a; ulft_1] -[]) (spec! ( *[ulft_a; ulft_1]) : 2 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) (place_rfnRT Z) Z RefSynType RefSynType (IntSynType USize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) REFusizeasSubREFausize_spec_attrs-[] -[(shr_ref ulft_1 (int USize)); (shr_ref ulft_a (int USize)); (int USize)])))).
End REFusizeasSubREFausize_spec.

Section REFusizeasSubusize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFusizeasSubusize_spec  : (spec_with _ _ (Sub_spec ((place_rfnRT Z)) (Z) (Z))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_REFusizeasSubusize_sub 
             <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition REFusizeasSubusize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), REFusizeasSubusize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec (place_rfnRT Z) Z Z RefSynType (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) REFusizeasSubusize_spec_attrs-[] -[(shr_ref ulft_0 (int USize)); (int USize); (int USize)])))).
End REFusizeasSubusize_spec.

Section i128asAddREFai128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asAddREFai128_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i128asAddREFai128_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i128asAddREFai128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i128asAddREFai128_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType I128) RefSynType (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i128asAddREFai128_spec_attrs-[] -[(int I128); (shr_ref ulft_a (int I128)); (int I128)])))).
End i128asAddREFai128_spec.

Section i128asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i128asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i128asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType I128) (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i128asAdd_spec_attrs-[] -[(int I128); (int I128); (int I128)])))).
End i128asAdd_spec.

Section i128asAddAssignREFi128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asAddAssignREFi128_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i128asAddAssignREFi128_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i128asAddAssignREFi128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i128asAddAssignREFi128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType I128) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i128asAddAssignREFi128_spec_attrs-[] -[(int I128); (shr_ref ulft_0 (int I128))])))).
End i128asAddAssignREFi128_spec.

Section i128asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i128asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i128asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i128asAddAssign_spec_attrs-[] -[(int I128); (int I128)])))).
End i128asAddAssign_spec.

Section i128asMulREFai128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asMulREFai128_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i128asMulREFai128_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i128asMulREFai128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i128asMulREFai128_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType I128) RefSynType (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i128asMulREFai128_spec_attrs-[] -[(int I128); (shr_ref ulft_a (int I128)); (int I128)])))).
End i128asMulREFai128_spec.

Section i128asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i128asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i128asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType I128) (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i128asMul_spec_attrs-[] -[(int I128); (int I128); (int I128)])))).
End i128asMul_spec.

Section i128asMulAssignREFi128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asMulAssignREFi128_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i128asMulAssignREFi128_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i128asMulAssignREFi128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i128asMulAssignREFi128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType I128) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i128asMulAssignREFi128_spec_attrs-[] -[(int I128); (shr_ref ulft_0 (int I128))])))).
End i128asMulAssignREFi128_spec.

Section i128asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i128asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i128asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i128asMulAssign_spec_attrs-[] -[(int I128); (int I128)])))).
End i128asMulAssign_spec.

Section i128asSubREFai128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asSubREFai128_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i128asSubREFai128_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i128asSubREFai128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i128asSubREFai128_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType I128) RefSynType (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i128asSubREFai128_spec_attrs-[] -[(int I128); (shr_ref ulft_a (int I128)); (int I128)])))).
End i128asSubREFai128_spec.

Section i128asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i128asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i128asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType I128) (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i128asSub_spec_attrs-[] -[(int I128); (int I128); (int I128)])))).
End i128asSub_spec.

Section i128asSubAssignREFi128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asSubAssignREFi128_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i128asSubAssignREFi128_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i128asSubAssignREFi128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i128asSubAssignREFi128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType I128) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i128asSubAssignREFi128_spec_attrs-[] -[(int I128); (shr_ref ulft_0 (int I128))])))).
End i128asSubAssignREFi128_spec.

Section i128asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i128asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i128asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i128asSubAssign_spec_attrs-[] -[(int I128); (int I128)])))).
End i128asSubAssign_spec.

Section i16asAddREFai16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asAddREFai16_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i16asAddREFai16_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i16asAddREFai16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i16asAddREFai16_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType I16) RefSynType (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i16asAddREFai16_spec_attrs-[] -[(int I16); (shr_ref ulft_a (int I16)); (int I16)])))).
End i16asAddREFai16_spec.

Section i16asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i16asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i16asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType I16) (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i16asAdd_spec_attrs-[] -[(int I16); (int I16); (int I16)])))).
End i16asAdd_spec.

Section i16asAddAssignREFi16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asAddAssignREFi16_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i16asAddAssignREFi16_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i16asAddAssignREFi16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i16asAddAssignREFi16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType I16) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i16asAddAssignREFi16_spec_attrs-[] -[(int I16); (shr_ref ulft_0 (int I16))])))).
End i16asAddAssignREFi16_spec.

Section i16asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i16asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i16asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i16asAddAssign_spec_attrs-[] -[(int I16); (int I16)])))).
End i16asAddAssign_spec.

Section i16asMulREFai16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asMulREFai16_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i16asMulREFai16_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i16asMulREFai16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i16asMulREFai16_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType I16) RefSynType (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i16asMulREFai16_spec_attrs-[] -[(int I16); (shr_ref ulft_a (int I16)); (int I16)])))).
End i16asMulREFai16_spec.

Section i16asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i16asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i16asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType I16) (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i16asMul_spec_attrs-[] -[(int I16); (int I16); (int I16)])))).
End i16asMul_spec.

Section i16asMulAssignREFi16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asMulAssignREFi16_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i16asMulAssignREFi16_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i16asMulAssignREFi16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i16asMulAssignREFi16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType I16) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i16asMulAssignREFi16_spec_attrs-[] -[(int I16); (shr_ref ulft_0 (int I16))])))).
End i16asMulAssignREFi16_spec.

Section i16asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i16asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i16asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i16asMulAssign_spec_attrs-[] -[(int I16); (int I16)])))).
End i16asMulAssign_spec.

Section i16asSubREFai16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asSubREFai16_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i16asSubREFai16_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i16asSubREFai16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i16asSubREFai16_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType I16) RefSynType (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i16asSubREFai16_spec_attrs-[] -[(int I16); (shr_ref ulft_a (int I16)); (int I16)])))).
End i16asSubREFai16_spec.

Section i16asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i16asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i16asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType I16) (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i16asSub_spec_attrs-[] -[(int I16); (int I16); (int I16)])))).
End i16asSub_spec.

Section i16asSubAssignREFi16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asSubAssignREFi16_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i16asSubAssignREFi16_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i16asSubAssignREFi16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i16asSubAssignREFi16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType I16) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i16asSubAssignREFi16_spec_attrs-[] -[(int I16); (shr_ref ulft_0 (int I16))])))).
End i16asSubAssignREFi16_spec.

Section i16asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i16asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i16asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i16asSubAssign_spec_attrs-[] -[(int I16); (int I16)])))).
End i16asSubAssign_spec.

Section i32asAddREFai32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asAddREFai32_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i32asAddREFai32_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i32asAddREFai32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i32asAddREFai32_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType I32) RefSynType (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i32asAddREFai32_spec_attrs-[] -[(int I32); (shr_ref ulft_a (int I32)); (int I32)])))).
End i32asAddREFai32_spec.

Section i32asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i32asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i32asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType I32) (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i32asAdd_spec_attrs-[] -[(int I32); (int I32); (int I32)])))).
End i32asAdd_spec.

Section i32asAddAssignREFi32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asAddAssignREFi32_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i32asAddAssignREFi32_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i32asAddAssignREFi32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i32asAddAssignREFi32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType I32) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i32asAddAssignREFi32_spec_attrs-[] -[(int I32); (shr_ref ulft_0 (int I32))])))).
End i32asAddAssignREFi32_spec.

Section i32asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i32asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i32asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i32asAddAssign_spec_attrs-[] -[(int I32); (int I32)])))).
End i32asAddAssign_spec.

Section i32asMulREFai32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asMulREFai32_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i32asMulREFai32_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i32asMulREFai32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i32asMulREFai32_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType I32) RefSynType (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i32asMulREFai32_spec_attrs-[] -[(int I32); (shr_ref ulft_a (int I32)); (int I32)])))).
End i32asMulREFai32_spec.

Section i32asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i32asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i32asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType I32) (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i32asMul_spec_attrs-[] -[(int I32); (int I32); (int I32)])))).
End i32asMul_spec.

Section i32asMulAssignREFi32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asMulAssignREFi32_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i32asMulAssignREFi32_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i32asMulAssignREFi32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i32asMulAssignREFi32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType I32) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i32asMulAssignREFi32_spec_attrs-[] -[(int I32); (shr_ref ulft_0 (int I32))])))).
End i32asMulAssignREFi32_spec.

Section i32asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i32asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i32asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i32asMulAssign_spec_attrs-[] -[(int I32); (int I32)])))).
End i32asMulAssign_spec.

Section i32asSubREFai32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asSubREFai32_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i32asSubREFai32_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i32asSubREFai32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i32asSubREFai32_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType I32) RefSynType (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i32asSubREFai32_spec_attrs-[] -[(int I32); (shr_ref ulft_a (int I32)); (int I32)])))).
End i32asSubREFai32_spec.

Section i32asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i32asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i32asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType I32) (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i32asSub_spec_attrs-[] -[(int I32); (int I32); (int I32)])))).
End i32asSub_spec.

Section i32asSubAssignREFi32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asSubAssignREFi32_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i32asSubAssignREFi32_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i32asSubAssignREFi32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i32asSubAssignREFi32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType I32) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i32asSubAssignREFi32_spec_attrs-[] -[(int I32); (shr_ref ulft_0 (int I32))])))).
End i32asSubAssignREFi32_spec.

Section i32asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i32asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i32asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i32asSubAssign_spec_attrs-[] -[(int I32); (int I32)])))).
End i32asSubAssign_spec.

Section i64asAddREFai64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asAddREFai64_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i64asAddREFai64_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i64asAddREFai64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i64asAddREFai64_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType I64) RefSynType (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i64asAddREFai64_spec_attrs-[] -[(int I64); (shr_ref ulft_a (int I64)); (int I64)])))).
End i64asAddREFai64_spec.

Section i64asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i64asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i64asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType I64) (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i64asAdd_spec_attrs-[] -[(int I64); (int I64); (int I64)])))).
End i64asAdd_spec.

Section i64asAddAssignREFi64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asAddAssignREFi64_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i64asAddAssignREFi64_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i64asAddAssignREFi64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i64asAddAssignREFi64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType I64) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i64asAddAssignREFi64_spec_attrs-[] -[(int I64); (shr_ref ulft_0 (int I64))])))).
End i64asAddAssignREFi64_spec.

Section i64asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i64asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i64asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i64asAddAssign_spec_attrs-[] -[(int I64); (int I64)])))).
End i64asAddAssign_spec.

Section i64asMulREFai64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asMulREFai64_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i64asMulREFai64_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i64asMulREFai64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i64asMulREFai64_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType I64) RefSynType (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i64asMulREFai64_spec_attrs-[] -[(int I64); (shr_ref ulft_a (int I64)); (int I64)])))).
End i64asMulREFai64_spec.

Section i64asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i64asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i64asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType I64) (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i64asMul_spec_attrs-[] -[(int I64); (int I64); (int I64)])))).
End i64asMul_spec.

Section i64asMulAssignREFi64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asMulAssignREFi64_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i64asMulAssignREFi64_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i64asMulAssignREFi64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i64asMulAssignREFi64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType I64) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i64asMulAssignREFi64_spec_attrs-[] -[(int I64); (shr_ref ulft_0 (int I64))])))).
End i64asMulAssignREFi64_spec.

Section i64asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i64asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i64asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i64asMulAssign_spec_attrs-[] -[(int I64); (int I64)])))).
End i64asMulAssign_spec.

Section i64asSubREFai64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asSubREFai64_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i64asSubREFai64_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i64asSubREFai64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i64asSubREFai64_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType I64) RefSynType (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i64asSubREFai64_spec_attrs-[] -[(int I64); (shr_ref ulft_a (int I64)); (int I64)])))).
End i64asSubREFai64_spec.

Section i64asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i64asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i64asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType I64) (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i64asSub_spec_attrs-[] -[(int I64); (int I64); (int I64)])))).
End i64asSub_spec.

Section i64asSubAssignREFi64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asSubAssignREFi64_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i64asSubAssignREFi64_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i64asSubAssignREFi64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i64asSubAssignREFi64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType I64) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i64asSubAssignREFi64_spec_attrs-[] -[(int I64); (shr_ref ulft_0 (int I64))])))).
End i64asSubAssignREFi64_spec.

Section i64asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i64asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i64asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i64asSubAssign_spec_attrs-[] -[(int I64); (int I64)])))).
End i64asSubAssign_spec.

Section i8asAddREFai8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asAddREFai8_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i8asAddREFai8_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i8asAddREFai8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i8asAddREFai8_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType I8) RefSynType (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i8asAddREFai8_spec_attrs-[] -[(int I8); (shr_ref ulft_a (int I8)); (int I8)])))).
End i8asAddREFai8_spec.

Section i8asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_i8asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i8asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType I8) (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i8asAdd_spec_attrs-[] -[(int I8); (int I8); (int I8)])))).
End i8asAdd_spec.

Section i8asAddAssignREFi8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asAddAssignREFi8_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i8asAddAssignREFi8_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i8asAddAssignREFi8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i8asAddAssignREFi8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType I8) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i8asAddAssignREFi8_spec_attrs-[] -[(int I8); (shr_ref ulft_0 (int I8))])))).
End i8asAddAssignREFi8_spec.

Section i8asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_i8asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i8asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i8asAddAssign_spec_attrs-[] -[(int I8); (int I8)])))).
End i8asAddAssign_spec.

Section i8asMulREFai8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asMulREFai8_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i8asMulREFai8_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i8asMulREFai8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i8asMulREFai8_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType I8) RefSynType (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i8asMulREFai8_spec_attrs-[] -[(int I8); (shr_ref ulft_a (int I8)); (int I8)])))).
End i8asMulREFai8_spec.

Section i8asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_i8asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i8asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType I8) (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i8asMul_spec_attrs-[] -[(int I8); (int I8); (int I8)])))).
End i8asMul_spec.

Section i8asMulAssignREFi8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asMulAssignREFi8_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i8asMulAssignREFi8_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i8asMulAssignREFi8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i8asMulAssignREFi8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType I8) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i8asMulAssignREFi8_spec_attrs-[] -[(int I8); (shr_ref ulft_0 (int I8))])))).
End i8asMulAssignREFi8_spec.

Section i8asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_i8asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i8asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i8asMulAssign_spec_attrs-[] -[(int I8); (int I8)])))).
End i8asMulAssign_spec.

Section i8asSubREFai8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asSubREFai8_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i8asSubREFai8_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i8asSubREFai8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), i8asSubREFai8_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType I8) RefSynType (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) i8asSubREFai8_spec_attrs-[] -[(int I8); (shr_ref ulft_a (int I8)); (int I8)])))).
End i8asSubREFai8_spec.

Section i8asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_i8asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition i8asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType I8) (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i8asSub_spec_attrs-[] -[(int I8); (int I8); (int I8)])))).
End i8asSub_spec.

Section i8asSubAssignREFi8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asSubAssignREFi8_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i8asSubAssignREFi8_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i8asSubAssignREFi8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), i8asSubAssignREFi8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType I8) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) i8asSubAssignREFi8_spec_attrs-[] -[(int I8); (shr_ref ulft_0 (int I8))])))).
End i8asSubAssignREFi8_spec.

Section i8asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_i8asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition i8asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i8asSubAssign_spec_attrs-[] -[(int I8); (int I8)])))).
End i8asSubAssign_spec.

Section isizeasAddREFaisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasAddREFaisize_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_isizeasAddREFaisize_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition isizeasAddREFaisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), isizeasAddREFaisize_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType ISize) RefSynType (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) isizeasAddREFaisize_spec_attrs-[] -[(int ISize); (shr_ref ulft_a (int ISize)); (int ISize)])))).
End isizeasAddREFaisize_spec.

Section isizeasAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_isizeasAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition isizeasAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType ISize) (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) isizeasAdd_spec_attrs-[] -[(int ISize); (int ISize); (int ISize)])))).
End isizeasAdd_spec.

Section isizeasAddAssignREFisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasAddAssignREFisize_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_isizeasAddAssignREFisize_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition isizeasAddAssignREFisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), isizeasAddAssignREFisize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType ISize) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) isizeasAddAssignREFisize_spec_attrs-[] -[(int ISize); (shr_ref ulft_0 (int ISize))])))).
End isizeasAddAssignREFisize_spec.

Section isizeasAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_isizeasAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition isizeasAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) isizeasAddAssign_spec_attrs-[] -[(int ISize); (int ISize)])))).
End isizeasAddAssign_spec.

Section isizeasMulREFaisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasMulREFaisize_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_isizeasMulREFaisize_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition isizeasMulREFaisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), isizeasMulREFaisize_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType ISize) RefSynType (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) isizeasMulREFaisize_spec_attrs-[] -[(int ISize); (shr_ref ulft_a (int ISize)); (int ISize)])))).
End isizeasMulREFaisize_spec.

Section isizeasMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_isizeasMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition isizeasMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType ISize) (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) isizeasMul_spec_attrs-[] -[(int ISize); (int ISize); (int ISize)])))).
End isizeasMul_spec.

Section isizeasMulAssignREFisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasMulAssignREFisize_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_isizeasMulAssignREFisize_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition isizeasMulAssignREFisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), isizeasMulAssignREFisize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType ISize) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) isizeasMulAssignREFisize_spec_attrs-[] -[(int ISize); (shr_ref ulft_0 (int ISize))])))).
End isizeasMulAssignREFisize_spec.

Section isizeasMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_isizeasMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition isizeasMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) isizeasMulAssign_spec_attrs-[] -[(int ISize); (int ISize)])))).
End isizeasMulAssign_spec.

Section isizeasSubREFaisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasSubREFaisize_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_isizeasSubREFaisize_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition isizeasSubREFaisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), isizeasSubREFaisize_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType ISize) RefSynType (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) isizeasSubREFaisize_spec_attrs-[] -[(int ISize); (shr_ref ulft_a (int ISize)); (int ISize)])))).
End isizeasSubREFaisize_spec.

Section isizeasSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_isizeasSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition isizeasSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType ISize) (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) isizeasSub_spec_attrs-[] -[(int ISize); (int ISize); (int ISize)])))).
End isizeasSub_spec.

Section isizeasSubAssignREFisize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasSubAssignREFisize_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_isizeasSubAssignREFisize_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition isizeasSubAssignREFisize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), isizeasSubAssignREFisize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType ISize) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) isizeasSubAssignREFisize_spec_attrs-[] -[(int ISize); (shr_ref ulft_0 (int ISize))])))).
End isizeasSubAssignREFisize_spec.

Section isizeasSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_isizeasSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition isizeasSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) isizeasSubAssign_spec_attrs-[] -[(int ISize); (int ISize)])))).
End isizeasSubAssign_spec.

Section u128asAddREFau128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asAddREFau128_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u128asAddREFau128_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u128asAddREFau128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u128asAddREFau128_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType U128) RefSynType (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u128asAddREFau128_spec_attrs-[] -[(int U128); (shr_ref ulft_a (int U128)); (int U128)])))).
End u128asAddREFau128_spec.

Section u128asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u128asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u128asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType U128) (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u128asAdd_spec_attrs-[] -[(int U128); (int U128); (int U128)])))).
End u128asAdd_spec.

Section u128asAddAssignREFu128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asAddAssignREFu128_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u128asAddAssignREFu128_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u128asAddAssignREFu128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u128asAddAssignREFu128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType U128) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u128asAddAssignREFu128_spec_attrs-[] -[(int U128); (shr_ref ulft_0 (int U128))])))).
End u128asAddAssignREFu128_spec.

Section u128asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u128asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u128asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u128asAddAssign_spec_attrs-[] -[(int U128); (int U128)])))).
End u128asAddAssign_spec.

Section u128asMulREFau128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asMulREFau128_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u128asMulREFau128_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u128asMulREFau128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u128asMulREFau128_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType U128) RefSynType (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u128asMulREFau128_spec_attrs-[] -[(int U128); (shr_ref ulft_a (int U128)); (int U128)])))).
End u128asMulREFau128_spec.

Section u128asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u128asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u128asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType U128) (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u128asMul_spec_attrs-[] -[(int U128); (int U128); (int U128)])))).
End u128asMul_spec.

Section u128asMulAssignREFu128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asMulAssignREFu128_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u128asMulAssignREFu128_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u128asMulAssignREFu128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u128asMulAssignREFu128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType U128) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u128asMulAssignREFu128_spec_attrs-[] -[(int U128); (shr_ref ulft_0 (int U128))])))).
End u128asMulAssignREFu128_spec.

Section u128asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u128asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u128asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u128asMulAssign_spec_attrs-[] -[(int U128); (int U128)])))).
End u128asMulAssign_spec.

Section u128asSubREFau128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asSubREFau128_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u128asSubREFau128_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u128asSubREFau128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u128asSubREFau128_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType U128) RefSynType (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u128asSubREFau128_spec_attrs-[] -[(int U128); (shr_ref ulft_a (int U128)); (int U128)])))).
End u128asSubREFau128_spec.

Section u128asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u128asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u128asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType U128) (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u128asSub_spec_attrs-[] -[(int U128); (int U128); (int U128)])))).
End u128asSub_spec.

Section u128asSubAssignREFu128_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asSubAssignREFu128_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u128asSubAssignREFu128_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u128asSubAssignREFu128_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u128asSubAssignREFu128_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType U128) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u128asSubAssignREFu128_spec_attrs-[] -[(int U128); (shr_ref ulft_0 (int U128))])))).
End u128asSubAssignREFu128_spec.

Section u128asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u128asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u128asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u128asSubAssign_spec_attrs-[] -[(int U128); (int U128)])))).
End u128asSubAssign_spec.

Section u16asAddREFau16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asAddREFau16_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u16asAddREFau16_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u16asAddREFau16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u16asAddREFau16_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType U16) RefSynType (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u16asAddREFau16_spec_attrs-[] -[(int U16); (shr_ref ulft_a (int U16)); (int U16)])))).
End u16asAddREFau16_spec.

Section u16asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u16asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u16asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType U16) (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u16asAdd_spec_attrs-[] -[(int U16); (int U16); (int U16)])))).
End u16asAdd_spec.

Section u16asAddAssignREFu16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asAddAssignREFu16_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u16asAddAssignREFu16_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u16asAddAssignREFu16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u16asAddAssignREFu16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType U16) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u16asAddAssignREFu16_spec_attrs-[] -[(int U16); (shr_ref ulft_0 (int U16))])))).
End u16asAddAssignREFu16_spec.

Section u16asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u16asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u16asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u16asAddAssign_spec_attrs-[] -[(int U16); (int U16)])))).
End u16asAddAssign_spec.

Section u16asMulREFau16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asMulREFau16_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u16asMulREFau16_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u16asMulREFau16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u16asMulREFau16_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType U16) RefSynType (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u16asMulREFau16_spec_attrs-[] -[(int U16); (shr_ref ulft_a (int U16)); (int U16)])))).
End u16asMulREFau16_spec.

Section u16asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u16asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u16asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType U16) (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u16asMul_spec_attrs-[] -[(int U16); (int U16); (int U16)])))).
End u16asMul_spec.

Section u16asMulAssignREFu16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asMulAssignREFu16_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u16asMulAssignREFu16_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u16asMulAssignREFu16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u16asMulAssignREFu16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType U16) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u16asMulAssignREFu16_spec_attrs-[] -[(int U16); (shr_ref ulft_0 (int U16))])))).
End u16asMulAssignREFu16_spec.

Section u16asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u16asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u16asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u16asMulAssign_spec_attrs-[] -[(int U16); (int U16)])))).
End u16asMulAssign_spec.

Section u16asSubREFau16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asSubREFau16_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u16asSubREFau16_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u16asSubREFau16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u16asSubREFau16_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType U16) RefSynType (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u16asSubREFau16_spec_attrs-[] -[(int U16); (shr_ref ulft_a (int U16)); (int U16)])))).
End u16asSubREFau16_spec.

Section u16asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u16asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u16asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType U16) (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u16asSub_spec_attrs-[] -[(int U16); (int U16); (int U16)])))).
End u16asSub_spec.

Section u16asSubAssignREFu16_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asSubAssignREFu16_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u16asSubAssignREFu16_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u16asSubAssignREFu16_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u16asSubAssignREFu16_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType U16) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u16asSubAssignREFu16_spec_attrs-[] -[(int U16); (shr_ref ulft_0 (int U16))])))).
End u16asSubAssignREFu16_spec.

Section u16asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u16asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u16asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u16asSubAssign_spec_attrs-[] -[(int U16); (int U16)])))).
End u16asSubAssign_spec.

Section u32asAddREFau32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asAddREFau32_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u32asAddREFau32_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u32asAddREFau32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u32asAddREFau32_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType U32) RefSynType (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u32asAddREFau32_spec_attrs-[] -[(int U32); (shr_ref ulft_a (int U32)); (int U32)])))).
End u32asAddREFau32_spec.

Section u32asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u32asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u32asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType U32) (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u32asAdd_spec_attrs-[] -[(int U32); (int U32); (int U32)])))).
End u32asAdd_spec.

Section u32asAddAssignREFu32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asAddAssignREFu32_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u32asAddAssignREFu32_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u32asAddAssignREFu32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u32asAddAssignREFu32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType U32) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u32asAddAssignREFu32_spec_attrs-[] -[(int U32); (shr_ref ulft_0 (int U32))])))).
End u32asAddAssignREFu32_spec.

Section u32asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u32asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u32asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u32asAddAssign_spec_attrs-[] -[(int U32); (int U32)])))).
End u32asAddAssign_spec.

Section u32asMulREFau32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asMulREFau32_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u32asMulREFau32_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u32asMulREFau32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u32asMulREFau32_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType U32) RefSynType (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u32asMulREFau32_spec_attrs-[] -[(int U32); (shr_ref ulft_a (int U32)); (int U32)])))).
End u32asMulREFau32_spec.

Section u32asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u32asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u32asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType U32) (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u32asMul_spec_attrs-[] -[(int U32); (int U32); (int U32)])))).
End u32asMul_spec.

Section u32asMulAssignREFu32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asMulAssignREFu32_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u32asMulAssignREFu32_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u32asMulAssignREFu32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u32asMulAssignREFu32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType U32) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u32asMulAssignREFu32_spec_attrs-[] -[(int U32); (shr_ref ulft_0 (int U32))])))).
End u32asMulAssignREFu32_spec.

Section u32asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u32asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u32asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u32asMulAssign_spec_attrs-[] -[(int U32); (int U32)])))).
End u32asMulAssign_spec.

Section u32asSubREFau32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asSubREFau32_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u32asSubREFau32_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u32asSubREFau32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u32asSubREFau32_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType U32) RefSynType (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u32asSubREFau32_spec_attrs-[] -[(int U32); (shr_ref ulft_a (int U32)); (int U32)])))).
End u32asSubREFau32_spec.

Section u32asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u32asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u32asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType U32) (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u32asSub_spec_attrs-[] -[(int U32); (int U32); (int U32)])))).
End u32asSub_spec.

Section u32asSubAssignREFu32_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asSubAssignREFu32_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u32asSubAssignREFu32_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u32asSubAssignREFu32_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u32asSubAssignREFu32_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType U32) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u32asSubAssignREFu32_spec_attrs-[] -[(int U32); (shr_ref ulft_0 (int U32))])))).
End u32asSubAssignREFu32_spec.

Section u32asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u32asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u32asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u32asSubAssign_spec_attrs-[] -[(int U32); (int U32)])))).
End u32asSubAssign_spec.

Section u64asAddREFau64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asAddREFau64_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u64asAddREFau64_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u64asAddREFau64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u64asAddREFau64_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType U64) RefSynType (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u64asAddREFau64_spec_attrs-[] -[(int U64); (shr_ref ulft_a (int U64)); (int U64)])))).
End u64asAddREFau64_spec.

Section u64asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u64asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u64asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType U64) (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u64asAdd_spec_attrs-[] -[(int U64); (int U64); (int U64)])))).
End u64asAdd_spec.

Section u64asAddAssignREFu64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asAddAssignREFu64_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u64asAddAssignREFu64_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u64asAddAssignREFu64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u64asAddAssignREFu64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType U64) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u64asAddAssignREFu64_spec_attrs-[] -[(int U64); (shr_ref ulft_0 (int U64))])))).
End u64asAddAssignREFu64_spec.

Section u64asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u64asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u64asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u64asAddAssign_spec_attrs-[] -[(int U64); (int U64)])))).
End u64asAddAssign_spec.

Section u64asMulREFau64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asMulREFau64_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u64asMulREFau64_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u64asMulREFau64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u64asMulREFau64_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType U64) RefSynType (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u64asMulREFau64_spec_attrs-[] -[(int U64); (shr_ref ulft_a (int U64)); (int U64)])))).
End u64asMulREFau64_spec.

Section u64asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u64asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u64asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType U64) (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u64asMul_spec_attrs-[] -[(int U64); (int U64); (int U64)])))).
End u64asMul_spec.

Section u64asMulAssignREFu64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asMulAssignREFu64_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u64asMulAssignREFu64_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u64asMulAssignREFu64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u64asMulAssignREFu64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType U64) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u64asMulAssignREFu64_spec_attrs-[] -[(int U64); (shr_ref ulft_0 (int U64))])))).
End u64asMulAssignREFu64_spec.

Section u64asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u64asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u64asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u64asMulAssign_spec_attrs-[] -[(int U64); (int U64)])))).
End u64asMulAssign_spec.

Section u64asSubREFau64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asSubREFau64_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u64asSubREFau64_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u64asSubREFau64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u64asSubREFau64_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType U64) RefSynType (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u64asSubREFau64_spec_attrs-[] -[(int U64); (shr_ref ulft_a (int U64)); (int U64)])))).
End u64asSubREFau64_spec.

Section u64asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u64asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u64asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType U64) (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u64asSub_spec_attrs-[] -[(int U64); (int U64); (int U64)])))).
End u64asSub_spec.

Section u64asSubAssignREFu64_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asSubAssignREFu64_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u64asSubAssignREFu64_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u64asSubAssignREFu64_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u64asSubAssignREFu64_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType U64) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u64asSubAssignREFu64_spec_attrs-[] -[(int U64); (shr_ref ulft_0 (int U64))])))).
End u64asSubAssignREFu64_spec.

Section u64asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u64asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u64asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u64asSubAssign_spec_attrs-[] -[(int U64); (int U64)])))).
End u64asSubAssign_spec.

Section u8asAddREFau8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asAddREFau8_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u8asAddREFau8_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u8asAddREFau8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u8asAddREFau8_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType U8) RefSynType (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u8asAddREFau8_spec_attrs-[] -[(int U8); (shr_ref ulft_a (int U8)); (int U8)])))).
End u8asAddREFau8_spec.

Section u8asAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_u8asAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u8asAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType U8) (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u8asAdd_spec_attrs-[] -[(int U8); (int U8); (int U8)])))).
End u8asAdd_spec.

Section u8asAddAssignREFu8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asAddAssignREFu8_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u8asAddAssignREFu8_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u8asAddAssignREFu8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u8asAddAssignREFu8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType U8) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u8asAddAssignREFu8_spec_attrs-[] -[(int U8); (shr_ref ulft_0 (int U8))])))).
End u8asAddAssignREFu8_spec.

Section u8asAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_u8asAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u8asAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u8asAddAssign_spec_attrs-[] -[(int U8); (int U8)])))).
End u8asAddAssign_spec.

Section u8asMulREFau8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asMulREFau8_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u8asMulREFau8_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u8asMulREFau8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u8asMulREFau8_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType U8) RefSynType (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u8asMulREFau8_spec_attrs-[] -[(int U8); (shr_ref ulft_a (int U8)); (int U8)])))).
End u8asMulREFau8_spec.

Section u8asMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_u8asMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u8asMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType U8) (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u8asMul_spec_attrs-[] -[(int U8); (int U8); (int U8)])))).
End u8asMul_spec.

Section u8asMulAssignREFu8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asMulAssignREFu8_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u8asMulAssignREFu8_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u8asMulAssignREFu8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u8asMulAssignREFu8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType U8) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u8asMulAssignREFu8_spec_attrs-[] -[(int U8); (shr_ref ulft_0 (int U8))])))).
End u8asMulAssignREFu8_spec.

Section u8asMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_u8asMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u8asMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u8asMulAssign_spec_attrs-[] -[(int U8); (int U8)])))).
End u8asMulAssign_spec.

Section u8asSubREFau8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asSubREFau8_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u8asSubREFau8_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u8asSubREFau8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), u8asSubREFau8_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType U8) RefSynType (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) u8asSubREFau8_spec_attrs-[] -[(int U8); (shr_ref ulft_a (int U8)); (int U8)])))).
End u8asSubREFau8_spec.

Section u8asSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_u8asSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition u8asSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType U8) (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u8asSub_spec_attrs-[] -[(int U8); (int U8); (int U8)])))).
End u8asSub_spec.

Section u8asSubAssignREFu8_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asSubAssignREFu8_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u8asSubAssignREFu8_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u8asSubAssignREFu8_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), u8asSubAssignREFu8_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType U8) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) u8asSubAssignREFu8_spec_attrs-[] -[(int U8); (shr_ref ulft_0 (int U8))])))).
End u8asSubAssignREFu8_spec.

Section u8asSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_u8asSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition u8asSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u8asSubAssign_spec_attrs-[] -[(int U8); (int U8)])))).
End u8asSubAssign_spec.

Section usizeasAddREFausize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasAddREFausize_spec  : (spec_with _ _ (Add_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_usizeasAddREFausize_add 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition usizeasAddREFausize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), usizeasAddREFausize_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z (place_rfnRT Z) Z (IntSynType USize) RefSynType (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) usizeasAddREFausize_spec_attrs-[] -[(int USize); (shr_ref ulft_a (int USize)); (int USize)])))).
End usizeasAddREFausize_spec.

Section usizeasAdd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasAdd_spec  : (spec_with _ _ (Add_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Add_add_spec  :=
          type_of_usizeasAdd_add 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition usizeasAdd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Add_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasAdd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Add_base_spec Z Z Z (IntSynType USize) (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) usizeasAdd_spec_attrs-[] -[(int USize); (int USize); (int USize)])))).
End usizeasAdd_spec.

Section usizeasAddAssignREFusize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasAddAssignREFusize_spec  : (spec_with _ _ (AddAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_usizeasAddAssignREFusize_add_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition usizeasAddAssignREFusize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), usizeasAddAssignREFusize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z (place_rfnRT Z) (IntSynType USize) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) usizeasAddAssignREFusize_spec_attrs-[] -[(int USize); (shr_ref ulft_0 (int USize))])))).
End usizeasAddAssignREFusize_spec.

Section usizeasAddAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasAddAssign_spec  : (spec_with _ _ (AddAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        AddAssign_add_assign_spec  :=
          type_of_usizeasAddAssign_add_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition usizeasAddAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl AddAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasAddAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((AddAssign_base_spec Z Z (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) usizeasAddAssign_spec_attrs-[] -[(int USize); (int USize)])))).
End usizeasAddAssign_spec.

Section usizeasMulREFausize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasMulREFausize_spec  : (spec_with _ _ (Mul_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_usizeasMulREFausize_mul 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition usizeasMulREFausize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), usizeasMulREFausize_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z (place_rfnRT Z) Z (IntSynType USize) RefSynType (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) usizeasMulREFausize_spec_attrs-[] -[(int USize); (shr_ref ulft_a (int USize)); (int USize)])))).
End usizeasMulREFausize_spec.

Section usizeasMul_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasMul_spec  : (spec_with _ _ (Mul_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Mul_mul_spec  :=
          type_of_usizeasMul_mul 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition usizeasMul_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Mul_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasMul_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Mul_base_spec Z Z Z (IntSynType USize) (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) usizeasMul_spec_attrs-[] -[(int USize); (int USize); (int USize)])))).
End usizeasMul_spec.

Section usizeasMulAssignREFusize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasMulAssignREFusize_spec  : (spec_with _ _ (MulAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_usizeasMulAssignREFusize_mul_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition usizeasMulAssignREFusize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), usizeasMulAssignREFusize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z (place_rfnRT Z) (IntSynType USize) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) usizeasMulAssignREFusize_spec_attrs-[] -[(int USize); (shr_ref ulft_0 (int USize))])))).
End usizeasMulAssignREFusize_spec.

Section usizeasMulAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasMulAssign_spec  : (spec_with _ _ (MulAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        MulAssign_mul_assign_spec  :=
          type_of_usizeasMulAssign_mul_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition usizeasMulAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl MulAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasMulAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((MulAssign_base_spec Z Z (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) usizeasMulAssign_spec_attrs-[] -[(int USize); (int USize)])))).
End usizeasMulAssign_spec.

Section usizeasSubREFausize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasSubREFausize_spec  : (spec_with _ _ (Sub_spec (Z) ((place_rfnRT Z)) (Z))) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_usizeasSubREFausize_sub 
             <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Definition usizeasSubREFausize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), usizeasSubREFausize_spec-[ulft_a] -[]) (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z (place_rfnRT Z) Z (IntSynType USize) RefSynType (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) (drop_glue_trivial_spec_attrs (Z)) usizeasSubREFausize_spec_attrs-[] -[(int USize); (shr_ref ulft_a (int USize)); (int USize)])))).
End usizeasSubREFausize_spec.

Section usizeasSub_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasSub_spec  : (spec_with _ _ (Sub_spec (Z) (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let Output_rt := Z in {|
        Sub_sub_spec  :=
          type_of_usizeasSub_sub 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Definition usizeasSub_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Sub_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasSub_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Sub_base_spec Z Z Z (IntSynType USize) (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) usizeasSub_spec_attrs-[] -[(int USize); (int USize); (int USize)])))).
End usizeasSub_spec.

Section usizeasSubAssignREFusize_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasSubAssignREFusize_spec  : (spec_with _ _ (SubAssign_spec (Z) ((place_rfnRT Z)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_usizeasSubAssignREFusize_sub_assign 
             <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition usizeasSubAssignREFusize_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), usizeasSubAssignREFusize_spec-[ulft_0] -[]) (spec! ( *[ulft_0]) : 1 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z (place_rfnRT Z) (IntSynType USize) RefSynType (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs ((place_rfnRT Z))) usizeasSubAssignREFusize_spec_attrs-[] -[(int USize); (shr_ref ulft_0 (int USize))])))).
End usizeasSubAssignREFusize_spec.

Section usizeasSubAssign_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasSubAssign_spec  : (spec_with _ _ (SubAssign_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        SubAssign_sub_assign_spec  :=
          type_of_usizeasSubAssign_sub_assign 
             : (spec_with 1 [] fn_spec);
      |}
  .
  Definition usizeasSubAssign_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl SubAssign_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasSubAssign_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((SubAssign_base_spec Z Z (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) usizeasSubAssign_spec_attrs-[] -[(int USize); (int USize)])))).
End usizeasSubAssign_spec.

