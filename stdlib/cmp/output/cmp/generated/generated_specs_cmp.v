From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp.

Definition PartialEq_PEq_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → bool).
Record PartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_PartialEq_spec_attrs {
  PartialEq_PEq  : (PartialEq_PEq_sig (Self_rt) (Rhs_rt));
}.
#[global] Arguments PartialEq_spec_attrs : clear implicits.

#[global] Arguments PartialEq_spec_attrs {_ _}.

#[global] Arguments mk_PartialEq_spec_attrs  {_} {_} {_} {_}.


Definition Eq_PEq_refl_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) :=
  (∀ x : (RT_xt (Self_rt)), PartialEq_Self_Self_spec_attrs.(PartialEq_PEq) x x).
Definition Eq_PEq_sym_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_PEq_refl: (Eq_PEq_refl_sig (Self_rt) (PartialEq_Self_Self_spec_attrs))) :=
  (∀ x y : (RT_xt (Self_rt)), PartialEq_Self_Self_spec_attrs.(PartialEq_PEq) x y → PartialEq_Self_Self_spec_attrs.(PartialEq_PEq) y x).
Definition Eq_PEq_trans_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_PEq_refl: (Eq_PEq_refl_sig (Self_rt) (PartialEq_Self_Self_spec_attrs))) (Eq_PEq_sym: (Eq_PEq_sym_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_PEq_refl))) :=
  (∀ x y z: (RT_xt (Self_rt)), PartialEq_Self_Self_spec_attrs.(PartialEq_PEq) x y → PartialEq_Self_Self_spec_attrs.(PartialEq_PEq) y z → PartialEq_Self_Self_spec_attrs.(PartialEq_PEq) x z).
Definition Eq_PEq_leibniz_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_PEq_refl: (Eq_PEq_refl_sig (Self_rt) (PartialEq_Self_Self_spec_attrs))) (Eq_PEq_sym: (Eq_PEq_sym_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_PEq_refl))) (Eq_PEq_trans: (Eq_PEq_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_PEq_refl) (Eq_PEq_sym))) :=
  (∀ a b, PartialEq_Self_Self_spec_attrs.(PartialEq_PEq) a b ↔ a = b).
Record Eq_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )} : Type := mk_Eq_spec_attrs {
  Eq_PEq_refl  : (Eq_PEq_refl_sig (Self_rt) (PartialEq_Self_Self_spec_attrs));
  Eq_PEq_sym  : (Eq_PEq_sym_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_PEq_refl));
  Eq_PEq_trans  : (Eq_PEq_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_PEq_refl) (Eq_PEq_sym));
  Eq_PEq_leibniz  : (Eq_PEq_leibniz_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_PEq_refl) (Eq_PEq_sym) (Eq_PEq_trans));
}.
#[global] Arguments Eq_spec_attrs : clear implicits.

#[global] Arguments Eq_spec_attrs {_ _}.

#[global] Arguments mk_Eq_spec_attrs  {_} {_} {_} {_}.


Definition PartialOrd_POrd_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) :=
  ((RT_xt (Self_rt)) → (RT_xt (Rhs_rt)) → option ordering).
Definition PartialOrd_POrd_eq_cons_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Rhs_rt: RT) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (PartialOrd_POrd: (PartialOrd_POrd_sig (Self_rt) (Rhs_rt) (PartialEq_Self_Rhs_spec_attrs))) :=
  (∀ a b, PartialEq_Self_Rhs_spec_attrs.(PartialEq_PEq) a b ↔ PartialOrd_POrd a b = Some Equal).
Record PartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} `{PartialEq_Self_Rhs_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )} : Type := mk_PartialOrd_spec_attrs {
  PartialOrd_POrd  : (PartialOrd_POrd_sig (Self_rt) (Rhs_rt) (PartialEq_Self_Rhs_spec_attrs));
  PartialOrd_POrd_eq_cons  : (PartialOrd_POrd_eq_cons_sig (Self_rt) (Rhs_rt) (PartialEq_Self_Rhs_spec_attrs) (PartialOrd_POrd));
}.
#[global] Arguments PartialOrd_spec_attrs : clear implicits.

#[global] Arguments PartialOrd_spec_attrs {_ _}.

#[global] Arguments mk_PartialOrd_spec_attrs  {_} {_} {_} {_} {_}.


Definition Ord_Ord_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) :=
  ((RT_xt (Self_rt)) → (RT_xt (Self_rt)) → ordering).
Definition Ord_Ord_POrd_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Ord: (Ord_Ord_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs))) :=
  (∀ a b, PartialOrd_Self_Self_spec_attrs.(PartialOrd_POrd) a b = Some (Ord_Ord a b)).
Definition Ord_Ord_lt_trans_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Ord: (Ord_Ord_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs))) (Ord_Ord_POrd: (Ord_Ord_POrd_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord))) :=
  (∀ a b c, a<o{ Ord_Ord } b → b <o{ Ord_Ord } c → a <o{ Ord_Ord } c).
Definition Ord_Ord_eq_trans_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Ord: (Ord_Ord_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs))) (Ord_Ord_POrd: (Ord_Ord_POrd_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord))) (Ord_Ord_lt_trans: (Ord_Ord_lt_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd))) :=
  (∀ a b c, a=o{ Ord_Ord } b → b =o{ Ord_Ord } c → a =o{ Ord_Ord } c).
Definition Ord_Ord_gt_trans_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Ord: (Ord_Ord_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs))) (Ord_Ord_POrd: (Ord_Ord_POrd_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord))) (Ord_Ord_lt_trans: (Ord_Ord_lt_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd))) (Ord_Ord_eq_trans: (Ord_Ord_eq_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd) (Ord_Ord_lt_trans))) :=
  (∀ a b c, a>o{ Ord_Ord } b → b >o{ Ord_Ord } c → a >o{ Ord_Ord } c).
Definition Ord_Ord_antisym_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Ord: (Ord_Ord_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs))) (Ord_Ord_POrd: (Ord_Ord_POrd_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord))) (Ord_Ord_lt_trans: (Ord_Ord_lt_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd))) (Ord_Ord_eq_trans: (Ord_Ord_eq_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd) (Ord_Ord_lt_trans))) (Ord_Ord_gt_trans: (Ord_Ord_gt_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd) (Ord_Ord_lt_trans) (Ord_Ord_eq_trans))) :=
  (∀ a b, a <o{ Ord_Ord } b ↔ b >o{ Ord_Ord } a).
Record Ord_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )} `{Eq_Self_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)} `{PartialOrd_Self_Self_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)} : Type := mk_Ord_spec_attrs {
  Ord_Ord  : (Ord_Ord_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs));
  Ord_Ord_POrd  : (Ord_Ord_POrd_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord));
  Ord_Ord_lt_trans  : (Ord_Ord_lt_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd));
  Ord_Ord_eq_trans  : (Ord_Ord_eq_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd) (Ord_Ord_lt_trans));
  Ord_Ord_gt_trans  : (Ord_Ord_gt_trans_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd) (Ord_Ord_lt_trans) (Ord_Ord_eq_trans));
  Ord_Ord_antisym  : (Ord_Ord_antisym_sig (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Ord) (Ord_Ord_POrd) (Ord_Ord_lt_trans) (Ord_Ord_eq_trans) (Ord_Ord_gt_trans));
}.
#[global] Arguments Ord_spec_attrs : clear implicits.

#[global] Arguments Ord_spec_attrs {_ _}.

#[global] Arguments mk_Ord_spec_attrs  {_} {_} {_} {_} {_} {_}.


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFAasPartialEqREFB_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (B_rt: RT) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : ((PartialEq_spec_attrs ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))))) :=
  {|
    PartialEq_PEq  :=
      (PartialEq_A_B_spec_attrs.(PartialEq_PEq)) : ((PartialEq_PEq_sig ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt)))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFAasPartialEqREFmutB_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (B_rt: RT) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : ((PartialEq_spec_attrs ((place_rfnRT (A_rt))) (((place_rfnRT (B_rt)) * gname)%type))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, PartialEq_A_B_spec_attrs.(PartialEq_PEq) a b.cur) : ((PartialEq_PEq_sig ((place_rfnRT (A_rt))) (((place_rfnRT (B_rt)) * gname)%type)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFmutAasPartialEqREFB_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (B_rt: RT) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : ((PartialEq_spec_attrs (((place_rfnRT (A_rt)) * gname)%type) ((place_rfnRT (B_rt))))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, PartialEq_A_B_spec_attrs.(PartialEq_PEq) a.cur b) : ((PartialEq_PEq_sig (((place_rfnRT (A_rt)) * gname)%type) ((place_rfnRT (B_rt)))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFmutAasPartialEqREFmutB_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (B_rt: RT) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : ((PartialEq_spec_attrs (((place_rfnRT (A_rt)) * gname)%type) (((place_rfnRT (B_rt)) * gname)%type))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, PartialEq_A_B_spec_attrs.(PartialEq_PEq) a.cur b.cur) : ((PartialEq_PEq_sig (((place_rfnRT (A_rt)) * gname)%type) (((place_rfnRT (B_rt)) * gname)%type)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition unitasPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (unit) (unit))) :=
  {|
    PartialEq_PEq  :=
      (λ _ _, true) : ((PartialEq_PEq_sig (unit) (unit)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition boolasPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (bool) (bool))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (bool) (bool)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialEq_spec_attrs (Z) (Z))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, bool_decide (a = b)) : ((PartialEq_PEq_sig (Z) (Z)));
  |}
.


End attrs.

Section Ordering_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Section components.
    Definition Ordering_Less_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t Ordering_Less_sls +[])).
    Defined.

    Definition Ordering_Less_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (Ordering_Less_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent Ordering_Less_rt.
    #[global] Typeclasses Transparent Ordering_Less_ty.
    Definition Ordering_Equal_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t Ordering_Equal_sls +[])).
    Defined.

    Definition Ordering_Equal_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (Ordering_Equal_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent Ordering_Equal_rt.
    #[global] Typeclasses Transparent Ordering_Equal_ty.
    Definition Ordering_Greater_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t Ordering_Greater_sls +[])).
    Defined.

    Definition Ordering_Greater_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (Ordering_Greater_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent Ordering_Greater_rt.
    #[global] Typeclasses Transparent Ordering_Greater_ty.
    Definition Ordering_enum_rt  :=
      λ rfn : (ordering), match rfn with | Less => Ordering_Less_rt| Equal => Ordering_Equal_rt| Greater => Ordering_Greater_rt end.
    Definition Ordering_enum_ty  : (spec_with 0 [] (∀ (x: _), (type (Ordering_enum_rt (x))))) :=
      spec! ( *[]) : 0 | ( *[]) : ([] : list RT), λ rfn, match rfn as x return type (Ordering_enum_rt x) with | Less => Ordering_Less_ty -[] -[]| Equal => Ordering_Equal_ty -[] -[]| Greater => Ordering_Greater_ty -[] -[] end.
    Program Definition Ordering_enum  : (spec_with 0 [] ((enum ((ordering))))) :=
      spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_enum
        _
        (Ordering_els)
        (λ rfn, Some (match rfn with | Less => "Less" | Equal => "Equal" | Greater => "Greater" end))
        (Ordering_enum_rt)
        (Ordering_enum_ty -[] -[])
        (λ rfn, match rfn as x return RT_rt (Ordering_enum_rt x) with | Less => *[]| Equal => *[]| Greater => *[] end)
        ([("Less", mk_enum_tag_sem _ (Ordering_Less_ty -[] -[]) (λ '( *[]), Less)); ("Equal", mk_enum_tag_sem _ (Ordering_Equal_ty -[] -[]) (λ '( *[]), Equal)); ("Greater", mk_enum_tag_sem _ (Ordering_Greater_ty -[] -[]) (λ '( *[]), Greater))])
        _
        _
        _
        _.
    Next Obligation.
      solve_inhabited.
    Defined.

    Next Obligation.
      solve_enum_is_xrfn_congr.
    Qed.

    Next Obligation.
      done.
    Qed.

    Next Obligation.
      solve_mk_enum_tag_consistent.
    Defined.

    Final Obligation.
      solve_mk_enum_tag_inj_roundtrip.
    Defined.

    #[global] Arguments Ordering_enum : simpl never.

    Definition Ordering_ty_pre  : (spec_with 0 [] ((type _))) :=
      spec! ( *[]) : 0 | ( *[]) : ([] : list RT), enum_t (Ordering_enum -[] -[]).
    Definition Ordering_rt_pre  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (Ordering_ty_pre)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent Ordering_rt_pre.
  End components.
  Arguments enum_ty : simpl never.

  Definition Ordering_ty  : (spec_with 0 [] ((type _))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), enum_t (Ordering_enum -[] -[]).
  Definition Ordering_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (Ordering_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent Ordering_rt.
End Ordering_ty.
#[global] Typeclasses Transparent Ordering_ty.
#[global] Typeclasses Transparent Ordering_rt.
#[global] Arguments Ordering_enum : simpl never.

#[global] Arguments Ordering_rt : clear implicits.

#[global] Arguments Ordering_ty : clear implicits.

#[global] Arguments Ordering_ty {_ _}  .

Global Hint Unfold Ordering_ty : solve_protected_eq_db.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFAasEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (Eq_A_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((Eq_spec_attrs ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)))));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??? ???; simpl; by apply Eq_PEq_refl.
Qed.

Next Obligation.
  intros ??? ???; simpl; by apply Eq_PEq_sym.
Qed.

Next Obligation.
  intros ??? ???; simpl; by apply Eq_PEq_trans.
Qed.

Final Obligation.
  intros ??? ???; simpl; by apply Eq_PEq_leibniz.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFAasPartialOrdREFB_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (B_rt: RT) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : ((PartialOrd_spec_attrs ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, PartialOrd_A_B_spec_attrs.(PartialOrd_POrd) a b) : ((PartialOrd_POrd_sig ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs)))));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))) (_)));
  |}
.
Final Obligation.
  intros ??? ??????; simpl; apply PartialOrd_POrd_eq_cons.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition unitasEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (unit) (unitasPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (unit) (unitasPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (unit) (unitasPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (unit) (unitasPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (unit) (unitasPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ? [] []; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition unitasPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (unit) (unit) (unitasPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some Equal) : ((PartialOrd_POrd_sig (unit) (unit) (unitasPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (unit) (unit) (unitasPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition boolasEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (bool) (boolasPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (bool) (boolasPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (bool) (boolasPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (bool) (boolasPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (bool) (boolasPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (i128asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (i128asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (i128asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (i128asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (i128asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (i128asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (i128asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (i128asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (i16asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (i16asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (i16asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (i16asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (i16asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (i16asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (i16asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (i16asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (i32asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (i32asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (i32asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (i32asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (i32asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (i32asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (i32asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (i32asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (i64asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (i64asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (i64asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (i64asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (i64asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (i64asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (i64asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (i64asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (i8asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (i8asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (i8asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (i8asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (i8asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (i8asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (i8asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (i8asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (isizeasPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (isizeasPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (isizeasPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (isizeasPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (isizeasPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (isizeasPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (isizeasPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (isizeasPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (u128asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (u128asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (u128asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (u128asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (u128asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (u128asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (u128asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (u128asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (u16asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (u16asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (u16asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (u16asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (u16asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (u16asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (u16asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (u16asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (u32asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (u32asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (u32asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (u32asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (u32asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (u32asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (u32asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (u32asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (u64asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (u64asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (u64asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (u64asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (u64asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (u64asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (u64asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (u64asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (u8asPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (u8asPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (u8asPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (u8asPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (u8asPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (u8asPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (u8asPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (u8asPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Eq_spec_attrs (Z) (usizeasPartialEq_spec_attrs))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (Z) (usizeasPartialEq_spec_attrs)));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (Z) (usizeasPartialEq_spec_attrs) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (Z) (usizeasPartialEq_spec_attrs) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (Z) (usizeasPartialEq_spec_attrs) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??; solve_goal.
Qed.

Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((PartialOrd_spec_attrs (Z) (Z) (usizeasPartialEq_spec_attrs))) :=
  {|
    PartialOrd_POrd  :=
      (λ a b, Some(Z.compare a b)) : ((PartialOrd_POrd_sig (Z) (Z) (usizeasPartialEq_spec_attrs)));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (Z) (Z) (usizeasPartialEq_spec_attrs) (_)));
  |}
.
Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_option_OptionTasPartialEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((PartialEq_spec_attrs (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))))) :=
  {|
    PartialEq_PEq  :=
      (λ a b, match a, b with | Some a, Some b => PartialEq_T_T_spec_attrs.(PartialEq_PEq) a b | None, None => true | _, _ => false end) : ((PartialEq_PEq_sig (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt)))))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFAasOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (Eq_A_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (Ord_A_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((Ord_spec_attrs ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))))) :=
  {|
    Ord_Ord  :=
      (λ a b, Ord_A_spec_attrs.(Ord_Ord) a b) : ((Ord_Ord_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)))));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig ((place_rfnRT (A_rt))) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??? ?????; simpl; by apply Ord_Ord_POrd.
Qed.

Next Obligation.
  intros ???? ?????; simpl; by apply Ord_Ord_lt_trans.
Qed.

Next Obligation.
  intros ???? ?????; simpl; by apply Ord_Ord_eq_trans.
Qed.

Next Obligation.
  intros ???? ?????; simpl; by apply Ord_Ord_gt_trans.
Qed.

Final Obligation.
  intros ??? ?????; simpl; by apply Ord_Ord_antisym.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition unitasOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (unit) (unitasPartialEq_spec_attrs) (unitasEq_spec_attrs) (unitasPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (λ a b, Equal) : ((Ord_Ord_sig (unit) (unitasPartialEq_spec_attrs) (unitasEq_spec_attrs) (unitasPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (unit) (unitasPartialEq_spec_attrs) (unitasEq_spec_attrs) (unitasPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (unit) (unitasPartialEq_spec_attrs) (unitasEq_spec_attrs) (unitasPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (unit) (unitasPartialEq_spec_attrs) (unitasEq_spec_attrs) (unitasPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (unit) (unitasPartialEq_spec_attrs) (unitasEq_spec_attrs) (unitasPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (unit) (unitasPartialEq_spec_attrs) (unitasEq_spec_attrs) (unitasPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ? [] []; unfold ord_lt, ord_gt; naive_solver.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (i128asPartialEq_spec_attrs) (i128asEq_spec_attrs) (i128asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (i128asPartialEq_spec_attrs) (i128asEq_spec_attrs) (i128asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (i128asPartialEq_spec_attrs) (i128asEq_spec_attrs) (i128asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (i128asPartialEq_spec_attrs) (i128asEq_spec_attrs) (i128asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (i128asPartialEq_spec_attrs) (i128asEq_spec_attrs) (i128asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (i128asPartialEq_spec_attrs) (i128asEq_spec_attrs) (i128asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (i128asPartialEq_spec_attrs) (i128asEq_spec_attrs) (i128asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (i16asPartialEq_spec_attrs) (i16asEq_spec_attrs) (i16asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (i16asPartialEq_spec_attrs) (i16asEq_spec_attrs) (i16asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (i16asPartialEq_spec_attrs) (i16asEq_spec_attrs) (i16asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (i16asPartialEq_spec_attrs) (i16asEq_spec_attrs) (i16asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (i16asPartialEq_spec_attrs) (i16asEq_spec_attrs) (i16asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (i16asPartialEq_spec_attrs) (i16asEq_spec_attrs) (i16asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (i16asPartialEq_spec_attrs) (i16asEq_spec_attrs) (i16asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (i32asPartialEq_spec_attrs) (i32asEq_spec_attrs) (i32asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (i32asPartialEq_spec_attrs) (i32asEq_spec_attrs) (i32asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (i32asPartialEq_spec_attrs) (i32asEq_spec_attrs) (i32asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (i32asPartialEq_spec_attrs) (i32asEq_spec_attrs) (i32asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (i32asPartialEq_spec_attrs) (i32asEq_spec_attrs) (i32asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (i32asPartialEq_spec_attrs) (i32asEq_spec_attrs) (i32asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (i32asPartialEq_spec_attrs) (i32asEq_spec_attrs) (i32asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (i64asPartialEq_spec_attrs) (i64asEq_spec_attrs) (i64asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (i64asPartialEq_spec_attrs) (i64asEq_spec_attrs) (i64asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (i64asPartialEq_spec_attrs) (i64asEq_spec_attrs) (i64asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (i64asPartialEq_spec_attrs) (i64asEq_spec_attrs) (i64asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (i64asPartialEq_spec_attrs) (i64asEq_spec_attrs) (i64asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (i64asPartialEq_spec_attrs) (i64asEq_spec_attrs) (i64asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (i64asPartialEq_spec_attrs) (i64asEq_spec_attrs) (i64asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (i8asPartialEq_spec_attrs) (i8asEq_spec_attrs) (i8asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (i8asPartialEq_spec_attrs) (i8asEq_spec_attrs) (i8asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (i8asPartialEq_spec_attrs) (i8asEq_spec_attrs) (i8asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (i8asPartialEq_spec_attrs) (i8asEq_spec_attrs) (i8asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (i8asPartialEq_spec_attrs) (i8asEq_spec_attrs) (i8asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (i8asPartialEq_spec_attrs) (i8asEq_spec_attrs) (i8asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (i8asPartialEq_spec_attrs) (i8asEq_spec_attrs) (i8asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (isizeasPartialEq_spec_attrs) (isizeasEq_spec_attrs) (isizeasPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (isizeasPartialEq_spec_attrs) (isizeasEq_spec_attrs) (isizeasPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (isizeasPartialEq_spec_attrs) (isizeasEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (isizeasPartialEq_spec_attrs) (isizeasEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (isizeasPartialEq_spec_attrs) (isizeasEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (isizeasPartialEq_spec_attrs) (isizeasEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (isizeasPartialEq_spec_attrs) (isizeasEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (u128asPartialEq_spec_attrs) (u128asEq_spec_attrs) (u128asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (u128asPartialEq_spec_attrs) (u128asEq_spec_attrs) (u128asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (u128asPartialEq_spec_attrs) (u128asEq_spec_attrs) (u128asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (u128asPartialEq_spec_attrs) (u128asEq_spec_attrs) (u128asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (u128asPartialEq_spec_attrs) (u128asEq_spec_attrs) (u128asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (u128asPartialEq_spec_attrs) (u128asEq_spec_attrs) (u128asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (u128asPartialEq_spec_attrs) (u128asEq_spec_attrs) (u128asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (u16asPartialEq_spec_attrs) (u16asEq_spec_attrs) (u16asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (u16asPartialEq_spec_attrs) (u16asEq_spec_attrs) (u16asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (u16asPartialEq_spec_attrs) (u16asEq_spec_attrs) (u16asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (u16asPartialEq_spec_attrs) (u16asEq_spec_attrs) (u16asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (u16asPartialEq_spec_attrs) (u16asEq_spec_attrs) (u16asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (u16asPartialEq_spec_attrs) (u16asEq_spec_attrs) (u16asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (u16asPartialEq_spec_attrs) (u16asEq_spec_attrs) (u16asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (u32asPartialEq_spec_attrs) (u32asEq_spec_attrs) (u32asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (u32asPartialEq_spec_attrs) (u32asEq_spec_attrs) (u32asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (u32asPartialEq_spec_attrs) (u32asEq_spec_attrs) (u32asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (u32asPartialEq_spec_attrs) (u32asEq_spec_attrs) (u32asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (u32asPartialEq_spec_attrs) (u32asEq_spec_attrs) (u32asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (u32asPartialEq_spec_attrs) (u32asEq_spec_attrs) (u32asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (u32asPartialEq_spec_attrs) (u32asEq_spec_attrs) (u32asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (u64asPartialEq_spec_attrs) (u64asEq_spec_attrs) (u64asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (u64asPartialEq_spec_attrs) (u64asEq_spec_attrs) (u64asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (u64asPartialEq_spec_attrs) (u64asEq_spec_attrs) (u64asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (u64asPartialEq_spec_attrs) (u64asEq_spec_attrs) (u64asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (u64asPartialEq_spec_attrs) (u64asEq_spec_attrs) (u64asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (u64asPartialEq_spec_attrs) (u64asEq_spec_attrs) (u64asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (u64asPartialEq_spec_attrs) (u64asEq_spec_attrs) (u64asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (u8asPartialEq_spec_attrs) (u8asEq_spec_attrs) (u8asPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (u8asPartialEq_spec_attrs) (u8asEq_spec_attrs) (u8asPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (u8asPartialEq_spec_attrs) (u8asEq_spec_attrs) (u8asPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (u8asPartialEq_spec_attrs) (u8asEq_spec_attrs) (u8asPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (u8asPartialEq_spec_attrs) (u8asEq_spec_attrs) (u8asPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (u8asPartialEq_spec_attrs) (u8asEq_spec_attrs) (u8asPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (u8asPartialEq_spec_attrs) (u8asEq_spec_attrs) (u8asPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Ord_spec_attrs (Z) (usizeasPartialEq_spec_attrs) (usizeasEq_spec_attrs) (usizeasPartialOrd_spec_attrs))) :=
  {|
    Ord_Ord  :=
      (Z.compare) : ((Ord_Ord_sig (Z) (usizeasPartialEq_spec_attrs) (usizeasEq_spec_attrs) (usizeasPartialOrd_spec_attrs)));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (Z) (usizeasPartialEq_spec_attrs) (usizeasEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (Z) (usizeasPartialEq_spec_attrs) (usizeasEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (Z) (usizeasPartialEq_spec_attrs) (usizeasEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (Z) (usizeasPartialEq_spec_attrs) (usizeasEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (Z) (usizeasPartialEq_spec_attrs) (usizeasEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ???; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Next Obligation.
  intros ????; solve_goal.
Qed.

Final Obligation.
  intros ???; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_option_OptionTasEq_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Eq_spec_attrs (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))))) :=
  {|
    Eq_PEq_refl  :=
      (_) : ((Eq_PEq_refl_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)))));
    Eq_PEq_sym  :=
      (_) : ((Eq_PEq_sym_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_)));
    Eq_PEq_trans  :=
      (_) : ((Eq_PEq_trans_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_) (_)));
    Eq_PEq_leibniz  :=
      (_) : ((Eq_PEq_leibniz_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??? ?? []; simpl; by try apply Eq_PEq_refl.
Qed.

Next Obligation.
  intros ??? ?? [] []; simpl; by try apply Eq_PEq_sym.
Qed.

Next Obligation.
  intros ??? ?? [] [] []; simpl; by try apply Eq_PEq_trans.
Qed.

Final Obligation.
  intros ??? ?? [a | ] [b | ]; simpl; [etrans; first apply Eq_PEq_leibniz | ..]; naive_solver.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_option_OptionTasPartialOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((PartialOrd_spec_attrs (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))))) :=
  {|
    PartialOrd_POrd  :=
      (option_partial_cmp PartialOrd_T_T_spec_attrs.(PartialOrd_POrd)) : ((PartialOrd_POrd_sig (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)))));
    PartialOrd_POrd_eq_cons  :=
      (_) : ((PartialOrd_POrd_eq_cons_sig (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_)));
  |}
.
Final Obligation.
  intros ??? ?? [] []; simpl; by try apply PartialOrd_POrd_eq_cons.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_option_OptionTasOrd_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Ord_spec_attrs (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))))) :=
  {|
    Ord_Ord  :=
      (option_cmp Ord_T_spec_attrs.(Ord_Ord)) : ((Ord_Ord_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)))));
    Ord_Ord_POrd  :=
      (_) : ((Ord_Ord_POrd_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_)));
    Ord_Ord_lt_trans  :=
      (_) : ((Ord_Ord_lt_trans_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_) (_)));
    Ord_Ord_eq_trans  :=
      (_) : ((Ord_Ord_eq_trans_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_) (_) (_)));
    Ord_Ord_gt_trans  :=
      (_) : ((Ord_Ord_gt_trans_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_) (_) (_) (_)));
    Ord_Ord_antisym  :=
      (_) : ((Ord_Ord_antisym_sig (((((Option_rt)) ((T_rt))))) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??????? [] []; simpl; by try apply Ord_Ord_POrd.
Qed.

Next Obligation.
  intros ??????? [] [] []; simpl; by try apply Ord_Ord_lt_trans.
Qed.

Next Obligation.
  intros ??????? [] [] []; simpl; by try apply Ord_Ord_eq_trans.
Qed.

Next Obligation.
  intros ??????? [] [] []; simpl; by try apply Ord_Ord_gt_trans.
Qed.

Final Obligation.
  intros ??????? [] []; simpl; by try apply Ord_Ord_antisym.
Qed.



End attrs.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition Ord_max_closure0_FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) : ((FnOnce_spec_attrs (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)))) :=
  {|
    FnOnce_Params  :=
      ((plist id [])) : ((FnOnce_Params_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt))));
    FnOnce_Pre  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _), (∃ (a: _) (b: _), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (True))%I) : ((FnOnce_Pre_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (_)));
    FnOnce_Post  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _) (_ret: _), (∃ (a: _) (b: _), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ ((⌜(_ret = (Ord_Self_spec_attrs.(Ord_Ord) a b))%Z⌝))
      ∗ (True))%I) : ((FnOnce_Post_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (_) (_)));
    FnOnce_PostMut  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _) (_self_post: _) (_ret: _), (∃ (a: _) (b: _), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ ((⌜(_ret = (Ord_Self_spec_attrs.(Ord_Ord) a b))%Z⌝)
      ∗ (⌜(_self_post = (tt))%Z⌝))
      ∗ (True))%I) : ((FnOnce_PostMut_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (_) (_) (_)));
    FnOnce_UnwindCondition  :=
      (λ (_self: _) (_params: (plist id [])) (_args: _), False) : ((FnOnce_UnwindCondition_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (_) (_) (_) (_)));
  |}
.


Program Definition Ord_min_closure0_FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) : ((FnOnce_spec_attrs (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)))) :=
  {|
    FnOnce_Params  :=
      ((plist id [])) : ((FnOnce_Params_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt))));
    FnOnce_Pre  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _), (∃ (a: _) (b: _), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (True))%I) : ((FnOnce_Pre_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (_)));
    FnOnce_Post  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _) (_ret: _), (∃ (a: _) (b: _), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ ((⌜(_ret = (Ord_Self_spec_attrs.(Ord_Ord) a b))%Z⌝))
      ∗ (True))%I) : ((FnOnce_Post_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (_) (_)));
    FnOnce_PostMut  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _) (_self_post: _) (_ret: _), (∃ (a: _) (b: _), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ ((⌜(_ret = (Ord_Self_spec_attrs.(Ord_Ord) a b))%Z⌝)
      ∗ (⌜(_self_post = (tt))%Z⌝))
      ∗ (True))%I) : ((FnOnce_PostMut_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (_) (_) (_)));
    FnOnce_UnwindCondition  :=
      (λ (_self: _) (_params: (plist id [])) (_args: _), False) : ((FnOnce_UnwindCondition_sig (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (_) (_) (_) (_)));
  |}
.


End closure_attrs.

(* Included specifications from configured file extra_specs.v *)

(** Lift to Rocq-level typeclasses *)
Lemma eq_correct_eq `{!refinedrustGS Σ} rt
  (partial_eq_attrs : PartialEq_spec_attrs rt rt)
  (eq_attrs : Eq_spec_attrs rt partial_eq_attrs) : CorrectEq (PartialEq_PEq partial_eq_attrs).
Proof.
  constructor.
  - by unshelve eapply Eq_PEq_refl.
  - by unshelve eapply Eq_PEq_sym.
  - by unshelve eapply Eq_PEq_trans.
  - by unshelve eapply Eq_PEq_leibniz.
Qed.
Global Hint Extern 1 (CorrectEq (PartialEq_PEq _)) => apply eq_correct_eq; done : typeclass_instances.

Lemma ord_correct_ord `{!refinedrustGS Σ} rt
  (partial_eq_attrs : PartialEq_spec_attrs rt rt)
  (eq_attrs : Eq_spec_attrs rt partial_eq_attrs)
  (partial_ord_attrs : PartialOrd_spec_attrs rt rt partial_eq_attrs)
  (ord_attrs : Ord_spec_attrs rt partial_eq_attrs eq_attrs partial_ord_attrs) : CorrectOrd (PartialEq_PEq partial_eq_attrs) (Ord_Ord ord_attrs).
Proof.
  constructor.
  - apply _.
  - intros. rewrite PartialOrd_POrd_eq_cons.
    erewrite Ord_Ord_POrd. split; intros; simplify_eq; [done | f_equiv; done].
  - apply Ord_Ord_lt_trans.
  - apply Ord_Ord_gt_trans.
  - apply Ord_Ord_antisym.
Qed.
Global Hint Extern 1 (CorrectOrd _ (Ord_Ord _)) => apply ord_correct_ord; done : typeclass_instances.

Lemma ord_correct_partial_ord `{!refinedrustGS Σ} rt
  (partial_eq_attrs : PartialEq_spec_attrs rt rt)
  (eq_attrs : Eq_spec_attrs rt partial_eq_attrs)
  (partial_ord_attrs : PartialOrd_spec_attrs rt rt partial_eq_attrs)
  (ord_attrs : Ord_spec_attrs rt partial_eq_attrs eq_attrs partial_ord_attrs) : 
  PartialCmpToCmp (PartialOrd_POrd partial_ord_attrs) (Ord_Ord ord_attrs).
Proof.
  constructor.
  - intros. apply Ord_Ord_POrd.
Qed.
Global Hint Extern 30 (PartialCmpToCmp (PartialOrd_POrd _) (Ord_Ord _)) => apply ord_correct_partial_ord; done : typeclass_instances.
Record PartialEq_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_PartialEq_spec {
  PartialEq_eq_spec  : (spec_with 2 [] fn_spec);
  PartialEq_ne_spec  : (spec_with 2 [] fn_spec);
}.
#[global] Arguments PartialEq_spec : clear implicits.

#[global] Arguments PartialEq_spec {_ _}.


Record Eq_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Eq_spec {
  Eq_assert_fields_are_eq_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments Eq_spec : clear implicits.

#[global] Arguments Eq_spec {_ _}.


Record PartialOrd_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Rhs_rt : !RT} : Type := mk_PartialOrd_spec {
  PartialOrd_ge_spec  : (spec_with 2 [] fn_spec);
  PartialOrd_gt_spec  : (spec_with 2 [] fn_spec);
  PartialOrd_le_spec  : (spec_with 2 [] fn_spec);
  PartialOrd_lt_spec  : (spec_with 2 [] fn_spec);
  PartialOrd_partial_cmp_spec  : (spec_with 2 [] fn_spec);
}.
#[global] Arguments PartialOrd_spec : clear implicits.

#[global] Arguments PartialOrd_spec {_ _}.


Record Ord_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Ord_spec {
  Ord_clamp_spec  : (spec_with 0 [] fn_spec);
  Ord_cmp_spec  : (spec_with 2 [] fn_spec);
  Ord_max_spec  : (spec_with 0 [] fn_spec);
  Ord_min_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments Ord_spec : clear implicits.

#[global] Arguments Ord_spec {_ _}.


Section PartialEq.
Context `{RRGS : !refinedrustGS Σ}.
Definition PartialEq_spec_incl `{Self_rt : !RT} `{Rhs_rt : !RT} (spec1: ((PartialEq_spec (Self_rt) (Rhs_rt)))) (spec2: ((PartialEq_spec (Self_rt) (Rhs_rt)))) : Prop :=
  ((function_subtype (spec1.(PartialEq_eq_spec)) (spec2.(PartialEq_eq_spec)))) ∧ ((function_subtype (spec1.(PartialEq_ne_spec)) (spec2.(PartialEq_ne_spec)))).
Instance PartialEq_spec_incl_preorder `{Self_rt : !RT} `{Rhs_rt : !RT} : (PreOrder (PartialEq_spec_incl (Self_rt := Self_rt) (Rhs_rt := Rhs_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_PartialEq_spec `{Self_rt : !RT} `{Rhs_rt : !RT} : (ScopeBindable ((PartialEq_spec (Self_rt) (Rhs_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((PartialEq_spec (Self_rt) (Rhs_rt)))) :=
      {|
        PartialEq_eq_spec  :=
          (scope_add_typarams (rts) (tys) (s.(PartialEq_eq_spec)));
        PartialEq_ne_spec  :=
          (scope_add_typarams (rts) (tys) (s.(PartialEq_ne_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((PartialEq_spec (Self_rt) (Rhs_rt)))) :=
      {|
        PartialEq_eq_spec  :=
          (scope_add_elctx (E) (s.(PartialEq_eq_spec)));
        PartialEq_ne_spec  :=
          (scope_add_elctx (E) (s.(PartialEq_ne_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_PartialEq_spec.

Definition PartialEq_eq_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), other :@: (shr_ref ulft_2 Rhs_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, PartialEq_Self_Rhs_spec_attrs.(PartialEq_PEq) self other @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition PartialEq_ne_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), other :@: (shr_ref ulft_2 Rhs_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, negb (PartialEq_Self_Rhs_spec_attrs.(PartialEq_PEq) self other) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition PartialEq_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (_ATTRS: ((PartialEq_spec_attrs ((Self_rt)) ((Rhs_rt))))) : (spec_with _ _ (PartialEq_spec ((Self_rt)) ((Rhs_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), {|
      PartialEq_eq_spec  :=
        (PartialEq_eq_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 2 [] fn_spec);
      PartialEq_ne_spec  :=
        (PartialEq_ne_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 2 [] fn_spec);
    |}
.
Arguments PartialEq_base_spec : simpl never.


End PartialEq.

Section Eq.
Context `{RRGS : !refinedrustGS Σ}.
Definition Eq_spec_incl `{Self_rt : !RT} (spec1: ((Eq_spec (Self_rt)))) (spec2: ((Eq_spec (Self_rt)))) : Prop :=
  ((function_subtype (spec1.(Eq_assert_fields_are_eq_spec)) (spec2.(Eq_assert_fields_are_eq_spec)))).
Instance Eq_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Eq_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Eq_spec `{Self_rt : !RT} : (ScopeBindable ((Eq_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Eq_spec (Self_rt)))) :=
      {|
        Eq_assert_fields_are_eq_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Eq_assert_fields_are_eq_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Eq_spec (Self_rt)))) :=
      {|
        Eq_assert_fields_are_eq_spec  :=
          (scope_add_elctx (E) (s.(Eq_assert_fields_are_eq_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Eq_spec.

Definition Eq_assert_fields_are_eq_base_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Eq_base_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((Eq_spec_attrs ((Self_rt)) (PartialEq_Self_Self_spec_attrs)))) : (spec_with _ _ (Eq_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      Eq_assert_fields_are_eq_spec  :=
        (Eq_assert_fields_are_eq_base_spec ((Self_rt)) (Self_st)) PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 1 [] fn_spec);
    |}
.
Arguments Eq_base_spec : simpl never.


End Eq.

Section PartialOrd.
Context `{RRGS : !refinedrustGS Σ}.
Definition PartialOrd_spec_incl `{Self_rt : !RT} `{Rhs_rt : !RT} (spec1: ((PartialOrd_spec (Self_rt) (Rhs_rt)))) (spec2: ((PartialOrd_spec (Self_rt) (Rhs_rt)))) : Prop :=
  ((function_subtype (spec1.(PartialOrd_ge_spec)) (spec2.(PartialOrd_ge_spec)))) ∧ ((function_subtype (spec1.(PartialOrd_gt_spec)) (spec2.(PartialOrd_gt_spec)))) ∧ ((function_subtype (spec1.(PartialOrd_le_spec)) (spec2.(PartialOrd_le_spec)))) ∧ ((function_subtype (spec1.(PartialOrd_lt_spec)) (spec2.(PartialOrd_lt_spec)))) ∧ ((function_subtype (spec1.(PartialOrd_partial_cmp_spec)) (spec2.(PartialOrd_partial_cmp_spec)))).
Instance PartialOrd_spec_incl_preorder `{Self_rt : !RT} `{Rhs_rt : !RT} : (PreOrder (PartialOrd_spec_incl (Self_rt := Self_rt) (Rhs_rt := Rhs_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_PartialOrd_spec `{Self_rt : !RT} `{Rhs_rt : !RT} : (ScopeBindable ((PartialOrd_spec (Self_rt) (Rhs_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((PartialOrd_spec (Self_rt) (Rhs_rt)))) :=
      {|
        PartialOrd_ge_spec  :=
          (scope_add_typarams (rts) (tys) (s.(PartialOrd_ge_spec)));
        PartialOrd_gt_spec  :=
          (scope_add_typarams (rts) (tys) (s.(PartialOrd_gt_spec)));
        PartialOrd_le_spec  :=
          (scope_add_typarams (rts) (tys) (s.(PartialOrd_le_spec)));
        PartialOrd_lt_spec  :=
          (scope_add_typarams (rts) (tys) (s.(PartialOrd_lt_spec)));
        PartialOrd_partial_cmp_spec  :=
          (scope_add_typarams (rts) (tys) (s.(PartialOrd_partial_cmp_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((PartialOrd_spec (Self_rt) (Rhs_rt)))) :=
      {|
        PartialOrd_ge_spec  :=
          (scope_add_elctx (E) (s.(PartialOrd_ge_spec)));
        PartialOrd_gt_spec  :=
          (scope_add_elctx (E) (s.(PartialOrd_gt_spec)));
        PartialOrd_le_spec  :=
          (scope_add_elctx (E) (s.(PartialOrd_le_spec)));
        PartialOrd_lt_spec  :=
          (scope_add_elctx (E) (s.(PartialOrd_lt_spec)));
        PartialOrd_partial_cmp_spec  :=
          (scope_add_elctx (E) (s.(PartialOrd_partial_cmp_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_PartialOrd_spec.

Definition PartialOrd_ge_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), other :@: (shr_ref ulft_2 Rhs_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (PartialOrd_Self_Rhs_spec_attrs.(PartialOrd_POrd) self other = Some Greater) || bool_decide (PartialOrd_Self_Rhs_spec_attrs.(PartialOrd_POrd) self other = Some Equal) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition PartialOrd_gt_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), other :@: (shr_ref ulft_2 Rhs_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (PartialOrd_Self_Rhs_spec_attrs.(PartialOrd_POrd) self other = Some Greater) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition PartialOrd_le_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), other :@: (shr_ref ulft_2 Rhs_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (PartialOrd_Self_Rhs_spec_attrs.(PartialOrd_POrd) self other = Some Less) || bool_decide (PartialOrd_Self_Rhs_spec_attrs.(PartialOrd_POrd) self other = Some Equal) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition PartialOrd_lt_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), other :@: (shr_ref ulft_2 Rhs_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (PartialOrd_Self_Rhs_spec_attrs.(PartialOrd_POrd) self other = Some Less) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition PartialOrd_partial_cmp_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([(Self_rt, Self_st); (Rhs_rt, Rhs_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), other :@: (shr_ref ulft_2 Rhs_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, PartialOrd_Self_Rhs_spec_attrs.(PartialOrd_POrd) self other @ (Option_ty ((Ordering_rt)) -[] -[(Ordering_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition PartialOrd_base_spec (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (_ATTRS: ((PartialOrd_spec_attrs ((Self_rt)) ((Rhs_rt)) (PartialEq_Self_Rhs_spec_attrs)))) : (spec_with _ _ (PartialOrd_spec ((Self_rt)) ((Rhs_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), {|
      PartialOrd_ge_spec  :=
        (PartialOrd_ge_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 2 [] fn_spec);
      PartialOrd_gt_spec  :=
        (PartialOrd_gt_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 2 [] fn_spec);
      PartialOrd_le_spec  :=
        (PartialOrd_le_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 2 [] fn_spec);
      PartialOrd_lt_spec  :=
        (PartialOrd_lt_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 2 [] fn_spec);
      PartialOrd_partial_cmp_spec  :=
        (PartialOrd_partial_cmp_base_spec ((Self_rt)) ((Rhs_rt)) (Self_st) (Rhs_st)) PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Rhs_ty : (spec_with 2 [] fn_spec);
    |}
.
Arguments PartialOrd_base_spec : simpl never.


End PartialOrd.

Section Ord.
Context `{RRGS : !refinedrustGS Σ}.
Definition Ord_spec_incl `{Self_rt : !RT} (spec1: ((Ord_spec (Self_rt)))) (spec2: ((Ord_spec (Self_rt)))) : Prop :=
  ((function_subtype (spec1.(Ord_clamp_spec)) (spec2.(Ord_clamp_spec)))) ∧ ((function_subtype (spec1.(Ord_cmp_spec)) (spec2.(Ord_cmp_spec)))) ∧ ((function_subtype (spec1.(Ord_max_spec)) (spec2.(Ord_max_spec)))) ∧ ((function_subtype (spec1.(Ord_min_spec)) (spec2.(Ord_min_spec)))).
Instance Ord_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Ord_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Ord_spec `{Self_rt : !RT} : (ScopeBindable ((Ord_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Ord_spec (Self_rt)))) :=
      {|
        Ord_clamp_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Ord_clamp_spec)));
        Ord_cmp_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Ord_cmp_spec)));
        Ord_max_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Ord_max_spec)));
        Ord_min_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Ord_min_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Ord_spec (Self_rt)))) :=
      {|
        Ord_clamp_spec  :=
          (scope_add_elctx (E) (s.(Ord_clamp_spec)));
        Ord_cmp_spec  :=
          (scope_add_elctx (E) (s.(Ord_cmp_spec)));
        Ord_max_spec  :=
          (scope_add_elctx (E) (s.(Ord_max_spec)));
        Ord_min_spec  :=
          (scope_add_elctx (E) (s.(Ord_min_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Ord_spec.

Definition Ord_clamp_base_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, min, max) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, min :@: Self_ty, max :@: Self_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ Self_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Ord_cmp_base_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), other :@: (shr_ref ulft_2 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Ord_Self_spec_attrs.(Ord_Ord) self other @ (Ordering_ty  -[] -[]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Ord_max_base_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, other :@: Self_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (Ord_Self_spec_attrs.(Ord_Ord) self other = Less) then other else self @ Self_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) DropGlue_Self_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).

Definition Ord_min_base_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, other :@: Self_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (Ord_Self_spec_attrs.(Ord_Ord) self other = Less) then self else other @ Self_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) DropGlue_Self_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).

Definition Ord_base_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((Ord_spec_attrs ((Self_rt)) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs)))) : (spec_with _ _ (Ord_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      Ord_clamp_spec  :=
        (Ord_clamp_base_spec ((Self_rt)) (Self_st)) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
      Ord_cmp_spec  :=
        (Ord_cmp_base_spec ((Self_rt)) (Self_st)) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 2 [] fn_spec);
      Ord_max_spec  :=
        (Ord_max_base_spec ((Self_rt)) (Self_st)) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
      Ord_min_spec  :=
        (Ord_min_base_spec ((Self_rt)) (Self_st)) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
    |}
.
Arguments Ord_base_spec : simpl never.


End Ord.

Section PartialEq_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_PartialEq_eq (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt))))) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (PartialEq_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), (λ π, ((∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Rhs_lfts_inst : prod_vec lft DropGlue_Rhs_realization.(trait_ctx_lfts)) (DropGlue_Rhs_tys_inst : plist type DropGlue_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Rhs_realization.(trait_ctx_spec) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))⌝ ∗ DropGlue_Rhs_realization.(trait_ctx_wf) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst π)
      ∗ (∃ (PartialEq_Self_Rhs_lfts_inst : prod_vec lft PartialEq_Self_Rhs_realization.(trait_ctx_lfts)) (PartialEq_Self_Rhs_tys_inst : plist type PartialEq_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Rhs_realization.(trait_ctx_spec) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialEq_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialEq_Self_Rhs_realization.(trait_ctx_wf) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst π))%I).
  Definition trait_incl_of_PartialEq_ne (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt))))) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (PartialEq_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), (λ π, ((∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Rhs_lfts_inst : prod_vec lft DropGlue_Rhs_realization.(trait_ctx_lfts)) (DropGlue_Rhs_tys_inst : plist type DropGlue_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Rhs_realization.(trait_ctx_spec) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))⌝ ∗ DropGlue_Rhs_realization.(trait_ctx_wf) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst π)
      ∗ (∃ (PartialEq_Self_Rhs_lfts_inst : prod_vec lft PartialEq_Self_Rhs_realization.(trait_ctx_lfts)) (PartialEq_Self_Rhs_tys_inst : plist type PartialEq_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Rhs_realization.(trait_ctx_spec) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialEq_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialEq_Self_Rhs_realization.(trait_ctx_wf) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst π))%I).
End PartialEq_trait_req_incls.

Section Eq_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Eq_assert_fields_are_eq (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π))%I).
End Eq_trait_req_incls.

Section PartialOrd_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_PartialOrd_ge (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (PartialEq_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt))))) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) (PartialOrd_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Rhs_lfts_inst : prod_vec lft PartialEq_Self_Rhs_realization.(trait_ctx_lfts)) (PartialEq_Self_Rhs_tys_inst : plist type PartialEq_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Rhs_realization.(trait_ctx_spec) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialEq_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialEq_Self_Rhs_realization.(trait_ctx_wf) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Rhs_lfts_inst : prod_vec lft DropGlue_Rhs_realization.(trait_ctx_lfts)) (DropGlue_Rhs_tys_inst : plist type DropGlue_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Rhs_realization.(trait_ctx_spec) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))⌝ ∗ DropGlue_Rhs_realization.(trait_ctx_wf) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Rhs_lfts_inst : prod_vec lft PartialOrd_Self_Rhs_realization.(trait_ctx_lfts)) (PartialOrd_Self_Rhs_tys_inst : plist type PartialOrd_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Rhs_realization.(trait_ctx_spec) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialOrd_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialOrd_Self_Rhs_realization.(trait_ctx_wf) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst π))%I).
  Definition trait_incl_of_PartialOrd_gt (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (PartialEq_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt))))) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) (PartialOrd_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Rhs_lfts_inst : prod_vec lft PartialEq_Self_Rhs_realization.(trait_ctx_lfts)) (PartialEq_Self_Rhs_tys_inst : plist type PartialEq_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Rhs_realization.(trait_ctx_spec) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialEq_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialEq_Self_Rhs_realization.(trait_ctx_wf) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Rhs_lfts_inst : prod_vec lft DropGlue_Rhs_realization.(trait_ctx_lfts)) (DropGlue_Rhs_tys_inst : plist type DropGlue_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Rhs_realization.(trait_ctx_spec) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))⌝ ∗ DropGlue_Rhs_realization.(trait_ctx_wf) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Rhs_lfts_inst : prod_vec lft PartialOrd_Self_Rhs_realization.(trait_ctx_lfts)) (PartialOrd_Self_Rhs_tys_inst : plist type PartialOrd_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Rhs_realization.(trait_ctx_spec) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialOrd_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialOrd_Self_Rhs_realization.(trait_ctx_wf) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst π))%I).
  Definition trait_incl_of_PartialOrd_le (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (PartialEq_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt))))) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) (PartialOrd_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Rhs_lfts_inst : prod_vec lft PartialEq_Self_Rhs_realization.(trait_ctx_lfts)) (PartialEq_Self_Rhs_tys_inst : plist type PartialEq_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Rhs_realization.(trait_ctx_spec) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialEq_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialEq_Self_Rhs_realization.(trait_ctx_wf) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Rhs_lfts_inst : prod_vec lft DropGlue_Rhs_realization.(trait_ctx_lfts)) (DropGlue_Rhs_tys_inst : plist type DropGlue_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Rhs_realization.(trait_ctx_spec) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))⌝ ∗ DropGlue_Rhs_realization.(trait_ctx_wf) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Rhs_lfts_inst : prod_vec lft PartialOrd_Self_Rhs_realization.(trait_ctx_lfts)) (PartialOrd_Self_Rhs_tys_inst : plist type PartialOrd_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Rhs_realization.(trait_ctx_spec) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialOrd_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialOrd_Self_Rhs_realization.(trait_ctx_wf) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst π))%I).
  Definition trait_incl_of_PartialOrd_lt (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (PartialEq_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt))))) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) (PartialOrd_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Rhs_lfts_inst : prod_vec lft PartialEq_Self_Rhs_realization.(trait_ctx_lfts)) (PartialEq_Self_Rhs_tys_inst : plist type PartialEq_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Rhs_realization.(trait_ctx_spec) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialEq_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialEq_Self_Rhs_realization.(trait_ctx_wf) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Rhs_lfts_inst : prod_vec lft DropGlue_Rhs_realization.(trait_ctx_lfts)) (DropGlue_Rhs_tys_inst : plist type DropGlue_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Rhs_realization.(trait_ctx_spec) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))⌝ ∗ DropGlue_Rhs_realization.(trait_ctx_wf) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Rhs_lfts_inst : prod_vec lft PartialOrd_Self_Rhs_realization.(trait_ctx_lfts)) (PartialOrd_Self_Rhs_tys_inst : plist type PartialOrd_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Rhs_realization.(trait_ctx_spec) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialOrd_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialOrd_Self_Rhs_realization.(trait_ctx_wf) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst π))%I).
  Definition trait_incl_of_PartialOrd_partial_cmp (Self_rt: RT) (Rhs_rt: RT) (Self_st: syn_type) (Rhs_st: syn_type) (PartialEq_Self_Rhs_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) (PartialEq_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Rhs_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) (DropGlue_Rhs_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt))))) (PartialOrd_Self_Rhs_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) (PartialOrd_Self_Rhs_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Rhs_lfts_inst : prod_vec lft PartialEq_Self_Rhs_realization.(trait_ctx_lfts)) (PartialEq_Self_Rhs_tys_inst : plist type PartialEq_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Rhs_realization.(trait_ctx_spec) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialEq_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialEq_Self_Rhs_realization.(trait_ctx_wf) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Rhs_lfts_inst : prod_vec lft DropGlue_Rhs_realization.(trait_ctx_lfts)) (DropGlue_Rhs_tys_inst : plist type DropGlue_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Rhs_realization.(trait_ctx_spec) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Rhs_rt) Rhs_st DropGlue_Rhs_spec_attrs-[] -[Rhs_ty]))⌝ ∗ DropGlue_Rhs_realization.(trait_ctx_wf) DropGlue_Rhs_lfts_inst DropGlue_Rhs_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Rhs_lfts_inst : prod_vec lft PartialOrd_Self_Rhs_realization.(trait_ctx_lfts)) (PartialOrd_Self_Rhs_tys_inst : plist type PartialOrd_Self_Rhs_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Rhs_realization.(trait_ctx_spec) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Rhs_rt) Self_st Rhs_st PartialEq_Self_Rhs_spec_attrs DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialOrd_Self_Rhs_spec_attrs-[] -[Self_ty; Rhs_ty]))⌝ ∗ PartialOrd_Self_Rhs_realization.(trait_ctx_wf) PartialOrd_Self_Rhs_lfts_inst PartialOrd_Self_Rhs_tys_inst π))%I).
End PartialOrd_trait_req_incls.

Section Ord_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Ord_clamp (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
      ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π))%I).
  Definition trait_incl_of_Ord_cmp (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
      ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π))%I).
  Definition trait_incl_of_Ord_max (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
      ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π))%I).
  Definition trait_incl_of_Ord_min (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
      ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
      ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π))%I).
End Ord_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_std_option_OptionTasOrd_cmp (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (Eq_T_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (T_rt))))) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (Ord_T_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
    ∗ (∃ (Eq_T_lfts_inst : prod_vec lft Eq_T_realization.(trait_ctx_lfts)) (Eq_T_tys_inst : plist type Eq_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_T_realization.(trait_ctx_spec) Eq_T_lfts_inst Eq_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs Eq_T_spec_attrs-[] -[T_ty]))⌝ ∗ Eq_T_realization.(trait_ctx_wf) Eq_T_lfts_inst Eq_T_tys_inst π)
    ∗ (∃ (PartialOrd_T_T_lfts_inst : prod_vec lft PartialOrd_T_T_realization.(trait_ctx_lfts)) (PartialOrd_T_T_tys_inst : plist type PartialOrd_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_T_T_realization.(trait_ctx_spec) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (T_rt) (T_rt) T_st T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialOrd_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialOrd_T_T_realization.(trait_ctx_wf) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst π)
    ∗ (∃ (Ord_T_lfts_inst : prod_vec lft Ord_T_realization.(trait_ctx_lfts)) (Ord_T_tys_inst : plist type Ord_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_T_realization.(trait_ctx_spec) Ord_T_lfts_inst Ord_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs DropGlue_T_spec_attrs Ord_T_spec_attrs-[] -[T_ty]))⌝ ∗ Ord_T_realization.(trait_ctx_wf) Ord_T_lfts_inst Ord_T_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_std_option_OptionTasOrd_cmp (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))) ((std_option_OptionTasOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (Ord_T_spec_attrs) (DropGlue_T_spec_attrs))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty])]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_std_option_OptionTasPartialEq_eq (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_std_option_OptionTasPartialEq_eq (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (((Option_els (T_st)) : syn_type)) ((drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))) ((drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialEq_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty]); (Option_ty ((T_rt)) -[] -[T_ty])]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_std_option_OptionTasPartialOrd_partial_cmp (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
    ∗ (∃ (PartialOrd_T_T_lfts_inst : prod_vec lft PartialOrd_T_T_realization.(trait_ctx_lfts)) (PartialOrd_T_T_tys_inst : plist type PartialOrd_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_T_T_realization.(trait_ctx_spec) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (T_rt) (T_rt) T_st T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialOrd_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialOrd_T_T_realization.(trait_ctx_wf) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_std_option_OptionTasPartialOrd_partial_cmp (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (((Option_els (T_st)) : syn_type)) ((std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))) ((drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))) ((drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))) ((std_option_OptionTasPartialOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty]); (Option_ty ((T_rt)) -[] -[T_ty])]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasOrd_cmp (A_rt: RT) (A_st: syn_type) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (PartialEq_A_A_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (A_rt))))) (Eq_A_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) (Eq_A_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (A_rt))))) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (PartialOrd_A_A_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (A_rt))))) (Ord_A_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs)) (Ord_A_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3]) : 3 | ( *[A_ty]) : ([A_rt] : list RT), (λ π, ((∃ (PartialEq_A_A_lfts_inst : prod_vec lft PartialEq_A_A_realization.(trait_ctx_lfts)) (PartialEq_A_A_tys_inst : plist type PartialEq_A_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_A_realization.(trait_ctx_spec) PartialEq_A_A_lfts_inst PartialEq_A_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (A_rt) A_st A_st DropGlue_A_spec_attrs DropGlue_A_spec_attrs PartialEq_A_A_spec_attrs-[] -[A_ty; A_ty]))⌝ ∗ PartialEq_A_A_realization.(trait_ctx_wf) PartialEq_A_A_lfts_inst PartialEq_A_A_tys_inst π)
    ∗ (∃ (Eq_A_lfts_inst : prod_vec lft Eq_A_realization.(trait_ctx_lfts)) (Eq_A_tys_inst : plist type Eq_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_A_realization.(trait_ctx_spec) Eq_A_lfts_inst Eq_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (A_rt) A_st PartialEq_A_A_spec_attrs DropGlue_A_spec_attrs Eq_A_spec_attrs-[] -[A_ty]))⌝ ∗ Eq_A_realization.(trait_ctx_wf) Eq_A_lfts_inst Eq_A_tys_inst π)
    ∗ (∃ (PartialOrd_A_A_lfts_inst : prod_vec lft PartialOrd_A_A_realization.(trait_ctx_lfts)) (PartialOrd_A_A_tys_inst : plist type PartialOrd_A_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_A_A_realization.(trait_ctx_spec) PartialOrd_A_A_lfts_inst PartialOrd_A_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (A_rt) A_st A_st PartialEq_A_A_spec_attrs DropGlue_A_spec_attrs DropGlue_A_spec_attrs PartialOrd_A_A_spec_attrs-[] -[A_ty; A_ty]))⌝ ∗ PartialOrd_A_A_realization.(trait_ctx_wf) PartialOrd_A_A_lfts_inst PartialOrd_A_A_tys_inst π)
    ∗ (∃ (Ord_A_lfts_inst : prod_vec lft Ord_A_realization.(trait_ctx_lfts)) (Ord_A_tys_inst : plist type Ord_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_A_realization.(trait_ctx_spec) Ord_A_lfts_inst Ord_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (A_rt) A_st PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs DropGlue_A_spec_attrs Ord_A_spec_attrs-[] -[A_ty]))⌝ ∗ Ord_A_realization.(trait_ctx_wf) Ord_A_lfts_inst Ord_A_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I).

Definition type_of_REFAasOrd_cmp (A_rt: RT) (A_st: syn_type) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (Eq_A_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (Ord_A_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Ord_base_spec ((place_rfnRT (A_rt))) (RefSynType) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((REFAasOrd_spec_attrs (A_rt) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (Ord_A_spec_attrs) (DropGlue_A_spec_attrs))))
    -[] -[(shr_ref ulft_0 A_ty)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_unitasOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_unitasOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (unit) (UnitSynType) (unitasPartialEq_spec_attrs) (unitasEq_spec_attrs) (unitasPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (unit))) (unitasOrd_spec_attrs))
    -[] -[unit_t]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType I128)) (i128asPartialEq_spec_attrs) (i128asEq_spec_attrs) (i128asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (i128asOrd_spec_attrs))
    -[] -[(int I128)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType I16)) (i16asPartialEq_spec_attrs) (i16asEq_spec_attrs) (i16asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (i16asOrd_spec_attrs))
    -[] -[(int I16)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType I32)) (i32asPartialEq_spec_attrs) (i32asEq_spec_attrs) (i32asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (i32asOrd_spec_attrs))
    -[] -[(int I32)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType I64)) (i64asPartialEq_spec_attrs) (i64asEq_spec_attrs) (i64asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (i64asOrd_spec_attrs))
    -[] -[(int I64)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType I8)) (i8asPartialEq_spec_attrs) (i8asEq_spec_attrs) (i8asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (i8asOrd_spec_attrs))
    -[] -[(int I8)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType ISize)) (isizeasPartialEq_spec_attrs) (isizeasEq_spec_attrs) (isizeasPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (isizeasOrd_spec_attrs))
    -[] -[(int ISize)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType U128)) (u128asPartialEq_spec_attrs) (u128asEq_spec_attrs) (u128asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (u128asOrd_spec_attrs))
    -[] -[(int U128)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType U16)) (u16asPartialEq_spec_attrs) (u16asEq_spec_attrs) (u16asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (u16asOrd_spec_attrs))
    -[] -[(int U16)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType U32)) (u32asPartialEq_spec_attrs) (u32asEq_spec_attrs) (u32asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (u32asOrd_spec_attrs))
    -[] -[(int U32)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType U64)) (u64asPartialEq_spec_attrs) (u64asEq_spec_attrs) (u64asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (u64asOrd_spec_attrs))
    -[] -[(int U64)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType U8)) (u8asPartialEq_spec_attrs) (u8asEq_spec_attrs) (u8asPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (u8asOrd_spec_attrs))
    -[] -[(int U8)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasOrd_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasOrd_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Ord_base_spec (Z) ((IntSynType USize)) (usizeasPartialEq_spec_attrs) (usizeasEq_spec_attrs) (usizeasPartialOrd_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) (usizeasOrd_spec_attrs))
    -[] -[(int USize)]).(Ord_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialEqREFB_eq (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialEqREFB_eq (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialEq_base_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFAasPartialEqREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialEqREFmutB_eq (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialEqREFmutB_eq (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialEq_base_spec ((place_rfnRT (A_rt))) (((place_rfnRT (B_rt)) * gname)%type) (RefSynType) (RefSynType) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs (((place_rfnRT (B_rt)) * gname)%type))) ((REFAasPartialEqREFmutB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (mut_ref ulft_0 B_ty)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFmutAasPartialEqREFB_eq (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFmutAasPartialEqREFB_eq (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialEq_base_spec (((place_rfnRT (A_rt)) * gname)%type) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((drop_glue_trivial_spec_attrs (((place_rfnRT (A_rt)) * gname)%type))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFmutAasPartialEqREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(mut_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFmutAasPartialEqREFmutB_eq (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFmutAasPartialEqREFmutB_eq (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialEq_base_spec (((place_rfnRT (A_rt)) * gname)%type) (((place_rfnRT (B_rt)) * gname)%type) (RefSynType) (RefSynType) ((drop_glue_trivial_spec_attrs (((place_rfnRT (A_rt)) * gname)%type))) ((drop_glue_trivial_spec_attrs (((place_rfnRT (B_rt)) * gname)%type))) ((REFmutAasPartialEqREFmutB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(mut_ref ulft_1 A_ty); (mut_ref ulft_0 B_ty)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_unitasPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_unitasPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (unit) (unit) (UnitSynType) (UnitSynType) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit))) (unitasPartialEq_spec_attrs))
    -[] -[unit_t; unit_t]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_boolasPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_boolasPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (bool) (bool) (BoolSynType) (BoolSynType) ((drop_glue_trivial_spec_attrs (bool))) ((drop_glue_trivial_spec_attrs (bool))) (boolasPartialEq_spec_attrs))
    -[] -[bool_t; bool_t]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asPartialEq_spec_attrs))
    -[] -[(int I128); (int I128)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asPartialEq_spec_attrs))
    -[] -[(int I16); (int I16)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asPartialEq_spec_attrs))
    -[] -[(int I32); (int I32)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asPartialEq_spec_attrs))
    -[] -[(int I64); (int I64)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asPartialEq_spec_attrs))
    -[] -[(int I8); (int I8)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasPartialEq_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asPartialEq_spec_attrs))
    -[] -[(int U128); (int U128)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asPartialEq_spec_attrs))
    -[] -[(int U16); (int U16)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asPartialEq_spec_attrs))
    -[] -[(int U32); (int U32)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asPartialEq_spec_attrs))
    -[] -[(int U64); (int U64)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asPartialEq_spec_attrs))
    -[] -[(int U8); (int U8)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasPartialEq_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasPartialEq_eq  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasPartialEq_spec_attrs))
    -[] -[(int USize); (int USize)]).(PartialEq_eq_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialOrdREFB_ge (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (PartialOrd_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (PartialOrd_A_B_lfts_inst : prod_vec lft PartialOrd_A_B_realization.(trait_ctx_lfts)) (PartialOrd_A_B_tys_inst : plist type PartialOrd_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_A_B_realization.(trait_ctx_spec) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (B_rt) A_st B_st PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialOrd_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialOrd_A_B_realization.(trait_ctx_wf) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialOrdREFB_ge (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialOrd_base_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFAasPartialOrdREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (PartialOrd_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) (i128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asPartialOrd_spec_attrs))
    -[] -[(int I128); (int I128)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) (i16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asPartialOrd_spec_attrs))
    -[] -[(int I16); (int I16)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) (i32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asPartialOrd_spec_attrs))
    -[] -[(int I32); (int I32)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) (i64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asPartialOrd_spec_attrs))
    -[] -[(int I64); (int I64)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) (i8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asPartialOrd_spec_attrs))
    -[] -[(int I8); (int I8)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) (isizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasPartialOrd_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) (u128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asPartialOrd_spec_attrs))
    -[] -[(int U128); (int U128)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) (u16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asPartialOrd_spec_attrs))
    -[] -[(int U16); (int U16)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) (u32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asPartialOrd_spec_attrs))
    -[] -[(int U32); (int U32)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) (u64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asPartialOrd_spec_attrs))
    -[] -[(int U64); (int U64)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) (u8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asPartialOrd_spec_attrs))
    -[] -[(int U8); (int U8)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasPartialOrd_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasPartialOrd_ge  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) (usizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasPartialOrd_spec_attrs))
    -[] -[(int USize); (int USize)]).(PartialOrd_ge_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialOrdREFB_gt (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (PartialOrd_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (PartialOrd_A_B_lfts_inst : prod_vec lft PartialOrd_A_B_realization.(trait_ctx_lfts)) (PartialOrd_A_B_tys_inst : plist type PartialOrd_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_A_B_realization.(trait_ctx_spec) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (B_rt) A_st B_st PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialOrd_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialOrd_A_B_realization.(trait_ctx_wf) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialOrdREFB_gt (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialOrd_base_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFAasPartialOrdREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (PartialOrd_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) (i128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asPartialOrd_spec_attrs))
    -[] -[(int I128); (int I128)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) (i16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asPartialOrd_spec_attrs))
    -[] -[(int I16); (int I16)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) (i32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asPartialOrd_spec_attrs))
    -[] -[(int I32); (int I32)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) (i64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asPartialOrd_spec_attrs))
    -[] -[(int I64); (int I64)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) (i8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asPartialOrd_spec_attrs))
    -[] -[(int I8); (int I8)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) (isizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasPartialOrd_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) (u128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asPartialOrd_spec_attrs))
    -[] -[(int U128); (int U128)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) (u16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asPartialOrd_spec_attrs))
    -[] -[(int U16); (int U16)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) (u32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asPartialOrd_spec_attrs))
    -[] -[(int U32); (int U32)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) (u64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asPartialOrd_spec_attrs))
    -[] -[(int U64); (int U64)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) (u8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asPartialOrd_spec_attrs))
    -[] -[(int U8); (int U8)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasPartialOrd_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasPartialOrd_gt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) (usizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasPartialOrd_spec_attrs))
    -[] -[(int USize); (int USize)]).(PartialOrd_gt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialOrdREFB_le (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (PartialOrd_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (PartialOrd_A_B_lfts_inst : prod_vec lft PartialOrd_A_B_realization.(trait_ctx_lfts)) (PartialOrd_A_B_tys_inst : plist type PartialOrd_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_A_B_realization.(trait_ctx_spec) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (B_rt) A_st B_st PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialOrd_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialOrd_A_B_realization.(trait_ctx_wf) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialOrdREFB_le (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialOrd_base_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFAasPartialOrdREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (PartialOrd_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) (i128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asPartialOrd_spec_attrs))
    -[] -[(int I128); (int I128)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) (i16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asPartialOrd_spec_attrs))
    -[] -[(int I16); (int I16)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) (i32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asPartialOrd_spec_attrs))
    -[] -[(int I32); (int I32)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) (i64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asPartialOrd_spec_attrs))
    -[] -[(int I64); (int I64)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) (i8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asPartialOrd_spec_attrs))
    -[] -[(int I8); (int I8)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) (isizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasPartialOrd_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) (u128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asPartialOrd_spec_attrs))
    -[] -[(int U128); (int U128)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) (u16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asPartialOrd_spec_attrs))
    -[] -[(int U16); (int U16)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) (u32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asPartialOrd_spec_attrs))
    -[] -[(int U32); (int U32)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) (u64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asPartialOrd_spec_attrs))
    -[] -[(int U64); (int U64)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) (u8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asPartialOrd_spec_attrs))
    -[] -[(int U8); (int U8)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasPartialOrd_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasPartialOrd_le  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) (usizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasPartialOrd_spec_attrs))
    -[] -[(int USize); (int USize)]).(PartialOrd_le_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialOrdREFB_lt (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (PartialOrd_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (PartialOrd_A_B_lfts_inst : prod_vec lft PartialOrd_A_B_realization.(trait_ctx_lfts)) (PartialOrd_A_B_tys_inst : plist type PartialOrd_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_A_B_realization.(trait_ctx_spec) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (B_rt) A_st B_st PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialOrd_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialOrd_A_B_realization.(trait_ctx_wf) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialOrdREFB_lt (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialOrd_base_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFAasPartialOrdREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (PartialOrd_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) (i128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asPartialOrd_spec_attrs))
    -[] -[(int I128); (int I128)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) (i16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asPartialOrd_spec_attrs))
    -[] -[(int I16); (int I16)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) (i32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asPartialOrd_spec_attrs))
    -[] -[(int I32); (int I32)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) (i64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asPartialOrd_spec_attrs))
    -[] -[(int I64); (int I64)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) (i8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asPartialOrd_spec_attrs))
    -[] -[(int I8); (int I8)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) (isizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasPartialOrd_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) (u128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asPartialOrd_spec_attrs))
    -[] -[(int U128); (int U128)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) (u16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asPartialOrd_spec_attrs))
    -[] -[(int U16); (int U16)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) (u32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asPartialOrd_spec_attrs))
    -[] -[(int U32); (int U32)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) (u64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asPartialOrd_spec_attrs))
    -[] -[(int U64); (int U64)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) (u8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asPartialOrd_spec_attrs))
    -[] -[(int U8); (int U8)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasPartialOrd_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasPartialOrd_lt  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) (usizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasPartialOrd_spec_attrs))
    -[] -[(int USize); (int USize)]).(PartialOrd_lt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialEqREFB_ne (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialEqREFB_ne (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialEq_base_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFAasPartialEqREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialEqREFmutB_ne (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialEqREFmutB_ne (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialEq_base_spec ((place_rfnRT (A_rt))) (((place_rfnRT (B_rt)) * gname)%type) (RefSynType) (RefSynType) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs (((place_rfnRT (B_rt)) * gname)%type))) ((REFAasPartialEqREFmutB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (mut_ref ulft_0 B_ty)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFmutAasPartialEqREFB_ne (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFmutAasPartialEqREFB_ne (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialEq_base_spec (((place_rfnRT (A_rt)) * gname)%type) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((drop_glue_trivial_spec_attrs (((place_rfnRT (A_rt)) * gname)%type))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFmutAasPartialEqREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(mut_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFmutAasPartialEqREFmutB_ne (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFmutAasPartialEqREFmutB_ne (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialEq_base_spec (((place_rfnRT (A_rt)) * gname)%type) (((place_rfnRT (B_rt)) * gname)%type) (RefSynType) (RefSynType) ((drop_glue_trivial_spec_attrs (((place_rfnRT (A_rt)) * gname)%type))) ((drop_glue_trivial_spec_attrs (((place_rfnRT (B_rt)) * gname)%type))) ((REFmutAasPartialEqREFmutB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(mut_ref ulft_1 A_ty); (mut_ref ulft_0 B_ty)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_unitasPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_unitasPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (unit) (unit) (UnitSynType) (UnitSynType) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit))) (unitasPartialEq_spec_attrs))
    -[] -[unit_t; unit_t]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_boolasPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_boolasPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (bool) (bool) (BoolSynType) (BoolSynType) ((drop_glue_trivial_spec_attrs (bool))) ((drop_glue_trivial_spec_attrs (bool))) (boolasPartialEq_spec_attrs))
    -[] -[bool_t; bool_t]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asPartialEq_spec_attrs))
    -[] -[(int I128); (int I128)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asPartialEq_spec_attrs))
    -[] -[(int I16); (int I16)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asPartialEq_spec_attrs))
    -[] -[(int I32); (int I32)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asPartialEq_spec_attrs))
    -[] -[(int I64); (int I64)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asPartialEq_spec_attrs))
    -[] -[(int I8); (int I8)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasPartialEq_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asPartialEq_spec_attrs))
    -[] -[(int U128); (int U128)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asPartialEq_spec_attrs))
    -[] -[(int U16); (int U16)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asPartialEq_spec_attrs))
    -[] -[(int U32); (int U32)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asPartialEq_spec_attrs))
    -[] -[(int U64); (int U64)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asPartialEq_spec_attrs))
    -[] -[(int U8); (int U8)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasPartialEq_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasPartialEq_ne  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialEq_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasPartialEq_spec_attrs))
    -[] -[(int USize); (int USize)]).(PartialEq_ne_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFAasPartialOrdREFB_partial_cmp (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (PartialOrd_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (λ π, ((∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
    ∗ (∃ (PartialOrd_A_B_lfts_inst : prod_vec lft PartialOrd_A_B_realization.(trait_ctx_lfts)) (PartialOrd_A_B_tys_inst : plist type PartialOrd_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_A_B_realization.(trait_ctx_spec) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (B_rt) A_st B_st PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialOrd_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialOrd_A_B_realization.(trait_ctx_wf) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I).

Definition type_of_REFAasPartialOrdREFB_partial_cmp (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) :=
  spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; B_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0); (ϝ, ulft_1)]) (((PartialOrd_base_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))) (RefSynType) (RefSynType) ((REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt))))) ((REFAasPartialOrdREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (PartialOrd_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))))
    -[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_unitasPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_unitasPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (unit) (unit) (UnitSynType) (UnitSynType) (unitasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit))) (unitasPartialOrd_spec_attrs))
    -[] -[unit_t; unit_t]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I128)) ((IntSynType I128)) (i128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i128asPartialOrd_spec_attrs))
    -[] -[(int I128); (int I128)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I16)) ((IntSynType I16)) (i16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i16asPartialOrd_spec_attrs))
    -[] -[(int I16); (int I16)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I32)) ((IntSynType I32)) (i32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i32asPartialOrd_spec_attrs))
    -[] -[(int I32); (int I32)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I64)) ((IntSynType I64)) (i64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i64asPartialOrd_spec_attrs))
    -[] -[(int I64); (int I64)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType I8)) ((IntSynType I8)) (i8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (i8asPartialOrd_spec_attrs))
    -[] -[(int I8); (int I8)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType ISize)) ((IntSynType ISize)) (isizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (isizeasPartialOrd_spec_attrs))
    -[] -[(int ISize); (int ISize)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U128)) ((IntSynType U128)) (u128asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u128asPartialOrd_spec_attrs))
    -[] -[(int U128); (int U128)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U16)) ((IntSynType U16)) (u16asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u16asPartialOrd_spec_attrs))
    -[] -[(int U16); (int U16)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U32)) ((IntSynType U32)) (u32asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u32asPartialOrd_spec_attrs))
    -[] -[(int U32); (int U32)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U64)) ((IntSynType U64)) (u64asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u64asPartialOrd_spec_attrs))
    -[] -[(int U64); (int U64)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType U8)) ((IntSynType U8)) (u8asPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (u8asPartialOrd_spec_attrs))
    -[] -[(int U8); (int U8)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasPartialOrd_partial_cmp  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasPartialOrd_partial_cmp  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((PartialOrd_base_spec (Z) (Z) ((IntSynType USize)) ((IntSynType USize)) (usizeasPartialEq_spec_attrs) ((drop_glue_trivial_spec_attrs (Z))) ((drop_glue_trivial_spec_attrs (Z))) (usizeasPartialOrd_spec_attrs))
    -[] -[(int USize); (int USize)]).(PartialOrd_partial_cmp_spec)   a b))) <MERGE!>.

Definition trait_incl_of_Ordering_as_raw  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_Ordering_as_raw  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Ordering_ty  -[] -[]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, match self with | Less => -1 | Equal => 0 | Greater => 1 end @ (int I8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Ordering_is_eq  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_Ordering_is_eq  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Ordering_ty  -[] -[]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide(self = Equal) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Ordering_is_ge  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_Ordering_is_ge  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Ordering_ty  -[] -[]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide(self ≠ Less) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Ordering_is_gt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_Ordering_is_gt  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Ordering_ty  -[] -[]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide(self = Greater) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Ordering_is_le  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_Ordering_is_le  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Ordering_ty  -[] -[]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide(self ≠ Greater) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Ordering_is_lt  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_Ordering_is_lt  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Ordering_ty  -[] -[]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide(self = Less) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Ordering_is_ne  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_Ordering_is_ne  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Ordering_ty  -[] -[]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide(self ≠ Equal) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_max (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (Eq_T_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (T_rt))))) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (Ord_T_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
    ∗ (∃ (Eq_T_lfts_inst : prod_vec lft Eq_T_realization.(trait_ctx_lfts)) (Eq_T_tys_inst : plist type Eq_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_T_realization.(trait_ctx_spec) Eq_T_lfts_inst Eq_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs Eq_T_spec_attrs-[] -[T_ty]))⌝ ∗ Eq_T_realization.(trait_ctx_wf) Eq_T_lfts_inst Eq_T_tys_inst π)
    ∗ (∃ (PartialOrd_T_T_lfts_inst : prod_vec lft PartialOrd_T_T_realization.(trait_ctx_lfts)) (PartialOrd_T_T_tys_inst : plist type PartialOrd_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_T_T_realization.(trait_ctx_spec) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (T_rt) (T_rt) T_st T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialOrd_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialOrd_T_T_realization.(trait_ctx_wf) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst π)
    ∗ (∃ (Ord_T_lfts_inst : prod_vec lft Ord_T_realization.(trait_ctx_lfts)) (Ord_T_tys_inst : plist type Ord_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_T_realization.(trait_ctx_spec) Ord_T_lfts_inst Ord_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs DropGlue_T_spec_attrs Ord_T_spec_attrs-[] -[T_ty]))⌝ ∗ Ord_T_realization.(trait_ctx_wf) Ord_T_lfts_inst Ord_T_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_max (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (v1, v2) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) v1 :@: T_ty, v2 :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (Ord_T_spec_attrs.(Ord_Ord) v1 v2 = Less) then v2 else v1 @ T_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_max_by (T_rt: RT) (F_rt: RT) (T_st: syn_type) (F_st: syn_type) (FnOnce_F_REFTREFT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt) )) (FnOnce_F_REFTREFT_realization: (trait_spec_realization (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; F_ty]) : ([T_rt; F_rt] : list RT), (λ π, ((∃ (FnOnce_F_REFTREFT_lfts_inst : prod_vec lft FnOnce_F_REFTREFT_realization.(trait_ctx_lfts)) (FnOnce_F_REFTREFT_tys_inst : plist type FnOnce_F_REFTREFT_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_REFTREFT_realization.(trait_ctx_spec) FnOnce_F_REFTREFT_lfts_inst FnOnce_F_REFTREFT_tys_inst) (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt) F_st ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) Ordering_st DropGlue_F_spec_attrs (drop_glue_tuple2_spec_attrs ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt)))))) (drop_glue_trivial_spec_attrs ((Ordering_rt))) FnOnce_F_REFTREFT_spec_attrs-[] -[F_ty; (tuple2_ty ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))) -[] -[(shr_ref _lft_for_1 T_ty); (shr_ref _lft_for_0 T_ty)]); (Ordering_ty  -[] -[])]))⌝ ∗ FnOnce_F_REFTREFT_realization.(trait_ctx_wf) FnOnce_F_REFTREFT_lfts_inst FnOnce_F_REFTREFT_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π))%I).

Definition type_of_max_by (T_rt: RT) (F_rt: RT) (T_st: syn_type) (F_st: syn_type) (FnOnce_F_REFTREFT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; F_ty]) : ([(T_rt, T_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, v1, v2, compare) : ((_ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) v1 :@: T_ty, v2 :@: T_ty, compare :@: F_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_F_REFTREFT_spec_attrs.(FnOnce_Pre) π p compare *[v2; v1])) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ord, ret) : ((_ * _)), ret @ T_ty;
      (* postcondition *) (λ π : thread_id, (FnOnce_F_REFTREFT_spec_attrs.(FnOnce_Post) π p compare *[v2; v1] ord)
      ∗ (⌜(ret = if bool_decide(ord = Less) then v1 else v2)%Z⌝)) |
      (* unwind cond... *) FnOnce_F_REFTREFT_spec_attrs.(FnOnce_UnwindCondition) compare p *[v2; v1] ∨ DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_min (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (Eq_T_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (T_rt))))) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (Ord_T_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
    ∗ (∃ (Eq_T_lfts_inst : prod_vec lft Eq_T_realization.(trait_ctx_lfts)) (Eq_T_tys_inst : plist type Eq_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_T_realization.(trait_ctx_spec) Eq_T_lfts_inst Eq_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs Eq_T_spec_attrs-[] -[T_ty]))⌝ ∗ Eq_T_realization.(trait_ctx_wf) Eq_T_lfts_inst Eq_T_tys_inst π)
    ∗ (∃ (PartialOrd_T_T_lfts_inst : prod_vec lft PartialOrd_T_T_realization.(trait_ctx_lfts)) (PartialOrd_T_T_tys_inst : plist type PartialOrd_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_T_T_realization.(trait_ctx_spec) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (T_rt) (T_rt) T_st T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialOrd_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialOrd_T_T_realization.(trait_ctx_wf) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst π)
    ∗ (∃ (Ord_T_lfts_inst : prod_vec lft Ord_T_realization.(trait_ctx_lfts)) (Ord_T_tys_inst : plist type Ord_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_T_realization.(trait_ctx_spec) Ord_T_lfts_inst Ord_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs DropGlue_T_spec_attrs Ord_T_spec_attrs-[] -[T_ty]))⌝ ∗ Ord_T_realization.(trait_ctx_wf) Ord_T_lfts_inst Ord_T_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_min (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (v1, v2) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) v1 :@: T_ty, v2 :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (Ord_T_spec_attrs.(Ord_Ord) v1 v2 = Less) then v1 else v2 @ T_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_min_by (T_rt: RT) (F_rt: RT) (T_st: syn_type) (F_st: syn_type) (FnOnce_F_REFTREFT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt) )) (FnOnce_F_REFTREFT_realization: (trait_spec_realization (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; F_ty]) : ([T_rt; F_rt] : list RT), (λ π, ((∃ (FnOnce_F_REFTREFT_lfts_inst : prod_vec lft FnOnce_F_REFTREFT_realization.(trait_ctx_lfts)) (FnOnce_F_REFTREFT_tys_inst : plist type FnOnce_F_REFTREFT_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_REFTREFT_realization.(trait_ctx_spec) FnOnce_F_REFTREFT_lfts_inst FnOnce_F_REFTREFT_tys_inst) (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt) F_st ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) Ordering_st DropGlue_F_spec_attrs (drop_glue_tuple2_spec_attrs ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt)))))) (drop_glue_trivial_spec_attrs ((Ordering_rt))) FnOnce_F_REFTREFT_spec_attrs-[] -[F_ty; (tuple2_ty ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))) -[] -[(shr_ref _lft_for_1 T_ty); (shr_ref _lft_for_0 T_ty)]); (Ordering_ty  -[] -[])]))⌝ ∗ FnOnce_F_REFTREFT_realization.(trait_ctx_wf) FnOnce_F_REFTREFT_lfts_inst FnOnce_F_REFTREFT_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π))%I).

Definition type_of_min_by (T_rt: RT) (F_rt: RT) (T_st: syn_type) (F_st: syn_type) (FnOnce_F_REFTREFT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; F_ty]) : ([(T_rt, T_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, v1, v2, compare) : ((_ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) v1 :@: T_ty, v2 :@: T_ty, compare :@: F_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_F_REFTREFT_spec_attrs.(FnOnce_Pre) π p compare *[v2; v1])) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ord) : ((_)), if bool_decide(ord = Less) then v2 else v1 @ T_ty;
      (* postcondition *) (λ π : thread_id, (FnOnce_F_REFTREFT_spec_attrs.(FnOnce_Post) π p compare *[v2; v1] ord)) |
      (* unwind cond... *) FnOnce_F_REFTREFT_spec_attrs.(FnOnce_UnwindCondition) compare p *[v2; v1] ∨ DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).


Definition trait_incl_of_Ord_max_closure0 (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
    ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
    ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
    ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π)
    ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π))%I).

Definition type_of_Ord_max_closure0 (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (a, b) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_2); (ϝ, ulft_3)]);
      (* args......... *) () :@: unit_t, a :@: (shr_ref ulft_2 Self_ty), b :@: (shr_ref ulft_3 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Ord_Self_spec_attrs.(Ord_Ord) a b @ (Ordering_ty  -[] -[]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Ord_min_closure0 (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
    ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
    ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
    ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π)
    ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π))%I).

Definition type_of_Ord_min_closure0 (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (a, b) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_2); (ϝ, ulft_3)]);
      (* args......... *) () :@: unit_t, a :@: (shr_ref ulft_2 Self_ty), b :@: (shr_ref ulft_3 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Ord_Self_spec_attrs.(Ord_Ord) a b @ (Ordering_ty  -[] -[]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).


Definition Ord_max_closure0_call_once_trait_req_incl (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
    ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
    ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
    ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π)
    ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π))%I).

Definition Ord_max_closure0_call_once_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT),(λ a b, scope_add_typarams _ -[Self_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_2); (ϝ, ulft_3)]) (((FnOnce_base_spec (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (UnitSynType) (((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) (Ordering_st) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_tuple2_spec_attrs ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (Self_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (Self_rt))))))) ((drop_glue_trivial_spec_attrs ((Ordering_rt)))) ((Ord_max_closure0_FnOnce_spec_attrs (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs))))
    -[] -[unit_t; (tuple2_ty ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))) -[] -[(shr_ref ulft_2 Self_ty); (shr_ref ulft_3 Self_ty)]); (Ordering_ty  -[] -[])]).(FnOnce_call_once_spec)   a b))) <MERGE!>.

Definition Ord_min_closure0_call_once_trait_req_incl (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
    ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
    ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
    ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π)
    ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π))%I).

Definition Ord_min_closure0_call_once_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT),(λ a b, scope_add_typarams _ -[Self_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_2); (ϝ, ulft_3)]) (((FnOnce_base_spec (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)) (UnitSynType) (((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) (Ordering_st) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_tuple2_spec_attrs ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (Self_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (Self_rt))))))) ((drop_glue_trivial_spec_attrs ((Ordering_rt)))) ((Ord_min_closure0_FnOnce_spec_attrs (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs))))
    -[] -[unit_t; (tuple2_ty ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))) -[] -[(shr_ref ulft_2 Self_ty); (shr_ref ulft_3 Self_ty)]); (Ordering_ty  -[] -[])]).(FnOnce_call_once_spec)   a b))) <MERGE!>.


End specs.
Section REFAasEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFAasEq_spec (A_rt: RT) (A_st: syn_type) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (Eq_A_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (Eq_spec ((place_rfnRT (A_rt))))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec ((place_rfnRT (A_rt))) (RefSynType)) (REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (REFAasEq_spec_attrs (A_rt) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs)) 
             <TY> (shr_ref ulft_0 A_ty) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments REFAasEq_spec : simpl never.

  Program Definition REFAasEq_realization (A_rt: RT) (A_st: syn_type) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (PartialEq_A_A_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (A_rt))))) (Eq_A_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) (Eq_A_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (place_rfnRT (A_rt)))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty]) π, (((typaram_wf A_rt A_st A_ty))
  ∗ (∃ (PartialEq_A_A_lfts_inst : prod_vec lft PartialEq_A_A_realization.(trait_ctx_lfts)) (PartialEq_A_A_tys_inst : plist type PartialEq_A_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_A_realization.(trait_ctx_spec) PartialEq_A_A_lfts_inst PartialEq_A_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (A_rt) A_st A_st DropGlue_A_spec_attrs DropGlue_A_spec_attrs PartialEq_A_A_spec_attrs-[] -[A_ty; A_ty]))⌝ ∗ PartialEq_A_A_realization.(trait_ctx_wf) PartialEq_A_A_lfts_inst PartialEq_A_A_tys_inst π)
  ∗ (∃ (Eq_A_lfts_inst : prod_vec lft Eq_A_realization.(trait_ctx_lfts)) (Eq_A_tys_inst : plist type Eq_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_A_realization.(trait_ctx_spec) Eq_A_lfts_inst Eq_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (A_rt) A_st PartialEq_A_A_spec_attrs DropGlue_A_spec_attrs Eq_A_spec_attrs-[] -[A_ty]))⌝ ∗ Eq_A_realization.(trait_ctx_wf) Eq_A_lfts_inst Eq_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty]) _ _, (REFAasEq_spec (A_rt) (A_st) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))-[ulft_0] -[A_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFAasEq_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(A_st : !syn_type) `(PartialEq_A_A_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) `(Eq_A_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), (REFAasEq_spec (A_rt) (A_st) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))-[ulft_0] -[A_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), scope_add_typarams _ -[A_ty] ((Eq_base_spec (place_rfnRT (A_rt)) RefSynType (REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (REFAasEq_spec_attrs (A_rt) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs))-[] -[(shr_ref ulft_0 A_ty)])))).
End REFAasEq_spec.

Section REFAasOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFAasOrd_spec (A_rt: RT) (A_st: syn_type) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (Eq_A_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (Ord_A_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (Ord_spec ((place_rfnRT (A_rt))))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec ((place_rfnRT (A_rt))) (RefSynType)) (REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (REFAasOrd_spec_attrs (A_rt) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (Ord_A_spec_attrs) (DropGlue_A_spec_attrs)) 
             <TY> (shr_ref ulft_0 A_ty) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          (type_of_REFAasOrd_cmp ((A_rt)) (A_st)) PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs Ord_A_spec_attrs DropGlue_A_spec_attrs 
             <TY> A_ty <LFT> ulft_0 : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec ((place_rfnRT (A_rt))) (RefSynType)) (REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (REFAasOrd_spec_attrs (A_rt) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (Ord_A_spec_attrs) (DropGlue_A_spec_attrs)) 
             <TY> (shr_ref ulft_0 A_ty) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec ((place_rfnRT (A_rt))) (RefSynType)) (REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (REFAasOrd_spec_attrs (A_rt) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (Ord_A_spec_attrs) (DropGlue_A_spec_attrs)) 
             <TY> (shr_ref ulft_0 A_ty) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments REFAasOrd_spec : simpl never.

  Program Definition REFAasOrd_realization (A_rt: RT) (A_st: syn_type) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (PartialEq_A_A_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (A_rt))))) (Eq_A_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) (Eq_A_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (A_rt))))) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (PartialOrd_A_A_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (A_rt))))) (Ord_A_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs)) (Ord_A_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (place_rfnRT (A_rt)))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty]) π, (((typaram_wf A_rt A_st A_ty))
  ∗ (∃ (PartialEq_A_A_lfts_inst : prod_vec lft PartialEq_A_A_realization.(trait_ctx_lfts)) (PartialEq_A_A_tys_inst : plist type PartialEq_A_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_A_realization.(trait_ctx_spec) PartialEq_A_A_lfts_inst PartialEq_A_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (A_rt) A_st A_st DropGlue_A_spec_attrs DropGlue_A_spec_attrs PartialEq_A_A_spec_attrs-[] -[A_ty; A_ty]))⌝ ∗ PartialEq_A_A_realization.(trait_ctx_wf) PartialEq_A_A_lfts_inst PartialEq_A_A_tys_inst π)
  ∗ (∃ (Eq_A_lfts_inst : prod_vec lft Eq_A_realization.(trait_ctx_lfts)) (Eq_A_tys_inst : plist type Eq_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_A_realization.(trait_ctx_spec) Eq_A_lfts_inst Eq_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (A_rt) A_st PartialEq_A_A_spec_attrs DropGlue_A_spec_attrs Eq_A_spec_attrs-[] -[A_ty]))⌝ ∗ Eq_A_realization.(trait_ctx_wf) Eq_A_lfts_inst Eq_A_tys_inst π)
  ∗ (∃ (PartialOrd_A_A_lfts_inst : prod_vec lft PartialOrd_A_A_realization.(trait_ctx_lfts)) (PartialOrd_A_A_tys_inst : plist type PartialOrd_A_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_A_A_realization.(trait_ctx_spec) PartialOrd_A_A_lfts_inst PartialOrd_A_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (A_rt) A_st A_st PartialEq_A_A_spec_attrs DropGlue_A_spec_attrs DropGlue_A_spec_attrs PartialOrd_A_A_spec_attrs-[] -[A_ty; A_ty]))⌝ ∗ PartialOrd_A_A_realization.(trait_ctx_wf) PartialOrd_A_A_lfts_inst PartialOrd_A_A_tys_inst π)
  ∗ (∃ (Ord_A_lfts_inst : prod_vec lft Ord_A_realization.(trait_ctx_lfts)) (Ord_A_tys_inst : plist type Ord_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_A_realization.(trait_ctx_spec) Ord_A_lfts_inst Ord_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (A_rt) A_st PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs DropGlue_A_spec_attrs Ord_A_spec_attrs-[] -[A_ty]))⌝ ∗ Ord_A_realization.(trait_ctx_wf) Ord_A_lfts_inst Ord_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty]) _ _, (REFAasOrd_spec (A_rt) (A_st) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (Ord_A_spec_attrs) (DropGlue_A_spec_attrs))-[ulft_0] -[A_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFAasOrd_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(A_st : !syn_type) `(PartialEq_A_A_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) `(Eq_A_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) `(PartialOrd_A_A_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) `(Ord_A_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs)) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), (REFAasOrd_spec (A_rt) (A_st) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (Ord_A_spec_attrs) (DropGlue_A_spec_attrs))-[ulft_0] -[A_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), scope_add_typarams _ -[A_ty] ((Ord_base_spec (place_rfnRT (A_rt)) RefSynType (REFAasPartialEqREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFAasEq_spec_attrs ((A_rt)) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFAasPartialOrdREFB_spec_attrs ((A_rt)) ((A_rt)) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_A_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (REFAasOrd_spec_attrs (A_rt) (PartialEq_A_A_spec_attrs) (Eq_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (Ord_A_spec_attrs) (DropGlue_A_spec_attrs))-[] -[(shr_ref ulft_0 A_ty)])))).
End REFAasOrd_spec.

Section REFAasPartialEqREFB_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFAasPartialEqREFB_spec (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : (spec_with _ _ (PartialEq_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))))) :=
    spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), {|
        PartialEq_eq_spec  :=
          (type_of_REFAasPartialEqREFB_eq ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          (type_of_REFAasPartialEqREFB_ne ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments REFAasPartialEqREFB_spec : simpl never.

  Program Definition REFAasPartialEqREFB_realization (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (place_rfnRT (A_rt)) (place_rfnRT (B_rt)))) :=
  {|
    trait_ctx_lfts := 2;
    trait_ctx_tys := [A_rt; B_rt];
    trait_ctx_wf := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) _ _, (REFAasPartialEqREFB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFAasPartialEqREFB_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(B_rt : !RT) `(A_st : !syn_type) `(B_st : !syn_type) `(PartialEq_A_B_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_B_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )), trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (REFAasPartialEqREFB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty]) (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), scope_add_typarams _ -[A_ty; B_ty] ((PartialEq_base_spec (place_rfnRT (A_rt)) (place_rfnRT (B_rt)) RefSynType RefSynType (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt)))) (REFAasPartialEqREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)])))).
End REFAasPartialEqREFB_spec.

Section REFAasPartialEqREFmutB_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFAasPartialEqREFmutB_spec (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : (spec_with _ _ (PartialEq_spec ((place_rfnRT (A_rt))) (((place_rfnRT (B_rt)) * gname)%type))) :=
    spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), {|
        PartialEq_eq_spec  :=
          (type_of_REFAasPartialEqREFmutB_eq ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          (type_of_REFAasPartialEqREFmutB_ne ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments REFAasPartialEqREFmutB_spec : simpl never.

  Program Definition REFAasPartialEqREFmutB_realization (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (place_rfnRT (A_rt)) ((place_rfnRT (B_rt)) * gname)%type)) :=
  {|
    trait_ctx_lfts := 2;
    trait_ctx_tys := [A_rt; B_rt];
    trait_ctx_wf := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) _ _, (REFAasPartialEqREFmutB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFAasPartialEqREFmutB_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(B_rt : !RT) `(A_st : !syn_type) `(B_st : !syn_type) `(PartialEq_A_B_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_B_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )), trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (REFAasPartialEqREFmutB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty]) (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), scope_add_typarams _ -[A_ty; B_ty] ((PartialEq_base_spec (place_rfnRT (A_rt)) ((place_rfnRT (B_rt)) * gname)%type RefSynType RefSynType (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (drop_glue_trivial_spec_attrs (((place_rfnRT (B_rt)) * gname)%type)) (REFAasPartialEqREFmutB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[] -[(shr_ref ulft_1 A_ty); (mut_ref ulft_0 B_ty)])))).
End REFAasPartialEqREFmutB_spec.

Section REFAasPartialOrdREFB_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFAasPartialOrdREFB_spec (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : (spec_with _ _ (PartialOrd_spec ((place_rfnRT (A_rt))) ((place_rfnRT (B_rt))))) :=
    spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), {|
        PartialOrd_ge_spec  :=
          (type_of_REFAasPartialOrdREFB_ge ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs PartialOrd_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          (type_of_REFAasPartialOrdREFB_gt ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs PartialOrd_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          (type_of_REFAasPartialOrdREFB_le ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs PartialOrd_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          (type_of_REFAasPartialOrdREFB_lt ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs PartialOrd_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          (type_of_REFAasPartialOrdREFB_partial_cmp ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs PartialOrd_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments REFAasPartialOrdREFB_spec : simpl never.

  Program Definition REFAasPartialOrdREFB_realization (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (PartialOrd_A_B_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) (PartialOrd_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (place_rfnRT (A_rt)) (place_rfnRT (B_rt)))) :=
  {|
    trait_ctx_lfts := 2;
    trait_ctx_tys := [A_rt; B_rt];
    trait_ctx_wf := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
  ∗ (∃ (PartialOrd_A_B_lfts_inst : prod_vec lft PartialOrd_A_B_realization.(trait_ctx_lfts)) (PartialOrd_A_B_tys_inst : plist type PartialOrd_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_A_B_realization.(trait_ctx_spec) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (B_rt) A_st B_st PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialOrd_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialOrd_A_B_realization.(trait_ctx_wf) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) _ _, (REFAasPartialOrdREFB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (PartialOrd_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFAasPartialOrdREFB_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(B_rt : !RT) `(A_st : !syn_type) `(B_st : !syn_type) `(PartialEq_A_B_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) `(PartialOrd_A_B_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_B_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )), trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (REFAasPartialOrdREFB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (PartialOrd_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty]) (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), scope_add_typarams _ -[A_ty; B_ty] ((PartialOrd_base_spec (place_rfnRT (A_rt)) (place_rfnRT (B_rt)) RefSynType RefSynType (REFAasPartialEqREFB_spec_attrs ((A_rt)) ((B_rt)) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt)))) (REFAasPartialOrdREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (PartialOrd_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[] -[(shr_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)])))).
End REFAasPartialOrdREFB_spec.

Section REFmutAasPartialEqREFB_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFmutAasPartialEqREFB_spec (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : (spec_with _ _ (PartialEq_spec (((place_rfnRT (A_rt)) * gname)%type) ((place_rfnRT (B_rt))))) :=
    spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), {|
        PartialEq_eq_spec  :=
          (type_of_REFmutAasPartialEqREFB_eq ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          (type_of_REFmutAasPartialEqREFB_ne ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments REFmutAasPartialEqREFB_spec : simpl never.

  Program Definition REFmutAasPartialEqREFB_realization (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) ((place_rfnRT (A_rt)) * gname)%type (place_rfnRT (B_rt)))) :=
  {|
    trait_ctx_lfts := 2;
    trait_ctx_tys := [A_rt; B_rt];
    trait_ctx_wf := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) _ _, (REFmutAasPartialEqREFB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFmutAasPartialEqREFB_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(B_rt : !RT) `(A_st : !syn_type) `(B_st : !syn_type) `(PartialEq_A_B_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_B_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )), trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (REFmutAasPartialEqREFB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty]) (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), scope_add_typarams _ -[A_ty; B_ty] ((PartialEq_base_spec ((place_rfnRT (A_rt)) * gname)%type (place_rfnRT (B_rt)) RefSynType RefSynType (drop_glue_trivial_spec_attrs (((place_rfnRT (A_rt)) * gname)%type)) (drop_glue_trivial_spec_attrs ((place_rfnRT (B_rt)))) (REFmutAasPartialEqREFB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[] -[(mut_ref ulft_1 A_ty); (shr_ref ulft_0 B_ty)])))).
End REFmutAasPartialEqREFB_spec.

Section REFmutAasPartialEqREFmutB_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFmutAasPartialEqREFmutB_spec (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) : (spec_with _ _ (PartialEq_spec (((place_rfnRT (A_rt)) * gname)%type) (((place_rfnRT (B_rt)) * gname)%type))) :=
    spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), {|
        PartialEq_eq_spec  :=
          (type_of_REFmutAasPartialEqREFmutB_eq ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          (type_of_REFmutAasPartialEqREFmutB_ne ((A_rt)) ((B_rt)) (A_st) (B_st)) PartialEq_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs 
             <TY> A_ty <TY> B_ty <LFT> ulft_0 <LFT> ulft_1 : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments REFmutAasPartialEqREFmutB_spec : simpl never.

  Program Definition REFmutAasPartialEqREFmutB_realization (A_rt: RT) (B_rt: RT) (A_st: syn_type) (B_st: syn_type) (PartialEq_A_B_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) (PartialEq_A_B_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_B_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) (DropGlue_B_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) ((place_rfnRT (A_rt)) * gname)%type ((place_rfnRT (B_rt)) * gname)%type)) :=
  {|
    trait_ctx_lfts := 2;
    trait_ctx_tys := [A_rt; B_rt];
    trait_ctx_wf := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (∃ (PartialEq_A_B_lfts_inst : prod_vec lft PartialEq_A_B_realization.(trait_ctx_lfts)) (PartialEq_A_B_tys_inst : plist type PartialEq_A_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_A_B_realization.(trait_ctx_spec) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (B_rt) A_st B_st DropGlue_A_spec_attrs DropGlue_B_spec_attrs PartialEq_A_B_spec_attrs-[] -[A_ty; B_ty]))⌝ ∗ PartialEq_A_B_realization.(trait_ctx_wf) PartialEq_A_B_lfts_inst PartialEq_A_B_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st DropGlue_B_spec_attrs-[] -[B_ty]))⌝ ∗ DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0; ulft_1]) '( *[A_ty; B_ty]) _ _, (REFmutAasPartialEqREFmutB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFmutAasPartialEqREFmutB_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(B_rt : !RT) `(A_st : !syn_type) `(B_st : !syn_type) `(PartialEq_A_B_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_B_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )), trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), (REFmutAasPartialEqREFmutB_spec (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[ulft_0; ulft_1] -[A_ty; B_ty]) (spec! ( *[ulft_0; ulft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), scope_add_typarams _ -[A_ty; B_ty] ((PartialEq_base_spec ((place_rfnRT (A_rt)) * gname)%type ((place_rfnRT (B_rt)) * gname)%type RefSynType RefSynType (drop_glue_trivial_spec_attrs (((place_rfnRT (A_rt)) * gname)%type)) (drop_glue_trivial_spec_attrs (((place_rfnRT (B_rt)) * gname)%type)) (REFmutAasPartialEqREFmutB_spec_attrs (A_rt) (B_rt) (PartialEq_A_B_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_B_spec_attrs))-[] -[(mut_ref ulft_1 A_ty); (mut_ref ulft_0 B_ty)])))).
End REFmutAasPartialEqREFmutB_spec.

Section unitasEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition unitasEq_spec  : (spec_with _ _ (Eq_spec (unit))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (unit) (UnitSynType)) unitasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (unit)) unitasEq_spec_attrs 
             <TY> unit_t : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments unitasEq_spec : simpl never.

  Program Definition unitasEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) unit)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, unitasEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition unitasEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), unitasEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec unit UnitSynType unitasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (unit)) unitasEq_spec_attrs-[] -[unit_t])))).
End unitasEq_spec.

Section unitasOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition unitasOrd_spec  : (spec_with _ _ (Ord_spec (unit))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (unit) (UnitSynType)) unitasPartialEq_spec_attrs unitasEq_spec_attrs unitasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (unit)) unitasOrd_spec_attrs 
             <TY> unit_t : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_unitasOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (unit) (UnitSynType)) unitasPartialEq_spec_attrs unitasEq_spec_attrs unitasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (unit)) unitasOrd_spec_attrs 
             <TY> unit_t : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (unit) (UnitSynType)) unitasPartialEq_spec_attrs unitasEq_spec_attrs unitasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (unit)) unitasOrd_spec_attrs 
             <TY> unit_t : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments unitasOrd_spec : simpl never.

  Program Definition unitasOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) unit)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, unitasOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition unitasOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), unitasOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec unit UnitSynType unitasPartialEq_spec_attrs unitasEq_spec_attrs unitasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (unit)) unitasOrd_spec_attrs-[] -[unit_t])))).
End unitasOrd_spec.

Section unitasPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition unitasPartialEq_spec  : (spec_with _ _ (PartialEq_spec (unit) (unit))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_unitasPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_unitasPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments unitasPartialEq_spec : simpl never.

  Program Definition unitasPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) unit unit)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, unitasPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition unitasPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), unitasPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec unit unit UnitSynType UnitSynType (drop_glue_trivial_spec_attrs (unit)) (drop_glue_trivial_spec_attrs (unit)) unitasPartialEq_spec_attrs-[] -[unit_t; unit_t])))).
End unitasPartialEq_spec.

Section unitasPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition unitasPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (unit) (unit))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          (PartialOrd_ge_base_spec (unit) (unit) (UnitSynType) (UnitSynType)) unitasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (unit)) (drop_glue_trivial_spec_attrs (unit)) unitasPartialOrd_spec_attrs 
             <TY> unit_t <TY> unit_t : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          (PartialOrd_gt_base_spec (unit) (unit) (UnitSynType) (UnitSynType)) unitasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (unit)) (drop_glue_trivial_spec_attrs (unit)) unitasPartialOrd_spec_attrs 
             <TY> unit_t <TY> unit_t : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          (PartialOrd_le_base_spec (unit) (unit) (UnitSynType) (UnitSynType)) unitasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (unit)) (drop_glue_trivial_spec_attrs (unit)) unitasPartialOrd_spec_attrs 
             <TY> unit_t <TY> unit_t : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          (PartialOrd_lt_base_spec (unit) (unit) (UnitSynType) (UnitSynType)) unitasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (unit)) (drop_glue_trivial_spec_attrs (unit)) unitasPartialOrd_spec_attrs 
             <TY> unit_t <TY> unit_t : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_unitasPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments unitasPartialOrd_spec : simpl never.

  Program Definition unitasPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) unit unit)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, unitasPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition unitasPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), unitasPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec unit unit UnitSynType UnitSynType unitasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (unit)) (drop_glue_trivial_spec_attrs (unit)) unitasPartialOrd_spec_attrs-[] -[unit_t; unit_t])))).
End unitasPartialOrd_spec.

Section boolasEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition boolasEq_spec  : (spec_with _ _ (Eq_spec (bool))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (bool) (BoolSynType)) boolasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (bool)) boolasEq_spec_attrs 
             <TY> bool_t : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments boolasEq_spec : simpl never.

  Program Definition boolasEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) bool)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, boolasEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition boolasEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), boolasEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec bool BoolSynType boolasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (bool)) boolasEq_spec_attrs-[] -[bool_t])))).
End boolasEq_spec.

Section boolasPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition boolasPartialEq_spec  : (spec_with _ _ (PartialEq_spec (bool) (bool))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_boolasPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_boolasPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments boolasPartialEq_spec : simpl never.

  Program Definition boolasPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) bool bool)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, boolasPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition boolasPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), boolasPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec bool bool BoolSynType BoolSynType (drop_glue_trivial_spec_attrs (bool)) (drop_glue_trivial_spec_attrs (bool)) boolasPartialEq_spec_attrs-[] -[bool_t; bool_t])))).
End boolasPartialEq_spec.

Section i128asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType I128))) i128asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i128asEq_spec_attrs 
             <TY> (int I128) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments i128asEq_spec : simpl never.

  Program Definition i128asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i128asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i128asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType I128) i128asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i128asEq_spec_attrs-[] -[(int I128)])))).
End i128asEq_spec.

Section i128asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType I128))) i128asPartialEq_spec_attrs i128asEq_spec_attrs i128asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i128asOrd_spec_attrs 
             <TY> (int I128) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_i128asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType I128))) i128asPartialEq_spec_attrs i128asEq_spec_attrs i128asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i128asOrd_spec_attrs 
             <TY> (int I128) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType I128))) i128asPartialEq_spec_attrs i128asEq_spec_attrs i128asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i128asOrd_spec_attrs 
             <TY> (int I128) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments i128asOrd_spec : simpl never.

  Program Definition i128asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i128asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i128asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType I128) i128asPartialEq_spec_attrs i128asEq_spec_attrs i128asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i128asOrd_spec_attrs-[] -[(int I128)])))).
End i128asOrd_spec.

Section i128asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_i128asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_i128asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i128asPartialEq_spec : simpl never.

  Program Definition i128asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i128asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i128asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType I128) (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i128asPartialEq_spec_attrs-[] -[(int I128); (int I128)])))).
End i128asPartialEq_spec.

Section i128asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_i128asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_i128asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_i128asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_i128asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_i128asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i128asPartialOrd_spec : simpl never.

  Program Definition i128asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i128asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i128asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType I128) (IntSynType I128) i128asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i128asPartialOrd_spec_attrs-[] -[(int I128); (int I128)])))).
End i128asPartialOrd_spec.

Section i16asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType I16))) i16asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i16asEq_spec_attrs 
             <TY> (int I16) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments i16asEq_spec : simpl never.

  Program Definition i16asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i16asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i16asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType I16) i16asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i16asEq_spec_attrs-[] -[(int I16)])))).
End i16asEq_spec.

Section i16asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType I16))) i16asPartialEq_spec_attrs i16asEq_spec_attrs i16asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i16asOrd_spec_attrs 
             <TY> (int I16) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_i16asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType I16))) i16asPartialEq_spec_attrs i16asEq_spec_attrs i16asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i16asOrd_spec_attrs 
             <TY> (int I16) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType I16))) i16asPartialEq_spec_attrs i16asEq_spec_attrs i16asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i16asOrd_spec_attrs 
             <TY> (int I16) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments i16asOrd_spec : simpl never.

  Program Definition i16asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i16asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i16asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType I16) i16asPartialEq_spec_attrs i16asEq_spec_attrs i16asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i16asOrd_spec_attrs-[] -[(int I16)])))).
End i16asOrd_spec.

Section i16asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_i16asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_i16asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i16asPartialEq_spec : simpl never.

  Program Definition i16asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i16asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i16asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType I16) (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i16asPartialEq_spec_attrs-[] -[(int I16); (int I16)])))).
End i16asPartialEq_spec.

Section i16asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_i16asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_i16asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_i16asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_i16asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_i16asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i16asPartialOrd_spec : simpl never.

  Program Definition i16asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i16asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i16asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType I16) (IntSynType I16) i16asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i16asPartialOrd_spec_attrs-[] -[(int I16); (int I16)])))).
End i16asPartialOrd_spec.

Section i32asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType I32))) i32asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i32asEq_spec_attrs 
             <TY> (int I32) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments i32asEq_spec : simpl never.

  Program Definition i32asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i32asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i32asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType I32) i32asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i32asEq_spec_attrs-[] -[(int I32)])))).
End i32asEq_spec.

Section i32asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType I32))) i32asPartialEq_spec_attrs i32asEq_spec_attrs i32asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i32asOrd_spec_attrs 
             <TY> (int I32) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_i32asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType I32))) i32asPartialEq_spec_attrs i32asEq_spec_attrs i32asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i32asOrd_spec_attrs 
             <TY> (int I32) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType I32))) i32asPartialEq_spec_attrs i32asEq_spec_attrs i32asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i32asOrd_spec_attrs 
             <TY> (int I32) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments i32asOrd_spec : simpl never.

  Program Definition i32asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i32asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i32asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType I32) i32asPartialEq_spec_attrs i32asEq_spec_attrs i32asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i32asOrd_spec_attrs-[] -[(int I32)])))).
End i32asOrd_spec.

Section i32asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_i32asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_i32asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i32asPartialEq_spec : simpl never.

  Program Definition i32asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i32asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i32asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType I32) (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i32asPartialEq_spec_attrs-[] -[(int I32); (int I32)])))).
End i32asPartialEq_spec.

Section i32asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_i32asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_i32asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_i32asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_i32asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_i32asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i32asPartialOrd_spec : simpl never.

  Program Definition i32asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i32asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i32asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType I32) (IntSynType I32) i32asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i32asPartialOrd_spec_attrs-[] -[(int I32); (int I32)])))).
End i32asPartialOrd_spec.

Section i64asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType I64))) i64asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i64asEq_spec_attrs 
             <TY> (int I64) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments i64asEq_spec : simpl never.

  Program Definition i64asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i64asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i64asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType I64) i64asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i64asEq_spec_attrs-[] -[(int I64)])))).
End i64asEq_spec.

Section i64asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType I64))) i64asPartialEq_spec_attrs i64asEq_spec_attrs i64asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i64asOrd_spec_attrs 
             <TY> (int I64) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_i64asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType I64))) i64asPartialEq_spec_attrs i64asEq_spec_attrs i64asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i64asOrd_spec_attrs 
             <TY> (int I64) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType I64))) i64asPartialEq_spec_attrs i64asEq_spec_attrs i64asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i64asOrd_spec_attrs 
             <TY> (int I64) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments i64asOrd_spec : simpl never.

  Program Definition i64asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i64asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i64asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType I64) i64asPartialEq_spec_attrs i64asEq_spec_attrs i64asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i64asOrd_spec_attrs-[] -[(int I64)])))).
End i64asOrd_spec.

Section i64asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_i64asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_i64asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i64asPartialEq_spec : simpl never.

  Program Definition i64asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i64asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i64asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType I64) (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i64asPartialEq_spec_attrs-[] -[(int I64); (int I64)])))).
End i64asPartialEq_spec.

Section i64asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_i64asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_i64asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_i64asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_i64asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_i64asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i64asPartialOrd_spec : simpl never.

  Program Definition i64asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i64asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i64asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType I64) (IntSynType I64) i64asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i64asPartialOrd_spec_attrs-[] -[(int I64); (int I64)])))).
End i64asPartialOrd_spec.

Section i8asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType I8))) i8asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i8asEq_spec_attrs 
             <TY> (int I8) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments i8asEq_spec : simpl never.

  Program Definition i8asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i8asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i8asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType I8) i8asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i8asEq_spec_attrs-[] -[(int I8)])))).
End i8asEq_spec.

Section i8asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType I8))) i8asPartialEq_spec_attrs i8asEq_spec_attrs i8asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i8asOrd_spec_attrs 
             <TY> (int I8) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_i8asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType I8))) i8asPartialEq_spec_attrs i8asEq_spec_attrs i8asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i8asOrd_spec_attrs 
             <TY> (int I8) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType I8))) i8asPartialEq_spec_attrs i8asEq_spec_attrs i8asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i8asOrd_spec_attrs 
             <TY> (int I8) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments i8asOrd_spec : simpl never.

  Program Definition i8asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i8asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i8asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType I8) i8asPartialEq_spec_attrs i8asEq_spec_attrs i8asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i8asOrd_spec_attrs-[] -[(int I8)])))).
End i8asOrd_spec.

Section i8asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_i8asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_i8asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i8asPartialEq_spec : simpl never.

  Program Definition i8asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i8asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i8asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType I8) (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i8asPartialEq_spec_attrs-[] -[(int I8); (int I8)])))).
End i8asPartialEq_spec.

Section i8asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_i8asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_i8asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_i8asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_i8asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_i8asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i8asPartialOrd_spec : simpl never.

  Program Definition i8asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i8asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i8asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType I8) (IntSynType I8) i8asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) i8asPartialOrd_spec_attrs-[] -[(int I8); (int I8)])))).
End i8asPartialOrd_spec.

Section isizeasEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType ISize))) isizeasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) isizeasEq_spec_attrs 
             <TY> (int ISize) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments isizeasEq_spec : simpl never.

  Program Definition isizeasEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, isizeasEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition isizeasEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType ISize) isizeasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) isizeasEq_spec_attrs-[] -[(int ISize)])))).
End isizeasEq_spec.

Section isizeasOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType ISize))) isizeasPartialEq_spec_attrs isizeasEq_spec_attrs isizeasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) isizeasOrd_spec_attrs 
             <TY> (int ISize) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_isizeasOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType ISize))) isizeasPartialEq_spec_attrs isizeasEq_spec_attrs isizeasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) isizeasOrd_spec_attrs 
             <TY> (int ISize) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType ISize))) isizeasPartialEq_spec_attrs isizeasEq_spec_attrs isizeasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) isizeasOrd_spec_attrs 
             <TY> (int ISize) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments isizeasOrd_spec : simpl never.

  Program Definition isizeasOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, isizeasOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition isizeasOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType ISize) isizeasPartialEq_spec_attrs isizeasEq_spec_attrs isizeasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) isizeasOrd_spec_attrs-[] -[(int ISize)])))).
End isizeasOrd_spec.

Section isizeasPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_isizeasPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_isizeasPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments isizeasPartialEq_spec : simpl never.

  Program Definition isizeasPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, isizeasPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition isizeasPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType ISize) (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) isizeasPartialEq_spec_attrs-[] -[(int ISize); (int ISize)])))).
End isizeasPartialEq_spec.

Section isizeasPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_isizeasPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_isizeasPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_isizeasPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_isizeasPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_isizeasPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments isizeasPartialOrd_spec : simpl never.

  Program Definition isizeasPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, isizeasPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition isizeasPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType ISize) (IntSynType ISize) isizeasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) isizeasPartialOrd_spec_attrs-[] -[(int ISize); (int ISize)])))).
End isizeasPartialOrd_spec.

Section u128asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType U128))) u128asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u128asEq_spec_attrs 
             <TY> (int U128) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments u128asEq_spec : simpl never.

  Program Definition u128asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u128asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u128asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType U128) u128asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u128asEq_spec_attrs-[] -[(int U128)])))).
End u128asEq_spec.

Section u128asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType U128))) u128asPartialEq_spec_attrs u128asEq_spec_attrs u128asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u128asOrd_spec_attrs 
             <TY> (int U128) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_u128asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType U128))) u128asPartialEq_spec_attrs u128asEq_spec_attrs u128asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u128asOrd_spec_attrs 
             <TY> (int U128) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType U128))) u128asPartialEq_spec_attrs u128asEq_spec_attrs u128asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u128asOrd_spec_attrs 
             <TY> (int U128) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments u128asOrd_spec : simpl never.

  Program Definition u128asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u128asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u128asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType U128) u128asPartialEq_spec_attrs u128asEq_spec_attrs u128asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u128asOrd_spec_attrs-[] -[(int U128)])))).
End u128asOrd_spec.

Section u128asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_u128asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_u128asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u128asPartialEq_spec : simpl never.

  Program Definition u128asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u128asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u128asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType U128) (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u128asPartialEq_spec_attrs-[] -[(int U128); (int U128)])))).
End u128asPartialEq_spec.

Section u128asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_u128asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_u128asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_u128asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_u128asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_u128asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u128asPartialOrd_spec : simpl never.

  Program Definition u128asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u128asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u128asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType U128) (IntSynType U128) u128asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u128asPartialOrd_spec_attrs-[] -[(int U128); (int U128)])))).
End u128asPartialOrd_spec.

Section u16asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType U16))) u16asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u16asEq_spec_attrs 
             <TY> (int U16) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments u16asEq_spec : simpl never.

  Program Definition u16asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u16asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u16asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType U16) u16asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u16asEq_spec_attrs-[] -[(int U16)])))).
End u16asEq_spec.

Section u16asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType U16))) u16asPartialEq_spec_attrs u16asEq_spec_attrs u16asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u16asOrd_spec_attrs 
             <TY> (int U16) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_u16asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType U16))) u16asPartialEq_spec_attrs u16asEq_spec_attrs u16asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u16asOrd_spec_attrs 
             <TY> (int U16) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType U16))) u16asPartialEq_spec_attrs u16asEq_spec_attrs u16asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u16asOrd_spec_attrs 
             <TY> (int U16) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments u16asOrd_spec : simpl never.

  Program Definition u16asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u16asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u16asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType U16) u16asPartialEq_spec_attrs u16asEq_spec_attrs u16asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u16asOrd_spec_attrs-[] -[(int U16)])))).
End u16asOrd_spec.

Section u16asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_u16asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_u16asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u16asPartialEq_spec : simpl never.

  Program Definition u16asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u16asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u16asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType U16) (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u16asPartialEq_spec_attrs-[] -[(int U16); (int U16)])))).
End u16asPartialEq_spec.

Section u16asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_u16asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_u16asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_u16asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_u16asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_u16asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u16asPartialOrd_spec : simpl never.

  Program Definition u16asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u16asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u16asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType U16) (IntSynType U16) u16asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u16asPartialOrd_spec_attrs-[] -[(int U16); (int U16)])))).
End u16asPartialOrd_spec.

Section u32asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType U32))) u32asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u32asEq_spec_attrs 
             <TY> (int U32) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments u32asEq_spec : simpl never.

  Program Definition u32asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u32asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u32asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType U32) u32asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u32asEq_spec_attrs-[] -[(int U32)])))).
End u32asEq_spec.

Section u32asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType U32))) u32asPartialEq_spec_attrs u32asEq_spec_attrs u32asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u32asOrd_spec_attrs 
             <TY> (int U32) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_u32asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType U32))) u32asPartialEq_spec_attrs u32asEq_spec_attrs u32asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u32asOrd_spec_attrs 
             <TY> (int U32) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType U32))) u32asPartialEq_spec_attrs u32asEq_spec_attrs u32asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u32asOrd_spec_attrs 
             <TY> (int U32) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments u32asOrd_spec : simpl never.

  Program Definition u32asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u32asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u32asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType U32) u32asPartialEq_spec_attrs u32asEq_spec_attrs u32asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u32asOrd_spec_attrs-[] -[(int U32)])))).
End u32asOrd_spec.

Section u32asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_u32asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_u32asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u32asPartialEq_spec : simpl never.

  Program Definition u32asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u32asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u32asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType U32) (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u32asPartialEq_spec_attrs-[] -[(int U32); (int U32)])))).
End u32asPartialEq_spec.

Section u32asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_u32asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_u32asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_u32asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_u32asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_u32asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u32asPartialOrd_spec : simpl never.

  Program Definition u32asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u32asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u32asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType U32) (IntSynType U32) u32asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u32asPartialOrd_spec_attrs-[] -[(int U32); (int U32)])))).
End u32asPartialOrd_spec.

Section u64asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType U64))) u64asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u64asEq_spec_attrs 
             <TY> (int U64) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments u64asEq_spec : simpl never.

  Program Definition u64asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u64asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u64asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType U64) u64asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u64asEq_spec_attrs-[] -[(int U64)])))).
End u64asEq_spec.

Section u64asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType U64))) u64asPartialEq_spec_attrs u64asEq_spec_attrs u64asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u64asOrd_spec_attrs 
             <TY> (int U64) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_u64asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType U64))) u64asPartialEq_spec_attrs u64asEq_spec_attrs u64asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u64asOrd_spec_attrs 
             <TY> (int U64) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType U64))) u64asPartialEq_spec_attrs u64asEq_spec_attrs u64asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u64asOrd_spec_attrs 
             <TY> (int U64) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments u64asOrd_spec : simpl never.

  Program Definition u64asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u64asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u64asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType U64) u64asPartialEq_spec_attrs u64asEq_spec_attrs u64asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u64asOrd_spec_attrs-[] -[(int U64)])))).
End u64asOrd_spec.

Section u64asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_u64asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_u64asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u64asPartialEq_spec : simpl never.

  Program Definition u64asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u64asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u64asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType U64) (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u64asPartialEq_spec_attrs-[] -[(int U64); (int U64)])))).
End u64asPartialEq_spec.

Section u64asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_u64asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_u64asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_u64asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_u64asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_u64asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u64asPartialOrd_spec : simpl never.

  Program Definition u64asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u64asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u64asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType U64) (IntSynType U64) u64asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u64asPartialOrd_spec_attrs-[] -[(int U64); (int U64)])))).
End u64asPartialOrd_spec.

Section u8asEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType U8))) u8asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u8asEq_spec_attrs 
             <TY> (int U8) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments u8asEq_spec : simpl never.

  Program Definition u8asEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u8asEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u8asEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType U8) u8asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u8asEq_spec_attrs-[] -[(int U8)])))).
End u8asEq_spec.

Section u8asOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType U8))) u8asPartialEq_spec_attrs u8asEq_spec_attrs u8asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u8asOrd_spec_attrs 
             <TY> (int U8) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_u8asOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType U8))) u8asPartialEq_spec_attrs u8asEq_spec_attrs u8asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u8asOrd_spec_attrs 
             <TY> (int U8) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType U8))) u8asPartialEq_spec_attrs u8asEq_spec_attrs u8asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u8asOrd_spec_attrs 
             <TY> (int U8) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments u8asOrd_spec : simpl never.

  Program Definition u8asOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u8asOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u8asOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType U8) u8asPartialEq_spec_attrs u8asEq_spec_attrs u8asPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u8asOrd_spec_attrs-[] -[(int U8)])))).
End u8asOrd_spec.

Section u8asPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_u8asPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_u8asPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u8asPartialEq_spec : simpl never.

  Program Definition u8asPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u8asPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u8asPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType U8) (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u8asPartialEq_spec_attrs-[] -[(int U8); (int U8)])))).
End u8asPartialEq_spec.

Section u8asPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_u8asPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_u8asPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_u8asPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_u8asPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_u8asPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u8asPartialOrd_spec : simpl never.

  Program Definition u8asPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u8asPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u8asPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType U8) (IntSynType U8) u8asPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) u8asPartialOrd_spec_attrs-[] -[(int U8); (int U8)])))).
End u8asPartialOrd_spec.

Section usizeasEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasEq_spec  : (spec_with _ _ (Eq_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (Z) ((IntSynType USize))) usizeasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) usizeasEq_spec_attrs 
             <TY> (int USize) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments usizeasEq_spec : simpl never.

  Program Definition usizeasEq_realization  : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, usizeasEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition usizeasEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Eq_base_spec Z (IntSynType USize) usizeasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) usizeasEq_spec_attrs-[] -[(int USize)])))).
End usizeasEq_spec.

Section usizeasOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasOrd_spec  : (spec_with _ _ (Ord_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (Z) ((IntSynType USize))) usizeasPartialEq_spec_attrs usizeasEq_spec_attrs usizeasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) usizeasOrd_spec_attrs 
             <TY> (int USize) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          type_of_usizeasOrd_cmp 
             : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (Z) ((IntSynType USize))) usizeasPartialEq_spec_attrs usizeasEq_spec_attrs usizeasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) usizeasOrd_spec_attrs 
             <TY> (int USize) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (Z) ((IntSynType USize))) usizeasPartialEq_spec_attrs usizeasEq_spec_attrs usizeasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) usizeasOrd_spec_attrs 
             <TY> (int USize) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments usizeasOrd_spec : simpl never.

  Program Definition usizeasOrd_realization  : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, usizeasOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition usizeasOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Ord_base_spec Z (IntSynType USize) usizeasPartialEq_spec_attrs usizeasEq_spec_attrs usizeasPartialOrd_spec_attrs (drop_glue_trivial_spec_attrs (Z)) usizeasOrd_spec_attrs-[] -[(int USize)])))).
End usizeasOrd_spec.

Section usizeasPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasPartialEq_spec  : (spec_with _ _ (PartialEq_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialEq_eq_spec  :=
          type_of_usizeasPartialEq_eq 
             : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          type_of_usizeasPartialEq_ne 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments usizeasPartialEq_spec : simpl never.

  Program Definition usizeasPartialEq_realization  : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, usizeasPartialEq_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition usizeasPartialEq_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasPartialEq_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialEq_base_spec Z Z (IntSynType USize) (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) usizeasPartialEq_spec_attrs-[] -[(int USize); (int USize)])))).
End usizeasPartialEq_spec.

Section usizeasPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasPartialOrd_spec  : (spec_with _ _ (PartialOrd_spec (Z) (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        PartialOrd_ge_spec  :=
          type_of_usizeasPartialOrd_ge 
             : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          type_of_usizeasPartialOrd_gt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          type_of_usizeasPartialOrd_le 
             : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          type_of_usizeasPartialOrd_lt 
             : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          type_of_usizeasPartialOrd_partial_cmp 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments usizeasPartialOrd_spec : simpl never.

  Program Definition usizeasPartialOrd_realization  : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) Z Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, usizeasPartialOrd_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition usizeasPartialOrd_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasPartialOrd_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((PartialOrd_base_spec Z Z (IntSynType USize) (IntSynType USize) usizeasPartialEq_spec_attrs (drop_glue_trivial_spec_attrs (Z)) (drop_glue_trivial_spec_attrs (Z)) usizeasPartialOrd_spec_attrs-[] -[(int USize); (int USize)])))).
End usizeasPartialOrd_spec.

Section std_option_OptionTasEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_option_OptionTasEq_spec (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Eq_spec (((((Option_rt)) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Eq_assert_fields_are_eq_spec  :=
          (Eq_assert_fields_are_eq_base_spec (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type))) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasEq_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments std_option_OptionTasEq_spec : simpl never.

  Program Definition std_option_OptionTasEq_realization (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (Eq_T_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) ((((Option_rt)) ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
  ∗ (∃ (Eq_T_lfts_inst : prod_vec lft Eq_T_realization.(trait_ctx_lfts)) (Eq_T_tys_inst : plist type Eq_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_T_realization.(trait_ctx_spec) Eq_T_lfts_inst Eq_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs Eq_T_spec_attrs-[] -[T_ty]))⌝ ∗ Eq_T_realization.(trait_ctx_wf) Eq_T_lfts_inst Eq_T_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (std_option_OptionTasEq_spec (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition std_option_OptionTasEq_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(PartialEq_T_T_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) `(Eq_T_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Eq_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_option_OptionTasEq_spec (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Eq_base_spec ((((Option_rt)) ((T_rt)))) ((Option_els (T_st)) : syn_type) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasEq_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[(Option_ty ((T_rt)) -[] -[T_ty])])))).
End std_option_OptionTasEq_spec.

Section std_option_OptionTasOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_option_OptionTasOrd_spec (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Ord_spec (((((Option_rt)) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Ord_clamp_spec  :=
          (Ord_clamp_base_spec (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type))) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (Ord_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 0 [] fn_spec);
        Ord_cmp_spec  :=
          (type_of_std_option_OptionTasOrd_cmp ((T_rt)) (T_st)) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs Ord_T_spec_attrs DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 2 [] fn_spec);
        Ord_max_spec  :=
          (Ord_max_base_spec (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type))) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (Ord_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 0 [] fn_spec);
        Ord_min_spec  :=
          (Ord_min_base_spec (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type))) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (Ord_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments std_option_OptionTasOrd_spec : simpl never.

  Program Definition std_option_OptionTasOrd_realization (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Eq_T_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) (Eq_T_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (T_rt))))) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (Ord_T_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) (Ord_T_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) ((((Option_rt)) ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
  ∗ (∃ (Eq_T_lfts_inst : prod_vec lft Eq_T_realization.(trait_ctx_lfts)) (Eq_T_tys_inst : plist type Eq_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_T_realization.(trait_ctx_spec) Eq_T_lfts_inst Eq_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs Eq_T_spec_attrs-[] -[T_ty]))⌝ ∗ Eq_T_realization.(trait_ctx_wf) Eq_T_lfts_inst Eq_T_tys_inst π)
  ∗ (∃ (PartialOrd_T_T_lfts_inst : prod_vec lft PartialOrd_T_T_realization.(trait_ctx_lfts)) (PartialOrd_T_T_tys_inst : plist type PartialOrd_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_T_T_realization.(trait_ctx_spec) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (T_rt) (T_rt) T_st T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialOrd_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialOrd_T_T_realization.(trait_ctx_wf) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst π)
  ∗ (∃ (Ord_T_lfts_inst : prod_vec lft Ord_T_realization.(trait_ctx_lfts)) (Ord_T_tys_inst : plist type Ord_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_T_realization.(trait_ctx_spec) Ord_T_lfts_inst Ord_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (T_rt) T_st PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs DropGlue_T_spec_attrs Ord_T_spec_attrs-[] -[T_ty]))⌝ ∗ Ord_T_realization.(trait_ctx_wf) Ord_T_lfts_inst Ord_T_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (std_option_OptionTasOrd_spec (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (Ord_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition std_option_OptionTasOrd_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(PartialEq_T_T_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) `(Eq_T_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) `(PartialOrd_T_T_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) `(Ord_T_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Ord_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_option_OptionTasOrd_spec (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (Ord_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Ord_base_spec ((((Option_rt)) ((T_rt)))) ((Option_els (T_st)) : syn_type) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (std_option_OptionTasEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (Eq_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (Ord_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[(Option_ty ((T_rt)) -[] -[T_ty])])))).
End std_option_OptionTasOrd_spec.

Section std_option_OptionTasPartialEq_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_option_OptionTasPartialEq_spec (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (PartialEq_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        PartialEq_eq_spec  :=
          (type_of_std_option_OptionTasPartialEq_eq ((T_rt)) (T_st)) PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 2 [] fn_spec);
        PartialEq_ne_spec  :=
          (PartialEq_ne_base_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (((Option_els (T_st)) : syn_type))) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialEq_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments std_option_OptionTasPartialEq_spec : simpl never.

  Program Definition std_option_OptionTasPartialEq_realization (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) ((((Option_rt)) ((T_rt)))) ((((Option_rt)) ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (std_option_OptionTasPartialEq_spec (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition std_option_OptionTasPartialEq_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(PartialEq_T_T_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl PartialEq_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_option_OptionTasPartialEq_spec (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((PartialEq_base_spec ((((Option_rt)) ((T_rt)))) ((((Option_rt)) ((T_rt)))) ((Option_els (T_st)) : syn_type) ((Option_els (T_st)) : syn_type) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialEq_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[(Option_ty ((T_rt)) -[] -[T_ty]); (Option_ty ((T_rt)) -[] -[T_ty])])))).
End std_option_OptionTasPartialEq_spec.

Section std_option_OptionTasPartialOrd_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_option_OptionTasPartialOrd_spec (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (PartialOrd_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        PartialOrd_ge_spec  :=
          (PartialOrd_ge_base_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (((Option_els (T_st)) : syn_type))) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 2 [] fn_spec);
        PartialOrd_gt_spec  :=
          (PartialOrd_gt_base_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (((Option_els (T_st)) : syn_type))) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 2 [] fn_spec);
        PartialOrd_le_spec  :=
          (PartialOrd_le_base_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (((Option_els (T_st)) : syn_type))) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 2 [] fn_spec);
        PartialOrd_lt_spec  :=
          (PartialOrd_lt_base_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (((Option_els (T_st)) : syn_type))) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 2 [] fn_spec);
        PartialOrd_partial_cmp_spec  :=
          (type_of_std_option_OptionTasPartialOrd_partial_cmp ((T_rt)) (T_st)) PartialEq_T_T_spec_attrs PartialOrd_T_T_spec_attrs DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments std_option_OptionTasPartialOrd_spec : simpl never.

  Program Definition std_option_OptionTasPartialOrd_realization (T_rt: RT) (T_st: syn_type) (PartialEq_T_T_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) (PartialEq_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (PartialOrd_T_T_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) (PartialOrd_T_T_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (T_rt) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) ((((Option_rt)) ((T_rt)))) ((((Option_rt)) ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (PartialEq_T_T_lfts_inst : prod_vec lft PartialEq_T_T_realization.(trait_ctx_lfts)) (PartialEq_T_T_tys_inst : plist type PartialEq_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_T_T_realization.(trait_ctx_spec) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (T_rt) (T_rt) T_st T_st DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialEq_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialEq_T_T_realization.(trait_ctx_wf) PartialEq_T_T_lfts_inst PartialEq_T_T_tys_inst π)
  ∗ (∃ (PartialOrd_T_T_lfts_inst : prod_vec lft PartialOrd_T_T_realization.(trait_ctx_lfts)) (PartialOrd_T_T_tys_inst : plist type PartialOrd_T_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_T_T_realization.(trait_ctx_spec) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (T_rt) (T_rt) T_st T_st PartialEq_T_T_spec_attrs DropGlue_T_spec_attrs DropGlue_T_spec_attrs PartialOrd_T_T_spec_attrs-[] -[T_ty; T_ty]))⌝ ∗ PartialOrd_T_T_realization.(trait_ctx_wf) PartialOrd_T_T_lfts_inst PartialOrd_T_T_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (std_option_OptionTasPartialOrd_spec (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition std_option_OptionTasPartialOrd_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(PartialEq_T_T_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) `(PartialOrd_T_T_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_option_OptionTasPartialOrd_spec (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((PartialOrd_base_spec ((((Option_rt)) ((T_rt)))) ((((Option_rt)) ((T_rt)))) ((Option_els (T_st)) : syn_type) ((Option_els (T_st)) : syn_type) (std_option_OptionTasPartialEq_spec_attrs ((T_rt)) (PartialEq_T_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (std_option_OptionTasPartialOrd_spec_attrs (T_rt) (PartialEq_T_T_spec_attrs) (PartialOrd_T_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[(Option_ty ((T_rt)) -[] -[T_ty]); (Option_ty ((T_rt)) -[] -[T_ty])])))).
End std_option_OptionTasPartialOrd_spec.

Section Ord_max_closure0_FnOnce_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition Ord_max_closure0_FnOnce_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) : (spec_with _ _ (FnOnce_spec (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)))) :=
    spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), let Output_rt := (Ordering_rt) in {|
        FnOnce_call_once_spec  :=
          (Ord_max_closure0_call_once_spec ((Self_rt)) (Self_st)) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs Ord_Self_spec_attrs DropGlue_Self_spec_attrs 
             <TY> Self_ty <LFT> ulft_2 <LFT> ulft_3 : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments Ord_max_closure0_FnOnce_spec : simpl never.

  Program Definition Ord_max_closure0_FnOnce_realization (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) : trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) unit (((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))))) (Ordering_rt))) :=
  {|
    trait_ctx_lfts := 2;
    trait_ctx_tys := [Self_rt];
    trait_ctx_wf := λ '( *[ulft_2; ulft_3]) '( *[Self_ty]) π, (((typaram_wf Self_rt Self_st Self_ty))
  ∗ (∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
  ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
  ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
  ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π)
  ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_2; ulft_3]) '( *[Self_ty]) _ _, (Ord_max_closure0_FnOnce_spec (Self_rt) (Self_st) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs))-[ulft_2; ulft_3] -[Self_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition Ord_max_closure0_FnOnce_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(Self_st : !syn_type) `(PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) `(Eq_Self_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(PartialOrd_Self_Self_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(Ord_Self_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), (Ord_max_closure0_FnOnce_spec (Self_rt) (Self_st) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs))-[ulft_2; ulft_3] -[Self_ty]) (spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), scope_add_typarams _ -[Self_ty] ((FnOnce_base_spec unit (((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))))) (Ordering_rt) UnitSynType ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) Ordering_st (drop_glue_trivial_spec_attrs (unit)) (drop_glue_tuple2_spec_attrs ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (Self_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (Self_rt)))))) (drop_glue_trivial_spec_attrs ((Ordering_rt))) (Ord_max_closure0_FnOnce_spec_attrs (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs))-[] -[unit_t; (tuple2_ty ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))) -[] -[(shr_ref ulft_2 Self_ty); (shr_ref ulft_3 Self_ty)]); (Ordering_ty  -[] -[])])))).
End Ord_max_closure0_FnOnce_spec.

Section Ord_min_closure0_FnOnce_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition Ord_min_closure0_FnOnce_spec (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) : (spec_with _ _ (FnOnce_spec (unit) ((((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt)))))) ((Ordering_rt)))) :=
    spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), let Output_rt := (Ordering_rt) in {|
        FnOnce_call_once_spec  :=
          (Ord_min_closure0_call_once_spec ((Self_rt)) (Self_st)) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs Ord_Self_spec_attrs DropGlue_Self_spec_attrs 
             <TY> Self_ty <LFT> ulft_2 <LFT> ulft_3 : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments Ord_min_closure0_FnOnce_spec : simpl never.

  Program Definition Ord_min_closure0_FnOnce_realization (Self_rt: RT) (Self_st: syn_type) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Eq_Self_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Eq_Self_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) (Ord_Self_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (Ord_Self_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) : trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) unit (((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))))) (Ordering_rt))) :=
  {|
    trait_ctx_lfts := 2;
    trait_ctx_tys := [Self_rt];
    trait_ctx_wf := λ '( *[ulft_2; ulft_3]) '( *[Self_ty]) π, (((typaram_wf Self_rt Self_st Self_ty))
  ∗ (∃ (PartialEq_Self_Self_lfts_inst : prod_vec lft PartialEq_Self_Self_realization.(trait_ctx_lfts)) (PartialEq_Self_Self_tys_inst : plist type PartialEq_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_Self_Self_realization.(trait_ctx_spec) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialEq_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialEq_Self_Self_realization.(trait_ctx_wf) PartialEq_Self_Self_lfts_inst PartialEq_Self_Self_tys_inst π)
  ∗ (∃ (Eq_Self_lfts_inst : prod_vec lft Eq_Self_realization.(trait_ctx_lfts)) (Eq_Self_tys_inst : plist type Eq_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_Self_realization.(trait_ctx_spec) Eq_Self_lfts_inst Eq_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs Eq_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Eq_Self_realization.(trait_ctx_wf) Eq_Self_lfts_inst Eq_Self_tys_inst π)
  ∗ (∃ (PartialOrd_Self_Self_lfts_inst : prod_vec lft PartialOrd_Self_Self_realization.(trait_ctx_lfts)) (PartialOrd_Self_Self_tys_inst : plist type PartialOrd_Self_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_Self_Self_realization.(trait_ctx_spec) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Self_spec_attrs PartialOrd_Self_Self_spec_attrs-[] -[Self_ty; Self_ty]))⌝ ∗ PartialOrd_Self_Self_realization.(trait_ctx_wf) PartialOrd_Self_Self_lfts_inst PartialOrd_Self_Self_tys_inst π)
  ∗ (∃ (Ord_Self_lfts_inst : prod_vec lft Ord_Self_realization.(trait_ctx_lfts)) (Ord_Self_tys_inst : plist type Ord_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_Self_realization.(trait_ctx_spec) Ord_Self_lfts_inst Ord_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Ord_Self_realization.(trait_ctx_wf) Ord_Self_lfts_inst Ord_Self_tys_inst π)
  ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_2; ulft_3]) '( *[Self_ty]) _ _, (Ord_min_closure0_FnOnce_spec (Self_rt) (Self_st) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs))-[ulft_2; ulft_3] -[Self_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition Ord_min_closure0_FnOnce_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(Self_st : !syn_type) `(PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) `(Eq_Self_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(PartialOrd_Self_Self_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(Ord_Self_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), (Ord_min_closure0_FnOnce_spec (Self_rt) (Self_st) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs))-[ulft_2; ulft_3] -[Self_ty]) (spec! ( *[ulft_2; ulft_3]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), scope_add_typarams _ -[Self_ty] ((FnOnce_base_spec unit (((tuple2_rt) ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))))) (Ordering_rt) UnitSynType ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) Ordering_st (drop_glue_trivial_spec_attrs (unit)) (drop_glue_tuple2_spec_attrs ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (Self_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (Self_rt)))))) (drop_glue_trivial_spec_attrs ((Ordering_rt))) (Ord_min_closure0_FnOnce_spec_attrs (Self_rt) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs))-[] -[unit_t; (tuple2_ty ((place_rfnRT (Self_rt))) ((place_rfnRT (Self_rt))) -[] -[(shr_ref ulft_2 Self_ty); (shr_ref ulft_3 Self_ty)]); (Ordering_ty  -[] -[])])))).
End Ord_min_closure0_FnOnce_spec.

