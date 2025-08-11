From refinedrust Require Import typing.


(** * Built-in shims for low-level pointer operations *)

(** Tuple defs *)
(* Since the frontend doesn't generate them for now, we just provide a few pre-defined ones for reasonable sizes. *)
Definition tuple1_sls (T0_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple1" [("0", T0_st)] StructReprRust.
Definition tuple1_st (T0_st : syn_type) : syn_type := tuple1_sls T0_st.
Definition tuple1_rt (T0_rt : RT) : RT :=
  plist place_rfnRT [T0_rt].
Definition tuple1_ty `{!refinedrustGS Σ} (T0_rt : RT) : spec_with 0 [T0_rt] (type (tuple1_rt _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty]) : [T0_rt], struct_t (tuple1_sls (st_of T0_ty)) +[T0_ty].

Definition tuple2_sls (T0_st T1_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple2" [("0", T0_st); ("1", T1_st)] StructReprRust.
Definition tuple2_st (T0_st T1_st : syn_type) : syn_type := tuple2_sls T0_st T1_st.
Definition tuple2_rt (T0_rt : RT) (T1_rt : RT) : RT :=
  plist place_rfnRT [T0_rt; T1_rt].
Definition tuple2_ty `{!refinedrustGS Σ} (T0_rt T1_rt : RT) : spec_with 0 [T0_rt; T1_rt] (type (tuple2_rt _ _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty; T1_ty]) : [T0_rt; T1_rt], struct_t (tuple2_sls (st_of T0_ty) (st_of T1_ty)) +[T0_ty; T1_ty].

Definition tuple3_sls (T0_st T1_st T2_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple3" [("0", T0_st); ("1", T1_st); ("2", T2_st)] StructReprRust.
Definition tuple3_st (T0_st T1_st T2_st : syn_type) : syn_type := tuple3_sls T0_st T1_st T2_st.
Definition tuple3_rt (T0_rt : RT) (T1_rt : RT) (T2_rt : RT) : RT :=
  plist place_rfnRT [T0_rt; T1_rt; T2_rt].
Definition tuple3_ty `{!refinedrustGS Σ} (T0_rt T1_rt T2_rt : RT) : spec_with 0 [T0_rt; T1_rt; T2_rt] (type (tuple3_rt _ _ _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty]) : [T0_rt; T1_rt; T2_rt], struct_t (tuple3_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty)) +[T0_ty; T1_ty; T2_ty].

Definition tuple4_sls (T0_st T1_st T2_st T3_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple4" [("0", T0_st); ("1", T1_st); ("2", T2_st); ("3", T3_st)] StructReprRust.
Definition tuple4_st (T0_st T1_st T2_st T3_st : syn_type) : syn_type := tuple4_sls T0_st T1_st T2_st T3_st.
Definition tuple4_rt (T0_rt : RT) (T1_rt : RT) (T2_rt : RT) (T3_rt : RT) : RT :=
  plist place_rfnRT [T0_rt; T1_rt; T2_rt; T3_rt].
Definition tuple4_ty `{!refinedrustGS Σ} (T0_rt T1_rt T2_rt T3_rt : RT) : spec_with 0 [T0_rt; T1_rt; T2_rt; T3_rt] (type (tuple4_rt _ _ _ _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty]) : [T0_rt; T1_rt; T2_rt; T3_rt], struct_t (tuple4_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty) (st_of T3_ty)) +[T0_ty; T1_ty; T2_ty; T3_ty].

Definition tuple5_sls (T0_st T1_st T2_st T3_st T4_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple5" [("0", T0_st); ("1", T1_st); ("2", T2_st); ("3", T3_st); ("4", T4_st)] StructReprRust.
Definition tuple5_st (T0_st T1_st T2_st T3_st T4_st : syn_type) : syn_type := tuple5_sls T0_st T1_st T2_st T3_st T4_st.
Definition tuple5_rt (T0_rt : RT) (T1_rt : RT) (T2_rt : RT) (T3_rt : RT) (T4_rt : RT) : RT :=
  plist place_rfnRT [T0_rt; T1_rt; T2_rt; T3_rt; T4_rt].
Definition tuple5_ty `{!refinedrustGS Σ} (T0_rt T1_rt T2_rt T3_rt T4_rt : RT) : spec_with 0 [T0_rt; T1_rt; T2_rt; T3_rt; T4_rt] (type (tuple5_rt _ _ _ _ _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty]) : [T0_rt; T1_rt; T2_rt; T3_rt; T4_rt], struct_t (tuple5_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty) (st_of T3_ty) (st_of T4_ty)) +[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty].
