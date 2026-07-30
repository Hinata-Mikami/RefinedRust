From radium Require Import lang notation.
From refinedrust Require Import typing shims.
Section RwLock_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RwLock_sls (T_st: syn_type) : struct_layout_spec :=
    let RwLock_st (T_st: syn_type) := UnitSynType in
    mk_sls "RwLock" [
    ("_t", ((core_marker_PhantomData_sls (T_st)) : syn_type))] StructReprRust.
  Definition RwLock_st (T_st: syn_type) : syn_type := RwLock_sls T_st.
End RwLock_sls.

Section RwLockReadGuard_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RwLockReadGuard_sls (T_st: syn_type) : struct_layout_spec :=
    let RwLockReadGuard_st (T_st: syn_type) := UnitSynType in
    mk_sls "RwLockReadGuard" [
    ("_t", ((core_marker_PhantomData_sls (RefSynType)) : syn_type))] StructReprRust.
  Definition RwLockReadGuard_st (T_st: syn_type) : syn_type := RwLockReadGuard_sls T_st.
End RwLockReadGuard_sls.

Section PoisonError_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition PoisonError_sls (T_st: syn_type) : struct_layout_spec :=
    let PoisonError_st (T_st: syn_type) := UnitSynType in
    mk_sls "PoisonError" [
    ("guard", ((core_marker_PhantomData_sls (T_st)) : syn_type))] StructReprRust.
  Definition PoisonError_st (T_st: syn_type) : syn_type := PoisonError_sls T_st.
End PoisonError_sls.

Section RwLockWriteGuard_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RwLockWriteGuard_sls (T_st: syn_type) : struct_layout_spec :=
    let RwLockWriteGuard_st (T_st: syn_type) := UnitSynType in
    mk_sls "RwLockWriteGuard" [
    ("_l", RefSynType)] StructReprRust.
  Definition RwLockWriteGuard_st (T_st: syn_type) : syn_type := RwLockWriteGuard_sls T_st.
End RwLockWriteGuard_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

(* closure shims *)
End code.