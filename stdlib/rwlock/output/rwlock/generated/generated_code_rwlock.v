From radium Require Import lang notation.
From refinedrust Require Import typing shims.
Section RwLock_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RwLock_sls (T_st: syn_type) : struct_layout_spec :=
    let RwLock_st (T_st: syn_type) := UnitSynType in
    mk_sls "RwLock" [
    ("_t", T_st)] StructReprRust.
  Definition RwLock_st (T_st: syn_type) : syn_type := RwLock_sls T_st.
End RwLock_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

(* closure shims *)
End code.