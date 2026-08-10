From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.option.option.generated Require Export generated_specs_option.
Section BTreeMap_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition BTreeMap_sls (K_st: syn_type) (V_st: syn_type) (A_st: syn_type) : struct_layout_spec :=
    let BTreeMap_st (K_st: syn_type) (V_st: syn_type) (A_st: syn_type) := UnitSynType in
    mk_sls "BTreeMap" [
    ("_k", K_st);
    ("_v", V_st);
    ("_a", A_st)] StructReprRust.
  Definition BTreeMap_st (K_st: syn_type) (V_st: syn_type) (A_st: syn_type) : syn_type := BTreeMap_sls K_st V_st A_st.
End BTreeMap_sls.

Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

(* closure shims *)
End code.