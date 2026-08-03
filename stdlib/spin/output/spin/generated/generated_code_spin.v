From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops.generated Require Export generated_specs_arithops.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.option.option.generated Require Export generated_specs_option.
Section relax_Spin_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition relax_Spin_sls  : struct_layout_spec :=
    let relax_Spin_st  := UnitSynType in
    mk_sls "relax_Spin" [] StructReprRust.
  Definition relax_Spin_st  : syn_type := relax_Spin_sls .
End relax_Spin_sls.

Section rwlock_RwLockReadGuard_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition rwlock_RwLockReadGuard_sls (T_st: syn_type) : struct_layout_spec :=
    let rwlock_RwLockReadGuard_st (T_st: syn_type) := UnitSynType in
    mk_sls "rwlock_RwLockReadGuard" [
    ("_t", RefSynType)] StructReprRust.
  Definition rwlock_RwLockReadGuard_st (T_st: syn_type) : syn_type := rwlock_RwLockReadGuard_sls T_st.
End rwlock_RwLockReadGuard_sls.

Section once_Once_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition once_Once_sls (T_st: syn_type) (R_st: syn_type) : struct_layout_spec :=
    let once_Once_st (T_st: syn_type) (R_st: syn_type) := UnitSynType in
    mk_sls "once_Once" [
    ("_r", ((core_marker_PhantomData_sls (R_st)) : syn_type));
    ("_d", ((core_marker_PhantomData_sls (T_st)) : syn_type))] StructReprRust.
  Definition once_Once_st (T_st: syn_type) (R_st: syn_type) : syn_type := once_Once_sls T_st R_st.
End once_Once_sls.

Section rwlock_RwLock_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition rwlock_RwLock_sls (T_st: syn_type) (R_st: syn_type) : struct_layout_spec :=
    let rwlock_RwLock_st (T_st: syn_type) (R_st: syn_type) := UnitSynType in
    mk_sls "rwlock_RwLock" [
    ("phantom", ((core_marker_PhantomData_sls (R_st)) : syn_type));
    ("data", ((core_marker_PhantomData_sls (T_st)) : syn_type))] StructReprRust.
  Definition rwlock_RwLock_st (T_st: syn_type) (R_st: syn_type) : syn_type := rwlock_RwLock_sls T_st R_st.
End rwlock_RwLock_sls.

Section rwlock_RwLockWriteGuard_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition rwlock_RwLockWriteGuard_sls (T_st: syn_type) (R_st: syn_type) : struct_layout_spec :=
    let rwlock_RwLockWriteGuard_st (T_st: syn_type) (R_st: syn_type) := UnitSynType in
    mk_sls "rwlock_RwLockWriteGuard" [
    ("_l", RefSynType);
    ("_r", R_st)] StructReprRust.
  Definition rwlock_RwLockWriteGuard_st (T_st: syn_type) (R_st: syn_type) : syn_type := rwlock_RwLockWriteGuard_sls T_st R_st.
End rwlock_RwLockWriteGuard_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition drop_glue_rwlock_RwLockWriteGuard_def (DropGlue_R_drop_glue_loc: loc) (T_st: syn_type) (R_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      CallS DropGlue_R_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (rwlock_RwLockWriteGuard_sls (T_st) (R_st)) } "_r")] None
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.