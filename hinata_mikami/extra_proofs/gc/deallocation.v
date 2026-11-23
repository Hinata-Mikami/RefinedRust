From radium Require Import lang notation tactics.

(* Model Global deallocation using the layout of the pointed-to type. *)
Program Definition dealloc_storage_def `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("ptr", void*)];
  f_code :=
    <["_bb0" :=
      Free (i2v (ly_size (use_layout_alg' T_st)) USize)
           (i2v (ly_align_log (use_layout_alg' T_st)) USize)
           (copy{PtrOp} "ptr")
           (return zst_val)
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.
