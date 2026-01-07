From caesium Require Import lang notation.
From refinedrust Require Import annotations typing.


Program Definition mem_size_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_code :=
    <["_bb0" :=
      local_live{IntSynType USize} "ret";
      "ret" <-{IntOp USize} (i2v (ly_size (use_layout_alg' T_st)) USize);
      return (use{IntOp USize} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Program Definition mem_align_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_code :=
    <["_bb0" :=
    local_live{IntSynType USize} "ret";
    "ret" <-{IntOp USize} (i2v (ly_align (use_layout_alg' T_st)) USize);
    return (use{IntOp USize} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Program Definition mem_align_log_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_code :=
    <["_bb0" :=
    local_live{IntSynType USize} "ret";
    "ret" <-{IntOp USize} (i2v (ly_align_log (use_layout_alg' T_st)) USize);
    return (use{IntOp USize} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.
