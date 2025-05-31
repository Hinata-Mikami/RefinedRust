From caesium Require Import lang notation.
From refinedrust Require Import annotations.


Definition mem_size_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_local_vars := [("ret", USize : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
      "ret" <-{IntOp USize} (i2v (ly_size (use_layout_alg' T_st)) USize);
      return (use{IntOp USize} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

Definition mem_align_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_local_vars := [("ret", USize : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
    "ret" <-{IntOp USize} (i2v (ly_align (use_layout_alg' T_st)) USize);
    return (use{IntOp USize} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

Definition mem_align_log_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_local_vars := [("ret", USize : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
    "ret" <-{IntOp USize} (i2v (ly_align_log (use_layout_alg' T_st)) USize);
    return (use{IntOp USize} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
