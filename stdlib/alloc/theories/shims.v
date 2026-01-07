From caesium Require Import lang notation.
From refinedrust Require Import typing shims.

Program Definition alloc_alloc_def `{!LayoutAlg} : function := {|
  f_args := [("size", USize : layout); ("align_log2", USize : layout)];
  f_code :=
    <["_bb0" :=
        local_live{PtrSynType} "ret";
        "ret" <-{PtrOp} (Alloc (use{IntOp USize} "size") (use{IntOp USize} "align_log2"));
        return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
 |}.
Next Obligation. solve_fn_vars_nodup. Qed.

Notation "'free{' e_size ',' e_align '}' e_ptr ; s" := (Free e_size%E e_align%E e_ptr%E s%E)
  (at level 80, s at level 200, format "'[v' 'free{' e_size ','  e_align '}'  e_ptr ';' '/' s ']'") : expr_scope.
Program Definition alloc_dealloc_def `{!LayoutAlg} : function := {|
  f_args := [("size", USize : layout); ("align", USize : layout); ("ptr", void* )];
  f_code :=
    <["_bb0" :=
      free{ use{IntOp USize} "size", use{IntOp USize} "align"} (use{PtrOp} "ptr");
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.
