From caesium Require Import lang notation.
From refinedrust Require Import typing shims.

Definition alloc_alloc_def `{!LayoutAlg} : function := {|
  f_args := [("size", usize_t : layout); ("align_log2", usize_t : layout)];
  f_local_vars := [("ret", void*); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
        "ret" <-{PtrOp} (Alloc (use{IntOp usize_t} "size") (use{IntOp usize_t} "align_log2"));
        return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
 |}.

Notation "'free{' e_size ',' e_align '}' e_ptr ; s" := (Free e_size%E e_align%E e_ptr%E s%E)
  (at level 80, s at level 200, format "'[v' 'free{' e_size ','  e_align '}'  e_ptr ';' '/' s ']'") : expr_scope.
Definition alloc_dealloc_def `{!LayoutAlg} : function := {|
  f_args := [("size", usize_t : layout); ("align", usize_t : layout); ("ptr", void* )];
  f_local_vars := [("_0", use_layout_alg' UnitSynType); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
      free{ use{IntOp usize_t} "size", use{IntOp usize_t} "align"} (use{PtrOp} "ptr");
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
