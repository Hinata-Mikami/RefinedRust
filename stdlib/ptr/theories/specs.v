From refinedrust Require Import typing.

(* ptr::copy *)
Definition sublist_lookup' {A} (i n : nat) (l : list A) : list A :=
  take n (drop i l).
Definition ptr_copy_result {A} (off_src : Z) (off_dst : Z) (count : nat) (xs : list A) : list A :=
  (*let wipe_src := list_inserts (Z.to_nat off_src) (replicate count (#None)) xs in*)
  let ins_dst := list_inserts (Z.to_nat off_dst) (sublist_lookup' (Z.to_nat off_src) count xs) xs in
  ins_dst.


(* const_ptr::offset / mut_ptr::offset *)
Inductive trace_offset :=
  | TraceOffset (offset : Z).


(* with_addr *)
Definition with_addr (l : loc) (a : addr) : loc :=
  (l.1, a).
Arguments with_addr : simpl never.
