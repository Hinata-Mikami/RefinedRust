From radium Require Import lang.

(** Regression tests for Rust's built-in integer shift semantics. *)

Example shl_negative_lhs_is_defined :
  compute_arith_bin_op (-64) 2 I8 ShlOp = Some (-256).
Proof. vm_compute. reflexivity. Qed.

Example shl_discards_high_bits_without_overflow :
  check_arith_bin_op ShlOp I8 127 1 = Some false.
Proof. vm_compute. reflexivity. Qed.

Example shl_computes_shift_amount_equal_to_width :
  compute_arith_bin_op 1 8 I8 ShlOp = Some 256.
Proof. vm_compute. reflexivity. Qed.

Example shl_check_reports_invalid_shift_amount :
  check_arith_bin_op ShlOp I8 1 8 = Some true.
Proof. vm_compute. reflexivity. Qed.

Example shl_rejects_negative_shift_amount :
  compute_arith_bin_op 1 (-1) I8 ShlOp = None.
Proof. vm_compute. reflexivity. Qed.

Example rocq_shl_negative_amount_is_right_shift :
  Z.shiftl 1 (-1) = 0.
Proof. vm_compute. reflexivity. Qed.

Example shr_signed_is_arithmetic :
  compute_arith_bin_op (-64) 2 I8 ShrOp = Some (-16).
Proof. vm_compute. reflexivity. Qed.

Example shr_unsigned_is_logical :
  compute_arith_bin_op 192 2 U8 ShrOp = Some 48.
Proof. vm_compute. reflexivity. Qed.

Example shr_computes_shift_amount_equal_to_width :
  compute_arith_bin_op 1 8 I8 ShrOp = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example shr_check_reports_invalid_shift_amount :
  check_arith_bin_op ShrOp I8 1 8 = Some true.
Proof. vm_compute. reflexivity. Qed.

Example shr_signed_shift_amount_equal_to_width :
  compute_arith_bin_op (-1) 8 I8 ShrOp = Some (-1).
Proof. vm_compute. reflexivity. Qed.
