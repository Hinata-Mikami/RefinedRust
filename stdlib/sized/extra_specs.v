Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.
Existing Class Sized_semantic_interp. 
Global Instance Sized_semantic_TySized `{!refinedrustGS Σ} {rt} (ty : type rt) : 
  Sized_semantic_interp rt ty →
  TySized ty.
Proof. done. Qed.
End extra_specs.
