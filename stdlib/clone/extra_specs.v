Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.
Existing Class Copy_semantic_interp. 
Global Instance Copy_semantic_Copyable `{!refinedrustGS Σ} {rt} (ty : type rt) : 
  Copy_semantic_interp rt ty →
  Copyable ty.
Proof. done. Qed.
End extra_specs.
