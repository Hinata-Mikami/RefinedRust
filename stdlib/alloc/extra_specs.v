
Section extra_specs.
Context `{!refinedrustGS Σ}.

Global Instance shareable_discard_freeable {rt Self_rt : RT} (A : Allocator_spec_attrs Self_rt) π κ κs a l n (r : rt) (assumptions : Prop) :
  Shareable π κ κs r assumptions (A.(Allocator_FreeablePerm) a l n) := shareable_discard _ _ _ _ _ _.
Global Instance ghost_droppable_discard_freeable {Self_rt : RT} (A : Allocator_spec_attrs Self_rt) a l n :
  GhostDroppable (A.(Allocator_FreeablePerm) a l n) := ghost_droppable_discard _.

Definition FindAllocatorFreeable {Self_rt : RT} (A_attr : Allocator_spec_attrs Self_rt) (x : RT_xt Self_rt) (l : loc) :=
  {| fic_A := (nat); fic_Prop size := Allocator_FreeablePerm A_attr x l size |}.
Global Typeclasses Opaque FindAllocatorFreeable.

Global Instance related_to_allocator_freeable {Self_rt : RT} (A_attr : Allocator_spec_attrs Self_rt) x l n : RelatedTo (Allocator_FreeablePerm A_attr x l n) | 100 :=
  {| rt_fic := FindAllocatorFreeable A_attr x l |}.

Lemma subsume_allocator_freeable {Self_rt : RT} (A_attr : Allocator_spec_attrs Self_rt) x1 x2 l1 l2 n1 n2 T :
  ⌜l1 = l2⌝ ∗ ⌜n1 = n2⌝ ∗ ⌜x1 = x2⌝ ∗ T
  ⊢ subsume (Allocator_FreeablePerm A_attr x1 l1 n1) (Allocator_FreeablePerm A_attr x2 l2 n2) T.
Proof.
  iIntros "(-> & -> & -> & $)". eauto.
Qed.
Definition subsume_allocator_freeable_inst := [instance @subsume_allocator_freeable].
Global Existing Instance subsume_allocator_freeable_inst.

Lemma find_in_context_allocator_freeable {Self_rt : RT} (A_attr : Allocator_spec_attrs Self_rt) x l T :
  (∃ n, Allocator_FreeablePerm A_attr x l n ∗ T n)
  ⊢ find_in_context (FindAllocatorFreeable A_attr x l) T.
Proof.
  iDestruct 1 as (n) "(Ha & HT)".
  iExists n. by iFrame.
Qed.
Definition find_in_context_allocator_freeable_inst := [instance @find_in_context_allocator_freeable with FICSyntactic].
Global Existing Instance find_in_context_allocator_freeable_inst | 1.

End extra_specs.
