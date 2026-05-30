Global Instance shareable_discard_freeable `{!refinedrustGS Σ} {Self_rt : RT} (A : Allocator_spec_attrs Self_rt) π κ κs a l n :
  Shareable π κ κs (A.(Allocator_FreeablePerm) a l n) := shareable_discard _ _ _ _.
Global Instance ghost_droppable_discard_freeable `{!refinedrustGS Σ} {Self_rt : RT} (A : Allocator_spec_attrs Self_rt) a l n :
  GhostDroppable (A.(Allocator_FreeablePerm) a l n) := ghost_droppable_discard _.
