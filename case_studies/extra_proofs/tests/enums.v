From refinedrust Require Import typing.

Inductive sizes :=
 | Sz1
 | Sz2.

Global Instance sizes_inhabited : Inhabited sizes := populate Sz1.

Global Instance sizes_eqdec : EqDecision sizes.
Proof. solve_decision. Defined.

Canonical Structure sizesRT := directRT sizes.
