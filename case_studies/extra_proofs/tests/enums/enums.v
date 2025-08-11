From refinedrust Require Import typing.

Inductive sizes :=
 | Sz1
 | Sz2.

Global Instance sizes_inhabited : Inhabited sizes := populate Sz1.

Canonical Structure sizesRT := directRT sizes.
