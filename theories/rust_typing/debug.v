From refinedrust Require Export automation.
From refinedrust Require Import options.

(** * File to import for debugging sidecondition solving *)

Ltac hooks.shelve_sidecond_hook ::=
    match goal with
    | |- False => fail 4
    | |- _ => idtac
    end.
