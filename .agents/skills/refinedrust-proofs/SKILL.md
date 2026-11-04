---
name: refinedrust-proofs
description: Repairs persistent RefinedRust proof_*.v files using interactive ben-mcp Rocq checks. Use for liRStep failures, manual RefinedRust typing steps, shelved goals, side conditions, or failing generated function proofs.
---

# RefinedRust Proofs

Files under `output/<crate>/proofs/proof_*.v` are persistent and intended for
manual edits. Preserve their imports, prelude, and side-condition structure
unless the proof requires a change.

## Interactive Loop

1. Run `ben-mcp_rocq_check_file` with the proof's absolute path.
2. Fix the first diagnostic using its source sentence and proof state.
3. Use `ben-mcp_rocq_run_at` for `Check`, `About`, `Search`, `Locate`, or `Show`
   after imports or immediately before the failure. Run inside a proof only
   when its local context is needed.
4. Edit the proof and check it again. Leave `clear_cache` unset so successful
   sentences remain cached; the MCP rebuilds changed dependencies as needed.
5. Finish with `dune build` after the narrow file check succeeds.

Do not accept `Admitted`, `admit`, or a printed remaining goal as completion.

## Two Proof Phases

A proof commonly has this shape:

```rocq
Proof.
  function_prelude.

  1: rep <-! <3000 liRStep.
  (* Repeat bounded chunks as separate sentences until typing is complete. *)
  (* Temporarily add this next sentence to diagnose the actual failure. *)
  1: rep liRStep; liExplain.
  (* Manual typing steps; then resume with bounded chunks. *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* Manual side-condition proofs. *)
  Unshelve. all: print_remaining_sidecond.
Qed.
```

### Type Checking

The typing phase uses separate `1: rep <-! <3000 liRStep.` sentences. Prefer
this bounded form to plain `rep <-! liRStep` or `repeat liRStep`: `1:` advances
only the first typing goal, separate sentences remain independently cacheable,
and the bound gives predictable stopping while `<-!` preserves backtracking.

When it stops:

- Keep the completed bounded sentences. The last one stops at a useful
  backtracking point, not necessarily at the goal where automation actually
  failed.
- Append `1: rep liRStep; liExplain.` as a separate diagnostic sentence. It
  advances without backtracking to the actual failure; do not replace the
  bounded sentence with it.
- Inspect the guidance, case distinction, Rust program point, open Lithium
  evars, and proof state. Use `liShow` only when more raw-state detail is needed.
- Remove the diagnostic, add the required `liInst`, context operation, rewrite,
  Iris proof-mode step, or manual typing lemma, then resume bounded automation.
- Consult `theories/refinedrust/rust_typing/typing/manual.v` for available manual steps.
- Use `liStart` to return a manually exposed Iris subgoal to Lithium.
- Use `shelve_sidecond` only for a genuine pure obligation to solve later.

Do not start side-condition proofs while `print_remaining_goal` reports a
type-system goal.

### Side Conditions

Keep `sidecond_solver` and `sidecond_hammer` before manual proofs. Inspect each
remaining unshelved goal with the MCP checker or `Show`, then use the hypotheses
from type checking to prove its equality, bound, arithmetic, or list fact.
Prefer identifying a goal by proposition and context rather than incidental goal
number.

### Stable Hypothesis Handling

Give every `#[rr::requires]` and `#[rr::inv]` proposition a semantic hypothesis
name at its declaration site to keep the generated proof context stable:

```rust
#[rr::requires("Hsorted": "revsorted a.cur")]
#[rr::inv("Hupdate": "citation_update_k original a.cur i k")]
```

Flattened conjunctions may retain their name only for the first component. If
components are used independently, declare separately named requirements or
invariants, but do not duplicate equivalent assumptions just to obtain a name.

Do not refer directly to anonymous generated names such as `H12`, `H34`, or
`H89`. These names depend on symbolic-execution details and can change after
regeneration. Use declaration-site names directly. Reserve `rename select` for
facts that cannot be named there, such as branch conditions, specialized
postcondition premises, and facts produced by automation:

```rocq
rename select (revsorted _) into Hsorted.
rename select (_ < length _) into Hindex_bound.
rename select (forall i : nat, _ -> _) into Hprefix.
```

Make the pattern specific enough to select one hypothesis, and use semantic
names such as `Hsorted`, `Hlookup`, `Hbound`, and `Hmono`.

Use stdpp's `opose proof` or `opose proof*` for lemmas with proof premises.
Omit proof arguments already available in the context so they become ordinary
subgoals. Use explicit blocks when premises need distinct or diagnostic proofs:

```rocq
opose proof* (revsorted_lookup_mono a i j) as Hmono.
{ exact Hsorted. }
{ lia. }
{ lia. }
```

Use compact dispatch for routine premises, adding branches for different
automation when needed:

```rocq
opose proof* (some_lemma a x i) as Hresult;
  [done.. | naive_solver |].
```

Do not manually pass conjunction terms, long sequences of proof assumptions,
or proof escapes such as `ltac:(lia)` and `ltac:(done)`. Exposed premise
subgoals keep failures local and scripts stable as generated contexts change.

If a proof relies on manual Rocq definitions introduced for specifications, add
the supporting lemmas needed to reason about them.

Representative proofs:

- `case_studies/minivec/output/minivec/proofs/proof_Vec_T_get_mut.v`
- `case_studies/iterators/output/iterators/proofs/proof_counter.v`
- `case_studies/iterators/output/iterators/proofs/proof_decuple_range.v`
