---
name: refinedrust-verification
description: Guides end-to-end RefinedRust verification and classifies cargo refinedrust or dune build failures. Use for broad RefinedRust verification tasks before specializing in generated specifications, theories, or Rocq proofs.
---

# RefinedRust Verification

Use this skill to run and triage the verification pipeline. Load the specialized
skill named below once the failing stage is known.

## Workflow

1. Find the crate root containing `Cargo.toml` and `RefinedRust.toml`.
2. Read relevant crate-level `rr` attributes and RefinedRust configuration.
3. Run `cargo refinedrust` from the crate root.
4. Run `dune build` in the relevant Dune workspace.
5. Fix the first actionable failure and repeat the narrowest useful check.

## Classify Failures

- A frontend failure from `cargo refinedrust` belongs in the Rust code,
  annotations, configuration, or imported `.rrlib` dependencies.
- An error in `generated_specs_<crate>.v` indicates invalid Rocq syntax or types
  originating in an annotation, `extra_specs`, or imported theory. Load
  `refinedrust-specifications`.
- Work involving `rr::import`, Dune theory libraries, or reusable files under
  `theories/` also uses `refinedrust-specifications`.
- An error in `output/<crate>/proofs/proof_*.v`, `liRStep`, or a side condition
  requires interactive Rocq work. Load `refinedrust-proofs`.

## Artifact Rules

- Treat `output/<crate>/generated/` as disposable generated output. Inspect it
  to locate errors, but fix the source and regenerate it.
- Treat `output/<crate>/proofs/proof_*.v` as persistent proof files intended for
  manual edits and version control.
- Do not manually wire generated `generated/dune` or `proofs/dune` files.

Verification is complete when `cargo refinedrust` succeeds, all persistent
proofs check without admitted obligations, and `dune build` succeeds.
