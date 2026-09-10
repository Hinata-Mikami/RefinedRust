---
name: refinedrust-specifications
description: Explains how to write RefinedRust specifications, add Rocq definitions used by them, and diagnose generated_specs_*.v errors. Use for rr annotations, extra_specs, rr::import, crate-local theories, or generated specification failures.
---

# RefinedRust Specifications

Use this skill to write Rust-level specifications and supply the Rocq definitions
they reference. The full attribute reference is the
[specification-language wiki](https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/wikis/specification-language).

## Write Specifications

Start with inferred argument specifications. RefinedRust automatically creates
refinement parameters named after Rust arguments, so simple contracts need only
state their precondition and result:

```rust
#[rr::requires("x + 42 ∈ i32")]
#[rr::returns("x + 42")]
fn add_42(x: i32) -> i32 { x + 42 }
```

Build contracts with these attributes:

- `requires` states a precondition. It and other propositions may be named so
  later clauses and proofs can refer to the hypothesis.
- `returns` gives the return refinement. Without it, use `ret` in `ensures` to
  constrain the inferred result.
- `exists` introduces refinement variables produced by the function.
- `ensures` states postconditions, and `observe` updates an argument's ghost
  refinement.
- `context` adds assumptions available throughout the specification.

For mutable references, use `.cur` for the current value and `.ghost` for the
post-call ghost value. Project tuples and plain structs with syntax such as
`x.:1`.

Use explicit `params` only when the inferred parameters are insufficient. `
params` declares mathematical variables.

Specification strings are inserted into generated Rocq nearly verbatim. Use
the Rust-level `{...}` escapes described by the wiki for types, lifetimes,
associated types, trait attributes, and closure captures; double braces emit
literal braces. Proposition forms include pure propositions and explicit
`#iris`, `#type`, and `#linktime` forms.

For structs, use `refined_by` to declare the refinement, annotate fields with
their refinements, and add `exists` or `invariant` as needed. Invariants can
also use `#iris`, `#type`, `#own`, or `#shr`. For enums, use top-level
`refined_by` with variant `pattern` and `refinement`, or use `refine_as` for a
generated Rocq refinement type.

Use `verify` to request verification. Controls such as `only_spec`, `skip`,
`trust_me`, and `export_as` change generation or export behavior; do not use
`trust_me` as a substitute for a completed verification. See
`case_studies/evenint/src/lib.rs` for small contracts and
`case_studies/minivec/src/lib.rs` for complex ADTs and ownership specifications.

## Add Rocq Definitions

When a specification string refers to a custom Rocq definition or lemma, put it
in `theories/<module>.v` rather than generated output. Add a `theories/dune`
file modeled on the crate's package and logical namespace:

```lisp
(rocq.theory
 (flags -w -notation-overridden -w -redundant-canonical-projection)
 (package <dune-package>)
 (name <logical-prefix>.theories)
 (generate_project_file)
 (theories stdpp iris iris_contrib Ltac2 Equations lrust radium lithium refinedrust Stdlib))
```

Include every imported Rocq library in `theories`. Avoid cycles: a theory used
by generated specifications cannot depend on those specifications.

Import the module from the narrowest Rust scope that needs it:

```rust
#![rr::import("<logical-prefix>.theories", "<module>")]
```

Rerun `cargo refinedrust`; it propagates the import and generated Dune
dependencies. Never edit `output/**/generated/dune` or
`output/**/proofs/dune` to add the theory manually.

For nested libraries, give the nested directory its own `dune` file and full
logical name. Match `package` to one declared by the surrounding Dune project.

Use these examples:

- `stdlib/mem/theories/` and its `shims` import
- `stdlib/vec/theories/` and its `vec` import
- `stdlib/closures/theories/` for related modules
- `stdlib/spin/theories/once/` for a nested library
- `case_studies/extra_proofs/minivec/` for a separate shared package

## Fix Specification Errors

Run `cargo refinedrust` in the crate root, followed by `dune build`. A frontend
error generally points directly to an invalid attribute or Rust-level escape.
A Rocq error in
`output/<crate>/generated/generated_specs_<crate>.v` usually originates in a
Rust `rr` annotation, configured `extra_specs`, or imported theory definition.

1. Inspect the generated diagnostic and failing sentence to locate the source
   annotation or definition. Because most specification text is inserted
   literally, search for a distinctive fragment in the Rust source.
2. Check for malformed Rocq syntax, an identifier missing from imports, a term
   in the wrong scope, a proposition or refinement of the wrong type, or an
   argument/result shape inconsistent with the Rust type.
3. Fix the Rust source, `extra_specs` file, or reusable theory. Do not patch the
   generated file, which will be overwritten.
4. Rerun `cargo refinedrust`, then `dune build`.

When imports or output layout appear wrong, inspect `rr::package`,
`rr::coq_prefix`, `rr::include`, `rr::export_include`, `rr::import`,
`extra_specs`, `lib_load_paths`, and `output_dir` in the crate configuration and
attributes.
