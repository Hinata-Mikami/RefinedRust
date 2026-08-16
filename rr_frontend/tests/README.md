# UI Tests

This directory contains the `tests` crate UI regression tests.

## Harness

- The test entrypoint is `tests/tests/ui.rs`.
- It uses separate `ui_test` suites for failures and successful verification cases.
- Failure cases live under `tests/fail/`; successful cases live under `tests/success/`.
- The compiler under test is `target/debug/refinedrust-rustc`.
- The harness sets `RR_VERIFY_DEPS=true` for all UI tests.

## Default Mode

- The harness is annotation-first by default.
- That means failing tests normally use inline `//~` annotations instead of relying only on `.stderr` files.
- `ui_test` in this repo does not provide a built-in per-test directive to disable annotation requirements.

Successful tests should start with `//@check-pass`.

## `//@stderr-only`

The harness defines a custom per-test directive:

```rust
//@stderr-only
```

- This switches that test to stderr-only checking by setting `require_annotations = false`.
- Use it when the diagnostic is awkward to express with `//~` annotations and a full `.stderr` golden file is clearer.
- For these tests, keep the `.rs` input in `tests/fail/` and add a matching `.stderr` file next to it.

## File Layout

Typical stderr-only test:

```text
tests/fail/unknown-enum-variant-attr.rs
tests/fail/unknown-enum-variant-attr.stderr
```

## Running Tests

Run the UI suite with:

```sh
CARGO_INCREMENTAL=0 cargo test -p tests --test ui
```

If a `.stderr` file needs to be refreshed, bless the outputs:

```sh
CARGO_INCREMENTAL=0 cargo test -p tests --test ui -- --bless
```

This is the easiest way to capture the exact normalized output expected by `ui_test`.

## Practical Notes

- `.stderr` matching is exact after `ui_test` normalization.
- Trailing blank lines matter because they are part of the normalized golden output.
- If a stderr-only test fails with an output diff that looks visually identical, re-bless first before assuming the diagnostic changed.
