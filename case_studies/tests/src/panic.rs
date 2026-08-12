// Unwind specifications describe the exceptional outcome of a function call.
// `returns` and `ensures` apply only to the regular return branch. On the unwind branch,
// the caller learns the function's unwind condition and continues at the MIR unwind target.
//
// Unwinding is opt-in per function: without a `may_unwind_if` annotation, the unwind condition
// is False. `may_unwind_if("True")` permits an unwind without a more precise condition.
//
// `may_unwind_if("P")` means that an unwind is permitted only if P holds; it does not guarantee
// that the function unwinds when P holds. In particular, the regular return branch does not
// receive the negation of P. Multiple annotations describe alternative unwind causes and are
// combined by disjunction.

#[rr::may_unwind_if("x + 42 ∉ i32")]
#[rr::returns("x + 42")]
fn add_42(x: i32) -> i32 {
    x + 42
}

// An imprecise specification still has to opt in explicitly.
#[rr::may_unwind_if("True")]
#[rr::verify]
fn xyz() {
    panic!();
}

// A failing MIR assertion calls the same panic shim as an explicit panic.
#[rr::may_unwind_if("True")]
#[rr::verify]
fn assert_may_panic(b: bool) {
    assert!(b);
}

// Calling a potentially unwinding function requires the caller to expose an unwind condition
// covering the callee's unwind condition. Normal postconditions remain independent of it.
#[rr::may_unwind_if("True")]
#[rr::returns("5")]
fn call_xyz() -> i32 {
    xyz();
    5
}

// Multiple possible causes form a disjunction: this function may panic only if
// `x == 0 ∨ y == 0`.
#[rr::may_unwind_if("x = 0")]
#[rr::may_unwind_if("y = 0")]
fn either_zero(x: i32, y: i32) {
    if x == 0 || y == 0 {
        panic!();
    }
}

// Unwinding drops `x`; if that drop panics, the generated cleanup terminates.
#[rr::may_unwind_if("True")]
fn panic_with_cleanup<T>(_x: T) {
    panic!();
}

// Assertion failure unwinds through the cleanup that drops `x`.
#[rr::may_unwind_if("True")]
#[rr::verify]
fn assert_with_cleanup<T>(x: T, b: bool) {
    assert!(b);
    drop(x);
}

#[rr::params("p" : "{F::Params}")]
#[rr::requires(#iris "{F::Pre} π p x tt")]
#[rr::may_unwind_if("{F::UnwindCondition} x p tt")]
fn call_clos<F>(x: F)
where
    F: Fn(),
{
    x();
}

#[rr::params("x")]
#[rr::args("x")]
#[rr::may_unwind_if("x = 0")]
fn call_conditional_closure(x: i32) {
    let clos = #[rr::may_unwind_if("x = 0")]
    |x: i32| {
        if x == 0 {
            panic!();
        }
    };
    clos(x);
}

#[rr::params("x")]
#[rr::args("x")]
#[rr::may_unwind_if("x = 0 ∨ x = 1")]
fn call_captured_closure(x: i32) {
    let clos = #[rr::may_unwind_if("{x} = 0")]
    #[rr::may_unwind_if("{x} = 1")]
    || {
        if x == 0 || x == 1 {
            panic!();
        }
    };
    clos();
}

// No annotation is the way to require panic freedom; a separate
// `panic_ensures("False")` annotation is unnecessary.
#[rr::verify]
fn does_not_panic() {}

// The original panic path resumes unwinding after dropping `x`. A panic from that drop would
// terminate, but must not let this panic-free function avoid proving the assertion cannot fail.
#[rr::verify]
fn panic_free_with_cleanup<T>(x: T, b: bool) {
    assert!(b || !b);
    drop(x);
}
