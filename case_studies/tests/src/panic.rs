// Panic specifications describe a second, exceptional outcome of a function call.
// `returns` and `ensures` apply only to the regular return branch. On the panic branch,
// the caller learns the function's panic condition and continues at the MIR unwind target.
//
// Panics are opt-in per function: without a `may_panic_if` annotation, the panic condition
// is False, preserving RefinedRust's current panic-free behavior. `may_panic_if("True")` is
// the explicit escape hatch for a function that may panic without a more precise condition.
// There is no separate allow-panics mode that implicitly weakens panic conditions to True.
//
// `may_panic_if("P")` means that a panic is permitted only if P holds; it does not guarantee
// that the function panics when P holds. In particular, the regular return branch does not
// receive the negation of P. Multiple annotations describe alternative panic causes and are
// combined by disjunction.

#[rr::may_panic_if("x + 42 ∉ i32")]
#[rr::returns("x + 42")]
fn add_42(x: i32) -> i32 {
    x + 42
}

// An imprecise specification still has to opt in explicitly.
#[rr::may_panic_if("True")]
#[rr::verify]
fn xyz() {
    panic!();
}

// Calling a potentially panicking function requires the caller to expose a panic condition
// covering the callee's panic condition. Normal postconditions remain independent of it.
#[rr::may_panic_if("True")]
#[rr::returns("5")]
fn call_xyz() -> i32 {
    xyz();
    5
}

// Multiple possible causes form a disjunction: this function may panic only if
// `x == 0 ∨ y == 0`.
#[rr::may_panic_if("x = 0")]
#[rr::may_panic_if("y = 0")]
fn either_zero(x: i32, y: i32) {
    if x == 0 || y == 0 {
        panic!();
    }
}

// Unwinding drops `x`; if that drop panics, the generated cleanup terminates.
#[rr::may_panic_if("True")]
fn panic_with_cleanup<T>(_x: T) {
    panic!();
}

#[rr::params("p" : "{F::Params}")]
#[rr::requires(#iris "{F::Pre} π p x tt")]
#[rr::may_panic_if("{F::PanicCondition} x p tt")]
fn call_clos<F>(x: F)
where
    F: Fn(),
{
    x();
}

#[rr::params("x")]
#[rr::args("x")]
#[rr::may_panic_if("x = 0")]
fn call_conditional_closure(x: i32) {
    let clos = #[rr::may_panic_if("x = 0")]
    |x: i32| {
        if x == 0 {
            panic!();
        }
    };
    clos(x);
}

#[rr::params("x")]
#[rr::args("x")]
#[rr::may_panic_if("x = 0 ∨ x = 1")]
fn call_captured_closure(x: i32) {
    let clos = #[rr::may_panic_if("{x} = 0")]
    #[rr::may_panic_if("{x} = 1")]
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
