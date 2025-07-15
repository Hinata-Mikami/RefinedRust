#![allow(unused)]

/// Using closure arguments
#[rr::verify]
// NOTE: the params needs to be put into the trait_incl assumption!
//#[rr::params("c" : "Z")]
// For the general form, we don't have syntactic sugar. 
#[rr::requires(#trait T::Pre := "λ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ ret, (∃ c : Z, ⌜ret = c⌝)%I")]
//#[rr::require(#closure "T" : "True" -> "∃ c : Z, ret = c")]
//#[rr::closure_computes("T", "λ _, c")]
//#[rr::params("f" : "() → Z")]
//#[rr::require(#assume "{T::Post}": "ret = #(f args_0)")]
//#[rr::require("∃ c, ∀ x, f x = c")]
// TODO: this should make the spec non-trivial
//#[rr::requires(#iris "{T::Pre} ($# x) ()")]
fn closure_test_arg_fnonce_1<T>(x: T) 
    where T: FnOnce() -> i32
{
    let _ = x();
}

#[rr::verify]
fn closure_test_arg_fnonce_2<T>(x: T) 
    where T: FnOnce(i32) -> i32
{
    let r = x(42);
}

#[rr::verify]
#[rr::requires(#trait T::Pre := "λ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _, True%I")]
fn closure_test_arg_fn_1<T>(x: T)
    where T: Fn()
{
    x()
}

// Do I ever want to require how the state changes?
// I guess not, because I don't even know what the state is.
// I mean, I could require that there exists some projection, etc.. but...
#[rr::verify]
fn closure_test_arg_fnmut_1<T>(mut x: T)
    where T: FnMut()
{
    x()
}

// Calling functions with closures


#[rr::verify]
fn closure_test_call_fnonce_0<T>(x: T) 
    where T: FnOnce() -> i32
{
    closure_test_arg_fnonce_1(x);
}

#[rr::verify]
fn closure_test_call_fnonce_1() {
    closure_test_arg_fnonce_1(|| { 42 });
}

#[rr::verify]
fn closure_test_call_fnonce_2() {
    closure_test_arg_fnonce_2(|x| { x + 2});
}

#[rr::verify]
fn closure_test_call_fnmut_1() {
    let mut x = 1;
    closure_test_arg_fnmut_1(|| { x += 2; });
}

#[rr::verify]
fn closure_test_call_fn_1() {
    closure_test_arg_fn_1(|| { });
}


/// Closures with no captures
#[rr::returns("()")]
fn closure_test1() {

    // Fn-closure
    let x =
        #[rr::requires("(2 * x)%Z ∈ i32")]
        #[rr::returns("(2 * x)%Z")]
        |x: i32| {
            x * 2
        };

    // here we call the closure's implementation
    //x(2);
}

#[rr::verify]
fn closure_test8<T, U>(x: T, y: U) 
    where U: FnOnce(T)
{
    let cls = 
        // TODO
        #[rr::skip]
        #[rr::params("a", "w")]
        #[rr::args("a", "w")]
        |a: T, w: U| { w(a) };

    //cls(x, y);
}

#[rr::returns("()")]
fn closure_test12() {

    // Fn-closure
    let x =
        #[rr::requires("(y * x)%Z ∈ i32")]
        #[rr::returns("(y * x)%Z")]
        |x: i32, y: i32| {
            x * y
        };

    // here we call the closure's implementation
    //x(2, 2);
}

fn closure_test6<T>(x: T) {
    let cls = 
        #[rr::params("a")]
        #[rr::args("a")]
        #[rr::returns("a")]
        |a: T| { a };

    //cls(x);
}

/// Closures with shared captures
#[rr::returns("()")]
fn closure_test5() {
    let x = 5;

    // Fn-closure
    let x =
        #[rr::params("i")]
        #[rr::capture("x": "i")]
        #[rr::requires("(2 * i)%Z ∈ i32")]
        #[rr::returns("(2 * i)%Z")]
        || {
            x * 2
        };

    // here we call the closure's implementation
    //x(2);
}

#[rr::returns("()")]
fn closure_test9(z: &i32) {
    let x = 5;

    // Fn-closure
    let x =
        #[rr::params("i", "j")]
        #[rr::capture("x": "i")]
        #[rr::capture("z": "j")]
        #[rr::requires("(j * i)%Z ∈ i32")]
        //#[rr::returns("(j * i)%Z")]
        || {
            x;
            z;
            //x * z
        };

    // here we call the closure's implementation
    //x(2);
}

/// Closures with mutable captures
#[rr::returns("()")]
fn closure_test2() {
    let mut y = 2;

    // here, we prove initialization of the closure

    let mut x =
        // Note: the closure code has a doubly-nested mutable references, since it gets a mutref to
        // the capture also.
        #[rr::params("i")]
        #[rr::capture("y": "i" -> "(2*i)%Z")]
        #[rr::requires("(2 * i)%Z ∈ i32")]
        || { y *= 2; };

    //x();
    //x();

    // here, we deinitialize the closure
    y = y + 1;
}

#[rr::params("a", "γ")]
#[rr::args("(a, γ)")]
#[rr::requires("(4*a)%Z ∈ i32")]
//#[rr::observe("γ" : "(4 * a)%Z")]
#[rr::observe("γ" : "a")]
#[rr::returns("()")]
#[rr::tactics("unsafe_unfold_common_caesium_defs; solve_goal.")]
fn closure_test3(y: &mut i32) {
    let mut z = 5;
    let mut yy = 423;

    let mut x =
        // this effectively takes a mutable reference for initialization
        #[rr::params("i", "j")]
        // TODO: we should specify the projection here.
        #[rr::capture("y" : "i" -> "2*i")]
        #[rr::capture("z" : "j" -> "5*j")]
        #[rr::requires("(2 * i)%Z ∈ i32")]
        #[rr::requires("(5 * j)%Z ∈ i32")]
        || { *y *= 2; z *= 5; };

    //x();
    //x();
}

/*
#[rr::returns("()")]
fn closure_test4(y: &mut i32) {
    let mut z = 5;

    let mut x =
        // this effectively takes a mutable reference for initialization
        #[rr::params("i", "γ", "j", "γj")]
        #[rr::capture_pre("y" : "(i, γ)")]
        #[rr::capture_pre("z" : "(j, γj)")]
        #[rr::capture_post("y" : "(2*i, γ)")]
        #[rr::capture_post("z" : "(5*i, γj)")]
        |x: &mut i32, w: &mut i32| { *y *= z; *x *= *w; };
}
*/

#[rr::verify]
fn closure_test7<T, U>(x: T, y: U) 
    where U: FnOnce(T)
{
    let cls = 
        // TODO
        #[rr::skip]
        #[rr::params("a", "m")]
        #[rr::capture("y": "m")]
        #[rr::args("a")]
        |a: T| { y(a) };

    //cls(x);
}


mod fncoercion {
    fn bla(b: bool) {
        let x = |x: i32| {x };
        // uses ClosureFnPointer coercion to coerce whichever closure we pick to an fn pointer
        // (because there are no captures)
        let z = if b { x } else { |x : i32| { x } };
        // then we use the closure instance for fn pointers
        blub(z);
    }

    fn blub<T>(mut x : T) where T: Fn(i32) -> i32 {
        x(43);
    }
}

// Note: probably I could try to have a more creusot-like language that compiles down to this
// representation

