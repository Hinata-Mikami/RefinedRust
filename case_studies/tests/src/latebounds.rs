

//! This contains some tests regarding Rust's handling of early-bounds vs late-bounds.


trait Bla<T> {
    #[rr::verify]
    fn do_bla(&self, x: T);
}

/// 'a becomes an early bound.
#[rr::verify]
impl<'a> Bla<&'a i32> for u64 {
    fn do_bla(&self, x: &'a i32) {

    }
}

/// Strangely, while the elided impl lifetime is an early bound in terms of behavior, we get an
/// additional late-bound lifetime on the [do_bla] impl.
/// Very strange!
/// We need some workarounds for this in RefinedRust currently, as adding an additional lifetime
/// parameter to a trait method is not something an should do.
#[rr::verify]
impl Bla<&i32> for u32 {
    fn do_bla(&self, x: &i32) {

    }
}

trait ReverseBla<T> {
    #[rr::verify]
    fn do_reverse_bla<'a, 'b>(&'b self, x: &'a i32, extra: T);
}

// The elided trait argument introduces an extra call-region candidate, forcing heuristic
// selection. The method binders occur in reverse order in the signature.
#[rr::verify]
impl ReverseBla<&i32> for u32 {
    fn do_reverse_bla<'a, 'b>(&'b self, x: &'a i32, extra: &i32) {

    }
}


// This has a late bound and no early bound.
#[rr::verify]
fn foo(x: &i32) {

}

// This becomes an early bound.
#[rr::verify]
fn foo2<'a:'a>(x: &'a i32) {

}

#[rr::verify]
fn reverse_late_bound_order<'a, 'b>(x: &'b i32, y: &'a i32) -> (&'a i32, &'b i32) {
    (y, x)
}

#[rr::verify]
fn test_reverse_late_bound_order_distinct() {
    let x = 1;
    let y = 2;
    let _distinct = reverse_late_bound_order(&x, &y);
}

#[rr::verify]
fn test_reverse_late_bound_order_equal(x: &i32) {
    let _equal = reverse_late_bound_order(x, x);
}

#[rr::verify]
fn test_reverse_late_bound_order_fallback() {
    let receiver = 1;
    let argument = 2;
    let extra = 3;
    <u32 as ReverseBla<&i32>>::do_reverse_bla(&receiver, &argument, &extra);
}

struct Foo { }

impl<'a> Foo {
    #[rr::verify]
    fn bla(&'a self) {

    }
}


#[rr::verify]
fn test1() {
    let a = 5;
    let b = 3;
    let c = 4;
    <u32 as Bla<&i32>>::do_bla(&a, &b);

    <u64 as Bla<&i32>>::do_bla(&c, &b);
}


fn main<'b>() {
    //let foo: for<'a> fn(&'a i32) = foo;

    let f: for<'a> fn(&'a u32, &'b i32) = <u32 as Bla::<&'b i32>>::do_bla;
    //let f = &<u32 as Bla::<&i32>>::do_bla;

    //let f: fn(&u32, &i32) = <u32 as Bla<&i32>>::do_bla;

    //f(0, &1);

    //f(0, &2);
}
