

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


// This has a late bound and no early bound.
#[rr::verify]
fn foo(x: &i32) {

}

// This becomes an early bound.
#[rr::verify]
fn foo2<'a:'a>(x: &'a i32) {

}

struct Foo { }

impl<'a> Foo {
    #[rr::verify]
    fn bla(&'a self) {

    }
}


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
