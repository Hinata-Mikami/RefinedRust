
// WIP: handle obligations on associated types
/*
mod bla {
    trait Bupsed {

    }

    #[rr::exists("bb" : "{xt_of BB}")]
    trait Bar {
        type BB: Bupsed;
    }
    
    trait Foo {
        type FB: Bar;

        // this specification should maybe depend on Bar
        // i.e. I need the trait attributes of Bar
        //
        // For now, this is also problematic because we do not add FB's env here.
        #[rr::verify]
        #[rr::returns("{Self::FB::bb}")]
        fn bla() -> <<Self as Foo>::FB as Bar>::BB;
    }
    // Should the attrs record be allowed to depend on the attrs record of Bar?
    // I don't think so. This is different from a normal trait context assumption, so it shouldn't
    // depend on that. This is an obligation at the impl site, not a requirement.
    //
    // Can the attrs record depend on the associated type? I hope not.
    //
    // Can the spec record depend? Yeah, it should be allowed to depend on the obligation assoc types, because the type signature of the functions may depend on that.
    // not attrs.


    // Issue here: I see the obligation as a Self requirement and thus do not add it to the env.
    // Probably this shouldn't be just skipped. 
    // how do I handle the trait's own associated types? I guess they cannot be normalized.

    impl Bupsed for bool {

    }

    #[rr::instantiate("bb" := "true")]
    impl Bar for u32 {
        type BB = bool;
    }

    impl Foo for i32 {
        type FB = u32;
    
        #[rr::default_spec]
        fn bla() -> bool {
            true
        }
    }

    impl<T: Bar> Foo for (u32, T) {
        type FB = T;

        #[rr::default_spec]
        fn bla() -> <T as Bar>::BB {
            unimplemented!();
        }
    }

    #[rr::verify]
    fn foo<T>() 
        where T: Foo<FB = u32>,
              T::FB: Bar<BB = bool>
    {

    }
}
*/

// I want an example where I need to distinguish different sources of trait requirements.
mod dep {
    trait Bar {
        type BT;
    }

    trait Foo<T: Bar> {
        type FT;

        // Q: How dependent should the base spec be on the spec of Bar, for either of the two
        // occurrences?
        // The spec can definitely depend on the associated types of the two trait impls.
        // We should also be able to use their attributes, I think.
        #[rr::params("x")]
        #[rr::args("x")]
        fn foofoo<U: Bar>(x: U);
    }


    #[rr::verify]
    fn foo<T, U>(x: U) where U : Foo<T>, T: Bar {

    }

    #[rr::verify]
    fn bar<T, U>(x: T) where T: Bar {

    }

    impl Bar for i32 {
        type BT = bool;

    }
    impl<T: Bar> Foo<T> for u32 {
        type FT = usize;

        #[rr::verify]
        fn foofoo<U: Bar>(x: U) {

        }
    }

    #[rr::verify]
    fn call_foo() {
        <u32 as Foo<i32>>::foofoo(42);
    }
}

mod dep2 {
    trait Bar<T> {
        type BT;
    }

    trait Foo<T: Bar<i32>, W: Bar<T>> 
    {
        type FT;

        #[rr::verify]
        fn foofoo<U: Bar<W>>(x: U, y: W);
    }
}


/// Check that lifetime parameters are resolved correctly.
mod dep6 {
    trait Foo { }

    impl<'a, T> Foo for &'a T {  }


    #[rr::verify]
    fn foo<U: Foo>(x: U) {
    }

    #[rr::verify]
    fn call_foo<T>(x: T) {
        foo(&x);
    }
}


/// HRTB tests
mod dep5 {
    trait Foo<T> {
        
        #[rr::verify]
        fn foo(&self, x: T);
    }

    trait Bar 
        where Self: for<'a> Foo<&'a i32>
    {

    }


    #[rr::verify]
    fn bla<T>(x : T) where for<'a> T: Foo<&'a i32> {

    }

    impl<'a> Foo<&'a i32> for i32 {
        #[rr::default_spec]
        fn foo(&self, x: &'a i32) {

        }
    }

    #[rr::verify]
    fn call_bla2() {
        bla(42);
    }


    #[rr::verify]
    fn blub<T>(x : T) where for<'a> T: Foo<&'a &'a i32> {

    }

    #[rr::verify]
    // need to pass down the quantified trait requirement and specialize it
    fn call_blub<T>(x: T) where for<'a, 'b> T: Foo<&'a &'b i32> {
        blub(x)
    }

    #[rr::verify]
    fn call_inst<T>(x: T) where for<'a, 'b> T: Foo<&'a &'b i32> {
        let y = 42;
        let y_ref = &y;

        x.foo(&y_ref);
    }
}


mod dep7 {
    trait Foo {

    }

    #[rr::verify]
    fn bla<T : Foo>(x: T) {

    }

    impl<'a> Foo for &'a i32 {

    }

    #[rr::verify]
    fn call_bla() {
        let x = 42;
        bla(&x);
    }
}

mod dep4 {

    trait Bar {
        type BT;
    }

    trait Foo: Bar {

        #[rr::exists("x")]
        #[rr::returns("x")]
        fn foo() -> Self::BT;
    }
}

mod dep3 {
    trait Bar {

    }

    trait Foo<T: Bar> {

        #[rr::verify]
        fn foofoo(x: T);
    }

    impl Bar for i32 {

    }

    // the `T: Bar` can be directly dispatched with a concrete instance
    // TODO this does not work currently.
    // We should maybe make the spec still be parametric, but then instantiate that in the lemma
    // statement with the statically known instance.
    #[rr::skip]
    impl Foo<i32> for i32 {

        #[rr::default_spec]
        fn foofoo(x: i32) {

        }
    }

    // parametric dispatch
    impl<T: Bar> Foo<T> for u32 {

        #[rr::default_spec]
        fn foofoo(x: T) {

        }
    }
}
