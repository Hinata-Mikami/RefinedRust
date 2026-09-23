/// Ambient DropGlue attributes may instantiate an attribute value without
/// becoming indices of the trait's attribute record type.
mod drop_glue_attributes {
    #[rr::exists("MayUnwind" : "Prop")]
    trait Consume<T> {
        #[rr::params("x")]
        #[rr::args("x")]
        #[rr::may_unwind_if("{T::DropGlueUnwind}")]
        fn consume(value: T);
    }

    #[rr::instantiate("MayUnwind" := "{T::DropGlueUnwind}")]
    impl<T> Consume<T> for () {
        #[rr::params("x")]
        #[rr::args("x")]
        #[rr::may_unwind_if("{T::DropGlueUnwind}")]
        fn consume(value: T) {
            drop(value);
        }
    }

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
    fn call_generic<T, C: Consume<T>>(value: T) {
        C::consume(value);
    }

    fn call_concrete() {
        <() as Consume<i32>>::consume(42);
    }
}

/// Trait requirements on associated types are unfolded transitively.
mod bla {
    trait Bupsed {}

    trait Bar {
        type BB: Bupsed;
    }

    trait Foo {
        type FB: Bar;
    }

    #[rr::verify]
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("x")]
    fn roundtrip<T: Foo>(x: <<T as Foo>::FB as Bar>::BB) -> <<T as Foo>::FB as Bar>::BB {
        x
    }
}

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
        #[rr::may_unwind_if("{U::DropGlueUnwind}")]
        fn foofoo<U: Bar>(x: U);
    }


    #[rr::verify]
    #[rr::may_unwind_if("{U::DropGlueUnwind}")]
    fn foo<T, U>(x: U) where U : Foo<T>, T: Bar {

    }

    #[rr::verify]
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
    fn bar<T, U>(x: T) where T: Bar {

    }

    impl Bar for i32 {
        type BT = bool;

    }
    impl<T: Bar> Foo<T> for u32 {
        type FT = usize;

        #[rr::verify]
        #[rr::may_unwind_if("{U::DropGlueUnwind}")]
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
    #[rr::may_unwind_if("{U::DropGlueUnwind}")]
    fn foo<U: Foo>(x: U) {
    }

    #[rr::verify]
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
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
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
    fn bla<T>(x : T) where for<'a> T: Foo<&'a i32> {

    }

    #[rr::verify]
    impl<'a> Foo<&'a i32> for i32 {
        fn foo(&self, x: &'a i32) {

        }
    }

    #[rr::verify]
    fn call_bla2() {
        bla(42);
    }


    #[rr::verify]
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
    fn blub<T>(x : T) where for<'a> T: Foo<&'a &'a i32> {

    }

    #[rr::verify]
    // need to pass down the quantified trait requirement and specialize it
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
    fn call_blub<T>(x: T) where for<'a, 'b> T: Foo<&'a &'b i32> {
        blub(x)
    }

    #[rr::verify]
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
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
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
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
        #[rr::may_unwind_if("{T::DropGlueUnwind}")]
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

        fn foofoo(x: i32) {

        }
    }

    // parametric dispatch
    #[rr::verify]
    impl<T: Bar> Foo<T> for u32 {

        #[rr::may_unwind_if("{T::DropGlueUnwind}")]
        fn foofoo(x: T) {

        }
    }
}
