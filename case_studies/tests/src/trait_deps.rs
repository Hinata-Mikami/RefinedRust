
/*
// I want an example where I need to distinguish different sources of trait requirements.
mod dep {
    trait Bar {
        type BT;
    }

    // TODO: we are not translating this decl currently
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


    //#[rr::params("x")]
    //#[rr::args("x")]
    fn foo<T, U>(x: U) where U : Foo<T>, T: Bar {

    }

    #[rr::params("x")]
    #[rr::args("x")]
    fn bar<T, U>(x: T) where T: Bar {

    }

    impl Bar for i32 {
        type BT = bool;

    }
    impl<T: Bar> Foo<T> for u32 {
        type FT = usize;

        #[rr::params("x")]
        #[rr::args("x")]
        fn foofoo<U: Bar>(x: U) {

        }
    }

    //#[rr::verify]
    fn call_foo() {
        <u32 as Foo<i32>>::foofoo(42);
        //foo::<i32, u32>(53u32);
    }
}
*/

mod dep2 {
    trait Bar<T> {
        type BT;
    }

    // TODO: we are not translating this decl currently
    // -- here, I guess I'm trying to resolve this trait requirement -- but there's no solution?
    trait Foo<T: Bar<i32>, W: Bar<T>> 
    {
        type FT;

        #[rr::params("x", "y")]
        #[rr::args("x", "y")]
        fn foofoo<U: Bar<W>>(x: U, y: W);
    }
}

