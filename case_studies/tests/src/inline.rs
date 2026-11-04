#[rr::inline]
fn fct_inlined_id<T>(x: T) -> T {
    x
}

#[rr::params(x : "Z")]
#[rr::args("x")]
#[rr::returns("x")]
fn fct_inlined_id_i32(x: i32) -> i32 {
    fct_inlined_id(x)
}

struct InlineMethods;

impl InlineMethods {
    #[rr::inline]
    fn id<T>(x: T) -> T {
        x
    }
}

#[rr::params(x : "Z")]
#[rr::args("x")]
#[rr::returns("x")]
fn fct_inlined_inherent_id_i32(x: i32) -> i32 {
    InlineMethods::id(x)
}

#[rr::verify]
fn fct_inlined_ref_id_i32<'a>(x: &'a i32) -> &'a i32 {
    fct_inlined_ref_id(x)
}

#[rr::inline]
fn fct_inlined_ref_id<'a, T>(x: &'a T) -> &'a T {
    x
}

#[rr::returns("x")]
fn fct_inline_dependency<T>(x: T) -> T {
    x
}

#[rr::inline]
fn fct_inlined_calls_dependency<T>(x: T) -> T {
    fct_inline_dependency(x)
}

#[rr::returns("x")]
fn fct_inlined_calls_dependency_generic<T>(x: T) -> T {
    fct_inlined_calls_dependency(x)
}

#[rr::name("INLINE_STATIC")]
static INLINE_STATIC: i32 = 42;

#[rr::inline]
fn fct_inlined_reads_static() -> i32 {
    INLINE_STATIC
}

#[rr::requires("static_has_refinement \"INLINE_STATIC\" 42")]
#[rr::returns("42")]
fn fct_inlined_reads_static_42() -> i32 {
    fct_inlined_reads_static()
}

#[rr::returns("x")]
fn fct_inline_ref_dependency<'a, T>(x: &'a T) -> &'a T {
    x
}

#[rr::inline]
fn fct_inlined_calls_ref_dependency<'a, T>(x: &'a T) -> &'a T {
    fct_inline_ref_dependency(x)
}

#[rr::returns("x")]
fn fct_inlined_calls_ref_dependency_generic<T>(x: &T) -> &T {
    fct_inlined_calls_ref_dependency(x)
}

#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind}")]
struct InlineGenericMethods<T>(T);

impl<T> InlineGenericMethods<T> {
    #[rr::returns("x")]
    fn dependency(x: T) -> T {
        x
    }

    #[rr::inline]
    fn inline_dependency(x: T) -> T {
        Self::dependency(x)
    }
}

#[rr::returns("x")]
fn fct_inlined_calls_same_impl_dependency<T>(x: T) -> T {
    InlineGenericMethods::<T>::inline_dependency(x)
}

#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind}")]
struct InlineBodyLayout<T>(T);

#[rr::inline]
fn fct_inlined_uses_body_layout<T>(x: T) -> T {
    let wrapped = InlineBodyLayout(x);
    wrapped.0
}

#[rr::returns("x")]
fn fct_inlined_uses_body_layout_generic<T>(x: T) -> T {
    fct_inlined_uses_body_layout(x)
}
