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
