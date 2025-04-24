#![allow(unused)]

#[rr::name("MYINT")]
static MYINT: i32 = 42;

#[rr::requires("static_has_refinement \"MYINT\" 42")]
#[rr::returns("42")]
fn read_static_1() -> i32 {
    MYINT
}

#[rr::params("x")]
#[rr::requires("static_has_refinement \"MYINT\" x")]
#[rr::returns("x")]
fn ref_static_1() -> &'static i32 {
    &MYINT
}

#[rr::requires("static_has_refinement \"MYINT\" 42")]
fn read_static_2() {
    let r = ref_static_1();
    let _ = *r;
}

#[rr::params("x")]
#[rr::requires("static_has_refinement \"MYINT\" x")]
#[rr::returns("Some x")]
fn ref_static_2() -> Option<&'static i32> {
    Some(&MYINT)
}

#[rr::requires("static_has_refinement \"MYINT\" 42")]
fn read_static_3() {
    let r = ref_static_2();
    let r2 = r.unwrap();
    let _ = *r2;
}

#[rr::requires("static_has_refinement \"MYINT\" 42")]
#[rr::returns("*[ 42; 42 ]")]
fn read_static_4() -> (i32, i32) {
    (MYINT, MYINT)
}
