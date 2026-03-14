#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]

#![rr::include("stdlib")]
// #![rr::include("vec")]

/* ok */
#[rr::params("v")]
#[rr::args("v")]
#[rr::requires("length v.cur < MaxInt usize")] // precondition で長さに関する条件を要求
#[rr::requires("size_of_array_in_bytes (IntSynType i32) (2 * length v.cur) ≤ MaxInt isize")]
#[rr::observe("v.ghost" : "<$#> (v.cur ++ [42])")]
fn vec_add_42(v: &mut Vec<i32>) {
    // Rust関数自体をif文でオーバーフローしないように修正
    v.push(42);
}

// #[rr::params("v")]
// #[rr::args("v")]
// #[rr::observe("v.ghost" : "(v.cur ++ [42])")]
// fn vec_add_42_avoid_overflow(v: &mut Vec<i32>) {
//     if v.len() < 1000000 {
//         v.push(42);
//     }
// }

/* まだ */
#[rr::returns("()")]
fn main() {
    let mut v = Vec::new();
    vec_add_42(&mut v);

    assert!(v[0] == 42);
}
