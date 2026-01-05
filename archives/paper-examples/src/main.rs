#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]

// Examples from Section 2


fn main() {

}


#[rr::params("x" : "Z")]
#[rr::args("#x")]
#[rr::requires("x + 42 ∈ i32")]
#[rr::returns("#(x + 42)")]
fn box_add_42(mut r : Box<i32>) -> Box<i32> {
    *r += 42;
    r
}

#[rr::params(x : "Z", "γ" : "gname")]
#[rr::args("(#x, γ)")]
#[rr::requires("x + 42 ∈ i32")]
#[rr::ensures(#iris "Res γ (x + 42)")]
fn mut_ref_add_42(r : &mut i32) {
    *r += 42;
}

#[rr::returns("()")]
fn mut_ref_add_client() {
    let mut z = 1; mut_ref_add_42(&mut z); assert!(z == 43);
}

#[rr::returns("()")]
fn assert_pair() {
    let mut x = (0, 1);
    let xr = &mut x.0;
    *xr = 42;
    assert!(x.0 == 42 && x.1 == 1);
}

