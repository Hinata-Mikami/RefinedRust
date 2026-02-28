#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

fn main() {
}

/// paper_exampleでは可変参照を値とghost変数(γ)?の組として扱ったが...
// #[rr::params(x : "Z", "γ")]
// #[rr::args("(x, γ)")]
// #[rr::requires("(x + 42)%Z ∈ i32")]
// #[rr::observe("γ": "x + 42")]
/// ok
#[rr::params("x")]
#[rr::args("x")]
#[rr::requires("(x.cur + 42)%Z ∈ i32")]
#[rr::observe("x.ghost": "x.cur + 42")]
fn mut_ref_add_42(x : &mut i32) {
    *x += 42;
}

/// ok
#[rr::returns("()")]
fn logic() {
    let mut x = 1;
    let xr = &mut x;
    mut_ref_add_42(xr);
    assert!(x == 43);
}


#[rr::refined_by("v": "Z")]
struct Data {
    #[rr::field("v")]
    value: i32,
}

// ok
#[rr::params("ptr")]
#[rr::args("ptr")]
#[rr::requires("(ptr.cur + 42)%Z ∈ i32")]
#[rr::observe("ptr.ghost": "ptr.cur + 42")]
fn pointer_add_42(ptr: &mut Data) {
    ptr.value += 42;
}

// ok
#[rr::returns("()")]
fn logic_struct() {
    let mut d = Data { value: 1 };
    let p = &mut d.value;
    mut_ref_add_42(p);
    assert!(d.value == 43);
}
