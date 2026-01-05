#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

fn main() {
    logic();
    logic_struct();
}

#[rr::params(x : "Z", "γ")]
#[rr::args("(#x, γ)")]
#[rr::requires("x + 42 ∈ i32")]
#[rr::observe(#iris "Res γ (x + 42)")]
fn mut_ref_add_42(x : &mut i32) {
    *x += 42;
}

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


#[rr::params("v": "Z", "γ")]
#[rr::args("(#v, γ)")]
#[rr::requires("(v + 42)%Z ∈ i32")]
#[rr::observe("γ": "v + 42")]
fn pointer_add_42(ptr: &mut Data) {
    ptr.value += 42;
}

#[rr::returns("()")]
fn logic_struct() {
    let mut d = Data { value: 1 };
    let p = &mut d.value;
    mut_ref_add_42(p);
    assert!(d.value == 43);
}
